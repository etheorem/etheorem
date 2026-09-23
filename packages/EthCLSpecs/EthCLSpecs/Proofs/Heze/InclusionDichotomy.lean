import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope
import EthCLSpecs.Proofs.Heze.OnInclusionList
import EthCLLib.Proofs.EngineLaws

/-!
# `EthCLSpecs.Proofs.Heze.InclusionDichotomy`: one honest transaction, two answers

Take the block at root `r`, with the block state `state` at `r`. Take a transaction `tx`
from an honest inclusion list `il` whose committee key is the committee of
`state.slot - 1`. `inclusionList_dichotomy` proves that the envelope handler for `r`
succeeds and records the EL answer for the payload, and that one of two cases holds:

- the answer is `true`, and `tx` is in the payload or `isValidOmission payload tx` holds;
- the answer is `false`, and `UnsatisfiedPayload` holds at every later store `s` that
  meets the four conditions of `LaterStore`: `s` holds the block at `r`; `s` keeps the
  answer at `r`; the current slot of `s` is the slot after the block; and that slot
  increment does not overflow.

The two cases exclude each other, because the answer is a `Bool`. The answer is about the
whole collected list. A `false` answer can come from a transaction of another list, while
`tx` is in the payload. `inclusionList_missing_tx` states the direction for `tx`: if `tx`
is not in the payload and its omission is not valid, the answer is `false`.
`inclusionList_missing_tx_cost` composes that direction with `unsatisfiedPayload_cost`
(`CensorshipCost.lean`). At every such later store, the `getHead` loop continues from
the EMPTY node of `r` when it reaches the pending node, and a child on the EMPTY edge
does not settle the bid of `r`. At the epoch substep where the payment of the bid is
carried (`BidPaymentCarried`), the bid is paid if and only if its entry reaches the
quorum. Before the envelope arrives, a pending node with an unverified payload has only
its EMPTY child (`getNodeChildren_run_pending_unverified`), for any store and root.

The envelope usually arrives in the slot of its block, and fork choice reads the answer
one slot later. The block and answer conditions on the later store are per key at `r`.
So a handler run that writes only other roots keeps them, by
`LawfulFcMap.lookup_insert_ne`, and `onTickPerSlot_run_keeps` shows that a per-slot tick
writes neither the `blocks` nor the `payloadInclusionListSatisfaction` map. The clock
condition holds only in the slot after the block. A second envelope for `r` writes the
answer at `r` again from the IL store of that moment, so the answer can change. No
theorem here covers a whole trace of handler runs.

The theorem states each assumption as a hypothesis. `OnInclusionList.lean` explains the
arrival model: the IL store is the result of the arrival list, from the seed of
`getForkchoiceStore`. The EL satisfies `LawfulInclusionList` for the payload transactions
and for an `isValidOmission` that the reader supplies. The result for the `true` answer
is only as strong as that predicate.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Heze (Preset Config Store State Root ForkChoiceNode BeaconBlock
  ExecutionPayload ExecutionRequests Transaction InclusionList SignedInclusionList
  SignedExecutionPayloadEnvelope ValidatorIndex onExecutionPayloadEnvelope isDataAvailable
  verifyExecutionPayloadEnvelope isInclusionListSatisfied getCurrentSlot
  getInclusionListCommittee getInclusionListDueMs getParentPayloadStatus
  processParentExecutionPayload processBuilderPendingPayments)

section
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- The four conditions on a store `s` later than the store `post` after the envelope
handler, at the block root `r`. `s` holds the block at `r`. `s` keeps the answer of
`post` at `r`. The current slot of `s` is the slot after the block. That slot increment
does not overflow. -/
structure LaterStore (s post : Store map) (r : Root) (rootBlock : BeaconBlock) : Prop where
  /-- `s` holds the block at `r`. -/
  block : FcMap.lookup s.blocks r = some rootBlock
  /-- `s` keeps the answer of `post` at `r`. -/
  answer : FcMap.lookup s.payloadInclusionListSatisfaction r
    = FcMap.lookup post.payloadInclusionListSatisfaction r
  /-- The current slot of `s` is the slot after the block. -/
  currentSlot :
    (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) s).run s
      = .ok (rootBlock.slot + 1, s)
  /-- The slot increment does not overflow. -/
  noOverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot)

/-- `UnsatisfiedPayload` at a later store, when `post` records the answer `false` at
`r`. The lemma needs no arrival model: any caller that knows the recorded `false` can
use it. -/
theorem unsatisfiedPayload_of_recorded_false {s post : Store map} {r : Root}
    {rootBlock : BeaconBlock} (h : LaterStore s post r rootBlock)
    (hfalse : FcMap.lookup post.payloadInclusionListSatisfaction r = some false) :
    UnsatisfiedPayload s r rootBlock :=
  ⟨h.block, h.currentSlot, h.noOverflow, h.answer.trans hfalse⟩

variable [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

/-- The hypotheses of `inclusionList_dichotomy`, for the envelope `signedEnv` at the block
root `r` and the honest list `il`:

- `pre` is the store before the envelope handler.
- Envelope handler: `pre.blockStates[r] = state`. The data at `r` is available. The
  envelope verification of `state` returns `warm`. `state.slot` is not zero.
- Committee: `getInclusionListCommittee state (state.slot - 1)` returns `committee`, and
  `il.inclusionListCommitteeRoot = htr committee`.
- Arrivals: `pre.inclusionListStore` is the result of the arrival list
  `before ++ (signed, t) :: after`, with `signed.message = il`, under
  `ArrivalHypotheses il before after` (`OnInclusionList.lean`, which also explains when
  a key repeats across slots). The arrival `(signed, t)` is timely.
- EL: the rule `LawfulInclusionList` for the payload transactions and `isValidOmission`. -/
structure DichotomyHypotheses (isValidOmission : ExecutionPayload → Transaction → Prop)
    (pre : Store map) (signedEnv : SignedExecutionPayloadEnvelope) (state warm : State)
    (committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize)
    (before after : List (SignedInclusionList × UInt64)) (signed : SignedInclusionList)
    (t : UInt64) (il : InclusionList) : Prop where
  /-- The EL rule for the payload transactions and `isValidOmission`. -/
  el : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests
    (fun p => p.transactions.toArray) isValidOmission
  /-- `pre` holds the block state at `r`. -/
  blockState : FcMap.lookup pre.blockStates signedEnv.message.beaconBlockRoot = some state
  /-- The data at `r` is available. -/
  available : isDataAvailable signedEnv.message.beaconBlockRoot = true
  /-- The envelope verification of `state` returns `warm`. -/
  verify : verifyExecutionPayloadEnvelope state signedEnv = .ok warm
  /-- `state.slot` is not zero. -/
  slotNeZero : sszGet state slot ≠ 0
  /-- The committee of `state.slot - 1` is `committee`. -/
  committeeRun : (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun (Store map))
      state (sszGet state slot - 1)).run pre = .ok (committee, pre)
  /-- The committee key of `il` is the root of `committee`. -/
  key : il.inclusionListCommitteeRoot = htr committee
  /-- The IL store of `pre` is the result of the arrival list. -/
  ils : pre.inclusionListStore = ilStoreOfArrivals (before ++ (signed, t) :: after)
  /-- The arrival `(signed, t)` carries `il`. -/
  signedEq : signed.message = il
  /-- The arrival model of `OnInclusionList.lean`. -/
  arrivals : ArrivalHypotheses il before after
  /-- The arrival `(signed, t)` is timely. -/
  timely : t < getInclusionListDueMs

/-- The inclusion dichotomy for one honest transaction. The module docstring states the
two cases, and `DichotomyHypotheses` lists the hypotheses. The map must satisfy
`LawfulFcMap`. -/
theorem inclusionList_dichotomy [LawfulFcMap map Root]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state warm : State}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {before after : List (SignedInclusionList × UInt64)} {signed : SignedInclusionList}
    {t : UInt64} {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state warm committee before after
      signed t il) :
    ∃ post : Store map,
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      ((FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
          = some true ∧
        ∀ tx ∈ il.transactions.toArray,
          tx ∈ signedEnv.message.payload.transactions.toArray ∨
            isValidOmission signedEnv.message.payload tx) ∨
       (FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
          = some false ∧
        ∀ s : Store map, LaterStore s post signedEnv.message.beaconBlockRoot rootBlock →
          UnsatisfiedPayload s signedEnv.message.beaconBlockRoot rootBlock)) := by
  -- The honest list is in the IL store, so its transactions reach `ilTxs`.
  obtain ⟨hstored, htrue, -, hequiv⟩ :=
    honestStored_of_arrivals (map := map) before after signed t il h.signedEq h.arrivals
  rw [decide_eq_true h.timely] at htrue
  have htotal := total_arrivals (map := map) (before ++ (signed, t) :: after)
  rw [← h.ils] at hstored htrue hequiv htotal
  rw [h.key] at hstored hequiv
  obtain ⟨ilTxs, htxs, hmem⟩ := mem_getInclusionListTransactions pre.inclusionListStore state
    (sszGet state slot - 1) pre committee h.committeeRun (htotal (htr committee)) (htr il) il
    hstored htrue hequiv
  -- The handler run, and the answer at `r` after it.
  obtain ⟨post, hrun, -, hanswer⟩ := onExecutionPayloadEnvelope_run_pairing pre pre signedEnv
    state warm ilTxs h.blockState h.available h.verify h.slotNeZero htxs
  refine ⟨post, hrun, ?_⟩
  cases hel : isInclusionListSatisfied signedEnv.message.payload ilTxs
  · -- `false`: the payload fails the inclusion list.
    have hfalse : FcMap.lookup post.payloadInclusionListSatisfaction
        signedEnv.message.beaconBlockRoot = some false := by rw [hanswer, hel]
    exact Or.inr ⟨hfalse, fun _ hlater => unsatisfiedPayload_of_recorded_false hlater hfalse⟩
  · -- `true`: the EL rule covers each transaction of `ilTxs`, so each transaction of `il`.
    refine Or.inl ⟨by rw [hanswer, hel], fun tx htx => ?_⟩
    exact (h.el.satisfied_iff signedEnv.message.payload ilTxs).mp hel tx (hmem tx htx)

/-- The direction for one transaction. Under `DichotomyHypotheses`, take a transaction
`tx` of `il` that is not in the payload and whose omission is not valid. Then the
envelope handler succeeds and records the answer `false`. `UnsatisfiedPayload` holds at
every `LaterStore`. -/
theorem inclusionList_missing_tx [LawfulFcMap map Root]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state warm : State}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {before after : List (SignedInclusionList × UInt64)} {signed : SignedInclusionList}
    {t : UInt64} {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state warm committee before after
      signed t il)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ signedEnv.message.payload.transactions.toArray)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx) :
    ∃ post : Store map,
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
        = some false ∧
      ∀ s : Store map, LaterStore s post signedEnv.message.beaconBlockRoot rootBlock →
        UnsatisfiedPayload s signedEnv.message.beaconBlockRoot rootBlock := by
  obtain ⟨post, hrun, hcase⟩ := inclusionList_dichotomy rootBlock h
  rcases hcase with ⟨-, hincluded⟩ | ⟨hfalse, hunsat⟩
  · -- The `true` answer would put `tx` in the payload or make its omission valid.
    rcases hincluded tx htx with h | h
    · exact absurd h hmissing
    · exact absurd h hinvalid
  · exact ⟨post, hrun, hfalse, hunsat⟩

/-- The cost of one missing transaction. Under the hypotheses of
`inclusionList_missing_tx`, the envelope handler succeeds. At every `LaterStore`, the
three facts of `unsatisfiedPayload_cost` hold for the block at `r`. The `getHead` loop
continues from the EMPTY node of `r` when it reaches the pending node. A child on the
EMPTY edge, with the empty parent requests, does not pay the bid. At the epoch substep
where the payment of the bid is carried, the bid is paid if and only if its entry
reaches the quorum. -/
theorem inclusionList_missing_tx_cost [LawfulFcMap map Root]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state warm : State}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {before after : List (SignedInclusionList × UInt64)} {signed : SignedInclusionList}
    {t : UInt64} {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state warm committee before after
      signed t il)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ signedEnv.message.payload.transactions.toArray)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx) :
    ∃ post : Store map,
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      ∀ (s : Store map) (blocks : Array Root),
        LaterStore s post signedEnv.message.beaconBlockRoot rootBlock →
        (∀ (fuel : Nat) (exhausted : ForkChoiceNode),
          (fuelLoop (fuel + 1) (ForkChoiceNode.pending signedEnv.message.beaconBlockRoot)
              exhausted (headLoopBody s blocks)).run s
            = (fuelLoop fuel (ForkChoiceNode.empty signedEnv.message.beaconBlockRoot)
                exhausted (headLoopBody s blocks)).run s) ∧
        (∀ (child : BeaconBlock) (childState : State),
          child.parentRoot = signedEnv.message.beaconBlockRoot →
          (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
              s child).run s
            = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, s) →
          sszGet childState latestExecutionPayloadBid
            = rootBlock.body.signedExecutionPayloadBid.message →
          htr child.body.parentExecutionRequests = htr (default : ExecutionRequests) →
          (processParentExecutionPayload (StateTransition := HezeRun) child).run childState
            = .ok ((), childState)) ∧
        (∀ epochState : State,
          BidPaymentCarried epochState rootBlock.body.signedExecutionPayloadBid.message →
          (sszGet epochState builderPendingWithdrawals).val.size +
              (qualifyingBuilderWithdrawals epochState).length
            ≤ EthCLSpecs.Heze.Const.builderPendingWithdrawalsLimit →
          ∃ afterEpoch : State,
            (processBuilderPendingPayments : HezeRun Unit).run epochState
              = .ok ((), afterEpoch) ∧
            EpochPaysBidIffQuorum epochState afterEpoch
              rootBlock.body.signedExecutionPayloadBid.message) := by
  obtain ⟨post, hrun, -, hunsat⟩ := inclusionList_missing_tx rootBlock h htx hmissing hinvalid
  exact ⟨post, hrun, fun s blocks hlater =>
    unsatisfiedPayload_cost s _ rootBlock blocks (hunsat s hlater)⟩

end

end EthCLSpecs.Proofs.Heze
