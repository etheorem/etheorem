import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope
import EthCLSpecs.Proofs.Heze.OnInclusionList
import EthCLLib.Proofs.EngineLaws

/-!
# `EthCLSpecs.Proofs.Heze.InclusionDichotomy`: one honest transaction, two answers

Take the block `block` at root `r`, with the block state `state` at `r`. Take a
transaction `tx` from an honest inclusion list `il` whose key is the key that the
envelope handler reads: the slot `block.slot - 1` and the shuffling dependent root of `r`
for the epoch of that slot. `inclusionList_dichotomy` proves that the envelope handler for
`r` succeeds and records the EL answer for the payload, and that one of two cases holds:

- The answer is `true`, and `tx` is in the payload or `isValidOmission payload tx` holds.
- The answer is `false`, and `UnsatisfiedPayload` holds at every later store `s` that
  meets the four conditions of `LaterStore`. `s` holds the block at `r`. `s` keeps the
  answer at `r`. The current slot of `s` is the slot after the block. That slot
  increment does not overflow.

The two cases exclude each other, because the answer is a `Bool`. The answer is about the
whole collected list. A `false` answer can come from a transaction of another list, while
`tx` is in the payload. `inclusionList_missing_tx` states the direction for `tx`: if `tx`
is not in the payload and its omission is not valid, the answer is `false`.
`inclusionList_missing_tx_cost` composes that direction with `unsatisfiedPayload_cost`
(`CensorshipCost.lean`). At every such later store, the `getHead` loop continues from
the EMPTY node of `r` when it reaches the pending node and that node is viable, and a
child on the EMPTY edge
does not settle the bid of `r`. At the epoch substep where the payment of the bid is
carried (`BidPaymentCarried`), the entry of the bid is appended if and only if it reaches
the quorum. Before the envelope arrives, a pending node with an unverified payload has only
its EMPTY child (`getNodeChildren_run_pending_unverified`), for any store and root.

The envelope usually arrives in the slot of its block, and fork choice reads the answer
one slot later. The block and answer conditions on the later store are per key at `r`.
So a handler run that writes only other roots keeps them, by
`LawfulFcMap.lookup_insert_ne`. `onTickPerSlot_run_keeps` shows that a per-slot tick
writes neither the `blocks` nor the `payloadInclusionListSatisfaction` map. The clock
condition holds only in the slot after the block. A second envelope for `r` writes the
answer at `r` again from the IL store of that moment, so the answer can change. No
theorem here covers a whole trace of handler runs.

The theorem states each assumption as a hypothesis. `OnInclusionList.lean` explains the
arrival model: the IL store is the result of the arrival list, from the seed of
`getForkchoiceStore`, and each arrival carries the timeliness bit of its
`onInclusionList` run. The EL satisfies `LawfulInclusionList` for the payload transactions
and for an `isValidOmission` that the reader supplies. The result for the `true` answer
is only as strong as that predicate.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap LawfulInclusionList pureState runPure)
open EthCLSpecs.Heze (Preset Config Store BeaconState Root Slot ForkChoiceNode BeaconBlock
  ExecutionPayload ExecutionRequests Transaction InclusionList SignedInclusionList
  SignedExecutionPayloadEnvelope ValidatorIndex onExecutionPayloadEnvelope isDataAvailable
  verifyExecutionPayloadEnvelope isInclusionListSatisfied getCurrentSlot
  getShufflingDependentRoot getInclusionListTransactions computeEpochAtSlot
  getParentPayloadStatus processParentExecutionPayload processBuilderPendingPayments)

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
- Envelope handler: `pre.blockStates[r] = pureState state`. The data at `r` is
  available. The envelope verification on `pureState state` succeeds.
- Key: `pre.blocks[r] = block`, `block.slot` is not zero, and the shuffling dependent
  root of `r` for the epoch of `block.slot - 1` is `dependentRoot`, from the runner
  state `postRunnerStore`. The key of `il` is `(block.slot - 1, dependentRoot)`: the key
  that the envelope handler reads.
- Arrivals: `pre.inclusionListStore` is the result of the arrival list
  `before ++ (signed, true) :: after`, with `signed.message = il`, under
  `ArrivalHypotheses il before after` (`OnInclusionList.lean`). The bit `true` says that
  the `onInclusionList` run of `signed` judged it timely.
- EL: the rule `LawfulInclusionList` for the payload transactions and `isValidOmission`. -/
structure DichotomyHypotheses (isValidOmission : ExecutionPayload → Transaction → Prop)
    (pre : Store map) (signedEnv : SignedExecutionPayloadEnvelope) (state : BeaconState)
    (block : BeaconBlock) (dependentRoot : Root) (postRunnerStore : Store map)
    (before after : List (SignedInclusionList × Bool)) (signed : SignedInclusionList)
    (il : InclusionList) : Prop where
  /-- The EL rule for the payload transactions and `isValidOmission`. -/
  el : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests
    (fun p => p.transactions.toArray) isValidOmission
  /-- `pre` holds the block state at `r`. -/
  blockState : FcMap.lookup pre.blockStates signedEnv.message.beaconBlockRoot
    = some (pureState state)
  /-- The data at `r` is available. -/
  available : isDataAvailable signedEnv.message.beaconBlockRoot = true
  /-- The envelope verification on `pureState state` succeeds. -/
  verify : (verifyExecutionPayloadEnvelope (pureState state) signedEnv).isOk = true
  /-- `pre` holds the block at `r`. -/
  blockLookup : FcMap.lookup pre.blocks signedEnv.message.beaconBlockRoot = some block
  /-- `block.slot` is not zero. -/
  slotNeZero : block.slot ≠ 0
  /-- The shuffling dependent root of `r` for the epoch of `block.slot - 1`. -/
  dependent : (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
      pre signedEnv.message.beaconBlockRoot (computeEpochAtSlot (block.slot - 1))).run pre
    = .ok (dependentRoot, postRunnerStore)
  /-- The key of `il` is the key that the envelope handler reads. -/
  key : ilKey il = (block.slot - 1, dependentRoot)
  /-- The IL store of `pre` is the result of the arrival list. -/
  ils : pre.inclusionListStore = ilStoreOfArrivals (before ++ (signed, true) :: after)
  /-- The arrival `(signed, true)` carries `il`. -/
  signedEq : signed.message = il
  /-- The arrival model of `OnInclusionList.lean`. -/
  arrivals : ArrivalHypotheses il before after

/-- The inclusion dichotomy for one honest transaction. The module docstring states the
two cases, and `DichotomyHypotheses` lists the hypotheses. The maps must satisfy
`LawfulFcMap`. -/
theorem inclusionList_dichotomy [LawfulFcMap map Root] [LawfulFcMap map (Slot × Root)]
    [LawfulFcMap map ValidatorIndex]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state : BeaconState}
    {block : BeaconBlock} {dependentRoot : Root} {postRunnerStore : Store map}
    {before after : List (SignedInclusionList × Bool)} {signed : SignedInclusionList}
    {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state block dependentRoot
      postRunnerStore before after signed il) :
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
  -- The honest list is in the IL store, so its transactions reach the timely transactions
  -- of its key.
  obtain ⟨⟨e, hstored, hmsg, htimely⟩, hequiv⟩ :=
    honestStored_of_arrivals (map := map) before after signed true il h.signedEq h.arrivals
  rw [← h.ils, h.key] at hstored hequiv
  have hmem : ∀ tx ∈ il.transactions.toArray,
      tx ∈ getInclusionListTransactions pre.inclusionListStore (block.slot - 1)
        dependentRoot (onlyTimely := true) := by
    rw [← hmsg]
    exact mem_getInclusionListTransactions_of_stored pre.inclusionListStore (block.slot - 1)
      dependentRoot il.validatorIndex e hstored htimely hequiv
  -- The handler run, and the answer at `r` after it.
  obtain ⟨post, hrun, -, hanswer⟩ := onExecutionPayloadEnvelope_run_pairing pre
    postRunnerStore signedEnv state block dependentRoot h.blockState h.available h.verify
    h.blockLookup h.slotNeZero h.dependent
  refine ⟨post, hrun, ?_⟩
  cases hel : isInclusionListSatisfied signedEnv.message.payload
      (getInclusionListTransactions pre.inclusionListStore (block.slot - 1) dependentRoot
        (onlyTimely := true))
  · -- `false`: the payload fails the inclusion list.
    have hfalse : FcMap.lookup post.payloadInclusionListSatisfaction
        signedEnv.message.beaconBlockRoot = some false := by rw [hanswer, hel]
    exact Or.inr ⟨hfalse, fun _ hlater => unsatisfiedPayload_of_recorded_false hlater hfalse⟩
  · -- `true`: the EL rule covers each timely transaction of the key, so each transaction
    -- of `il`.
    refine Or.inl ⟨by rw [hanswer, hel], fun tx htx => ?_⟩
    exact (h.el.satisfied_iff signedEnv.message.payload _).mp hel tx (hmem tx htx)

/-- The direction for one transaction. Under `DichotomyHypotheses`, take a transaction
`tx` of `il` that is not in the payload and whose omission is not valid. Then the
envelope handler succeeds and records the answer `false`. `UnsatisfiedPayload` holds at
every `LaterStore`. -/
theorem inclusionList_missing_tx [LawfulFcMap map Root] [LawfulFcMap map (Slot × Root)]
    [LawfulFcMap map ValidatorIndex]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state : BeaconState}
    {block : BeaconBlock} {dependentRoot : Root} {postRunnerStore : Store map}
    {before after : List (SignedInclusionList × Bool)} {signed : SignedInclusionList}
    {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state block dependentRoot
      postRunnerStore before after signed il)
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
continues from the EMPTY node of `r` when it reaches the pending node and the EMPTY node
is viable. A child on the EMPTY edge, with the empty parent requests, does not pay the
bid. At the epoch substep where the payment of the bid is carried, the entry of the bid
is appended if and only if it reaches the quorum. -/
theorem inclusionList_missing_tx_cost [LawfulFcMap map Root] [LawfulFcMap map (Slot × Root)]
    [LawfulFcMap map ValidatorIndex]
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state : BeaconState}
    {block : BeaconBlock} {dependentRoot : Root} {postRunnerStore : Store map}
    {before after : List (SignedInclusionList × Bool)} {signed : SignedInclusionList}
    {il : InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state block dependentRoot
      postRunnerStore before after signed il)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ signedEnv.message.payload.transactions.toArray)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx) :
    ∃ post : Store map,
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      ∀ (s : Store map) (nodes : Array ForkChoiceNode),
        LaterStore s post signedEnv.message.beaconBlockRoot rootBlock →
        nodes.contains (ForkChoiceNode.empty signedEnv.message.beaconBlockRoot) = true →
        (∀ (fuel : Nat) (exhausted : ForkChoiceNode),
          (fuelLoop (fuel + 1) (ForkChoiceNode.pending signedEnv.message.beaconBlockRoot)
              exhausted (headLoopBody s nodes)).run s
            = (fuelLoop fuel (ForkChoiceNode.empty signedEnv.message.beaconBlockRoot)
                exhausted (headLoopBody s nodes)).run s) ∧
        (∀ (child : BeaconBlock) (childState : BeaconState),
          child.parentRoot = signedEnv.message.beaconBlockRoot →
          (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
              s child).run s
            = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, s) →
          childState.latestExecutionPayloadBid
            = rootBlock.body.signedExecutionPayloadBid.message →
          child.body.parentExecutionRequests = (default : ExecutionRequests) →
          (processParentExecutionPayload (StateTransition := HezeRun) child).run
              (pureState childState)
            = .ok ((), pureState childState)) ∧
        (∀ epochState : BeaconState,
          BidPaymentCarried epochState rootBlock.body.signedExecutionPayloadBid.message →
          ∃ afterEpoch : BeaconState,
            runPure (processBuilderPendingPayments (StateTransition := HezeRun)) epochState
              = .ok ((), afterEpoch) ∧
            EpochPaysBidIffQuorum epochState afterEpoch
              rootBlock.body.signedExecutionPayloadBid.message) := by
  obtain ⟨post, hrun, -, hunsat⟩ := inclusionList_missing_tx rootBlock h htx hmissing hinvalid
  exact ⟨post, hrun, fun s nodes hlater hviable =>
    unsatisfiedPayload_cost s _ rootBlock nodes (hunsat s hlater) hviable⟩

end

end EthCLSpecs.Proofs.Heze
