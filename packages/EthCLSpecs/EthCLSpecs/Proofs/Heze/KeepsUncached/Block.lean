import EthCLSpecs.Proofs.Heze.KeepsUncached
import EthCLLib.Proofs.KeepsUncachedMemLoop

/-!
# `EthCLSpecs.Proofs.Heze.KeepsUncached.Block`: the block substeps keep the uncached box

`processBlock` runs eight substeps. `processOperations` has its lemma in
`Proofs/Heze/KeepsUncached.lean`. This file proves `KeepsUncached` for the substeps that
read and write the state directly: `processBlockHeader`, `processRandao`,
`processEth1Data`, `processExecutionPayloadBid` and `processSyncAggregate`, with the
read helper `getRandaoMix` and the payment writer `settleBuilderPayment`.

Most proofs unfold the body and run the `keeps_uncached` tactic. `processBlockHeader`
takes one bind at a time, because the tactic runs out of heartbeats on it. A body that
threads a local state through a loop of balance writes, `processSyncAggregate`, takes
the per-start lemmas of `EthCLLib/Proofs/KeepsUncached.lean` one bind at a time. All the
lemmas are supporting facts, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze (Preset Config Epoch BeaconBlock BeaconBlockBody SyncAggregate
  SignedExecutionPayloadBid processBlockHeader processRandao processEth1Data
  processExecutionPayloadBid processSyncAggregate getRandaoMix settleBuilderPayment)
open EthCLLib.Proofs (pureState KeepsUncached KeepsUncachedFrom keepsUncached_bind keepsUncached_get
  keepsUncached_ite keepsUncached_liftErr keepsUncached_pure keepsUncached_throw
  keepsUncached_modify keepsUncached_iff_forall_from keepsUncachedFrom_get_bind
  keepsUncachedFrom_bind keepsUncachedFrom_ite keepsUncachedFrom_pure keepsUncachedFrom_throw
  keepsUncachedFrom_set keepsUncachedFrom_forIn'_range_bind_P IsPure ReturnsPureVia
  returnsPureVia_bind_returns returnsPureVia_pure step_of_returnsPureVia)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `processBlockHeader` keeps the flavour: one read of the state, five gates, and one
write of the new header through the record update. -/
theorem keepsUncached_processBlockHeader (block : BeaconBlock) :
    KeepsUncached (processBlockHeader (StateTransition := HezeRun) block) := by
  unfold processBlockHeader
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_bind (keepsUncached_ite (fun _ => keepsUncached_pure _)
    (fun _ => keepsUncached_throw _)) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_ite (fun _ => keepsUncached_pure _)
    (fun _ => keepsUncached_throw _)) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_ite (fun _ => keepsUncached_pure _)
    (fun _ => keepsUncached_throw _)) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_ite (fun _ => keepsUncached_pure _)
    (fun _ => keepsUncached_throw _)) (fun _ => ?_)
  -- The proposer read through `sszGetIdx`.
  refine keepsUncached_bind (keepsUncached_liftErr _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_ite (fun _ => keepsUncached_pure _)
    (fun _ => keepsUncached_throw _)) (fun _ => ?_)
  exact keepsUncached_modify _ (fun v => ⟨_, rfl⟩)

/-- `getRandaoMix` keeps the flavour: one read of the state and a pure return. -/
theorem keepsUncached_getRandaoMix (epoch : Epoch) :
    KeepsUncached (getRandaoMix (StateTransition := HezeRun) epoch) := by
  unfold getRandaoMix
  keeps_uncached

/-- `processRandao` keeps the flavour: the proposer read, the signature gate, and one
write of the new mix through the record update. -/
theorem keepsUncached_processRandao (body : BeaconBlockBody) :
    KeepsUncached (processRandao (StateTransition := HezeRun) body) := by
  unfold processRandao
  keeps_uncached

/-- `processEth1Data` keeps the flavour: an `appendState` of the vote, a read, and a
write of the new data when the vote has a majority. -/
theorem keepsUncached_processEth1Data (body : BeaconBlockBody) :
    KeepsUncached (processEth1Data (StateTransition := HezeRun) body) := by
  unfold processEth1Data
  keeps_uncached

/-- `settleBuilderPayment` keeps the flavour: a gate, an `appendState` of the withdrawal
when its amount is not zero, and a write that clears the payment slot. -/
theorem keepsUncached_settleBuilderPayment (paymentIndex : Nat) :
    KeepsUncached (settleBuilderPayment (StateTransition := HezeRun) paymentIndex) := by
  unfold settleBuilderPayment
  keeps_uncached

/-- `processExecutionPayloadBid` keeps the flavour. The bid gates read the state. The
parent root read goes through `getBlockRootAtSlot` and the mix read through
`getRandaoMix`, and each has a lemma of its own. Two writes follow: the pending payment
when the bid has a value, then the cached bid. -/
theorem keepsUncached_processExecutionPayloadBid (signedBid : SignedExecutionPayloadBid) :
    KeepsUncached (processExecutionPayloadBid (StateTransition := HezeRun) signedBid) := by
  unfold processExecutionPayloadBid
  keeps_uncached

/-- `processSyncAggregate` keeps the flavour. The key choice comes first. Its G1
arithmetic is a `liftErr` of an `Except` value, and it reads no state. The reads and the signature gate follow,
with the parent root read through `getBlockRootAtSlot`. The two reward totals are
`Except` reads, and the two reward products are checked. The committee index search maps the committee keys, and each step
returns a registry position or raises. Then a
`for h : i in [0:n]` loop threads a local state through the balance writes. Lean
elaborates this loop to `forIn'`, because the body reads `committeeIndices[i]` with the bound
`h`. The loop invariant says that the local state is pure (`IsPure`). Each body step
returns its new local state through `increaseBalance` or `decreaseBalance`, and the
final `set` writes a pure box. -/
theorem keepsUncached_processSyncAggregate (agg : SyncAggregate) :
    KeepsUncached (processSyncAggregate (StateTransition := HezeRun) agg) := by
  intro preState
  unfold processSyncAggregate
  apply keepsUncachedFrom_get_bind
  intro state
  -- The three branches of the key choice end in one join point, the rest of the body.
  -- `extract_lets` names it `jp`, and `hjp` proves it once.
  extract_lets syncCommittee bits participantCount previousSlot proposerIdx validators
    localState jp
  have hjp : ∀ y (w : EthCLSpecs.Heze.BeaconState), KeepsUncachedFrom w (jp y) := by
    intro y w
    refine keepsUncachedFrom_bind (T := EthCLSpecs.Heze.BeaconState) ?root
      (fun _ midState₁ => ?_)
    · exact keepsUncached_iff_forall_from.mp (keepsUncached_getBlockRootAtSlot state _) _
    refine keepsUncachedFrom_bind ?gate (fun _ midState₂ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
        (fun _ => keepsUncachedFrom_throw _ _)
    refine keepsUncachedFrom_bind ?total (fun _ midState₃ => ?_)
    · exact keepsUncached_iff_forall_from.mp (keepsUncached_liftErr _) _
    refine keepsUncachedFrom_bind ?base (fun _ midState₄ => ?_)
    · exact keepsUncached_iff_forall_from.mp (keepsUncached_liftErr _) _
    -- The two checked reward products.
    refine keepsUncachedFrom_bind ?totalRewards (fun _ midState₄a => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
        (fun _ => keepsUncachedFrom_pure _ _)
    refine keepsUncachedFrom_bind ?weightedRewards (fun _ midState₄b => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
        (fun _ => keepsUncachedFrom_pure _ _)
    refine keepsUncachedFrom_bind ?indices (fun _ midState₅ => ?_)
    · refine keepsUncached_iff_forall_from.mp
        (EthCLLib.Proofs.keepsUncached_arrayMapM _ (fun _ => ?_) _) _
      split
      · exact keepsUncached_pure _
      · unfold EthCLLib.Spec.throwArithmetic
        exact keepsUncached_liftErr _
    refine keepsUncachedFrom_forIn'_range_bind_P _ _ _ IsPure ?body ?tail _ ⟨state, rfl⟩
    · intro i hi b
      rintro v r s ⟨w, rfl⟩ hrun
      revert v r s hrun
      -- The `refine` unifies the action of `step_of_returnsPureVia` with the body that the
      -- goal names.
      refine step_of_returnsPureVia ?_
      dsimp only
      split
      · exact returnsPureVia_bind_returns (returnsUncached_increaseBalance _ _ _)
          (fun w₁ => returnsPureVia_bind_returns (returnsUncached_increaseBalance _ _ _)
            (fun w₂ => returnsPureVia_pure _ ⟨w₂, rfl⟩))
      · exact returnsPureVia_bind_returns (returnsUncached_decreaseBalance _ _ _)
          (fun w₁ => returnsPureVia_pure _ ⟨w₁, rfl⟩)
    · intro b w' hb
      obtain ⟨w, rfl⟩ := hb
      exact keepsUncachedFrom_set w' w
  refine keepsUncachedFrom_ite (fun _ => ?_) (fun _ => ?_)
  · exact keepsUncachedFrom_bind (keepsUncachedFrom_pure _ _) hjp
  · refine keepsUncachedFrom_ite (fun _ => ?_) (fun _ => ?_)
    · -- The G1 arithmetic: three `Except` results, then the join point.
      refine keepsUncachedFrom_bind
        (keepsUncached_iff_forall_from.mp (keepsUncached_liftErr _) _) (fun _ w₁ => ?_)
      refine keepsUncachedFrom_bind
        (keepsUncached_iff_forall_from.mp (keepsUncached_liftErr _) _) (fun _ w₂ => ?_)
      refine keepsUncachedFrom_bind
        (keepsUncached_iff_forall_from.mp (keepsUncached_liftErr _) _) (fun _ w₃ => ?_)
      exact keepsUncachedFrom_bind (keepsUncachedFrom_pure _ _) hjp
    · exact keepsUncachedFrom_bind (keepsUncachedFrom_pure _ _) hjp

end

end EthCLSpecs.Proofs.Heze
