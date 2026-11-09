import EthCLSpecs.Proofs.Fulu.Reachable
import EthCLSpecs.Proofs.Fulu.Invariants.Slots
import EthCLSpecs.Proofs.Fulu.Invariants.Block

/-!
# `EthCLSpecs.Proofs.Fulu.ReachableInvariants`: every reachable Fulu state satisfies the invariants

`ReachableState.simpleStateInvariants` is the induction over `ReachableState`
(`Proofs/Fulu/Reachable.lean`). An anchor satisfies the invariants by hypothesis; a `slots` step
keeps them by `processSlots_ensures`; a `block` step keeps them by `processBlock_ensures`, which
composes the header step with the six `KeepsCore` block substeps.

The module also proves what follows from the same facts:

* `ReachableState.slot_le_forkSlot`: a reachable state lies inside its fork window.
* `ReachableState.anchor_slot_le`: a reachable state's slot is at least some anchor's slot.
* `ReachableState.stateTransition`: one `stateTransition` from a reachable state, with the block
  below the window's end, reaches a reachable state. The inductive's `slots` and `block` steps
  are the two halves of `stateTransition`, and this lemma joins them back.
* `simpleStateInvariants_not_sufficient`: the invariants do not imply reachability. A state one
  slot before the only anchor satisfies them and is not reachable.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend htr bytesToRoot getStateRoot)
open EthCLSpecs.Fulu
open EthCLSpecs.Fulu.Const (fuluForkVersion farFutureEpoch)

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The header step and `process_block` -/

omit [CryptoBackend] in
/-- `process_block_header` writes a header whose slot is the block's, which it asserts is the
state's. Every other value the invariants read stays. -/
theorem processBlockHeader_ensures (block : BeaconBlock) (v : BeaconState)
    (hv : SimpleStateInvariants v) :
    RunEnsures v (processBlockHeader (StateTransition := FuluRun) block)
      (fun _ w => w.slot = v.slot ∧ SimpleStateInvariants w) := by
  unfold processBlockHeader
  run_ensures
  have h : (block.slot == (pureState v).view.slot) = true := by with_reducible assumption
  simp only [box_reduce, beq_iff_eq] at h
  refine ⟨rfl, ?_, hv.registrySizes, hv.checkpointOrder, hv.forkConsistent⟩
  show block.slot ≤ v.slot
  rw [h]
  exact UInt64.le_refl _

omit [HasherTag] [CryptoBackend] in
/-- The six `KeepsCore` block substeps keep the post-header core values, so the final state has
the start's slot and satisfies the invariants. -/
theorem slot_inv_of_stepInv {v w1 w : BeaconState} (hs : w1.slot = v.slot)
    (hinv : SimpleStateInvariants w1) (hw : StepInv (coreFields w1) w) :
    w.slot = v.slot ∧ SimpleStateInvariants w :=
  ⟨(congrArg CoreFields.slot hw.1).trans hs, SimpleStateInvariants.of_coreFields_eq hw.1 hw.2 hinv⟩

theorem processBlock_ensures (block : BeaconBlock) (v : BeaconState)
    (hv : SimpleStateInvariants v) :
    RunEnsures v (processBlock (StateTransition := FuluRun) block)
      (fun _ w => w.slot = v.slot ∧ SimpleStateInvariants w) := by
  unfold processBlock
  run_ensures
  refine (processBlockHeader_ensures block v hv).weaken fun _ w1 h1 => ?_
  obtain ⟨hs1, hinv1⟩ := h1
  have _hst : StepInv (coreFields w1) w1 := ⟨rfl, hinv1.registrySizes⟩
  run_ensures
  call processWithdrawals_keepsCore _
  run_ensures
  call processExecutionPayload_keepsCore _
  run_ensures
  call processRandao_keepsCore _
  run_ensures
  call processEth1Data_keepsCore _
  run_ensures
  call processOperations_keepsCore _
  run_ensures
  call processSyncAggregate_keepsCore _
  exact slot_inv_of_stepInv hs1 hinv1 (by assumption)

/-! ## The induction -/

namespace ReachableState

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- Every reachable Fulu state satisfies `SimpleStateInvariants`, once every anchor does. -/
theorem simpleStateInvariants (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u)
    {v : BeaconState} (h : ReachableState anchors validated nextForkEpoch v) :
    SimpleStateInvariants v := by
  induction h with
  | anchor ha _ => exact hA _ ha
  | slots target _ _ hrun ih => exact ((processSlots_ensures target _ ih).runPure_ok hrun).2.2
  | block sb _ _ _ hrun _ ih => exact ((processBlock_ensures _ _ ih).runPure_ok hrun).2

/-- A reachable state lies inside its fork window: its slot is at most the next fork's first
slot. -/
theorem slot_le_forkSlot (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u) {v : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch v) :
    v.slot.toNat ≤ forkSlot nextForkEpoch := by
  induction h with
  | anchor _ hw => exact hw
  | slots target hv hw hrun _ =>
    rw [((processSlots_ensures target _ (hv.simpleStateInvariants hA)).runPure_ok hrun).1]
    exact hw
  | block sb hv hw _ hrun _ _ =>
    rw [((processBlock_ensures _ _ (hv.simpleStateInvariants hA)).runPure_ok hrun).1]
    exact Nat.le_of_lt hw

/-- Slots only grow along a run: every reachable state's slot is at least some anchor's. -/
theorem anchor_slot_le (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u) {v : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch v) :
    ∃ a, anchors.fulu a ∧ a.slot ≤ v.slot := by
  induction h with
  | anchor ha _ => exact ⟨_, ha, UInt64.le_refl _⟩
  | slots target hv _ hrun ih =>
    obtain ⟨a, ha, hle⟩ := ih
    obtain ⟨hs, hlt, _⟩ := (processSlots_ensures target _ (hv.simpleStateInvariants hA)).runPure_ok hrun
    refine ⟨a, ha, ?_⟩
    rw [hs]
    exact UInt64.le_trans hle (UInt64.le_of_lt hlt)
  | block sb hv _ _ hrun _ ih =>
    obtain ⟨a, ha, hle⟩ := ih
    refine ⟨a, ha, ?_⟩
    rw [((processBlock_ensures _ _ (hv.simpleStateInvariants hA)).runPure_ok hrun).1]
    exact hle

omit [Config] [CryptoBackend] in
/-- A triple and the run it describes: when `act` keeps the box uncached from `v`, its triple can
also record the run's own `runPure` reading, so a later step can name the state it ran from. -/
theorem runEnsures_with_run {α : Type} {act : FuluRun α} {v : BeaconState}
    {Q : α → BeaconState → Prop} (h : RunEnsures v act Q) :
    RunEnsures v act (fun a w => runPure act v = .ok (a, w) ∧ Q a w) :=
  (runEnsures_of_keepsUncachedFrom h.keepsUncachedFrom (fun _ _ hr => hr)).and h

/-- One `stateTransition` from a reachable state reaches a reachable state, when the block lies
below the window's end. It is the inductive's `slots` step followed by its `block` step, with the
same `validated` flag as `validateResult`. -/
theorem stateTransition_reachable (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u)
    {v w : BeaconState} (hv : ReachableState anchors validated nextForkEpoch v)
    (sb : SignedBeaconBlock) (hslot : sb.message.slot.toNat < forkSlot nextForkEpoch)
    (hrun : runPure (stateTransition (StateTransition := FuluRun) sb validated) v = .ok ((), w)) :
    ReachableState anchors validated nextForkEpoch w := by
  have hinv := hv.simpleStateInvariants hA
  refine (?_ : RunEnsures v (stateTransition (StateTransition := FuluRun) sb validated)
    (fun _ w => ReachableState anchors validated nextForkEpoch w)).runPure_ok hrun
  unfold stateTransition
  run_ensures
  refine (runEnsures_with_run (processSlots_ensures _ v hinv)).weaken fun _ w1 h1 => ?_
  obtain ⟨hrun1, hs1, _, hinv1⟩ := h1
  have hr1 : ReachableState anchors validated nextForkEpoch w1 :=
    .slots _ hv (Nat.le_of_lt hslot) hrun1
  have hw1 : w1.slot.toNat < forkSlot nextForkEpoch := by rw [hs1]; exact hslot
  run_ensures
  all_goals refine (runEnsures_with_run (processBlock_ensures _ _ hinv1)).weaken fun _ w2 h2 => ?_
  all_goals obtain ⟨hrun2, _hs2, _hinv2⟩ := h2
  all_goals run_ensures
  all_goals try
    exact absurd (show validated = true by with_reducible assumption)
      (show ¬validated = true by with_reducible assumption)
  · rename_i hsig _ _ hroot
    exact .block sb hr1 hw1 (fun _ => hsig) hrun2 (fun _ => beq_iff_eq.mp hroot)
  · rename_i _ hnv
    exact .block sb hr1 hw1 (fun h => absurd h hnv) hrun2 (fun h => absurd h hnv)

end ReachableState

/-! ## The invariants do not imply reachability -/

/-- A state at slot `slot` with every other field at its default, but the `fork` field naming
Fulu's version. -/
def witnessState (slot : Slot) : BeaconState :=
  { (default : BeaconState) with
    slot := slot
    forkData := { (default : BeaconState).forkData with currentVersion := fuluForkVersion, epoch := 0 } }

omit [HasherTag] [CryptoBackend] in
theorem witnessState_invariants (slot : Slot) : SimpleStateInvariants (witnessState slot) := by
  refine ⟨UInt64.zero_le, ⟨rfl, rfl, rfl, rfl⟩, ⟨UInt64.le_refl _, UInt64.le_refl _,
    UInt64.zero_le⟩, ⟨UInt64.zero_le, rfl⟩⟩

/-- `SimpleStateInvariants` is necessary for reachability and not sufficient: with one anchor at
slot `5`, the state at slot `4` satisfies the invariants, and no reachable state sits below the
anchor's slot. The `false` flag makes this the claim about the larger, unchecked set. -/
theorem simpleStateInvariants_not_sufficient :
    ∃ (anchors : Anchors) (v : BeaconState),
      (∀ a, anchors.fulu a → SimpleStateInvariants a) ∧ SimpleStateInvariants v ∧
      ¬ ReachableState anchors false farFutureEpoch v := by
  refine ⟨⟨fun a => a = witnessState 5⟩, witnessState 4, ?_, witnessState_invariants 4, ?_⟩
  · rintro a rfl
    exact witnessState_invariants 5
  · intro h
    have hA : ∀ a, a = witnessState 5 → SimpleStateInvariants a := by
      rintro a rfl
      exact witnessState_invariants 5
    obtain ⟨a, rfl, hle⟩ := h.anchor_slot_le hA
    exact absurd hle (by show ¬ ((5 : UInt64) ≤ 4); decide)

end

end EthCLSpecs.Proofs.Fulu
