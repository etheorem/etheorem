import EthCLSpecs.Proofs.Gloas.Reachable
import EthCLSpecs.Proofs.Gloas.Invariants.Slots
import EthCLSpecs.Proofs.Gloas.Invariants.Block
import EthCLSpecs.Proofs.Fulu.ReachableInvariants

/-!
# `EthCLSpecs.Proofs.Gloas.ReachableInvariants`: every reachable Gloas state satisfies the invariants

The Gloas counterpart of `Proofs/Fulu/ReachableInvariants.lean`. `ReachableState.simpleStateInvariants`
is the induction over the Gloas `ReachableState` (`Proofs/Gloas/Reachable.lean`), which has one
more case than the Fulu one:

* `upgrade`: the Fulu state the upgrade starts from is reachable in Fulu, so it satisfies the
  Fulu invariants (`EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants`).
  `upgradeToGloas` copies the slot, the header, the checkpoints and the registry lists, and sets
  `fork` to the current epoch and `GLOAS_FORK_VERSION`, so its result satisfies the Gloas
  invariants (`upgradeToGloas_invariants`). `completeUpgradeToGloas` fills the PTC window and
  onboards builders, a `KeepsCore` step.

`processBlock_ensures` composes the Gloas block: the parent payload first, then the header step,
then the six other `KeepsCore` substeps. The window bound, slot monotonicity across the upgrade,
and closure under `stateTransition` follow from the same facts, as in Fulu.

The cross-fork statements name a Fulu state and its invariants, so this module opens the
Gloas-to-Fulu preset bridge, as `Proofs/Gloas/Reachable.lean` does.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend htr bytesToRoot)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas.Const (gloasForkVersion gloasForkEpoch)
open scoped EthCLSpecs.Gloas.Downgrade

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The upgrade -/

omit [CryptoBackend] in
/-- `upgradeToGloas` carries the Fulu invariants to the Gloas ones: it copies every value they
read, maps the registry lists element by element, and writes a `fork` field for the current
epoch and Gloas's version. -/
theorem upgradeToGloas_invariants (u : EthCLSpecs.Fulu.BeaconState)
    (hu : EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u) :
    SimpleStateInvariants (upgradeToGloas gloasForkVersion u) := by
  obtain ⟨hh, hr, hc, _⟩ := hu
  refine ⟨hh, ?_, hc, ⟨UInt64.le_refl _, rfl⟩⟩
  obtain ⟨hb, hi, hp, hq⟩ := hr
  simp only [SizzLean.Repr.SSZList.size] at hb hi hp hq
  simp only [RegistrySizes, upgradeToGloas, SizzLean.Repr.ProgressiveList.size, Array.size_map]
  exact ⟨hb, hi, hp, hq⟩

theorem applyDepositForBuilder_keepsCore (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei)
    (sig : BLSSignature) (slot : Slot) :
    KeepsCore (applyDepositForBuilder (StateTransition := GloasRun) pk wc amt sig slot) := by
  intro c v hv
  unfold applyDepositForBuilder
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try (call addBuilderToRegistry_keepsCore _ _ _ _ _; run_ensures)
  all_goals frame_close

theorem onboardBuildersFromPendingDeposits_keepsCore :
    KeepsCore (onboardBuildersFromPendingDeposits (StateTransition := GloasRun)) := by
  intro c v hv
  unfold onboardBuildersFromPendingDeposits
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hv (fun _ w hw => ?_)
  · intro w hw
    run_ensures
    all_goals try frame_close
    call applyDepositForBuilder_keepsCore _ _ _ _ _
    run_ensures
    frame_close
  · run_ensures
    frame_close

theorem completeUpgradeToGloas_keepsCore :
    KeepsCore (completeUpgradeToGloas (StateTransition := GloasRun)) := by
  intro c v hv
  unfold completeUpgradeToGloas
  run_ensures
  call onboardBuildersFromPendingDeposits_keepsCore
  frame_close

/-! ## The header step and `process_block` -/

omit [CryptoBackend] in
theorem processBlockHeader_ensures (block : BeaconBlock) (v : BeaconState)
    (hv : SimpleStateInvariants v) :
    RunEnsures v (processBlockHeader (StateTransition := GloasRun) block)
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
theorem slot_inv_of_stepInv {v w1 w : BeaconState} (hs : w1.slot = v.slot)
    (hinv : SimpleStateInvariants w1) (hw : StepInv (coreFields w1) w) :
    w.slot = v.slot ∧ SimpleStateInvariants w :=
  ⟨(congrArg CoreFields.slot hw.1).trans hs, SimpleStateInvariants.of_coreFields_eq hw.1 hw.2 hinv⟩

/-- The Gloas block applies the parent payload before the header. Both the payload step and
the substeps after the header keep the core values, so the slot stays and the invariants hold. -/
theorem processBlock_ensures (block : BeaconBlock) (v : BeaconState)
    (hv : SimpleStateInvariants v) :
    RunEnsures v (processBlock (StateTransition := GloasRun) block)
      (fun _ w => w.slot = v.slot ∧ SimpleStateInvariants w) := by
  unfold processBlock
  run_ensures
  refine Preserves.run (processParentExecutionPayload_keepsCore _ (coreFields v))
    ⟨rfl, hv.registrySizes⟩ (fun _ w0 h0 => ?_)
  have hinv0 := SimpleStateInvariants.of_coreFields_eq h0.1 h0.2 hv
  have hs0 : w0.slot = v.slot := congrArg CoreFields.slot h0.1
  run_ensures
  refine (processBlockHeader_ensures block w0 hinv0).weaken fun _ w1 h1 => ?_
  obtain ⟨hs1, hinv1⟩ := h1
  have _hst : StepInv (coreFields w1) w1 := ⟨rfl, hinv1.registrySizes⟩
  run_ensures
  call processWithdrawals_keepsCore
  run_ensures
  call processExecutionPayloadBid_keepsCore _
  run_ensures
  call processRandao_keepsCore _
  run_ensures
  call processEth1Data_keepsCore _
  run_ensures
  call processOperations_keepsCore _ _
  run_ensures
  call processSyncAggregate_keepsCore _
  exact slot_inv_of_stepInv (hs1.trans hs0) hinv1 (by assumption)

/-! ## The induction -/

namespace ReachableState

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- Every reachable Gloas state satisfies `SimpleStateInvariants`, once every Fulu and every
Gloas anchor satisfies its fork's invariants. -/
theorem simpleStateInvariants
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ v, anchors.gloas v → SimpleStateInvariants v)
    {v : BeaconState} (h : ReachableState anchors validated nextForkEpoch v) :
    SimpleStateInvariants v := by
  induction h with
  | anchor ha _ => exact hG _ ha
  | upgrade hu _ _ hrun =>
    have hFu := EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hF hu
    exact (completeUpgradeToGloas_keepsCore.preserves_invariants _
      (upgradeToGloas_invariants _ hFu)).runPure_ok hrun
  | slots target _ _ hrun ih => exact ((processSlots_ensures target _ ih).runPure_ok hrun).2.2
  | block sb _ _ _ hrun _ ih => exact ((processBlock_ensures _ _ ih).runPure_ok hrun).2

/-- A reachable state lies inside its fork window. -/
theorem slot_le_forkSlot
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ v, anchors.gloas v → SimpleStateInvariants v) {v : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch v) :
    v.slot.toNat ≤ forkSlot nextForkEpoch := by
  induction h with
  | anchor _ hw => exact hw
  | @upgrade u w hu _ hw hrun =>
    have hFu := EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hF hu
    have hk := (completeUpgradeToGloas_keepsCore _ _
      ⟨rfl, (upgradeToGloas_invariants _ hFu).registrySizes⟩).runPure_ok hrun
    have hs : w.slot = (upgradeToGloas gloasForkVersion u).slot := congrArg CoreFields.slot hk.1
    rw [hs]
    exact hw
  | slots target hv hw hrun _ =>
    rw [((processSlots_ensures target _ (hv.simpleStateInvariants hF hG)).runPure_ok hrun).1]
    exact hw
  | block sb hv hw _ hrun _ _ =>
    rw [((processBlock_ensures _ _ (hv.simpleStateInvariants hF hG)).runPure_ok hrun).1]
    exact Nat.le_of_lt hw

/-- Slots only grow along a run, across the upgrade too: every reachable Gloas state's slot is
at least the slot of some anchor, a Gloas one or a Fulu one the run started from. -/
theorem anchor_slot_le
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ v, anchors.gloas v → SimpleStateInvariants v) {v : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch v) :
    (∃ a, anchors.gloas a ∧ a.slot ≤ v.slot) ∨ (∃ a, anchors.fulu a ∧ a.slot ≤ v.slot) := by
  induction h with
  | anchor ha _ => exact .inl ⟨_, ha, UInt64.le_refl _⟩
  | @upgrade u w hu _ _ hrun =>
    have hFu := EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hF hu
    obtain ⟨a, ha, hle⟩ := EthCLSpecs.Proofs.Fulu.ReachableState.anchor_slot_le hF hu
    have hk := (completeUpgradeToGloas_keepsCore _ _
      ⟨rfl, (upgradeToGloas_invariants _ hFu).registrySizes⟩).runPure_ok hrun
    have hs : w.slot = (upgradeToGloas gloasForkVersion u).slot := congrArg CoreFields.slot hk.1
    refine .inr ⟨a, ha, ?_⟩
    rw [hs]
    exact hle
  | slots target hv _ hrun ih =>
    obtain ⟨hs, hlt, _⟩ :=
      (processSlots_ensures target _ (hv.simpleStateInvariants hF hG)).runPure_ok hrun
    have hgrow : ∀ {x : Slot}, x ≤ _ → x ≤ _ := fun hx =>
      UInt64.le_trans hx (hs ▸ UInt64.le_of_lt hlt)
    rcases ih with ⟨a, ha, hle⟩ | ⟨a, ha, hle⟩
    · exact .inl ⟨a, ha, hgrow hle⟩
    · exact .inr ⟨a, ha, hgrow hle⟩
  | block sb hv _ _ hrun _ ih =>
    have hs := ((processBlock_ensures _ _ (hv.simpleStateInvariants hF hG)).runPure_ok hrun).1
    rcases ih with ⟨a, ha, hle⟩ | ⟨a, ha, hle⟩
    · exact .inl ⟨a, ha, hs ▸ hle⟩
    · exact .inr ⟨a, ha, hs ▸ hle⟩

omit [Config] [CryptoBackend] in
theorem runEnsures_with_run {α : Type} {act : GloasRun α} {v : BeaconState}
    {Q : α → BeaconState → Prop} (h : RunEnsures v act Q) :
    RunEnsures v act (fun a w => runPure act v = .ok (a, w) ∧ Q a w) :=
  (runEnsures_of_keepsUncachedFrom h.keepsUncachedFrom (fun _ _ hr => hr)).and h

/-- One `stateTransition` from a reachable state reaches a reachable state, when the block lies
below the window's end. -/
theorem stateTransition_reachable
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ v, anchors.gloas v → SimpleStateInvariants v)
    {v w : BeaconState} (hv : ReachableState anchors validated nextForkEpoch v)
    (sb : SignedBeaconBlock) (hslot : sb.message.slot.toNat < forkSlot nextForkEpoch)
    (hrun : runPure (stateTransition (StateTransition := GloasRun) sb validated) v = .ok ((), w)) :
    ReachableState anchors validated nextForkEpoch w := by
  have hinv := hv.simpleStateInvariants hF hG
  refine (?_ : RunEnsures v (stateTransition (StateTransition := GloasRun) sb validated)
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

end

end EthCLSpecs.Proofs.Gloas
