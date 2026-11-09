import EthCLSpecs.Proofs.Gloas.Invariants.Epoch
import EthCLSpecs.Proofs.Gloas.Invariants.Justification

/-!
# `EthCLSpecs.Proofs.Gloas.Invariants.Slots`: `process_slots` keeps the invariants

The Gloas counterpart of `Proofs/Fulu/Invariants/Slots.lean`. Gloas's `processSlot` also clears
the next slot's payload-availability bit, and its `processEpoch` runs two more substeps; neither
writes a field the invariants read.

`processSlots target` (`Gloas/Transition.lean:77-82`) asserts `slot < target`, then runs one
iteration per slot: `processSlot`, then `processEpoch` at the last slot of an epoch, then the
slot increment. Each iteration keeps `SimpleStateInvariants`:

* `processSlot` caches roots and fills the header's state root, and keeps the core values
  (`processSlot_keepsCore`).
* `processEpoch` moves the checkpoint bound from the previous epoch to the current one and keeps
  every other invariant (`processEpoch_ensures`).
* The increment moves the state one slot on. Off an epoch boundary the epoch does not change;
  at a boundary the epoch grows by one, so the previous epoch of the new slot is the epoch the
  checkpoints were bounded by (`SimpleStateInvariants.succ_slot`,
  `SimpleStateInvariants.succ_slot_boundary`).

The loop's invariant also counts the slot, `slot = start + i`. With the assert, the counter keeps
every slot below `target`, so no increment wraps, and the loop ends at `slot = target`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt gloasForkVersion)

/-! ## Slot arithmetic -/

/-- Dividing a successor: the quotient grows by one exactly when the successor is a multiple. -/
theorem succ_div_eq (s k : Nat) (hk : 0 < k) :
    (s + 1) / k = if (s + 1) % k = 0 then s / k + 1 else s / k := by
  have hs : k * (s / k) + s % k = s := Nat.div_add_mod s k
  have hr : s % k < k := Nat.mod_lt s hk
  by_cases hlast : s % k + 1 = k
  · have heq : s + 1 = k * (s / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [heq, Nat.mul_mod_right, ite_eq_left_of_eq_true _ _ (eq_true rfl), Nat.mul_div_cancel_left _ hk]
  · have heq : s + 1 = (s % k + 1) + k * (s / k) := by omega
    have hlt : s % k + 1 < k := by omega
    have hmod : (s + 1) % k = s % k + 1 := by
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), heq, Nat.add_mul_div_left _ _ hk,
      Nat.div_eq_of_lt hlt, Nat.zero_add]

section

variable [Preset]

/-- `computeEpochAtSlot` in `Nat`: the slot divided by `SLOTS_PER_EPOCH`. -/
theorem computeEpochAtSlot_toNat (s : Slot) :
    (computeEpochAtSlot s).toNat = s.toNat / slotsPerEpoch := by
  unfold computeEpochAtSlot
  rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt]

omit [Preset] in
/-- A slot increment that does not wrap. -/
theorem slot_succ_toNat (s : Slot) (h : s.toNat + 1 < 2 ^ 64) : (s + 1).toNat = s.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_one]
  exact Nat.mod_eq_of_lt h

variable [Config]

/-- Off an epoch boundary, the slot increment keeps the invariants: the epoch is unchanged. -/
theorem SimpleStateInvariants.succ_slot {w : BeaconState} (hw : SimpleStateInvariants w)
    (hno : w.slot.toNat + 1 < 2 ^ 64) (hb : (w.slot.toNat + 1) % slotsPerEpoch ≠ 0) :
    SimpleStateInvariants { w with slot := w.slot + 1 } := by
  obtain ⟨hh, hr, ⟨c1, c2, c3⟩, ⟨f1, f2⟩⟩ := hw
  have hs := slot_succ_toNat w.slot hno
  have he : (computeEpochAtSlot (w.slot + 1)).toNat = (computeEpochAtSlot w.slot).toNat := by
    rw [computeEpochAtSlot_toNat, computeEpochAtSlot_toNat, hs,
      succ_div_eq _ _ slotsPerEpochPos, ite_eq_right_of_eq_false _ _ (eq_false hb)]
  have hp := EthCLLib.Proofs.saturatingSub_toNat (computeEpochAtSlot (w.slot + 1)) 1
  have hp' := EthCLLib.Proofs.saturatingSub_toNat (computeEpochAtSlot w.slot) 1
  refine ⟨?_, hr, ⟨c1, c2, ?_⟩, ⟨?_, f2⟩⟩
  · show w.latestBlockHeader.slot ≤ w.slot + 1
    simp only [UInt64.le_iff_toNat_le] at hh ⊢
    omega
  · show w.currentJustifiedCheckpoint.epoch ≤ saturatingSub (computeEpochAtSlot (w.slot + 1)) 1
    simp only [UInt64.le_iff_toNat_le] at c3 ⊢
    omega
  · show w.forkData.epoch ≤ computeEpochAtSlot (w.slot + 1)
    simp only [UInt64.le_iff_toNat_le] at f1 ⊢
    omega

/-- At an epoch boundary, the slot increment after epoch processing restores the invariants:
the new slot's previous epoch is the epoch the checkpoints were bounded by. -/
theorem SimpleStateInvariants.succ_slot_boundary {w : BeaconState}
    (hh : w.latestBlockHeader.slot ≤ w.slot) (hr : RegistrySizes w)
    (hc : CheckpointsBelowCurrent w)
    (hf : w.forkData.epoch ≤ computeEpochAtSlot w.slot ∧ w.forkData.currentVersion = gloasForkVersion)
    (hno : w.slot.toNat + 1 < 2 ^ 64) (hb : (w.slot.toNat + 1) % slotsPerEpoch = 0) :
    SimpleStateInvariants { w with slot := w.slot + 1 } := by
  obtain ⟨c1, c2, c3⟩ := hc
  obtain ⟨f1, f2⟩ := hf
  have hs := slot_succ_toNat w.slot hno
  have he : (computeEpochAtSlot (w.slot + 1)).toNat = (computeEpochAtSlot w.slot).toNat + 1 := by
    rw [computeEpochAtSlot_toNat, computeEpochAtSlot_toNat, hs,
      succ_div_eq _ _ slotsPerEpochPos, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  have hp := EthCLLib.Proofs.saturatingSub_toNat (computeEpochAtSlot (w.slot + 1)) 1
  rw [UInt64.toNat_one] at hp
  refine ⟨?_, hr, ⟨c1, c2, ?_⟩, ⟨?_, f2⟩⟩
  · show w.latestBlockHeader.slot ≤ w.slot + 1
    simp only [UInt64.le_iff_toNat_le] at hh ⊢
    omega
  · show w.currentJustifiedCheckpoint.epoch ≤ saturatingSub (computeEpochAtSlot (w.slot + 1)) 1
    simp only [UInt64.le_iff_toNat_le] at c3 ⊢
    omega
  · show w.forkData.epoch ≤ computeEpochAtSlot (w.slot + 1)
    simp only [UInt64.le_iff_toNat_le] at f1 ⊢
    omega

/-! ## The three parts of an iteration -/

variable [HasherTag] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- `process_slot` caches the state and block roots and fills the header's empty state root. The
header's slot stays. -/
theorem processSlot_keepsCore : KeepsCore (processSlot (StateTransition := GloasRun)) := by
  intro c v hv
  unfold processSlot
  run_ensures
  frame_close

/-- What epoch processing leaves at the last slot of an epoch: every value
`SimpleStateInvariants` reads except the checkpoints is the start's, the checkpoints are bounded
by the current epoch, and the registry sizes agree. -/
def EpochPost (w v : BeaconState) : Prop :=
  w.slot = v.slot ∧ w.latestBlockHeader.slot = v.latestBlockHeader.slot ∧
  w.forkData = v.forkData ∧ CheckpointsBelowCurrent w ∧ RegistrySizes w

omit [Config] [HasherTag] [CryptoBackend] in
/-- The sixteen `KeepsCore` substeps after justification keep the post-justification core
values, so the final state agrees with the post-justification state on them. -/
theorem epochPost_of_stepInv {v w1 w : BeaconState} (hs : w1.slot = v.slot)
    (hh : w1.latestBlockHeader.slot = v.latestBlockHeader.slot) (hf : w1.forkData = v.forkData)
    (hc : CheckpointsBelowCurrent w1) (hw : StepInv (coreFields w1) w) : EpochPost w v := by
  obtain ⟨hcore, hreg⟩ := hw
  simp only [coreFields, CoreFields.mk.injEq] at hcore
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hcore
  refine ⟨e1.trans hs, e2.trans hh, e3.trans hf, ?_, hreg⟩
  unfold CheckpointsBelowCurrent
  rw [e4, e5, e6, e1]
  exact hc

theorem processEpoch_ensures (v : BeaconState) (hv : SimpleStateInvariants v) :
    RunEnsures v (processEpoch (StateTransition := GloasRun)) (fun _ w => EpochPost w v) := by
  unfold processEpoch
  run_ensures
  refine (processJustificationAndFinalization_ensures v hv.checkpointOrder).weaken
    fun _ w1 h1 => ?_
  obtain ⟨⟨hs, hh, hf, hl⟩, hc⟩ := h1
  have _hst : StepInv (coreFields w1) w1 := ⟨rfl, hv.registrySizes.of_listSizes hl⟩
  run_ensures
  call processInactivityUpdates_keepsCore
  run_ensures
  call processRewardsAndPenalties_keepsCore
  run_ensures
  call processRegistryUpdates_keepsCore
  run_ensures
  call processSlashings_keepsCore
  run_ensures
  call processEth1DataReset_keepsCore
  run_ensures
  call processPendingDeposits_keepsCore
  run_ensures
  call processPendingConsolidations_keepsCore
  run_ensures
  call processBuilderPendingPayments_keepsCore
  run_ensures
  call processEffectiveBalanceUpdates_keepsCore
  run_ensures
  call processSlashingsReset_keepsCore
  run_ensures
  call processRandaoMixesReset_keepsCore
  run_ensures
  call processHistoricalSummariesUpdate_keepsCore
  run_ensures
  call processParticipationFlagUpdates_keepsCore
  run_ensures
  call processSyncCommitteeUpdates_keepsCore
  run_ensures
  call processProposerLookahead_keepsCore
  run_ensures
  call processPtcWindow_keepsCore
  exact epochPost_of_stepInv hs hh hf hc (by assumption)

/-! ## `process_slots` -/

/-- `processSlots target` from a state that satisfies the invariants ends at `slot = target`, past
the start's slot, at a state that satisfies them. -/
theorem processSlots_ensures (target : Slot) (v : BeaconState) (hv : SimpleStateInvariants v) :
    RunEnsures v (processSlots (StateTransition := GloasRun) target)
      (fun _ w => w.slot = target ∧ v.slot < target ∧ SimpleStateInvariants w) := by
  unfold processSlots
  run_ensures
  rename_i hlt
  simp only [box_reduce] at hlt
  have hlt' : v.slot.toNat < target.toNat := UInt64.lt_iff_toNat_lt.mp hlt
  have hn : (target - v.slot).toNat = target.toNat - v.slot.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
  have hn' : (target - (pureState v).view.slot).toNat = target.toNat - v.slot.toNat := hn
  have htgt : target.toNat < 2 ^ 64 := target.toNat_lt
  refine runEnsures_forIn_range _
    (fun (i : Nat) (_ : PUnit) (w : BeaconState) =>
      w.slot.toNat = v.slot.toNat + i ∧ SimpleStateInvariants w) _ ?_ ?_ _ ⟨by simp, hv⟩
  · intro i b w hi ⟨hw, hinv⟩
    refine runEnsures_bind ((processSlot_keepsCore (coreFields w) w
      ⟨rfl, hinv.registrySizes⟩).weaken fun _ w1 h1 => ?_)
    have hinv1 := SimpleStateInvariants.of_coreFields_eq h1.1 h1.2 hinv
    have hs1 : w1.slot = w.slot := congrArg CoreFields.slot h1.1
    have hno : w1.slot.toNat + 1 < 2 ^ 64 := by rw [hs1]; omega
    run_ensures
    · rename_i hb
      simp only [box_reduce, beq_iff_eq] at hb
      have hb' : (w1.slot.toNat + 1) % slotsPerEpoch = 0 := by
        have := congrArg UInt64.toNat hb
        rwa [UInt64.toNat_mod, slot_succ_toNat _ hno, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt]
          at this
      refine (processEpoch_ensures w1 hinv1).weaken fun _ w2 h2 => ?_
      obtain ⟨e1, e2, e3, e4, e5⟩ := h2
      run_ensures
      show ({ w2 with slot := w2.slot + 1 } : BeaconState).slot.toNat = v.slot.toNat + (i + 1) ∧
        SimpleStateInvariants { w2 with slot := w2.slot + 1 }
      have hno2 : w2.slot.toNat + 1 < 2 ^ 64 := by rw [e1]; exact hno
      refine ⟨?_, SimpleStateInvariants.succ_slot_boundary ?_ e5 e4 ?_ hno2 (by rw [e1]; exact hb')⟩
      · show (w2.slot + 1).toNat = _
        rw [slot_succ_toNat _ hno2, e1, hs1, hw]; omega
      · rw [e2, e1]; exact hinv1.headerSlotLe
      · rw [e3, e1]; exact hinv1.forkConsistent
    · rename_i hb
      simp only [box_reduce, beq_iff_eq] at hb
      have hb' : (w1.slot.toNat + 1) % slotsPerEpoch ≠ 0 := by
        intro h
        apply hb
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, slot_succ_toNat _ hno, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt, h]
        rfl
      show ({ w1 with slot := w1.slot + 1 } : BeaconState).slot.toNat = v.slot.toNat + (i + 1) ∧
        SimpleStateInvariants { w1 with slot := w1.slot + 1 }
      refine ⟨?_, hinv1.succ_slot hno hb'⟩
      show (w1.slot + 1).toNat = _
      rw [slot_succ_toNat _ hno, hs1, hw]; omega
  · intro b w ⟨hw, hinv⟩
    run_ensures
    exact ⟨UInt64.toNat_inj.mp (by omega), hlt, hinv⟩

end

end EthCLSpecs.Proofs.Gloas
