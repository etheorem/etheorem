import EthCLSpecs.Proofs.Fulu.EpochSuccess.Stage
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Selection
import EthCLSpecs.Proofs.Fulu.Invariants.Slots

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag] [Config]

omit [Config] in
/-- `getCurrentEpoch` succeeds and keeps the state. -/
theorem getCurrentEpoch_succeeds (w : BeaconState) :
    RunSucceeds w (getCurrentEpoch (StateTransition := FuluRun)) (fun _ w' => w' = w) := by
  unfold getCurrentEpoch
  run_succeeds

omit [Config] in
/-- `getRandaoMix` succeeds and keeps the state. -/
theorem getRandaoMix_succeeds (w : BeaconState) (e : Epoch) :
    RunSucceeds w (getRandaoMix (StateTransition := FuluRun) e) (fun _ w' => w' = w) := by
  unfold getRandaoMix
  run_succeeds

omit [Config] in
/-- `getBlockRootAtSlot` succeeds when its recency asserts hold and the window bound does not
overflow, and keeps the state. -/
theorem getBlockRootAtSlot_succeeds (s : BeaconState) (sl : Slot) (u : BeaconState)
    (h1 : sl < s.slot) (h2 : sl.toNat + Const.slotsPerHistoricalRoot < 2 ^ 64)
    (h3 : s.slot.toNat ≤ sl.toNat + Const.slotsPerHistoricalRoot) :
    RunSucceeds u (getBlockRootAtSlot (StateTransition := FuluRun) (pureState s) sl)
      (fun _ u' => u' = u) := by
  have hsphr : (UInt64.ofNat Const.slotsPerHistoricalRoot).toNat = Const.slotsPerHistoricalRoot :=
    UInt64.toNat_ofNat_of_lt' Const.slotsPerHistoricalRootLt
  unfold getBlockRootAtSlot
  run_succeeds
  · exact uint64_not_add_lt_of_toNat (by rw [hsphr]; exact h2)
  · rename_i hc
    apply hc
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, hsphr, Nat.mod_eq_of_lt h2]
    exact h3
  · rename_i hc
    exact hc h1

omit [Config] in
/-- `getBlockRoot` at an epoch whose first slot lies in the state's root window. -/
theorem getBlockRoot_succeeds (s : BeaconState) (e : Epoch) (u : BeaconState)
    (h1 : e.toNat * Const.slotsPerEpoch < s.slot.toNat)
    (h2 : s.slot.toNat + Const.slotsPerHistoricalRoot < 2 ^ 64)
    (h3 : s.slot.toNat ≤ e.toNat * Const.slotsPerEpoch + Const.slotsPerHistoricalRoot) :
    RunSucceeds u (getBlockRoot (StateTransition := FuluRun) (pureState s) e)
      (fun _ u' => u' = u) := by
  have hspe : (UInt64.ofNat Const.slotsPerEpoch).toNat = Const.slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt' Const.slotsPerEpochLt
  have hslot : s.slot.toNat < 2 ^ 64 := s.slot.toNat_lt
  have hmul : (e * UInt64.ofNat Const.slotsPerEpoch).toNat = e.toNat * Const.slotsPerEpoch := by
    rw [UInt64.toNat_mul, hspe, Nat.mod_eq_of_lt (by omega)]
  unfold getBlockRoot
  exact getBlockRootAtSlot_succeeds s _ u (by rw [UInt64.lt_iff_toNat_lt, hmul]; exact h1)
    (by rw [hmul]; omega) (by rw [hmul]; exact h3)

/-- Step over a call to an accessor that succeeds and keeps the state. The state after the call
is replaced by the one before, so hypotheses about it still apply. -/
macro "ro_call " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunSucceeds.weaken $h (fun _ _ hro => ?_)
             replace hro := hro.symm
             subst hro))

theorem processInactivityUpdates_succeeds {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processInactivityUpdates (StateTransition := FuluRun)) (fun _ w' => Stage b v caps w') := by
  unfold processInactivityUpdates
  run_succeeds
  · exact hw
  · -- The scores loop runs inside the write; each step overwrites one score in place.
    refine runSucceeds_modifyThe (Exists.imp (fun _ h => ⟨h.1, hw.of_frame h.2⟩)
      (pureState_forIn_array_inv (fun s => stageFields s = stageFields w)
        (by
          intro _ s hs
          refine ⟨_, rfl, ?_⟩
          rw [← hs]
          simp [stageFields, listSizes, box_reduce, SizzLean.Proofs.sszListSet!_size]) _ _ rfl))

theorem processEth1DataReset_succeeds {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processEth1DataReset (StateTransition := FuluRun)) (fun _ w' => Stage b v caps w') := by
  unfold processEth1DataReset
  run_succeeds
  ro_call getCurrentEpoch_succeeds _
  run_succeeds
  all_goals stage_close

theorem processSlashingsReset_succeeds {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processSlashingsReset (StateTransition := FuluRun)) (fun _ w' => Stage b v caps w') := by
  unfold processSlashingsReset
  run_succeeds
  ro_call getCurrentEpoch_succeeds _
  run_succeeds
  stage_close

theorem processRandaoMixesReset_succeeds {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processRandaoMixesReset (StateTransition := FuluRun)) (fun _ w' => Stage b v caps w') := by
  unfold processRandaoMixesReset
  run_succeeds
  ro_call getCurrentEpoch_succeeds _
  run_succeeds
  ro_call getRandaoMix_succeeds _ _
  run_succeeds
  stage_close

omit [HasherTag] [Config] in
/-- At the last slot of epoch `E`, the first slots of `E` and of `E - 1` lie in the block-root
window, at a valid preset: `start < slot ≤ start + SLOTS_PER_HISTORICAL_ROOT`. -/
theorem epochStart_window [PresetValid] (slot : Slot) (hpos : (slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (e : Epoch) (he : e = computeEpochAtSlot slot ∨ e.toNat + 1 = (computeEpochAtSlot slot).toNat) :
    e.toNat * Const.slotsPerEpoch < slot.toNat ∧
      slot.toNat ≤ e.toNat * Const.slotsPerEpoch + Const.slotsPerHistoricalRoot := by
  have h2 := PresetValid.twoLeSlotsPerEpoch (self := ‹_›)
  have hh := PresetValid.twoSlotsPerEpochLeSlotsPerHistoricalRoot (self := ‹_›)
  have hdm := Nat.div_add_mod slot.toNat Const.slotsPerEpoch
  have hr : slot.toNat % Const.slotsPerEpoch = Const.slotsPerEpoch - 1 := by
    have := Nat.mod_lt slot.toNat (show 0 < Const.slotsPerEpoch by omega)
    have hsucc := Nat.add_mod slot.toNat 1 Const.slotsPerEpoch
    rw [hpos, Nat.mod_eq_of_lt (show 1 < Const.slotsPerEpoch by omega)] at hsucc
    rcases Nat.lt_or_ge (slot.toNat % Const.slotsPerEpoch + 1) Const.slotsPerEpoch with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hsucc; omega
    · omega
  rw [computeEpochAtSlot_toNat] at he
  rcases he with rfl | he
  · rw [computeEpochAtSlot_toNat, Nat.mul_comm]
    omega
  · have hmul : (e.toNat + 1) * Const.slotsPerEpoch = e.toNat * Const.slotsPerEpoch + Const.slotsPerEpoch :=
      Nat.succ_mul _ _
    rw [he, Nat.mul_comm] at hmul
    omega

set_option maxHeartbeats 4000000 in
theorem weighJustificationAndFinalization_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hpos : (w.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hroom : w.slot.toNat + Const.slotsPerHistoricalRoot < 2 ^ 64)
    (hE : 2 ≤ (computeEpochAtSlot w.slot).toNat) (totalActive prevTarget currTarget : Gwei) :
    RunSucceeds w (weighJustificationAndFinalization (StateTransition := FuluRun) totalActive prevTarget currTarget)
      (fun _ w' => Stage b v caps w') := by
  have hprev := epochStart_window w.slot hpos (previousEpochOf (pureState w)) (Or.inr (by
    show (EthCLLib.Spec.saturatingSub (computeEpochAtSlot w.slot) 1).toNat + 1 = _
    rw [EthCLLib.Proofs.saturatingSub_toNat]
    simp only [UInt64.toNat_one]
    omega))
  have hcurr := epochStart_window w.slot hpos (currentEpochOf (pureState w)) (Or.inl rfl)
  unfold weighJustificationAndFinalization
  run_succeeds
  all_goals (try (ro_call getBlockRoot_succeeds w (previousEpochOf (pureState w)) _ hprev.1 hroom hprev.2))
  all_goals (try run_succeeds)
  all_goals (try (ro_call getBlockRoot_succeeds w (currentEpochOf (pureState w)) _ hcurr.1 hroom hcurr.2))
  all_goals (try run_succeeds)
  all_goals refine runSucceeds_modifyThe_view ?_ (hw.of_frame ?_)
  all_goals simp only [box_reduce, Id.run, *]
  all_goals repeat' split_ite
  all_goals first
    | rfl
    | simp [stageFields, listSizes]

theorem processJustificationAndFinalization_succeeds [PresetValid] {b : EpochBudget}
    {v : BeaconState} {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hpos : (w.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hroom : w.slot.toNat + Const.slotsPerHistoricalRoot < 2 ^ 64) :
    RunSucceeds w (processJustificationAndFinalization (StateTransition := FuluRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processJustificationAndFinalization
  run_succeeds
  · exact hw
  · rename_i hc
    refine weighJustificationAndFinalization_succeeds hw hpos hroom ?_ _ _ _
    -- The step weighs only from epoch 2: the guard is `current_epoch <= GENESIS_EPOCH + 1`.
    have : ¬ (computeEpochAtSlot w.slot).toNat ≤ 1 := fun h => hc (by
      show computeEpochAtSlot w.slot ≤ 0 + 1
      rw [UInt64.le_iff_toNat_le]
      exact h)
    omega

theorem processSyncCommitteeUpdates_succeeds [CryptoBackend] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hz : ZeroChunksOften Const.syncCommitteeSize) :
    RunSucceeds w (processSyncCommitteeUpdates (StateTransition := FuluRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processSyncCommitteeUpdates
  run_succeeds
  · have hlive := hw.live.1
    rw [← hw.slot] at hlive
    exact getNextSyncCommittee_ok _ hz hlive.activeIndices_pos
  all_goals stage_close

theorem processProposerLookahead_succeeds {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w) (hz : ZeroChunksOften 1) :
    RunSucceeds w (processProposerLookahead (StateTransition := FuluRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processProposerLookahead
  run_succeeds
  · have hlive := hw.live.2
    rw [← hw.slot] at hlive
    exact getBeaconProposerIndices_ok _ _ hz hlive.activeIndices_pos
  all_goals stage_close

end

end EthCLSpecs.Proofs.Fulu
