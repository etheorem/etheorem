import EthCLSpecs.Proofs.Gloas.EpochSuccess.Deposits
import EthCLSpecs.Proofs.Gloas.EpochSuccess.Rewards
import EthCLSpecs.Proofs.Gloas.EpochSuccess.Consolidations
import EthCLSpecs.Proofs.Gloas.Invariants.Slots

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess`: `process_epoch` cannot fail on an `EpochSafe` state

The Gloas counterpart of `Proofs/Fulu/EpochSuccess.lean`, over Gloas's seventeen substeps: the
Fulu fifteen, the builder-payment step, and the payload-timeliness committee window. The hash
premise now covers the committee's size too.

The main theorem, `processEpoch_succeeds`: from a state that satisfies `EpochSafe b (n + 1)`, at
the last slot of an epoch, `processEpoch` returns `.ok`, and the post-state satisfies
`EpochSafe b n`. Two premises sit outside the state:

* `RewardsWithin b.reward v` bounds each flag reward (`Proofs/Gloas/EpochSafe.lean` gives the
  reason it is a premise of each call);
* `ZeroChunksOften` is the hash premise for the two balance-weighted selections
  (`EthCLLib/Proofs/ZeroChunks.lean`).

The proof runs the seventeen substeps in order. Each takes a `Stage` state to a `Stage` state with
updated caps (`Proofs/Gloas/EpochSuccess/Stage.lean`); this module supplies each substep's room
from `EpochSafe` and reads `EpochSafe b n` back off the final `Stage`. Justification and the
inactivity update also keep the fields the reward formula reads, so the reward premise on the
start carries to the rewards substep.

The epoch transition follows, as in Fulu. From the last slot of an epoch, `processSlots`
(`Gloas/Transition.lean:77-82`) with target `slot + 1` runs `processSlot`, `processEpoch` and the
slot increment once.
Gloas's `processSlot` also clears the next slot's payload-availability bit, and `EpochSafe` does
not read that field either. So the run succeeds and ends at an `EpochSafe b n` state moved one
slot on (`processSlots_epoch_succeeds`), and `processSlots_epoch_ok` adds `SimpleStateInvariants`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Gloas

section

variable [Preset] [Config] [HasherTag] [CryptoBackend]

/-- `processEpoch` succeeds from an `EpochSafe b (n + 1)` state at the last slot of an epoch, under
the reward and hash premises, and ends at an `EpochSafe b n` state. -/
theorem processEpoch_succeeds [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max (max Const.syncCommitteeSize 1) Const.ptcSize)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) :
    RunSucceeds v (processEpoch (StateTransition := GloasRun)) (fun _ w => EpochSafe b n w) := by
  obtain ⟨hgrow, hbal⟩ := hv.balanceRoom
  -- The balance cap the budget leaves for this call, and the room each substep raises it into.
  have hG : (n + 1 + 1) * b.growth = (n + 1) * b.growth + b.growth := Nat.succ_mul _ _
  have hst0 := Stage.start hv (2 ^ 64 - 1 - (n + 1 + 1) * b.growth)
    (fun x hx => by have := hbal x hx; omega)
  have hgrowth : b.growth = 3 * b.reward + Const.maxPendingDepositsPerEpoch * b.deposit +
      b.consolidations * Const.maxEffectiveBalanceElectra := rfl
  have hslotroom := hv.slotRoom
  have hpot := hv.registryRoom
  have hexit := hv.exitRoom
  have hhist := hv.historyRoom
  have hptc := hv.ptcRoom
  -- The registry indexes below `2^64` at every stage: the potential never passes the start's.
  have hreg0 : registryPotential v + 0 < 2 ^ 64 := by omega
  unfold processEpoch
  refine runSucceeds_bind_cut _ (processJustificationAndFinalization_succeeds hst0 hpos hslotroom.1)
    (fun _ w1 h1 => ?_)
  obtain ⟨hs1, hr1⟩ := h1
  refine runSucceeds_bind_cut _ (processInactivityUpdates_succeeds hs1) (fun _ w2 h2 => ?_)
  obtain ⟨hs2, hr2⟩ := h2
  refine runSucceeds_bind_cut _ (processRewardsAndPenalties_succeeds hs2 (hr.congr (hr2.trans hr1))
    hreg0 (by dsimp only; omega)) (fun _ w3 hs3 => ?_)
  -- The registry has not grown yet, so the ejections are bounded by the start's potential.
  have hv3 : w3.validators.val.size ≤ registryPotential v := by
    have := hs3.potential; unfold registryPotential at this ⊢; dsimp only at this; omega
  have hmul3 : w3.validators.val.size * ejectionStep ≤ (n + 1 + 1) * (ejectionStep * registryPotential v) :=
    calc w3.validators.val.size * ejectionStep ≤ registryPotential v * ejectionStep :=
          Nat.mul_le_mul_right _ hv3
      _ = 1 * (ejectionStep * registryPotential v) := by rw [Nat.one_mul, Nat.mul_comm]
      _ ≤ (n + 1 + 1) * (ejectionStep * registryPotential v) := Nat.mul_le_mul_right _ (by omega)
  have hroom4 : exitStart v + 0 + w3.validators.val.size * ejectionStep +
      Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64 := by
    have := hexit
    generalize w3.validators.val.size * ejectionStep = A at hmul3 ⊢
    generalize (n + 1 + 1) * (ejectionStep * registryPotential v) = B at hmul3 this
    omega
  refine runSucceeds_bind_cut _ (processRegistryUpdates_succeeds hs3 hslotroom.2
    (by dsimp only; exact hroom4) (hs3.vFits hreg0)) (fun _ w4 hs4 => ?_)
  refine runSucceeds_bind_cut _ (processSlashings_succeeds hs4 (hs4.vFits hreg0)) (fun _ w5 hs5 => ?_)
  refine runSucceeds_bind_cut _ (processEth1DataReset_succeeds hs5) (fun _ w6 hs6 => ?_)
  refine runSucceeds_bind_cut _ (processPendingDeposits_succeeds hs6 (by dsimp only; omega)
    (by dsimp only; omega)) (fun _ w7 hs7 => ?_)
  refine runSucceeds_bind_cut _ (processPendingConsolidations_succeeds hs7 (by dsimp only; omega))
    (fun _ w8 hs8' => ?_)
  refine runSucceeds_bind_cut _ (processBuilderPendingPayments_succeeds hs8') (fun _ w8' hs8 => ?_)
  refine runSucceeds_bind_cut _ (processEffectiveBalanceUpdates_succeeds hs8) (fun _ w9 hs9 => ?_)
  refine runSucceeds_bind_cut _ (processSlashingsReset_succeeds hs9) (fun _ w10 hs10 => ?_)
  refine runSucceeds_bind_cut _ (processRandaoMixesReset_succeeds hs10) (fun _ w11 hs11 => ?_)
  refine runSucceeds_bind_cut _ (processHistoricalSummariesUpdate_succeeds hs11
    (by have := hs11.historyBound; dsimp only at this; omega)) (fun _ w12 hs12 => ?_)
  refine runSucceeds_bind_cut _ (processParticipationFlagUpdates_succeeds hs12) (fun _ w13 hs13 => ?_)
  have hmax : max Const.syncCommitteeSize 1 ≤ max (max Const.syncCommitteeSize 1) Const.ptcSize :=
    Nat.le_max_left _ _
  refine runSucceeds_bind_cut _ (processSyncCommitteeUpdates_succeeds hs13
    (hz.mono (Nat.le_trans (Nat.le_max_left _ _) hmax))) (fun _ w14 hs14 => ?_)
  refine runSucceeds_bind_cut _ (processProposerLookahead_succeeds hs14
    (hz.mono (Nat.le_trans (Nat.le_max_right _ _) hmax)) (hs14.vFits hreg0)) (fun _ w15 hs15 => ?_)
  refine (processPtcWindow_succeeds hs15 (hz.mono (Nat.le_max_right _ _)) hptc).weaken
    (fun _ w hs => ?_)
  -- Read `EpochSafe b n` off the final stage.
  dsimp only at hs
  have hslot := hs.slot
  have hpotw := hs.potential
  have hxb := hs.exitBound
  have hhb := hs.historyBound
  dsimp only at hpotw hxb hhb
  have hpotw' : registryPotential w ≤ registryPotential v := by omega
  refine ⟨hs.registrySizes, hs.consolidationIdx, hs.consolidationCount, hs.effCap, hs.depositCap,
    by rw [hslot]; exact hslotroom, by omega, by rw [hslot]; exact hptc, ?_, by omega, ⟨by omega, ?_⟩,
    by rw [hslot]; exact hs.live, by rw [hslot]; exact hs.liveUnslashed,
    by rw [hslot]; exact hs.liveCount⟩
  · -- The exit budget: one unit spent on this call's ejections, at most one step per validator.
    have hX : w3.validators.val.size * ejectionStep ≤ ejectionStep * registryPotential v := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hv3
    have hZ : (n + 1) * (ejectionStep * registryPotential w) ≤
        (n + 1) * (ejectionStep * registryPotential v) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpotw')
    have hS : (n + 1 + 1) * (ejectionStep * registryPotential v) =
        (n + 1) * (ejectionStep * registryPotential v) + ejectionStep * registryPotential v :=
      Nat.succ_mul _ _
    have : exitStart w ≤ exitStart v + w3.validators.val.size * ejectionStep := by omega
    generalize w3.validators.val.size * ejectionStep = A at hX this
    generalize ejectionStep * registryPotential v = X at hX hS hZ hexit
    generalize (n + 1) * X = Y at hS hZ
    generalize (n + 1 + 1) * X = Y2 at hS hexit
    generalize (n + 1) * (ejectionStep * registryPotential w) = Z at hZ ⊢
    omega
  · intro x hx
    have := hs.balanceBound x hx
    dsimp only at this
    omega

/-- The value-level reading of `processEpoch_succeeds`: `runPure` returns `.ok`, and the
post-state satisfies `EpochSafe` with one unit less of budget. -/
theorem processEpoch_ok [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max (max Const.syncCommitteeSize 1) Const.ptcSize)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) :
    ∃ w, runPure (processEpoch (StateTransition := GloasRun)) v = .ok ((), w) ∧ EpochSafe b n w := by
  obtain ⟨⟨⟩, w, hrun, hw⟩ := (processEpoch_succeeds hz v hpos hv hr).runPure_ok
  exact ⟨w, hrun, hw⟩

/-- With `SimpleStateInvariants` on the start, the post-state also keeps the slot, the header
slot and the fork, the registry sizes, and the checkpoint order up to the current epoch
(`EpochPost`, from the partial-correctness `processEpoch_ensures`). -/
theorem processEpoch_succeeds_simple [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max (max Const.syncCommitteeSize 1) Const.ptcSize)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) (hsimple : SimpleStateInvariants v) :
    RunSucceeds v (processEpoch (StateTransition := GloasRun))
      (fun _ w => EpochSafe b n w ∧ EpochPost w v) :=
  (processEpoch_succeeds hz v hpos hv hr).and_ensures (processEpoch_ensures v hsimple)

/-! ## The epoch transition -/

omit [Config] [CryptoBackend] in
/-- `processSlot` always succeeds. It writes the state-root and block-root caches, the latest
header, and the payload-availability bits, and leaves every other field. -/
theorem processSlot_succeeds (v : BeaconState) :
    RunSucceeds v (processSlot (StateTransition := GloasRun)) (fun _ w => ∃ sr lbh br epa,
      w = { v with
        stateRoots := sr
        latestBlockHeader := lbh
        blockRoots := br
        executionPayloadAvailability := epa }) := by
  unfold processSlot
  run_succeeds
  simp only [box_reduce]
  exact ⟨_, _, _, _, rfl⟩

/-- The step across an epoch boundary: from the last slot of an epoch, `processSlots (slot + 1)`
succeeds and ends at an `EpochSafe b n` state with the slot moved one on. -/
theorem processSlots_epoch_succeeds [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max (max Const.syncCommitteeSize 1) Const.ptcSize)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) :
    RunSucceeds v (processSlots (StateTransition := GloasRun) (v.slot + 1))
      (fun _ w => ∃ u, EpochSafe b n u ∧ w = { u with slot := u.slot + 1 }) := by
  have hno : v.slot.toNat + 1 < 2 ^ 64 := by
    have := hv.slotRoom.1
    have : 2 ≤ Const.slotsPerEpoch := (PresetValid.toFulu (self := ‹_›)).twoLeSlotsPerEpoch
    have : 2 * Const.slotsPerEpoch ≤ Const.slotsPerHistoricalRoot :=
      (PresetValid.toFulu (self := ‹_›)).twoSlotsPerEpochLeSlotsPerHistoricalRoot
    omega
  unfold processSlots
  run_succeeds
  · rename_i hlt
    -- The target is one slot on, so the loop runs once.
    have hcount : (v.slot + 1 - (pureState v).view.slot).toNat = 1 := by
      have hlt' : v.slot < v.slot + 1 := hlt
      show (v.slot + 1 - v.slot).toNat = 1
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt'), slot_succ_toNat _ hno]
      omega
    rw [hcount]
    refine RunSucceeds.weaken (P := fun _ w => ∃ u, EpochSafe b n u ∧ w = { u with slot := u.slot + 1 })
      ?_ (fun _ w h => runSucceeds_pure h)
    refine runSucceeds_forIn_range 1
      (fun i _ w => (i = 0 ∧ w = v) ∨ (i = 1 ∧ ∃ u, EpochSafe b n u ∧ w = { u with slot := u.slot + 1 }))
      (fun _ w => ∃ u, EpochSafe b n u ∧ w = { u with slot := u.slot + 1 }) ?_ ?_ _ (Or.inl ⟨rfl, rfl⟩)
    · intro i _ w hi hI
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ w = v := by
        rcases hI with h | h
        · exact h
        · omega
      refine runSucceeds_bind_cut _ (processSlot_succeeds _) (fun _ w1 h1 => ?_)
      obtain ⟨sr, lbh, br, epa, h1⟩ := h1
      -- `EpochSafe` and the reward formula read none of the fields `processSlot` writes.
      have hv1 : EpochSafe b (n + 1) w1 := by
        subst h1
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hv
        exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
      have hr1 : RewardsWithin b.reward w1 := by subst h1; exact hr
      have hs1 : w1.slot = w.slot := by subst h1; rfl
      have hno1 : w1.slot.toNat + 1 < 2 ^ 64 := by rw [hs1]; exact hno
      run_succeeds
      · refine (processEpoch_succeeds hz w1 (by rw [hs1]; exact hpos) hv1 hr1).weaken
          (fun _ w2 h2 => ?_)
        run_succeeds
        exact Or.inr ⟨trivial, w2, h2, rfl⟩
      · -- The skip branch: the slot is the last of its epoch, so the guard holds.
        rename_i hc
        simp only [box_reduce, beq_iff_eq] at hc
        exfalso
        apply hc
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, slot_succ_toNat _ hno1, UInt64.toNat_ofNat_of_lt' Const.slotsPerEpochLt,
          hs1, hpos]
        rfl
    · intro _ w h
      rcases h with h | h
      · omega
      · exact h.2
  · rename_i hc
    apply hc
    show v.slot < v.slot + 1
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hno]
    omega

/-- The value-level epoch transition with the state invariants: `runPure` of
`processSlots (slot + 1)` returns `.ok` at an `EpochSafe b n` state moved one slot on, and the end
state satisfies `SimpleStateInvariants`. -/
theorem processSlots_epoch_ok [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max (max Const.syncCommitteeSize 1) Const.ptcSize)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) (hsimple : SimpleStateInvariants v) :
    ∃ w, runPure (processSlots (StateTransition := GloasRun) (v.slot + 1)) v = .ok ((), w) ∧
      (∃ u, EpochSafe b n u ∧ w = { u with slot := u.slot + 1 }) ∧ SimpleStateInvariants w := by
  obtain ⟨⟨⟩, w, hrun, hu, -, -, hw⟩ :=
    ((processSlots_epoch_succeeds hz v hpos hv hr).and_ensures
      (processSlots_ensures (v.slot + 1) v hsimple)).runPure_ok
  exact ⟨w, hrun, hu, hw⟩

end

end EthCLSpecs.Proofs.Gloas
