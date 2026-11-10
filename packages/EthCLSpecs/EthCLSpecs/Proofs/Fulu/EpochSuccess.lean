import EthCLSpecs.Proofs.Fulu.EpochSuccess.Deposits
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Rewards
import EthCLSpecs.Proofs.Fulu.Invariants.Slots

/-!
# `EthCLSpecs.Proofs.Fulu.EpochSuccess`: `process_epoch` cannot fail on an `EpochSafe` state

The main theorem, `processEpoch_succeeds`: from a state that satisfies `EpochSafe b (n + 1)`, at
the last slot of an epoch, `processEpoch` returns `.ok`, and the post-state satisfies
`EpochSafe b n`. Two premises sit outside the state:

* `RewardsWithin b.reward v` bounds each flag reward (`Proofs/Fulu/EpochSafe.lean` gives the
  reason it is a premise of each call);
* `ZeroChunksOften` is the hash premise for the two balance-weighted selections
  (`EthCLLib/Proofs/ZeroChunks.lean`).

The proof runs the fifteen substeps in order. Each takes a `Stage` state to a `Stage` state with
updated caps (`Proofs/Fulu/EpochSuccess/Stage.lean`); this module supplies each substep's room
from `EpochSafe` and reads `EpochSafe b n` back off the final `Stage`. Justification and the
inactivity update also keep the fields the reward formula reads, so the reward premise on the
start carries to the rewards substep.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [Config] [HasherTag] [CryptoBackend]

theorem processEpoch_succeeds [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max Const.syncCommitteeSize 1)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) :
    RunSucceeds v (processEpoch (StateTransition := FuluRun)) (fun _ w => EpochSafe b n w) := by
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
  unfold processEpoch
  refine runSucceeds_bind_cut _ (processJustificationAndFinalization_succeeds hst0 hpos hslotroom.1)
    (fun _ w1 h1 => ?_)
  obtain ⟨hs1, hr1⟩ := h1
  refine runSucceeds_bind_cut _ (processInactivityUpdates_succeeds hs1) (fun _ w2 h2 => ?_)
  obtain ⟨hs2, hr2⟩ := h2
  refine runSucceeds_bind_cut _ (processRewardsAndPenalties_succeeds hs2 (hr.congr (hr2.trans hr1))
    (by dsimp only; omega)) (fun _ w3 hs3 => ?_)
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
    (by dsimp only; exact hroom4)) (fun _ w4 hs4 => ?_)
  refine runSucceeds_bind_cut _ (processSlashings_succeeds hs4) (fun _ w5 hs5 => ?_)
  refine runSucceeds_bind_cut _ (processEth1DataReset_succeeds hs5) (fun _ w6 hs6 => ?_)
  refine runSucceeds_bind_cut _ (processPendingDeposits_succeeds hs6 (by dsimp only; omega)
    (by dsimp only; omega)) (fun _ w7 hs7 => ?_)
  refine runSucceeds_bind_cut _ (processPendingConsolidations_succeeds hs7 (by dsimp only; omega))
    (fun _ w8 hs8 => ?_)
  refine runSucceeds_bind_cut _ (processEffectiveBalanceUpdates_succeeds hs8) (fun _ w9 hs9 => ?_)
  refine runSucceeds_bind_cut _ (processSlashingsReset_succeeds hs9) (fun _ w10 hs10 => ?_)
  refine runSucceeds_bind_cut _ (processRandaoMixesReset_succeeds hs10) (fun _ w11 hs11 => ?_)
  refine runSucceeds_bind_cut _ (processHistoricalSummariesUpdate_succeeds hs11
    (by have := hs11.historyBound; dsimp only at this; omega)) (fun _ w12 hs12 => ?_)
  refine runSucceeds_bind_cut _ (processParticipationFlagUpdates_succeeds hs12) (fun _ w13 hs13 => ?_)
  refine runSucceeds_bind_cut _ (processSyncCommitteeUpdates_succeeds hs13
    (hz.mono (Nat.le_max_left _ _))) (fun _ w14 hs14 => ?_)
  refine (processProposerLookahead_succeeds hs14 (hz.mono (Nat.le_max_right _ _))).weaken
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
    by rw [hslot]; exact hslotroom, by omega, ?_, by omega, ⟨by omega, ?_⟩,
    by rw [hslot]; exact hs.live⟩
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
    (hz : ZeroChunksOften (max Const.syncCommitteeSize 1)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) :
    ∃ w, runPure (processEpoch (StateTransition := FuluRun)) v = .ok ((), w) ∧ EpochSafe b n w := by
  obtain ⟨⟨⟩, w, hrun, hw⟩ := (processEpoch_succeeds hz v hpos hv hr).runPure_ok
  exact ⟨w, hrun, hw⟩

/-- With `SimpleStateInvariants` on the start, the post-state also keeps the slot, the header
slot and the fork, the registry sizes, and the checkpoint order up to the current epoch
(`EpochPost`, from the partial-correctness `processEpoch_ensures`). -/
theorem processEpoch_succeeds_simple [PresetValid] [ConfigValid]
    (hz : ZeroChunksOften (max Const.syncCommitteeSize 1)) {b : EpochBudget} {n : Nat}
    (v : BeaconState) (hpos : (v.slot.toNat + 1) % Const.slotsPerEpoch = 0)
    (hv : EpochSafe b (n + 1) v) (hr : RewardsWithin b.reward v) (hsimple : SimpleStateInvariants v) :
    RunSucceeds v (processEpoch (StateTransition := FuluRun))
      (fun _ w => EpochSafe b n w ∧ EpochPost w v) :=
  (processEpoch_succeeds hz v hpos hv hr).and_ensures (processEpoch_ensures v hsimple)

end

end EthCLSpecs.Proofs.Fulu
