import EthCLSpecs.Proofs.Fulu.Invariants.Helpers
import EthCLLib.Proofs.Arith

/-!
# `EthCLSpecs.Proofs.Fulu.Invariants.Justification`: justification keeps the checkpoints in order

`processJustificationAndFinalization` (`Fulu/EpochProcessing.lean:78-85`) is the only Fulu
step that writes the three checkpoints. It runs at the last slot of an epoch `E`, through
`weighJustificationAndFinalization` (`Fulu/EpochProcessing.lean:33-75`), which

* moves the old current-justified checkpoint into `previousJustifiedCheckpoint`;
* leaves `currentJustifiedCheckpoint` alone, or sets it to the previous epoch `E - 1` or to
  `E`, when that epoch's target reaches two thirds of the stake;
* leaves `finalizedCheckpoint` alone, or sets it to the old previous-justified or the old
  current-justified checkpoint.

So from a state whose checkpoints are ordered and bounded by the **previous** epoch
(`CheckpointsBelowPrevious`), the step reaches a state whose checkpoints are ordered and
bounded by the **current** epoch (`CheckpointsBelowCurrent`). The slot increment that follows
the epoch's processing moves the state into `E + 1`, whose previous epoch is `E`, and so
restores the first bound. The step writes no other field `SimpleStateInvariants` reads
(`JFFrame`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag]

/-- The checkpoints are ordered and the current-justified epoch is at most the previous
epoch: the `checkpointOrder` field of `SimpleStateInvariants`. -/
def CheckpointsBelowPrevious (v : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
  v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
  v.currentJustifiedCheckpoint.epoch ≤ saturatingSub (computeEpochAtSlot v.slot) 1

/-- The checkpoints are ordered and the current-justified epoch is at most the current epoch:
what holds between an epoch's processing and the slot increment that ends it. -/
def CheckpointsBelowCurrent (v : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
  v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
  v.currentJustifiedCheckpoint.epoch ≤ computeEpochAtSlot v.slot

/-- `w` agrees with `v` on every field `SimpleStateInvariants` reads except the checkpoints. -/
def JFFrame (w v : BeaconState) : Prop :=
  w.slot = v.slot ∧ w.latestBlockHeader.slot = v.latestBlockHeader.slot ∧
  w.forkData = v.forkData ∧ listSizes w = listSizes v

omit [Preset] [HasherTag] in
/-- The ordering argument, on plain epochs. `fin`, `prev`, `curr` are the old checkpoint epochs,
`p = saturatingSub e 1` and `e` the previous and current epochs; the new epochs are drawn from
the sets the step can choose. -/
theorem checkpoint_order_step {fin prev curr e fin' curr' : UInt64}
    (h1 : fin ≤ prev) (h2 : prev ≤ curr) (h3 : curr ≤ saturatingSub e 1)
    (hcurr' : curr' = curr ∨ curr' = saturatingSub e 1 ∨ curr' = e)
    (hfin' : fin' = fin ∨ fin' = prev ∨ fin' = curr) :
    fin' ≤ curr ∧ curr ≤ curr' ∧ curr' ≤ e := by
  have hp : (saturatingSub e 1).toNat = e.toNat - 1 := EthCLLib.Proofs.saturatingSub_toNat e 1
  simp only [UInt64.le_iff_toNat_le] at h1 h2 h3 ⊢
  rcases hcurr' with rfl | rfl | rfl <;> rcases hfin' with rfl | rfl | rfl <;> omega

variable [Config] [CryptoBackend]

/-- Step over a read-only call with any postcondition: the state after it is the state
before it. -/
local macro "call_reads " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunEnsures.weaken ($h _) (fun _ _ hro => ?_); subst hro))

/-- One of the three choices the step makes for a checkpoint, by `rfl`. -/
local macro "pick_choice" : tactic =>
  `(tactic| first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))

set_option maxHeartbeats 4000000 in
omit [Config] [CryptoBackend] in
theorem weighJustificationAndFinalization_ensures (total prevT currT : Gwei) (v : BeaconState)
    (hv : CheckpointsBelowPrevious v) :
    RunEnsures v (weighJustificationAndFinalization (StateTransition := FuluRun) total prevT currT)
      (fun _ w => JFFrame w v ∧ CheckpointsBelowCurrent w) := by
  unfold weighJustificationAndFinalization
  run_ensures
  all_goals try (call_reads getBlockRoot_readsOnly _ _; run_ensures)
  all_goals try (call_reads getBlockRoot_readsOnly _ _; run_ensures)
  all_goals refine runEnsures_modifyThe_view ?_ ?_
  all_goals simp only [box_reduce, Id.run, *]
  all_goals repeat' split_ite
  all_goals first
    | rfl
    | exact ⟨⟨rfl, rfl, rfl, rfl⟩,
        checkpoint_order_step hv.1 hv.2.1 hv.2.2 (by pick_choice) (by pick_choice)⟩

omit [HasherTag] [Config] [CryptoBackend] in
/-- The previous-epoch bound implies the current-epoch bound: the previous epoch is at most the
current one. -/
theorem CheckpointsBelowPrevious.belowCurrent {v : BeaconState} (hv : CheckpointsBelowPrevious v) :
    CheckpointsBelowCurrent v :=
  ⟨hv.1, hv.2.1, by
    have h := hv.2.2
    have hle := EthCLLib.Proofs.saturatingSub_le (computeEpochAtSlot v.slot) 1
    simp only [UInt64.le_iff_toNat_le] at h hle ⊢
    omega⟩

omit [Config] [CryptoBackend] in
theorem processJustificationAndFinalization_ensures (v : BeaconState)
    (hv : CheckpointsBelowPrevious v) :
    RunEnsures v (processJustificationAndFinalization (StateTransition := FuluRun))
      (fun _ w => JFFrame w v ∧ CheckpointsBelowCurrent w) := by
  unfold processJustificationAndFinalization
  run_ensures
  · exact ⟨⟨rfl, rfl, rfl, rfl⟩, hv.belowCurrent⟩
  · exact weighJustificationAndFinalization_ensures _ _ _ v hv

end

end EthCLSpecs.Proofs.Fulu
