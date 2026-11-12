import EthCLSpecs.Proofs.Gloas.EpochSafe
import EthCLLib.Proofs.RunSucceeds

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Stage`: what holds between the epoch substeps

The Gloas counterpart of the Fulu module of the same name, over Gloas's progressive lists.

`processEpoch` runs fifteen substeps from a start `v`. `Stage b n v caps w` is what each
intermediate state `w` satisfies: `v`'s slot, the registry facts of `EpochSafe`, and three bounds
that the substeps move, carried in `caps`. A substep's success lemma takes a `Stage` state to a
`Stage` state with updated `caps`:

* `caps.balance` bounds every balance. Rewards, deposits and consolidations raise it.
* `caps.exit` bounds how far `exitStart` has moved since `v`. Ejections raise it.
* `caps.history` bounds how many summaries have been appended since `v`.
* `caps.slack` lets the registry potential run ahead of `v`'s inside the deposit scan.

A substep that writes none of the fields `Stage` reads keeps it as it is: `Stage.of_frame` reads
the frame fact `stageFields w' = stageFields w`, and `stage_close` proves it for a record update
that leaves those fields alone.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs (pureState)
open EthCLSpecs.Gloas

/-- The bounds the substeps move. -/
structure StageCaps where
  /-- The cap on every balance. -/
  balance : Nat
  /-- How far `exitStart` may have moved since the start. -/
  exit : Nat
  /-- How many historical summaries may have been appended since the start. -/
  history : Nat
  /-- How far the registry potential may exceed the start's. Zero between substeps; the deposit
  scan grows the registry before it trims the queue, and uses it in between. -/
  slack : Nat := 0

/-- What every state between two substeps of one call from `v` satisfies. -/
structure Stage [Preset] [Config] (b : EpochBudget) (v : BeaconState) (caps : StageCaps)
    (w : BeaconState) : Prop where
  slot : w.slot = v.slot
  registrySizes : RegistrySizes w
  vGrows : v.validators.val.size ≤ w.validators.val.size
  potential : registryPotential w ≤ registryPotential v + caps.slack
  consolidationIdx : ∀ pc ∈ w.pendingConsolidations.val,
    pc.sourceIndex.toNat < w.validators.val.size ∧ pc.targetIndex.toNat < w.validators.val.size
  consolidationCount : w.pendingConsolidations.val.size ≤ b.consolidations
  effCap : ∀ x ∈ w.validators.val, x.effectiveBalance.toNat ≤ Const.maxEffectiveBalanceElectra
  depositCap : ∀ d ∈ w.pendingDeposits.val, d.amount.toNat ≤ b.deposit
  exitBound : exitStart w ≤ exitStart v + caps.exit
  historyBound : w.historicalSummaries.val.size ≤ v.historicalSummaries.val.size + caps.history
  balanceBound : ∀ x ∈ w.balances.val, x.toNat ≤ caps.balance
  live : Live w (computeEpochAtSlot v.slot + 1) ∧
    Live w (computeEpochAtSlot v.slot + Const.minSeedLookahead + 1)
  liveUnslashed : LiveUnslashed w (computeEpochAtSlot v.slot + Const.minSeedLookahead + 1)
  liveCount : LiveCount w (computeEpochAtSlot v.slot + Const.minSeedLookahead + 1) Const.slotsPerEpoch

/-- The fields `Stage` reads, and the list sizes. -/
structure StageFields [Preset] where
  slot : Slot
  validators : SizzLean.Repr.ProgressiveList Validator
  balances : SizzLean.Repr.ProgressiveList Gwei
  pendingDeposits : SizzLean.Repr.ProgressiveList PendingDeposit
  pendingConsolidations : SizzLean.Repr.ProgressiveList PendingConsolidation
  historicalSummaries : SizzLean.Repr.SSZList HistoricalSummary Const.historicalRootsLimit
  earliestExitEpoch : Epoch
  sizes : Nat × Nat × Nat × Nat × Nat

/-- Project a state onto the fields `Stage` reads. -/
def stageFields [Preset] (w : BeaconState) : StageFields where
  slot := w.slot
  validators := w.validators
  balances := w.balances
  pendingDeposits := w.pendingDeposits
  pendingConsolidations := w.pendingConsolidations
  historicalSummaries := w.historicalSummaries
  earliestExitEpoch := w.earliestExitEpoch
  sizes := listSizes w

/-- A state that agrees with a `Stage` state on the fields `Stage` reads is a `Stage` state. -/
theorem Stage.of_frame [Preset] [Config] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w w' : BeaconState} (hw : Stage b v caps w) (h : stageFields w' = stageFields w) :
    Stage b v caps w' := by
  simp only [stageFields, StageFields.mk.injEq] at h
  obtain ⟨hslot, hval, hbal, hpd, hpc, hhs, hee, hsizes⟩ := h
  have hrs : RegistrySizes w' := RegistrySizes.of_listSizes hsizes hw.registrySizes
  have hstart : exitStart w' = exitStart w := by unfold exitStart; rw [hee, hslot]
  have hpot : registryPotential w' = registryPotential w := by
    unfold registryPotential; rw [hval, hpd]
  refine ⟨hslot.trans hw.slot, hrs, hval ▸ hw.vGrows, hpot ▸ hw.potential, ?_, hpc ▸ hw.consolidationCount,
    hval ▸ hw.effCap, hpd ▸ hw.depositCap, hstart ▸ hw.exitBound, hhs ▸ hw.historyBound,
    hbal ▸ hw.balanceBound, ?_, ?_, ?_⟩
  · rw [hpc, hval]; exact hw.consolidationIdx
  · unfold Live; rw [hval]; exact hw.live
  · unfold LiveUnslashed; rw [hval]; exact hw.liveUnslashed
  · unfold LiveCount; rw [hval]; exact hw.liveCount

/-- The start is a `Stage` state with no movement yet, once the balance cap covers it. -/
theorem Stage.start [Preset] [Config] {b : EpochBudget} {n : Nat} {v : BeaconState}
    (hv : EpochSafe b n v) (cap : Nat) (hcap : ∀ x ∈ v.balances.val, x.toNat ≤ cap) :
    Stage b v ⟨cap, 0, 0, 0⟩ v :=
  ⟨rfl, hv.registrySizes, Nat.le_refl _, Nat.le_add_right _ _, hv.consolidationIdx, hv.consolidationCount,
    hv.effCap, hv.depositCap, Nat.le_add_right _ _, Nat.le_add_right _ _, hcap, hv.live,
    hv.liveUnslashed, hv.liveCount⟩

/-- Weaken the caps. -/
theorem Stage.mono [Preset] [Config] {b : EpochBudget} {v : BeaconState} {caps caps' : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) (hb : caps.balance ≤ caps'.balance)
    (he : caps.exit ≤ caps'.exit) (hh : caps.history ≤ caps'.history)
    (hs : caps.slack ≤ caps'.slack := by exact Nat.le_refl _) : Stage b v caps' w :=
  { hw with
    potential := Nat.le_trans hw.potential (Nat.add_le_add_left hs _)
    exitBound := Nat.le_trans hw.exitBound (Nat.add_le_add_left he _)
    historyBound := Nat.le_trans hw.historyBound (Nat.add_le_add_left hh _)
    balanceBound := fun x hx => Nat.le_trans (hw.balanceBound x hx) hb }

/-- A stage's registry indexes below `2^64` when the start's potential, plus the slack, does. -/
theorem Stage.vFits [Preset] [Config] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) (h : registryPotential v + caps.slack < 2 ^ 64) :
    w.validators.val.size < 2 ^ 64 := by
  have := hw.potential
  unfold registryPotential at this h
  omega

/-- Close a `Stage` leaf: a hypothesis that states it, or a record update of the state some
`Stage` hypothesis is about that leaves the fields `Stage` reads alone. -/
macro "stage_close" : tactic => `(tactic| first
  | assumption
  | (refine Stage.of_frame ‹Stage _ _ _ _› ?_
     simp [stageFields, listSizes, box_reduce, SizzLean.Proofs.progressiveListSet!_size]; done))

/-- Close a write whose box is an `if` over record updates of a `Stage` state, such as the
justification update: split the guards to show the written box is uncached, then keep `Stage`
when no branch writes a field it reads. -/
macro "stage_write" : tactic => `(tactic|
  (refine EthCLLib.Proofs.runSucceeds_modifyThe_view ?_ ?_
   (simp only [box_reduce, Id.run] <;> (repeat' split_ite) <;> rfl)
   refine Stage.of_frame ‹Stage _ _ _ _› ?_
   simp only [stageFields, listSizes, box_reduce, Id.run] <;> (repeat' split_ite) <;>
     simp [stageFields, listSizes, box_reduce]))

end EthCLSpecs.Proofs.Gloas
