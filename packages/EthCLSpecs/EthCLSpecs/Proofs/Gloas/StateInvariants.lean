import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Proofs.Gloas.StateInvariants`: four facts every reachable Gloas state satisfies

`SimpleStateInvariants v` collects, for a Gloas `BeaconState`, the four facts
`Proofs/Fulu/StateInvariants.lean` states for Fulu, with Gloas's fork version in the last one.
Each fork elaborates its own `BeaconState`, so each fork states the facts over its own type.
Every state in `ReachableState` (`Proofs/Gloas/Reachable.lean`) satisfies them, once the
anchors do. Gloas turns the registry lists into `ProgressiveList`s; `.size` reads the length
of either list kind. The
converse fails by design: the four facts read a handful of fields, so a state that satisfies
them can still be one no chain produces. The invariants are necessary for reachability and
far from sufficient.

* `headerSlotLe`: the latest block header is no later than the state. Only
  `processBlockHeader` writes the header's slot, and it writes the state's own slot.
* `registrySizes`: the four lists that run parallel to `validators` have its length. The
  spec indexes `balances[i]`, `inactivityScores[i]` and both participation lists by a
  validator index, so a reachable state never reads past one of them.
* `checkpointOrder`: finalized, previous-justified and current-justified epochs are in order,
  and the current-justified one is at most the **previous** epoch. Epoch processing runs at
  the last slot of epoch `E` and may justify `E`, and the slot increment then moves the state
  into `E + 1`, so the bound holds at every state a run exposes. The weaker bound "at most the
  current epoch" is also true, but it is not inductive: a state at the last slot of `E` with
  both justified epochs at `E`, whose previous-epoch target alone justifies, would step to a
  current-justified epoch below the previous-justified one.
* `forkConsistent`: the `fork` field records an epoch no later than the current one, and the
  current version is Gloas's. Only a fork upgrade writes the field.

`invFields` projects a state onto exactly the fields these four facts read.
`SimpleStateInvariants.of_invFields_eq` then turns "this step keeps `invFields`" into "this
step keeps the invariants", which is how most spec substeps are handled.

The anchors must satisfy all four, including the previous-epoch bound. A genesis state and an
epoch-start checkpoint state do.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (saturatingSub)
open EthCLSpecs.Gloas (Preset Config BeaconState Slot Epoch Fork computeEpochAtSlot)
open EthCLSpecs.Gloas.Const (gloasForkVersion)

/-- The fields `SimpleStateInvariants` reads, and nothing else. Two states with equal
`invFields` satisfy the invariants together or not at all. `Fork` is a `forkcontainer`, and
every `forkcontainer` takes the preset, so this structure does too. -/
structure InvFields [Preset] where
  slot : Slot
  headerSlot : Slot
  forkData : Fork
  finalizedEpoch : Epoch
  previousJustifiedEpoch : Epoch
  currentJustifiedEpoch : Epoch
  validatorsSize : Nat
  balancesSize : Nat
  inactivityScoresSize : Nat
  previousParticipationSize : Nat
  currentParticipationSize : Nat

/-- Project a state onto the fields `SimpleStateInvariants` reads. A step whose run keeps
`invFields` is a frame step for the invariants. -/
def invFields [Preset] (v : BeaconState) : InvFields where
  slot := v.slot
  headerSlot := v.latestBlockHeader.slot
  forkData := v.forkData
  finalizedEpoch := v.finalizedCheckpoint.epoch
  previousJustifiedEpoch := v.previousJustifiedCheckpoint.epoch
  currentJustifiedEpoch := v.currentJustifiedCheckpoint.epoch
  validatorsSize := v.validators.size
  balancesSize := v.balances.size
  inactivityScoresSize := v.inactivityScores.size
  previousParticipationSize := v.previousEpochParticipation.size
  currentParticipationSize := v.currentEpochParticipation.size

/-- Four facts every reachable Gloas state satisfies. The module docstring gives the reason
for each, and the reason the checkpoint bound is the previous epoch. -/
structure SimpleStateInvariants [Preset] [Config] (v : BeaconState) : Prop where
  /-- The latest block header is no later than the state. -/
  headerSlotLe : v.latestBlockHeader.slot ≤ v.slot
  /-- The four lists indexed by validator index have the registry's length. -/
  registrySizes :
    v.balances.size = v.validators.size ∧
    v.inactivityScores.size = v.validators.size ∧
    v.previousEpochParticipation.size = v.validators.size ∧
    v.currentEpochParticipation.size = v.validators.size
  /-- Finalized ≤ previous-justified ≤ current-justified ≤ previous epoch. -/
  checkpointOrder :
    v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
    v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
    v.currentJustifiedCheckpoint.epoch ≤ saturatingSub (computeEpochAtSlot v.slot) 1
  /-- The `fork` field names an epoch no later than the current one, and Gloas's version. -/
  forkConsistent :
    v.forkData.epoch ≤ computeEpochAtSlot v.slot ∧
    v.forkData.currentVersion = gloasForkVersion

/-- A step that keeps `invFields` keeps the invariants. Each field of the conclusion is the
matching field of `hv`, rewritten along the field equations `h` unpacks into. -/
theorem SimpleStateInvariants.of_invFields_eq [Preset] [Config] {v w : BeaconState}
    (h : invFields w = invFields v) (hv : SimpleStateInvariants v) :
    SimpleStateInvariants w := by
  obtain ⟨hh, hr, hc, hf⟩ := hv
  simp only [invFields, InvFields.mk.injEq] at h
  obtain ⟨hslot, hhead, hfork, hfin, hprev, hcurr, hval, hbal, hinact, hpp, hcp⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hslot, hhead]; exact hh
  · rw [hval, hbal, hinact, hpp, hcp]; exact hr
  · rw [hfin, hprev, hcurr, hslot]; exact hc
  · rw [hfork, hslot]; exact hf

end EthCLSpecs.Proofs.Gloas
