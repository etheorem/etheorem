import EthCLSpecs.Fulu.Time
import EthCLSpecs.Fulu.RegistryUpdates
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Preserves

/-!
# `EthCLSpecs.Proofs.Fulu.StateInvariants`: four facts every reachable Fulu state satisfies

`SimpleStateInvariants v` collects four cheap facts about a Fulu `BeaconState`. Every state
in `ReachableState` (`Proofs/Fulu/Reachable.lean`) satisfies them, once the anchors do. The
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
  current version is Fulu's. Only a fork upgrade writes the field.

## How a step keeps them

Three of the four facts read only the slot, the header slot, the `fork` field and the three
checkpoint epochs. `coreFields` projects a state onto those six values. The fourth reads the
registry sizes, and `RegistrySizes` states it. Nearly every spec substep leaves the six values
alone and keeps the registry sizes equal: it writes other fields, overwrites list entries in
place, or appends to all five lists at once. `KeepsCore act` names that property, and
`SimpleStateInvariants.of_coreFields_eq` turns it into preservation of the invariants. Only the
header step, justification and finalization, and the slot increment change `coreFields`.

The anchors must satisfy all four, including the previous-epoch bound. A genesis state and an
epoch-start checkpoint state do.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag saturatingSub)
open EthCLSpecs.Fulu (Preset Config BeaconState Slot Epoch Fork computeEpochAtSlot)
open EthCLSpecs.Fulu.Const (fuluForkVersion)
open EthCLLib.Proofs (Preserves)

/-- The six values `SimpleStateInvariants` reads, other than the registry sizes. `Fork` is a
`forkcontainer`, and every `forkcontainer` takes the preset, so this structure does too. -/
structure CoreFields [Preset] where
  slot : Slot
  headerSlot : Slot
  forkData : Fork
  finalizedEpoch : Epoch
  previousJustifiedEpoch : Epoch
  currentJustifiedEpoch : Epoch

/-- Project a state onto the six values `CoreFields` holds. -/
def coreFields [Preset] (v : BeaconState) : CoreFields where
  slot := v.slot
  headerSlot := v.latestBlockHeader.slot
  forkData := v.forkData
  finalizedEpoch := v.finalizedCheckpoint.epoch
  previousJustifiedEpoch := v.previousJustifiedCheckpoint.epoch
  currentJustifiedEpoch := v.currentJustifiedCheckpoint.epoch

/-- The four lists indexed by validator index have the registry's length. -/
def RegistrySizes [Preset] (v : BeaconState) : Prop :=
  v.balances.size = v.validators.size ∧
  v.inactivityScores.size = v.validators.size ∧
  v.previousEpochParticipation.size = v.validators.size ∧
  v.currentEpochParticipation.size = v.validators.size

/-- Four facts every reachable Fulu state satisfies. The module docstring gives the reason
for each, and the reason the checkpoint bound is the previous epoch. -/
structure SimpleStateInvariants [Preset] [Config] (v : BeaconState) : Prop where
  /-- The latest block header is no later than the state. -/
  headerSlotLe : v.latestBlockHeader.slot ≤ v.slot
  /-- The four lists indexed by validator index have the registry's length. -/
  registrySizes : RegistrySizes v
  /-- Finalized ≤ previous-justified ≤ current-justified ≤ previous epoch. -/
  checkpointOrder :
    v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
    v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
    v.currentJustifiedCheckpoint.epoch ≤ saturatingSub (computeEpochAtSlot v.slot) 1
  /-- The `fork` field names an epoch no later than the current one, and Fulu's version. -/
  forkConsistent :
    v.forkData.epoch ≤ computeEpochAtSlot v.slot ∧
    v.forkData.currentVersion = fuluForkVersion

/-- A step that keeps `coreFields` and the registry sizes keeps the invariants. Each field of
the conclusion is the matching field of `hv`, rewritten along the field equations `h`
unpacks into. -/
theorem SimpleStateInvariants.of_coreFields_eq [Preset] [Config] {v w : BeaconState}
    (h : coreFields w = coreFields v) (hr : RegistrySizes w) (hv : SimpleStateInvariants v) :
    SimpleStateInvariants w := by
  obtain ⟨hh, _, hc, hf⟩ := hv
  simp only [coreFields, CoreFields.mk.injEq] at h
  obtain ⟨hslot, hhead, hfork, hfin, hprev, hcurr⟩ := h
  refine ⟨?_, hr, ?_, ?_⟩
  · rw [hslot, hhead]; exact hh
  · rw [hfin, hprev, hcurr, hslot]; exact hc
  · rw [hfork, hslot]; exact hf

/-- The step invariant at the fixed core values `c`: the state has those six values, and its
registry sizes agree. -/
def StepInv [Preset] (c : CoreFields) (v : BeaconState) : Prop :=
  coreFields v = c ∧ RegistrySizes v

/-- The lengths of `validators` and of the four lists that run parallel to it. -/
def listSizes [Preset] (v : BeaconState) : Nat × Nat × Nat × Nat × Nat :=
  (v.validators.size, v.balances.size, v.inactivityScores.size,
    v.previousEpochParticipation.size, v.currentEpochParticipation.size)

/-- `w` agrees with `v` on the six core values and on the five list sizes. A record update that
writes other fields, or overwrites list entries in place, gives such a pair. -/
def FrameEq [Preset] (w v : BeaconState) : Prop :=
  coreFields w = coreFields v ∧ listSizes w = listSizes v

theorem FrameEq.refl [Preset] (v : BeaconState) : FrameEq v v := ⟨rfl, rfl⟩

theorem FrameEq.trans [Preset] {u v w : BeaconState} (hwv : FrameEq w v) (hvu : FrameEq v u) :
    FrameEq w u :=
  ⟨hwv.1.trans hvu.1, hwv.2.trans hvu.2⟩

/-- Equal list sizes carry the registry-size equalities. -/
theorem RegistrySizes.of_listSizes [Preset] {v w : BeaconState} (h : listSizes w = listSizes v)
    (hv : RegistrySizes v) : RegistrySizes w := by
  obtain ⟨hb, hi, hp, hq⟩ := hv
  simp only [listSizes, Prod.mk.injEq] at h
  obtain ⟨sv, sb, si, sp, sq⟩ := h
  exact ⟨by rw [sb, sv]; exact hb, by rw [si, sv]; exact hi, by rw [sp, sv]; exact hp,
    by rw [sq, sv]; exact hq⟩

/-- A state that agrees with a `StepInv` state on the six values and on the five list sizes
satisfies `StepInv` too. The leaf of most frame proofs. -/
theorem StepInv.of_frameEq [Preset] {c : CoreFields} {v w : BeaconState} (hv : StepInv c v)
    (h : FrameEq w v) : StepInv c w := by
  obtain ⟨hc, hb, hi, hp, hq⟩ := hv
  obtain ⟨hcore, hsizes⟩ := h
  simp only [listSizes, Prod.mk.injEq] at hsizes
  obtain ⟨sv, sb, si, sp, sq⟩ := hsizes
  exact ⟨hcore.trans hc, by rw [sb, sv]; exact hb, by rw [si, sv]; exact hi,
    by rw [sp, sv]; exact hp, by rw [sq, sv]; exact hq⟩

-- The two record-update helpers the fork body writes through, `modBalance` and
-- `modValidator`, are plain definitions over `sszModify`. Tagging them `box_reduce` lets a frame
-- proof see the field they write.
attribute [box_reduce] EthCLSpecs.Fulu.modBalance EthCLSpecs.Fulu.modValidator

/-- Close a `FrameEq w v` goal where `w` is a record update of `v`: the six core values agree
by `rfl` or after splitting an `if` the update holds, and the list sizes agree by `rfl` or
through `SSZList.set!`'s size lemma. -/
macro "frame_eq" : tactic => `(tactic| first
  | exact ⟨rfl, rfl⟩
  | exact ⟨rfl, by simp [listSizes, box_reduce, SizzLean.Proofs.sszListSet!_size]⟩
  | (constructor
     <;> (simp only [coreFields, listSizes, box_reduce]
          <;> (repeat' split_ite)
          <;> simp [box_reduce, SizzLean.Proofs.sszListSet!_size])))

open Lean Elab Tactic in
/-- Close a `StepInv c w` leaf from some `StepInv c v` hypothesis, when `w` is a record update of
`v` that `frame_eq` handles. It tries each `StepInv` hypothesis, most recent first: a `subst`
reorders the context, so the right one need not be the last. -/
elab "frame_leaf" : tactic => withMainContext do
  for ld in (← getLCtx).decls.toList.reverse.filterMap id do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless ty.isAppOf ``StepInv do continue
    let saved ← saveState
    try
      let h ← Term.exprToSyntax ld.toExpr
      evalTactic (← `(tactic| (refine StepInv.of_frameEq $h ?_) <;> (frame_eq; done)))
      return
    catch _ =>
      saved.restore
  throwError "frame_leaf: no StepInv hypothesis gives the goal by a frame step"

/-- Close a step-invariant leaf: a hypothesis that states it, or a record update of the state
some `StepInv` hypothesis is about. -/
macro "frame_close" : tactic => `(tactic| first | assumption | frame_leaf)

/-- Step over a call to a `KeepsCore` step: the rest of the body runs from a state that
satisfies the same `StepInv`. `frame_close` proves the premise once the goal has fixed the
start, which may be a record update of an earlier state. -/
macro "call " h:term : tactic =>
  `(tactic| refine EthCLLib.Proofs.Preserves.run ($h _) (by frame_close) (fun _ _ _ => ?_))

/-- Step over a call to a `ReadsOnly` accessor. -/
macro "call_ro " h:term : tactic =>
  `(tactic| refine EthCLLib.Proofs.Preserves.run
    (EthCLLib.Proofs.ReadsOnly.preserves (P := StepInv _) $h) (by frame_close) (fun _ _ _ => ?_))

/-- Step over a call that writes only the box it is handed, such as `increaseBalance`. `h`
takes the `StepInv` fact for the handed value, which `frame_close` proves once the goal has
fixed that value, and returns one for the value of the box it hands back. The threaded state
stays, and the returned box is `pureState s'`. -/
macro "call_box " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunEnsures.weaken ($h (by frame_close)) (fun _ _ hbox => ?_)
             obtain ⟨hst, _, hb, _⟩ := hbox
             subst hst hb))

/-- A run of `act` keeps the six core values fixed and the registry sizes equal, from every
start. The property nearly every spec substep has. -/
abbrev KeepsCore [Preset] [HasherTag] {α : Type} (act : FuluRun α) : Prop :=
  ∀ c, Preserves (StepInv c) act

/-- A `KeepsCore` step keeps the invariants. -/
theorem KeepsCore.preserves_invariants [Preset] [HasherTag] [Config] {α : Type} {act : FuluRun α}
    (h : KeepsCore act) : Preserves SimpleStateInvariants act := by
  intro v hv
  refine (h (coreFields v) v ⟨rfl, hv.registrySizes⟩).weaken ?_
  intro _ w hw
  exact SimpleStateInvariants.of_coreFields_eq hw.1 hw.2 hv

end EthCLSpecs.Proofs.Fulu
