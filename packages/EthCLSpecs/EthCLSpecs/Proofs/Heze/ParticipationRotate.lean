import EthCLSpecs.Proofs.Heze.ParticipationKeep
import EthCLSpecs.Proofs.Heze.DriftDeposits

/-!
# `EthCLSpecs.Proofs.Heze.ParticipationRotate`: the epoch step moves a set current flag

The epoch step moves the current participation list to the previous list
(`processParticipationFlagUpdates`). Before the move, `processPendingDeposits` can append
validators. `addValidatorToRegistry` writes a zero flag byte at the index `len(validators)` of
each participation list. When a list is longer than the registry, that write overwrites an
entry. It can clear a set flag. The written index is past every registry index, so the write
never clears the flag of a registry index.

`regView cur i` is the target bit of `i` and the test `i < len(validators)`, with the slot. The
deposit functions keep a `regView` of `true` (`processPendingDeposits_frame_reg_true`). The
other substeps of the epoch step before the move keep the bit and the registry
(`partView`, `keyView`). So the epoch step moves the set current bit of a registry index to the
previous list (`processEpoch_moves`). A slot step that ends an epoch moves its current flag
(`SlotStep.targetFlag_moves`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState run_bind_eq_ok_pure run_get_bind_eq_ok run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState Epoch Gwei currentEpochOf
  previousEpochOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

section
variable [Preset] [HasherTag] {cur : Bool} {i : Nat}

/-- The target bit of `i` in one list and the test `i < len(validators)`, and the slot. -/
def regView (cur : Bool) (i : Nat) (st : State) : Bool × Slot :=
  (partBit cur i st && decide (i < (sszGet st validators).val.size), sszGet st slot)

/-- The registry. -/
def valsView (st : State) := sszGet st validators

omit [HasherTag] in
/-- A set target bit lies inside its list. -/
theorem lt_size_of_bitOf {l : PartList} (h : bitOf l i = true) : i < l.size := by
  refine Classical.byContradiction fun hi => ?_
  unfold bitOf at h
  rw [getElem!_neg (dom := fun (xs : PartList) i => i < xs.size) (h := hi)] at h
  have h0 : hasFlag (default : EthCLSpecs.Heze.ParticipationFlags)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex = false := hasFlag_zero_target
  rw [h0] at h
  cases h

omit [HasherTag] in
/-- An append keeps a set target bit. -/
theorem bitOf_push_true (l : PartList) (x : EthCLSpecs.Heze.ParticipationFlags)
    (h' : l.val.size < EthCLSpecs.Heze.Const.validatorRegistryLimit) (h : bitOf l i = true) :
    bitOf (l.push x h') i = true := by
  have hi := lt_size_of_bitOf h
  unfold bitOf at h ⊢
  rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size) (h := hi)] at h
  rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size)
    (h := by simp [SizzLean.Repr.SSZList.push, SizzLean.Repr.SSZList.size] at hi ⊢; omega)]
  show hasFlag ((l.val.push x)[i]'_) _ = true
  simp only [Array.getElem_push, dif_pos (show i < l.val.size from hi)]
  exact h

/-- An append of the zero byte to the previous list keeps a target bit of `true`. -/
theorem partView_push_prev_true {t : BeaconState} {l : PartList} {sl : Slot}
    (hl : (sszGet (pureState t) previousEpochParticipation).push? 0 = some l)
    (hs : partView cur i (pureState t) = (true, sl)) :
    partView cur i (sszUpdate (pureState t) with previousEpochParticipation := l)
      = (true, sl) := by
  obtain ⟨h', rfl⟩ := push?_eq_some hl
  refine (partView_update_prev t _).trans ?_
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (true, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact ⟨bitOf_push_true _ _ h' hs'.1, hs'.2⟩
  · exact hs'

/-- An append of the zero byte to the current list keeps a target bit of `true`. -/
theorem partView_push_cur_true {t : BeaconState} {l : PartList} {sl : Slot}
    (hl : (sszGet (pureState t) currentEpochParticipation).push? 0 = some l)
    (hs : partView cur i (pureState t) = (true, sl)) :
    partView cur i (sszUpdate (pureState t) with currentEpochParticipation := l)
      = (true, sl) := by
  obtain ⟨h', rfl⟩ := push?_eq_some hl
  refine (partView_update_cur t _).trans ?_
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (true, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact hs'
  · exact ⟨bitOf_push_true _ _ h' hs'.1, hs'.2⟩

/-- An overwrite with the zero byte in the previous list at an index other than `i` keeps a
target bit of `true`. -/
theorem partView_set_prev_true {t : BeaconState} {j : Nat} {sl : Slot} (hne : j ≠ i)
    (hs : partView cur i (pureState t) = (true, sl)) :
    partView cur i (sszUpdate (pureState t) with previousEpochParticipation[j]! := 0)
      = (true, sl) := by
  refine (partView_set_prev t j 0).trans ?_
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (true, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · refine ⟨?_, hs'.2⟩
    simp only [cond_false] at hs' ⊢
    unfold bitOf at hs' ⊢
    rw [SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ hne]
    exact hs'.1
  · exact hs'

/-- An overwrite with the zero byte in the current list at an index other than `i` keeps a
target bit of `true`. -/
theorem partView_set_cur_true {t : BeaconState} {j : Nat} {sl : Slot} (hne : j ≠ i)
    (hs : partView cur i (pureState t) = (true, sl)) :
    partView cur i (sszUpdate (pureState t) with currentEpochParticipation[j]! := 0)
      = (true, sl) := by
  refine (partView_set_cur t j 0).trans ?_
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (true, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact hs'
  · refine ⟨?_, hs'.2⟩
    simp only [cond_true] at hs' ⊢
    unfold bitOf at hs' ⊢
    rw [SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ hne]
    exact hs'.1

open EthCLSpecs.Heze (modifyState) in
/-- The zero write of `addValidatorToRegistry` into the previous list at an index other than
`i` keeps a target bit of `true`, and the slot. -/
theorem setOrAppend_prev_true {t t' : BeaconState} {idx : Nat} {sl : Slot} (hne : idx ≠ i)
    (h : (setOrAppendState previousEpochParticipation idx 0 : HezeRun Unit).run (pureState t)
      = .ok ((), pureState t'))
    (hs : partView cur i (pureState t) = (true, sl)) :
    partView cur i (pureState t') = (true, sl) := by
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
    split at h
    · rename_i s' heq
      rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp heq
      exact partView_push_prev_true hl hs
    · cases h
  · rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      exact partView_set_prev_true hne hs
    · obtain ⟨he, -⟩ := EthCLLib.Proofs.run_ofExcept_eq_ok h
      cases he

open EthCLSpecs.Heze (modifyState) in
/-- The zero write of `addValidatorToRegistry` into the current list at an index other than
`i` keeps a target bit of `true`, and the slot. -/
theorem setOrAppend_cur_true {t t' : BeaconState} {idx : Nat} {sl : Slot} (hne : idx ≠ i)
    (h : (setOrAppendState currentEpochParticipation idx 0 : HezeRun Unit).run (pureState t)
      = .ok ((), pureState t'))
    (hs : partView cur i (pureState t) = (true, sl)) :
    partView cur i (pureState t') = (true, sl) := by
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
    split at h
    · rename_i s' heq
      rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp heq
      exact partView_push_cur_true hl hs
    · cases h
  · rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      exact partView_set_cur_true hne hs
    · obtain ⟨he, -⟩ := EthCLLib.Proofs.run_ofExcept_eq_ok h
      cases he

variable [Config] [CryptoBackend]

/-- `addValidatorToRegistry` keeps a `regView` of `true`. It appends the new validator, so the
registry grows. Its zero flag writes go to the old length of the registry, which is past `i`. -/
@[frame] theorem addValidatorToRegistry_frame_reg_true {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : Gwei}
    {sl : Slot}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t'))
    (hs : regView cur i (pureState t) = (true, sl)) :
    regView cur i (pureState t') = (true, sl) := by
  have hs' : (partBit cur i (pureState t) && decide (i < t.validators.val.size), t.slot) =
      (true, sl) := hs
  rw [Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at hs'
  obtain ⟨⟨hb, hi⟩, hsl⟩ := hs'
  have hp0 : partView cur i (pureState t) = (true, sl) := Prod.ext hb hsl
  unfold EthCLSpecs.Heze.addValidatorToRegistry at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨⟨⟩, t1, h1, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have k1 : partView cur i (pureState t1) = partView cur i (pureState t) := by frame_invert h1
  -- The registry write appends: the index is the length.
  have hv1 : i < t1.validators.val.size := by
    have h1 := run_get_bind_eq_ok _ _ _ h1
    try dsimp only at h1
    rcases run_ite_eq_ok h1 with ⟨-, h1⟩ | ⟨hne, -⟩
    · obtain ⟨hlt1, e1⟩ := appendValidator_run _ _ h1
      cases pureState_inj e1
      show i < (t.validators.val.push _).size
      rw [Array.size_push]
      omega
    · simp at hne
  obtain ⟨⟨⟩, t2, h2, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have k2 : partView cur i (pureState t2) = partView cur i (pureState t1) := by frame_invert h2
  have v2 : valsView (pureState t2) = valsView (pureState t1) := by frame_invert h2
  obtain ⟨⟨⟩, t3, h3, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have k3 := setOrAppend_prev_true (Nat.ne_of_gt hi) h3 (k2.trans (k1.trans hp0))
  have v3 : valsView (pureState t3) = valsView (pureState t2) := by frame_invert h3
  obtain ⟨⟨⟩, t4, h4, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have k4 := setOrAppend_cur_true (Nat.ne_of_gt hi) h4 k3
  have v4 : valsView (pureState t4) = valsView (pureState t3) := by frame_invert h4
  have k5 : partView cur i (pureState t') = partView cur i (pureState t4) := by frame_invert h
  have v5 : valsView (pureState t') = valsView (pureState t4) := by frame_invert h
  have hv : t'.validators = t1.validators := v5.trans (v4.trans (v3.trans v2))
  have hk := k5.trans k4
  have hk1 : partBit cur i (pureState t') = true := congrArg Prod.fst hk
  have hk2 : t'.slot = sl := congrArg Prod.snd hk
  show (partBit cur i (pureState t') && decide (i < t'.validators.val.size), t'.slot) = (true, sl)
  rw [hk1, hk2, hv]
  simpa using hv1

/-! ## The substeps before the deposits keep the registry keys -/

/-- `processJustificationAndFinalization` keeps `keyView`. -/
@[frame] theorem processJustificationAndFinalization_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  jf_frame keyView h

/-- `processInactivityUpdates` keeps `keyView`. -/
@[frame] theorem processInactivityUpdates_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps `keyView`. -/
@[frame] theorem processRewardsAndPenalties_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps `keyView`. Its writes keep each public key. -/
@[frame] theorem processRegistryUpdates_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps `keyView`. -/
@[frame] theorem processSlashings_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps `keyView`. -/
@[frame] theorem processEth1DataReset_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-! ## The deposit scan -/

/-- `applyPendingDeposit` keeps a `regView` of `true`. -/
@[frame] theorem applyPendingDeposit_frame_reg_true {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit} {sl : Slot}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t'))
    (hs : regView cur i (pureState t) = (true, sl)) :
    regView cur i (pureState t') = (true, sl) := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps a `regView` of `true`. -/
@[frame] theorem ppdLoop_frame_reg_true {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch} {sl : Slot}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t'))
    (hs : regView cur i (pureState t) = (true, sl)) :
    regView cur i (pureState t') = (true, sl) := by
  frame_invert h

/-- `processPendingDeposits` keeps a `regView` of `true`. -/
@[frame] theorem processPendingDeposits_frame_reg_true {t t' : BeaconState} {a : PUnit}
    {sl : Slot}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t'))
    (hs : regView cur i (pureState t) = (true, sl)) :
    regView cur i (pureState t') = (true, sl) := by
  frame_invert h

/-! ## The steps inside an epoch keep the registry keys -/

/-- `processVoluntaryExit` keeps `keyView`. -/
@[frame] theorem processVoluntaryExit_frame_key {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps `keyView`. -/
@[frame] theorem processBlsToExecutionChange_frame_key {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps `keyView`. -/
@[frame] theorem processSyncAggregate_frame_key {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processBlock` keeps `keyView`. -/
@[frame] theorem processBlock_frame_key {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-- `processSlot` keeps `keyView`. -/
@[frame] theorem processSlot_frame_key {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    keyView (pureState t') = keyView (pureState t) := by
  frame_invert h

/-! ## The epoch step -/

/-- Two states with one `keyView` have registries of one length. -/
theorem size_of_keyView {s s' : BeaconState} (h : keyView (pureState s') = keyView (pureState s)) :
    s'.validators.val.size = s.validators.val.size := by
  have e := congrArg (fun x => x.1.size) h
  simpa [keyView] using e

/-- A step that keeps `partView` and `keyView` keeps a `regView` of `true`. -/
theorem regView_of_frames {s s' : BeaconState} {sl : Slot}
    (hp : partView cur i (pureState s') = partView cur i (pureState s))
    (hk : keyView (pureState s') = keyView (pureState s))
    (hs : regView cur i (pureState s) = (true, sl)) : regView cur i (pureState s') = (true, sl) := by
  have hb : partBit cur i (pureState s') = partBit cur i (pureState s) := congrArg Prod.fst hp
  have hsl : s'.slot = s.slot := congrArg Prod.snd hp
  have hsz := size_of_keyView hk
  show (partBit cur i (pureState s') && decide (i < s'.validators.val.size), s'.slot) = (true, sl)
  rw [hb, hsl, hsz]
  exact hs

/-- The epoch prefix keeps a current target bit of `true` at a registry index. -/
theorem processEpochPrefix_keeps_true {t t' : BeaconState}
    (h : processEpochPrefix.run (pureState t) = .ok ((), pureState t'))
    (hi : i < t.validators.val.size) (hb : partBit cur i (pureState t) = true) :
    partBit cur i (pureState t') = true := by
  have hs0 : regView cur i (pureState t) = (true, t.slot) := by
    show (partBit cur i (pureState t) && decide (i < t.validators.val.size), t.slot) = _
    rw [hb]
    simpa using hi
  unfold processEpochPrefix at h
  obtain ⟨⟨⟩, a1, h1, h⟩ := run_bind_eq_ok_pure keepsUncached_processJustificationAndFinalization h
  have r1 := regView_of_frames (processJustificationAndFinalization_frame_part h1)
    (processJustificationAndFinalization_frame_key h1) hs0
  obtain ⟨⟨⟩, a2, h2, h⟩ := run_bind_eq_ok_pure keepsUncached_processInactivityUpdates h
  have r2 := regView_of_frames (processInactivityUpdates_frame_part h2)
    (processInactivityUpdates_frame_key h2) r1
  obtain ⟨⟨⟩, a3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processRewardsAndPenalties h
  have r3 := regView_of_frames (processRewardsAndPenalties_frame_part h3)
    (processRewardsAndPenalties_frame_key h3) r2
  obtain ⟨⟨⟩, a4, h4, h⟩ := run_bind_eq_ok_pure keepsUncached_processRegistryUpdates h
  have r4 := regView_of_frames (processRegistryUpdates_frame_part h4)
    (processRegistryUpdates_frame_key h4) r3
  obtain ⟨⟨⟩, a5, h5, h⟩ := run_bind_eq_ok_pure keepsUncached_processSlashings h
  have r5 := regView_of_frames (processSlashings_frame_part h5) (processSlashings_frame_key h5) r4
  obtain ⟨⟨⟩, a6, h6, h⟩ := run_bind_eq_ok_pure keepsUncached_processEth1DataReset h
  have r6 := regView_of_frames (processEth1DataReset_frame_part h6)
    (processEth1DataReset_frame_key h6) r5
  obtain ⟨⟨⟩, a7, h7, h8⟩ := run_bind_eq_ok_pure keepsUncached_processPendingDeposits h
  have r7 := processPendingDeposits_frame_reg_true h7 r6
  have b7 : partBit cur i (pureState a7) = true := by
    have := congrArg Prod.fst r7
    simp only [regView, Bool.and_eq_true] at this
    exact this.1
  exact (congrArg Prod.fst (processPendingConsolidations_frame_part (cur := cur) (i := i) h8)).trans b7

/-- **The epoch step moves a set current bit of a registry index to the previous list.** -/
theorem processEpoch_moves {st1 st2 : BeaconState}
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run
      (pureState st1) = .ok ((), pureState st2))
    (hi : i < st1.validators.val.size) (hb : partBit true i (pureState st1) = true) :
    partBit false i (pureState st2) = true := by
  rw [processEpoch_eq] at h
  obtain ⟨⟨⟩, a, ha, h⟩ := run_bind_eq_ok_pure keepsUncached_processEpochPrefix h
  obtain ⟨⟨⟩, b, hbp, h⟩ := run_bind_eq_ok_pure keepsUncached_processBuilderPendingPayments h
  rw [processEpochSuffix_eq_rot] at h
  obtain ⟨⟨⟩, c, hc, h⟩ := run_bind_eq_ok_pure keepsUncached_epochSuffixPre h
  obtain ⟨⟨⟩, d, hd, he⟩ := run_bind_eq_ok_pure keepsUncached_processParticipationFlagUpdates h
  have k1 := processEpochPrefix_keeps_true ha hi hb
  have k2 : partBit true i (pureState b) = true :=
    (congrArg Prod.fst (processBuilderPendingPayments_frame_part (cur := true) (i := i) hbp)).trans k1
  have k3 : partBit true i (pureState c) = true :=
    (congrArg Prod.fst (epochSuffixPre_frame_part (cur := true) (i := i) hc)).trans k2
  obtain ⟨rp, -, -⟩ := processParticipationFlagUpdates_run c d hd i
  exact (congrArg Prod.fst (epochSuffixPost_frame_part (cur := false) (i := i) he)).trans
    (rp.trans k3)

/-! ## The slot step and the run -/

/-- A slot step that does not end an epoch keeps the registry keys. -/
theorem SlotStep.keyView_of_not_boundary {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch ≠ 0) :
    keyView (pureState u') = keyView (pureState u) := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := processSlot_frame_key h1
  have s1 : st1.slot = u.slot := congrArg Prod.snd (processSlot_frame_ord h1)
  split at h2
  · rename_i htest
    exact absurd ((epochTest_iff st1.slot (by rw [s1]; exact hlt)).mp htest) (by rw [s1]; exact hb)
  · subst h2
    rw [← e1, hst']
    rfl

/-- A run inside one epoch keeps the length of the registry. -/
theorem ChainRun.size_of_epoch {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w)
    (he : u.slot.toNat / slotsPerEpoch = w.slot.toNat / slotsPerEpoch) :
    w.validators.val.size = u.validators.val.size := by
  revert he
  induction h with
  | nil => intro _; rfl
  | @slot _ st st1 _ hlt hstep hrest ih =>
    intro he
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    have hle := hrest.epoch_le hhi
    by_cases hb : (st.slot.toNat + 1) % slotsPerEpoch = 0
    · exfalso
      have := succ_div_of_mod_eq hb
      rw [← hs] at this
      omega
    · have hep := epoch_succ_of_not_boundary hb
      rw [← hs] at hep
      rw [ih (by omega)]
      exact size_of_keyView (hstep.keyView_of_not_boundary (by omega) hb)
  | block sb v hstep _ ih =>
    intro he
    obtain ⟨hs, -⟩ := hstep.slot
    rw [ih (by rw [hs]; exact he)]
    exact size_of_keyView (processBlock_frame_key hstep.2.1)

/-- **A slot step that ends an epoch moves a current target flag of a registry index to the
previous list.** The flag of the old current epoch is then a flag of the previous epoch. -/
theorem SlotStep.targetFlag_moves {st st' : BeaconState} (h : SlotStep st st')
    (hlt : st.slot.toNat + 1 < 2 ^ 64) (hb : (st.slot.toNat + 1) % slotsPerEpoch = 0)
    (hi : i < st.validators.val.size) {e : Epoch} (he : e = currentEpochOf (pureState st))
    (hf : partBit true i (pureState st) = true) : TargetFlagSet st' i e := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 : ∀ w, partView w i (pureState st1) = partView w i (pureState st) := fun w =>
    processSlot_frame_part (cur := w) h1
  have sl1 : st1.slot = st.slot := congrArg Prod.snd (e1 true)
  have hi1 : i < st1.validators.val.size := by rw [size_of_keyView (processSlot_frame_key h1)]; exact hi
  have b' : partBit false i (pureState st') = partBit false i (pureState st2) := by
    rw [hst']
    rfl
  have sl' : st'.slot = st2.slot + 1 := by
    change sszGet (pureState st') slot = _
    rw [hst']
    rfl
  split at h2
  · obtain ⟨-, -, sl2⟩ := processEpoch_part h2 i
    have hm := processEpoch_moves h2 hi1 ((congrArg Prod.fst (e1 true)).trans hf)
    have hsn : st'.slot.toNat = st.slot.toNat + 1 := by
      rw [sl', sl2, sl1, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    have hprev : previousEpochOf (pureState st') = currentEpochOf (pureState st) := by
      apply UInt64.toNat_inj.mp
      rw [previousEpochOf_toNat_sub, currentEpochOf_toNat]
      change st'.slot.toNat / slotsPerEpoch - 1 = st.slot.toNat / slotsPerEpoch
      rw [hsn, succ_div_of_mod_eq hb]
      rfl
    have hne : currentEpochOf (pureState st') ≠ currentEpochOf (pureState st) := by
      intro heq
      have := congrArg UInt64.toNat heq
      rw [currentEpochOf_toNat, currentEpochOf_toNat] at this
      change st'.slot.toNat / slotsPerEpoch = st.slot.toNat / slotsPerEpoch at this
      rw [hsn, succ_div_of_mod_eq hb] at this
      omega
    refine .inr ⟨he.trans hprev.symm, fun h' => hne (h'.symm.trans he), ?_⟩
    rw [b']
    exact hm
  · rename_i htest
    exact absurd ((epochTest_iff st1.slot (by rw [sl1]; exact hlt)).mpr (by rw [sl1]; exact hb))
      htest

end

end EthCLSpecs.Proofs.Heze
