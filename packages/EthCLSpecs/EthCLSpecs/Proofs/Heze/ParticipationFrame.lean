import EthCLSpecs.Proofs.Heze.CheckpointFrame

/-!
# `EthCLSpecs.Proofs.Heze.ParticipationFrame`: the functions that keep a target flag

A beacon state holds two participation lists, one flag byte per validator for the previous
epoch and one for the current epoch. Bit `TIMELY_TARGET_FLAG_INDEX` of a byte is the target
flag. Three kinds of function write the lists:

- `processAttestation` sets flags (`Participation.lean`).
- `processParticipationFlagUpdates` moves the current list to the previous list, and writes
  a list of zeros as the current list (`processParticipationFlagUpdates_run`).
- `addValidatorToRegistry` writes a zero flag at the new index in both lists. That index is
  the length of `validators`. When a list is longer than `validators`, the write overwrites
  an entry. So the write can clear a flag, and it never sets one.

This module proves that every other function of a slot step and a block step keeps one flag
bit and the slot. The view is `partView cur i`: the target bit of index `i` in the current
list (`cur = true`) or the previous list (`cur = false`), and the slot. For the functions that
call `addValidatorToRegistry`, the lemmas keep the view at a bit of `false` only
(`processPendingDeposits_frame_part_false`). A bit that is `false` stays `false`.

Each function that writes the state has a frame lemma by `frame_invert`, in the same order
as the `ordView` lemmas of `CheckpointFrame.lean`. A function that reads the state only
needs no lemma here: its `PaymentFrame.lean` lemma serves each view.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState ValidatorIndex Gwei)

section
variable [Preset] [HasherTag]

/-- A participation list: one flag byte per validator. -/
abbrev PartList : Type :=
  SizzLean.Repr.SSZList EthCLSpecs.Heze.ParticipationFlags
    EthCLSpecs.Heze.Const.validatorRegistryLimit

/-- The target bit of index `i` in a list. An index past the end reads the zero byte, as the
spec's `[i]!` read does. -/
def bitOf (l : PartList) (i : Nat) : Bool :=
  hasFlag l[i]! EthCLSpecs.Heze.Const.timelyTargetFlagIndex

/-- The target bit of index `i`: in the current list when `cur`, else in the previous list. -/
def partBit (cur : Bool) (i : Nat) (st : State) : Bool :=
  bitOf (cond cur (sszGet st currentEpochParticipation) (sszGet st previousEpochParticipation)) i

/-- The target bit of index `i` in one list, and the slot. -/
def partView (cur : Bool) (i : Nat) (st : State) : Bool × Slot :=
  (partBit cur i st, sszGet st slot)

end

/-! ## The epoch functions -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend] {cur : Bool} {i : Nat}

/-- `processSlashingsReset` keeps `partView`. -/
@[frame] theorem processSlashingsReset_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps `partView`. -/
@[frame] theorem processEth1Data_frame_part {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps `partView`. -/
@[frame] theorem processEth1DataReset_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps `partView`. -/
@[frame] theorem processRandaoMixesReset_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps `partView`. -/
@[frame] theorem processHistoricalSummariesUpdate_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps `partView`. -/
@[frame] theorem processSyncCommitteeUpdates_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps `partView`. -/
@[frame] theorem processProposerLookahead_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps `partView`. -/
@[frame] theorem processPtcWindow_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `increaseBalance` returns a state value with the `partView` of its argument. -/
@[frame] theorem increaseBalance_ret_part {u t t' b : BeaconState} {j : ValidatorIndex}
    {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) j d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    partView cur i (pureState b) = partView cur i (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `partView` of its argument. -/
@[frame] theorem decreaseBalance_ret_part {u t t' b : BeaconState} {j : ValidatorIndex}
    {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) j d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    partView cur i (pureState b) = partView cur i (pureState u) := by
  frame_invert h

/-- `applyDeltas` returns a state value with the `partView` of its argument. -/
@[frame] theorem applyDeltas_ret_part {u t t' b : BeaconState} {r p : Array Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    partView cur i (pureState b) = partView cur i (pureState u) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps `partView`. -/
@[frame] theorem processRewardsAndPenalties_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps `partView`. -/
@[frame] theorem processSlashings_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processInactivityUpdates` keeps `partView`. -/
@[frame] theorem processInactivityUpdates_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processEffectiveBalanceUpdates` keeps `partView`. -/
@[frame] theorem processEffectiveBalanceUpdates_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps `partView`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_part {t t' : BeaconState} {a : _}
    {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps `partView`. -/
@[frame] theorem initiateValidatorExit_frame_part {t t' : BeaconState} {a : PUnit}
    {j : ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps `partView`. -/
@[frame] theorem processRegistryUpdates_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processPendingConsolidations` keeps `partView`. -/
@[frame] theorem processPendingConsolidations_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processSlot` keeps `partView`. It writes the state and block roots, the state root of
the latest header, and the next availability bit. -/
@[frame] theorem processSlot_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps `partView`. It writes the withdrawal queue and the
payment window. -/
@[frame] theorem processBuilderPendingPayments_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processJustificationAndFinalization` keeps `partView`. It writes the justification
bits and the three checkpoints. -/
@[frame] theorem processJustificationAndFinalization_frame_part {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  jf_frame (partView cur i) h

end

/-! ## The zero writes of `addValidatorToRegistry`

`addValidatorToRegistry` writes a zero byte into each participation list, by an append or by
an overwrite. A zero byte has no target flag. So a target bit that is `false` stays `false`
(`bitOf_set_zero`, `bitOf_push_zero`). The callers of `addValidatorToRegistry` keep
`partView` at a bit of `false` only. -/

section
variable [Preset] [HasherTag] {cur : Bool} {i : Nat}

omit [Preset] [HasherTag] in
/-- The zero byte has no target flag. -/
theorem hasFlag_zero_target :
    hasFlag 0 EthCLSpecs.Heze.Const.timelyTargetFlagIndex = false := by
  decide

omit [HasherTag] in
/-- An overwrite with the zero byte keeps a target bit of `false`. -/
theorem bitOf_set_zero (l : PartList) (j : Nat) (h : bitOf l i = false) :
    bitOf (l.set! j 0) i = false := by
  unfold bitOf at h ⊢
  by_cases hji : j = i
  · subst hji
    by_cases hj : j < l.size
    · rw [SizzLean.Proofs.sszListSet!_getElem!_self _ _ _ hj]
      exact hasFlag_zero_target
    · rw [SizzLean.Proofs.sszListSet!_eq_of_size_le _ _ _ (Nat.le_of_not_lt hj)]
      exact h
  · rw [SizzLean.Proofs.sszListSet!_getElem!_ne _ _ _ _ hji]
    exact h

omit [HasherTag] in
/-- An append of the zero byte keeps a target bit of `false`. -/
theorem bitOf_push_zero (l : PartList)
    (h' : l.val.size < EthCLSpecs.Heze.Const.validatorRegistryLimit) (h : bitOf l i = false) :
    bitOf (l.push 0 h') i = false := by
  unfold bitOf at h ⊢
  have hs : (l.push 0 h').size = l.size + 1 := by
    simp [SizzLean.Repr.SSZList.push, SizzLean.Repr.SSZList.size]
  by_cases hi : i < l.size
  · rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size) (h := by omega)]
    rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size) (h := hi)] at h
    show hasFlag ((l.val.push 0)[i]'_) _ = false
    simp only [Array.getElem_push, dif_pos (show i < l.val.size from hi)]
    exact h
  · by_cases hie : i = l.size
    · subst hie
      rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size) (h := by omega)]
      show hasFlag ((l.val.push 0)[l.val.size]'_) _ = false
      simp only [Array.getElem_push, Nat.lt_irrefl, dite_false]
      exact hasFlag_zero_target
    · rw [getElem!_neg (dom := fun (xs : PartList) i => i < xs.size) (h := by omega)]
      exact hasFlag_zero_target

omit [HasherTag] in
/-- A `push?` that succeeds is the `push` of the value. -/
theorem push?_eq_some {l l' : PartList} {x : EthCLSpecs.Heze.ParticipationFlags}
    (h : l.push? x = some l') :
    ∃ h' : l.val.size < EthCLSpecs.Heze.Const.validatorRegistryLimit, l' = l.push x h' := by
  unfold SizzLean.Repr.SSZList.push? at h
  split at h
  · rename_i h'
    exact ⟨h', (Option.some.inj h).symm⟩
  · cases h

/-- A write of the previous list changes the previous list only. -/
theorem partView_update_prev (t : BeaconState) (l : PartList) :
    partView cur i (sszUpdate (pureState t) with previousEpochParticipation := l)
      = (bitOf (cond cur t.currentEpochParticipation l) i, t.slot) := by
  with_unfolding_all rfl

/-- A write of the current list changes the current list only. -/
theorem partView_update_cur (t : BeaconState) (l : PartList) :
    partView cur i (sszUpdate (pureState t) with currentEpochParticipation := l)
      = (bitOf (cond cur l t.previousEpochParticipation) i, t.slot) := by
  with_unfolding_all rfl

/-- An entry write of the previous list is `set!` on the previous list. -/
theorem partView_set_prev (t : BeaconState) (j : Nat) (x : EthCLSpecs.Heze.ParticipationFlags) :
    partView cur i (sszUpdate (pureState t) with previousEpochParticipation[j]! := x)
      = (bitOf (cond cur t.currentEpochParticipation
          (t.previousEpochParticipation.set! j x)) i, t.slot) := by
  with_unfolding_all rfl

/-- An entry write of the current list is `set!` on the current list. -/
theorem partView_set_cur (t : BeaconState) (j : Nat) (x : EthCLSpecs.Heze.ParticipationFlags) :
    partView cur i (sszUpdate (pureState t) with currentEpochParticipation[j]! := x)
      = (bitOf (cond cur (t.currentEpochParticipation.set! j x)
          t.previousEpochParticipation) i, t.slot) := by
  with_unfolding_all rfl

/-- An append of the zero byte to the previous list keeps a target bit of `false`. -/
theorem partView_push_prev_false {t : BeaconState} {l : PartList} {sl : Slot}
    (hl : (sszGet (pureState t) previousEpochParticipation).push? 0 = some l)
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (sszUpdate (pureState t) with previousEpochParticipation := l)
      = (false, sl) := by
  obtain ⟨h', rfl⟩ := push?_eq_some hl
  rw [partView_update_prev]
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (false, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact ⟨bitOf_push_zero _ h' hs'.1, hs'.2⟩
  · exact hs'

/-- An append of the zero byte to the current list keeps a target bit of `false`. -/
theorem partView_push_cur_false {t : BeaconState} {l : PartList} {sl : Slot}
    (hl : (sszGet (pureState t) currentEpochParticipation).push? 0 = some l)
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (sszUpdate (pureState t) with currentEpochParticipation := l)
      = (false, sl) := by
  obtain ⟨h', rfl⟩ := push?_eq_some hl
  rw [partView_update_cur]
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (false, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact hs'
  · exact ⟨bitOf_push_zero _ h' hs'.1, hs'.2⟩

/-- An overwrite with the zero byte in the previous list keeps a target bit of `false`. -/
theorem partView_set_prev_false {t : BeaconState} {j : Nat} {sl : Slot}
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (sszUpdate (pureState t) with previousEpochParticipation[j]! := 0)
      = (false, sl) := by
  rw [partView_set_prev]
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (false, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact ⟨bitOf_set_zero _ _ hs'.1, hs'.2⟩
  · exact hs'

/-- An overwrite with the zero byte in the current list keeps a target bit of `false`. -/
theorem partView_set_cur_false {t : BeaconState} {j : Nat} {sl : Slot}
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (sszUpdate (pureState t) with currentEpochParticipation[j]! := 0)
      = (false, sl) := by
  rw [partView_set_cur]
  have hs' : (bitOf (cond cur t.currentEpochParticipation t.previousEpochParticipation) i,
      t.slot) = (false, sl) := hs
  rw [Prod.mk.injEq] at hs' ⊢
  cases cur
  · exact hs'
  · exact ⟨bitOf_set_zero _ _ hs'.1, hs'.2⟩

open EthCLSpecs.Heze (modifyState) in
/-- The zero write of `addValidatorToRegistry` into the previous list keeps a target bit of
`false`, and the slot. The write is an append at the length, or an overwrite inside the list. -/
theorem setOrAppend_prev_false {t t' : BeaconState} {idx : Nat} {sl : Slot}
    (h : (setOrAppendState previousEpochParticipation idx 0 : HezeRun Unit).run (pureState t)
      = .ok ((), pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases EthCLLib.Proofs.run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
    split at h
    · rename_i s' heq
      rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp heq
      exact partView_push_prev_false hl hs
    · cases h
  · rcases EthCLLib.Proofs.run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      exact partView_set_prev_false hs
    · obtain ⟨he, -⟩ := EthCLLib.Proofs.run_ofExcept_eq_ok h
      cases he

open EthCLSpecs.Heze (modifyState) in
/-- The zero write of `addValidatorToRegistry` into the current list keeps a target bit of
`false`, and the slot. -/
theorem setOrAppend_cur_false {t t' : BeaconState} {idx : Nat} {sl : Slot}
    (h : (setOrAppendState currentEpochParticipation idx 0 : HezeRun Unit).run (pureState t)
      = .ok ((), pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases EthCLLib.Proofs.run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
    split at h
    · rename_i s' heq
      rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp heq
      exact partView_push_cur_false hl hs
    · cases h
  · rcases EthCLLib.Proofs.run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      exact partView_set_cur_false hs
    · obtain ⟨he, -⟩ := EthCLLib.Proofs.run_ofExcept_eq_ok h
      cases he

variable [Config] [CryptoBackend]

/-- `addValidatorToRegistry` keeps a target bit of `false`, and the slot. It writes the zero
byte into both participation lists (`setOrAppend_prev_false`, `setOrAppend_cur_false`). Its
other writes keep `partView`. -/
@[frame] theorem addValidatorToRegistry_frame_part_false {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : Gwei}
    {sl : Slot}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  unfold EthCLSpecs.Heze.addValidatorToRegistry at h
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨⟨⟩, t1, h1, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  have k1 : partView cur i (pureState t1) = partView cur i (pureState t) := by frame_invert h1
  obtain ⟨⟨⟩, t2, h2, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  have k2 : partView cur i (pureState t2) = partView cur i (pureState t1) := by frame_invert h2
  obtain ⟨⟨⟩, t3, h3, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  have k3 := setOrAppend_prev_false h3 (k2.trans (k1.trans hs))
  obtain ⟨⟨⟩, t4, h4, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) h
  have k4 := setOrAppend_cur_false h4 k3
  have k5 : partView cur i (pureState t') = partView cur i (pureState t4) := by frame_invert h
  exact k5.trans k4

/-- `applyPendingDeposit` keeps a target bit of `false`, and the slot. -/
@[frame] theorem applyPendingDeposit_frame_part_false {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit} {sl : Slot}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps a target bit of `false`, and the slot. -/
@[frame] theorem ppdLoop_frame_part_false {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch} {sl : Slot}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  frame_invert h

/-- `processPendingDeposits` keeps a target bit of `false`, and the slot. -/
@[frame] theorem processPendingDeposits_frame_part_false {t t' : BeaconState} {a : PUnit}
    {sl : Slot}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  frame_invert h

end

/-! ## The block functions -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend] {cur : Bool} {i : Nat}

/-- `slashValidator` keeps `partView`. -/
@[frame] theorem slashValidator_frame_part {t t' : BeaconState} {a : PUnit}
    {j : ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) j).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `applyWithdrawals` writes the balances of validators and builders only. -/
@[frame] theorem applyWithdrawals_frame_part {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps `partView`. -/
@[frame] theorem processWithdrawals_frame_part {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processRandao` keeps `partView`. -/
@[frame] theorem processRandao_frame_part {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps `partView`. -/
@[frame] theorem processSyncAggregate_frame_part {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processAttesterSlashing` keeps `partView`. -/
@[frame] theorem processAttesterSlashing_frame_part {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processVoluntaryExit` keeps `partView`. -/
@[frame] theorem processVoluntaryExit_frame_part {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps `partView`. -/
@[frame] theorem processBlsToExecutionChange_frame_part {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps `partView`. -/
@[frame] theorem queueExcessActiveBalance_frame_part {t t' : BeaconState} {a : PUnit}
    {j : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps `partView`. -/
@[frame] theorem switchToCompoundingValidator_frame_part {t t' : BeaconState} {a : PUnit}
    {j : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps `partView`. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame_part {t t' : BeaconState}
    {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `partView`. -/
@[frame] theorem initiateBuilderExit_frame_part {t t' : BeaconState} {a : PUnit}
    {j : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `partView`. -/
@[frame] theorem addBuilderToRegistry_frame_part {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `partView`. -/
@[frame] theorem processDepositRequest_frame_part {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps `partView`. -/
@[frame] theorem processWithdrawalRequest_frame_part {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps `partView`. -/
@[frame] theorem processConsolidationRequest_frame_part {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `partView`. -/
@[frame] theorem processBuilderDepositRequest_frame_part {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `partView`. -/
@[frame] theorem processBuilderExitRequest_frame_part {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `partView`. -/
@[frame] theorem settleBuilderPayment_frame_part {t t' : BeaconState} {a : PUnit} {j : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) j).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps `partView`. -/
@[frame] theorem processProposerSlashing_frame_part {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps `partView`. -/
@[frame] theorem applyParentExecutionPayload_frame_part {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps `partView`. -/
@[frame] theorem processParentExecutionPayload_frame_part {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `partView`. Its builder checks need more than the
default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_part {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `processBlockHeader` keeps `partView`. -/
@[frame] theorem processBlockHeader_frame_part {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

end

/-! ## The epoch step

`processParticipationFlagUpdates` moves the current list to the previous list, and writes a
list of zeros as the current list (`processParticipationFlagUpdates_run`). The substeps of
`processEpoch` before it keep a current bit of `false`. The substeps after it keep both bits.
So after an epoch step the current bit is `false`, and a previous bit of `true` was a current
bit of `true` before the step (`processEpoch_part`). -/

section
variable [Preset] [HasherTag]

omit [HasherTag] in
/-- A list built from zeros has no target bit. -/
theorem bitOf_of_ofArray_replicate {l : PartList} {n : Nat}
    (h : SizzLean.Repr.SSZList.ofArray?
      (Array.replicate n (0 : EthCLSpecs.Heze.ParticipationFlags)) = some l)
    (i : Nat) : bitOf l i = false := by
  unfold SizzLean.Repr.SSZList.ofArray? at h
  split at h
  · cases h
    unfold bitOf
    by_cases hi : i < n
    · rw [getElem!_pos (dom := fun (xs : PartList) i => i < xs.size)
        (h := by show i < (Array.replicate n _).size; simpa using hi)]
      show hasFlag ((Array.replicate n 0)[i]'_) _ = false
      simp only [Array.getElem_replicate]
      exact hasFlag_zero_target
    · rw [getElem!_neg (dom := fun (xs : PartList) i => i < xs.size)
        (h := by show ¬ i < (Array.replicate n _).size; simpa using hi)]
      exact hasFlag_zero_target
  · cases h

/-- `processParticipationFlagUpdates` moves the current bit to the previous bit, clears the
current bit, and keeps the slot. -/
theorem processParticipationFlagUpdates_run (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState st) = .ok ((), pureState st')) (i : Nat) :
    partBit false i (pureState st') = partBit true i (pureState st) ∧
      partBit true i (pureState st') = false ∧ st'.slot = st.slot := by
  unfold EthCLSpecs.Heze.processParticipationFlagUpdates at h
  have h := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨zeros, s1, hz, h⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ h
  unfold sszOfArrayM at hz
  split at hz
  · rename_i l hl
    rw [EthCLLib.Proofs.run_pure] at hz
    injection hz with hz
    injection hz with hz1 hz2
    subst hz1 hz2
    -- The write: the previous list is the old current list, the current list is `l`.
    have e' := congrArg SizzLean.Cache.SSZ.Box.view (EthCLLib.Proofs.run_modifyThe_eq_ok h)
    refine ⟨?_, ?_, ?_⟩
    · show bitOf (sszGet (pureState st') previousEpochParticipation) i = _
      rw [e']
      rfl
    · show bitOf (sszGet (pureState st') currentEpochParticipation) i = false
      rw [e']
      exact bitOf_of_ofArray_replicate hl i
    · show (pureState st').view.slot = _
      rw [e']
      rfl
  · cases hz

variable [Config] [CryptoBackend] {cur : Bool} {i : Nat}

/-- The four substeps of `processEpochSuffix` before `processParticipationFlagUpdates`. -/
def epochSuffixPre : HezeRun Unit := do
  EthCLSpecs.Heze.processEffectiveBalanceUpdates
  EthCLSpecs.Heze.processSlashingsReset
  EthCLSpecs.Heze.processRandaoMixesReset
  EthCLSpecs.Heze.processHistoricalSummariesUpdate

/-- The three substeps of `processEpochSuffix` after `processParticipationFlagUpdates`. -/
def epochSuffixPost : HezeRun Unit := do
  EthCLSpecs.Heze.processSyncCommitteeUpdates
  EthCLSpecs.Heze.processProposerLookahead
  EthCLSpecs.Heze.processPtcWindow

omit [Config] in
/-- `processEpochSuffix` around its flag rotation. -/
theorem processEpochSuffix_eq_rot :
    processEpochSuffix = (epochSuffixPre >>= fun _ =>
      EthCLSpecs.Heze.processParticipationFlagUpdates >>= fun _ => epochSuffixPost) := by
  unfold processEpochSuffix epochSuffixPre epochSuffixPost
  simp only [bind_assoc]

/-- `epochSuffixPre` keeps the uncached box. -/
theorem keepsUncached_epochSuffixPre : EthCLLib.Proofs.KeepsUncached epochSuffixPre := by
  unfold epochSuffixPre
  refine EthCLLib.Proofs.keepsUncached_bind keepsUncached_processEffectiveBalanceUpdates
    fun _ => ?_
  refine EthCLLib.Proofs.keepsUncached_bind keepsUncached_processSlashingsReset fun _ => ?_
  refine EthCLLib.Proofs.keepsUncached_bind keepsUncached_processRandaoMixesReset fun _ => ?_
  exact keepsUncached_processHistoricalSummariesUpdate

/-- The epoch prefix keeps a target bit of `false`, and the slot. -/
theorem processEpochPrefix_frame_part_false {t t' : BeaconState} {a : Unit} {sl : Slot}
    (h : processEpochPrefix.run (pureState t) = .ok (a, pureState t'))
    (hs : partView cur i (pureState t) = (false, sl)) :
    partView cur i (pureState t') = (false, sl) := by
  frame_invert h

/-- `epochSuffixPre` keeps `partView`. -/
theorem epochSuffixPre_frame_part {t t' : BeaconState} {a : Unit}
    (h : epochSuffixPre.run (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- `epochSuffixPost` keeps `partView`. -/
theorem epochSuffixPost_frame_part {t t' : BeaconState} {a : Unit}
    (h : epochSuffixPost.run (pureState t) = .ok (a, pureState t')) :
    partView cur i (pureState t') = partView cur i (pureState t) := by
  frame_invert h

/-- An epoch step clears the current bit and keeps the slot. A previous bit of `true` after
the step was a current bit of `true` before it. -/
theorem processEpoch_part {st1 st2 : BeaconState}
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run
      (pureState st1) = .ok ((), pureState st2)) (i : Nat) :
    partBit true i (pureState st2) = false ∧
      (partBit false i (pureState st2) = true → partBit true i (pureState st1) = true) ∧
      st2.slot = st1.slot := by
  have hsp := processEpoch_frame_spine h
  rw [processEpoch_eq] at h
  obtain ⟨⟨⟩, a, ha, h⟩ :=
    EthCLLib.Proofs.run_bind_eq_ok_pure keepsUncached_processEpochPrefix h
  obtain ⟨⟨⟩, b, hb, h⟩ :=
    EthCLLib.Proofs.run_bind_eq_ok_pure keepsUncached_processBuilderPendingPayments h
  rw [processEpochSuffix_eq_rot] at h
  obtain ⟨⟨⟩, c, hc, h⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure keepsUncached_epochSuffixPre h
  obtain ⟨⟨⟩, d, hd, he⟩ :=
    EthCLLib.Proofs.run_bind_eq_ok_pure keepsUncached_processParticipationFlagUpdates h
  obtain ⟨rp, rc, -⟩ := processParticipationFlagUpdates_run c d hd i
  have post : ∀ w, partView w i (pureState st2) = partView w i (pureState d) := fun _ =>
    epochSuffixPost_frame_part he
  refine ⟨(congrArg Prod.fst (post true)).trans rc, fun hprev => ?_, congrArg Prod.fst hsp⟩
  have h1 : partBit true i (pureState c) = true := by
    rw [← rp, ← hprev]
    exact (congrArg Prod.fst (post false)).symm
  -- A current bit of `false` at `st1` stays `false` up to the rotation.
  cases h0 : partBit true i (pureState st1)
  · have k1 := processEpochPrefix_frame_part_false (cur := true) (i := i) (sl := st1.slot) ha
      (Prod.ext h0 rfl)
    have k2 := (processBuilderPendingPayments_frame_part (cur := true) (i := i) hb).trans k1
    have k3 := (epochSuffixPre_frame_part (cur := true) (i := i) hc).trans k2
    have k4 : partBit true i (pureState c) = false := congrArg Prod.fst k3
    rw [h1] at k4
    cases k4
  · rfl

end

end EthCLSpecs.Proofs.Heze
