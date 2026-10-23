import EthCLSpecs.Proofs.Heze.PaymentCarried
import EthCLSpecs.Proofs.Heze.PaymentWriters
import EthCLSpecs.Proofs.Heze.SyncFrame

/-!
# `EthCLSpecs.Proofs.Heze.ListLengths`: the registry lists keep one length along a chain run

The state holds five lists indexed by validator: `validators`, `balances`, the two
participation lists, and `inactivityScores`. The spec reads the four other lists at a
`validators` index, and each read raises `IndexError` past the end. `ChainRun.listLengths`
proves that the four lists have the length of `validators` at the end of a chain run when
they have it at the start.

`lengthsView` is the tuple of the five lengths, and `lengthsAgree` is the claim, a `Bool`
function of it. Most spec functions keep `lengthsView`. Their writes set one entry in range
(`[i]!`), and such a write keeps the length of its list (`array_size_set!`). `frame_invert`
proves those lemmas. Two functions change a length, and each has a proof of its own that
the lengths still agree:

- `addValidatorToRegistry` appends to all five lists (`addValidatorToRegistry_lengths`).
  Each `setOrAppendState` takes its append branch, since the index is the length of
  `validators` and the other lists have that length.
- `processParticipationFlagUpdates` moves the current list to the previous one and writes
  zeros, one per validator, as the current list (`processParticipationFlagUpdates_lengths`).

The functions that call these two keep `lengthsAgree` only from a start where it holds. Their
lemmas take that start fact, and `frame_invert` uses it at each call.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState run_get_bind_eq_ok run_bind_eq_ok run_bind_eq_ok_pure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState)

section
variable [Preset] [HasherTag]

/-- The lengths of `validators` and of the four lists that the spec indexes by validator. -/
def lengthsView (st : State) : Nat × Nat × Nat × Nat × Nat :=
  let v := st.view
  (v.validators.size, v.balances.size, v.previousEpochParticipation.size,
    v.currentEpochParticipation.size, v.inactivityScores.size)

/-- The four lists that the spec indexes by validator have the length of `validators`. -/
def lengthsAgree (st : State) : Bool :=
  let l := lengthsView st
  l.2.1 == l.1 && l.2.2.1 == l.1 && l.2.2.2.1 == l.1 && l.2.2.2.2 == l.1

/-- A run that keeps the lengths keeps whether they agree. -/
@[frame_proj] theorem lengthsAgree_of_view {a b : BeaconState}
    (h : lengthsView (pureState a) = lengthsView (pureState b)) :
    lengthsAgree (pureState a) = lengthsAgree (pureState b) := by
  unfold lengthsAgree
  rw [h]

end

/-- A list that `push?` returns is one longer. -/
theorem sszList_push?_size {α : Type} {cap : Nat} {xs l : SizzLean.Repr.SSZList α cap} {x : α}
    (h : xs.push? x = some l) : l.val.size = xs.val.size + 1 := by
  unfold SizzLean.Repr.SSZList.push? at h
  split at h
  · injection h with h
    subst h
    simp [SizzLean.Repr.SSZList.push]
  · cases h

/-- Run one `setOrAppendState` block of `addValidatorToRegistry` on its append branch.
`hc` is the test that the index equals the length. The tactic names the longer list `l`,
the fact `hl` that `push?` returns it, and the end state as a record update with `l`. -/
syntax "append_block " ident term:max ident ident : tactic
macro_rules
  | `(tactic| append_block $h $hc $l $hl) => `(tactic| (
      rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe,
        EthCLLib.Proofs.except_bind_ok] at $h:ident
      -- The test holds, so the other branches are void.
      split at $h:ident
      rotate_left
      · rename_i hneg _
        exact absurd $hc hneg
      rename_i _ $h:ident
      rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_getThe,
        EthCLLib.Proofs.except_bind_ok] at $h:ident
      split at $h:ident
      rotate_left
      · -- A full list: `throwListFull` raises.
        rename_i hrun
        unfold EthCLLib.Spec.throwListFull at hrun
        rw [EthCLLib.Proofs.run_liftErr_of_error _ _ rfl] at hrun
        cases hrun
      rename_i heq hrun
      obtain ⟨$l, $hl, hs⟩ := Option.map_eq_some_iff.mp heq
      have hw := (modifyState_run_eq hrun).trans hs.symm
      simp only [pureState_eq_uncached] at hw
      have e := congrArg SizzLean.Cache.SSZ.Box.view hw
      try dsimp only at e
      subst e))

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `addValidatorToRegistry` keeps lengths that agree. The new validator's index is the
length of `validators`, so each of the five `setOrAppendState` blocks appends, and each list
grows by one. -/
theorem addValidatorToRegistry_lengths {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  simp only [lengthsAgree, lengthsView, Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨⟨hb, hp⟩, hc⟩, hi⟩ := h0
  unfold EthCLSpecs.Heze.addValidatorToRegistry at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨_, w1, h1, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  append_block h1 (beq_self_eq_true _) l1 hl1
  obtain ⟨_, w2, h2, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  append_block h2 (beq_iff_eq.mpr hb.symm) l2 hl2
  obtain ⟨_, w3, h3, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  append_block h3 (beq_iff_eq.mpr hp.symm) l3 hl3
  obtain ⟨_, w4, h4, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  append_block h4 (beq_iff_eq.mpr hc.symm) l4 hl4
  append_block h (beq_iff_eq.mpr hi.symm) l5 hl5
  -- Each list is one longer than its old value, and the old values had one length.
  have s1 := sszList_push?_size hl1
  have s2 := sszList_push?_size hl2
  have s3 := sszList_push?_size hl3
  have s4 := sszList_push?_size hl4
  have s5 := sszList_push?_size hl5
  simp only [lengthsAgree, lengthsView, pureState_eq_uncached, SizzLean.Cache.SSZ.Box.view,
    SizzLean.Repr.SSZList.size, Bool.and_eq_true, beq_iff_eq] at s1 s2 s3 s4 s5 hb hp hc hi ⊢
  omega

/-- A list that `ofArray?` returns holds the array. -/
theorem sszList_ofArray?_val {α : Type} {cap : Nat} {a : Array α}
    {l : SizzLean.Repr.SSZList α cap} (h : SizzLean.Repr.SSZList.ofArray? a = some l) :
    l.val = a := by
  unfold SizzLean.Repr.SSZList.ofArray? at h
  split at h
  · injection h with h
    subst h
    rfl
  · cases h

/-- `processParticipationFlagUpdates` keeps lengths that agree. The previous list takes the
current one, and the current list is zeros, one per validator. -/
theorem processParticipationFlagUpdates_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  unfold EthCLSpecs.Heze.processParticipationFlagUpdates at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rw [EthCLLib.Proofs.run_bind] at h
  unfold EthCLLib.Spec.sszOfArrayM at h
  split at h
  rotate_left
  · -- Too many validators for the list: `throwListFull` raises.
    unfold EthCLLib.Spec.throwListFull at h
    rw [EthCLLib.Proofs.run_liftErr_of_error _ _ rfl, EthCLLib.Proofs.except_bind_error] at h
    cases h
  rename_i zeros hz
  rw [EthCLLib.Proofs.run_pure, EthCLLib.Proofs.except_bind_ok] at h
  have hw := modifyState_run_eq h
  have hzs := congrArg Array.size (sszList_ofArray?_val hz)
  rw [hw]
  simp only [lengthsAgree, lengthsView, pureState_eq_uncached, SizzLean.Cache.SSZ.Box.view,
    SizzLean.Repr.SSZList.size, Bool.and_eq_true, beq_iff_eq, Array.size_replicate]
    at h0 hzs ⊢
  omega

attribute [frame] addValidatorToRegistry_lengths processParticipationFlagUpdates_lengths

/-! ## The functions that keep the lengths

Each lemma below states `lengthsAgree (pureState t') = lengthsAgree (pureState t)` for a run
from `pureState t` to `pureState t'`, and `frame_invert` proves it. A write of one entry
keeps the length of its list (`array_size_set!`). A helper that returns a state value has a
`_ret` lemma for the value it returns. -/

/-- `increaseBalance` returns a state value with the lengths of its argument. -/
@[frame] theorem increaseBalance_ret_lengths {u t t' b : BeaconState}
    {i : EthCLSpecs.Heze.ValidatorIndex} {d : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    lengthsView (pureState b) = lengthsView (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the lengths of its argument. -/
@[frame] theorem decreaseBalance_ret_lengths {u t t' b : BeaconState}
    {i : EthCLSpecs.Heze.ValidatorIndex} {d : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    lengthsView (pureState b) = lengthsView (pureState u) := by
  frame_invert h

/-- `applyDeltas` returns a state value with the lengths of its argument. -/
@[frame] theorem applyDeltas_ret_lengths {u t t' b : BeaconState}
    {r p : Array EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.applyDeltas (StateTransition := HezeRun) r p (pureState u)).run
      (pureState t) = .ok (pureState b, pureState t')) :
    lengthsView (pureState b) = lengthsView (pureState u) := by
  frame_invert h

/-- `processSlot` keeps the lengths. -/
@[frame] theorem processSlot_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processJustificationAndFinalization` keeps the lengths. -/
@[frame] theorem processJustificationAndFinalization_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  jf_frame lengthsView h

/-- `processInactivityUpdates` keeps the lengths. -/
@[frame] theorem processInactivityUpdates_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processRewardsAndPenalties` keeps the lengths. -/
@[frame] theorem processRewardsAndPenalties_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `computeExitEpochAndUpdateChurn` keeps the lengths. -/
@[frame] theorem computeExitEpochAndUpdateChurn_lengths {t t' : BeaconState} {a : _}
    {b : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `initiateValidatorExit` keeps the lengths. -/
@[frame] theorem initiateValidatorExit_lengths {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.ValidatorIndex}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processRegistryUpdates` keeps the lengths. -/
@[frame] theorem processRegistryUpdates_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processSlashings` keeps the lengths. -/
@[frame] theorem processSlashings_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processEth1DataReset` keeps the lengths. -/
@[frame] theorem processEth1DataReset_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEth1DataReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `applyPendingDeposit` keeps lengths that agree. A new key with a valid signature runs
`addValidatorToRegistry`. -/
@[frame] theorem applyPendingDeposit_lengths {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps lengths that agree. -/
@[frame] theorem ppdLoop_lengths {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : EthCLSpecs.Heze.Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  frame_invert h

/-- `processPendingDeposits` keeps lengths that agree. -/
@[frame] theorem processPendingDeposits_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  frame_invert h

/-- `processPendingConsolidations` keeps the lengths. -/
@[frame] theorem processPendingConsolidations_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps the lengths. -/
@[frame] theorem processBuilderPendingPayments_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processEffectiveBalanceUpdates` keeps the lengths. -/
@[frame] theorem processEffectiveBalanceUpdates_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processSlashingsReset` keeps the lengths. -/
@[frame] theorem processSlashingsReset_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps the lengths. -/
@[frame] theorem processRandaoMixesReset_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps the lengths. -/
@[frame] theorem processHistoricalSummariesUpdate_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps the lengths. -/
@[frame] theorem processSyncCommitteeUpdates_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps the lengths. -/
@[frame] theorem processProposerLookahead_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps the lengths. -/
@[frame] theorem processPtcWindow_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- The epoch prefix keeps lengths that agree. -/
@[frame] theorem processEpochPrefix_lengths {t t' : BeaconState} {a : Unit}
    (h : processEpochPrefix.run (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  frame_invert h

/-- The epoch suffix keeps lengths that agree. -/
@[frame] theorem processEpochSuffix_lengths {t t' : BeaconState} {a : Unit}
    (h : processEpochSuffix.run (pureState t) = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  frame_invert h

/-- `processEpoch` keeps lengths that agree. -/
@[frame] theorem processEpoch_lengths {t t' : BeaconState} {a : Unit}
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t'))
    (h0 : lengthsAgree (pureState t) = true) : lengthsAgree (pureState t') = true := by
  rw [processEpoch_eq] at h
  frame_invert h

/-! ## The block functions -/

/-- `slashValidator` keeps the lengths. -/
@[frame] theorem slashValidator_lengths {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.ValidatorIndex}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `applyWithdrawals` keeps the lengths. -/
@[frame] theorem applyWithdrawals_lengths {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps the lengths. -/
@[frame] theorem processWithdrawals_lengths {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processRandao` keeps the lengths. -/
@[frame] theorem processRandao_lengths {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps the lengths. -/
@[frame] theorem processEth1Data_lengths {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processSyncAggregate` keeps the lengths. -/
@[frame] theorem processSyncAggregate_lengths {t t' : BeaconState} {a : PUnit}
    {agg : EthCLSpecs.Heze.SyncAggregate}
    (h : (EthCLSpecs.Heze.processSyncAggregate (StateTransition := HezeRun) agg).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  sync_frame lengthsView h

/-- `processAttesterSlashing` keeps the lengths. -/
@[frame] theorem processAttesterSlashing_lengths {t t' : BeaconState} {a : PUnit}
    {asl : EthCLSpecs.Heze.AttesterSlashing}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processProposerSlashing` keeps the lengths. -/
@[frame] theorem processProposerSlashing_lengths {t t' : BeaconState} {a : PUnit}
    {ps : EthCLSpecs.Heze.ProposerSlashing}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processAttestation` keeps the lengths. It writes one participation entry per flag. -/
@[frame] theorem processAttestation_lengths {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processVoluntaryExit` keeps the lengths. -/
@[frame] theorem processVoluntaryExit_lengths {t t' : BeaconState} {a : PUnit}
    {sve : EthCLSpecs.Heze.SignedVoluntaryExit}
    (h : (EthCLSpecs.Heze.processVoluntaryExit (StateTransition := HezeRun) sve).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processBlsToExecutionChange` keeps the lengths. -/
@[frame] theorem processBlsToExecutionChange_lengths {t t' : BeaconState} {a : PUnit}
    {sbc : EthCLSpecs.Heze.SignedBLSToExecutionChange}
    (h : (EthCLSpecs.Heze.processBlsToExecutionChange (StateTransition := HezeRun) sbc).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps the lengths. -/
@[frame] theorem queueExcessActiveBalance_lengths {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps the lengths. -/
@[frame] theorem switchToCompoundingValidator_lengths {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps the lengths. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_lengths {t t' : BeaconState} {a : _}
    {b : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps the lengths. -/
@[frame] theorem initiateBuilderExit_lengths {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps the lengths. -/
@[frame] theorem addBuilderToRegistry_lengths {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : EthCLSpecs.Heze.Gwei} {slot : EthCLSpecs.Heze.Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps the lengths. -/
@[frame] theorem processDepositRequest_lengths {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processWithdrawalRequest` keeps the lengths. -/
@[frame] theorem processWithdrawalRequest_lengths {t t' : BeaconState} {a : PUnit}
    {wr : EthCLSpecs.Heze.WithdrawalRequest}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processConsolidationRequest` keeps the lengths. -/
@[frame] theorem processConsolidationRequest_lengths {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps the lengths. -/
@[frame] theorem processBuilderDepositRequest_lengths {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps the lengths. -/
@[frame] theorem processBuilderExitRequest_lengths {t t' : BeaconState} {a : PUnit}
    {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps the lengths. -/
@[frame] theorem settleBuilderPayment_lengths {t t' : BeaconState} {a : PUnit} {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps the lengths. -/
@[frame] theorem applyParentExecutionPayload_lengths {t t' : BeaconState} {a : PUnit}
    {requests : EthCLSpecs.Heze.ExecutionRequests}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps the lengths. -/
@[frame] theorem processParentExecutionPayload_lengths {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processBlockHeader` keeps the lengths. -/
@[frame] theorem processBlockHeader_lengths {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processExecutionPayloadBid` keeps the lengths. -/
@[frame] theorem processExecutionPayloadBid_lengths {t t' : BeaconState} {a : PUnit}
    {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processOperations` keeps the lengths. -/
@[frame] theorem processOperations_lengths {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run
      (pureState t) = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-- `processBlock` keeps the lengths. -/
@[frame] theorem processBlock_lengths {t t' : BeaconState} {a : PUnit}
    {block : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) block).run (pureState t)
      = .ok (a, pureState t')) :
    lengthsView (pureState t') = lengthsView (pureState t) := by
  frame_invert h

/-! ## Along a chain run -/

/-- A slot step keeps lengths that agree. The slot increment writes the slot only. -/
theorem SlotStep.lengths {st st' : BeaconState} (h : SlotStep st st')
    (h0 : lengthsAgree (pureState st) = true) : lengthsAgree (pureState st') = true := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := (lengthsAgree_of_view (processSlot_lengths h1)).trans h0
  have e2 : lengthsAgree (pureState st2) = true := by
    split at h2
    · exact processEpoch_lengths h2 e1
    · rw [h2]
      exact e1
  rw [hst']
  exact e2

/-- A block step keeps the lengths. -/
theorem BlockStep.lengths {sb : EthCLSpecs.Heze.SignedBeaconBlock} {v : Bool}
    {st st' : BeaconState} (h : BlockStep sb v st st') :
    lengthsAgree (pureState st') = lengthsAgree (pureState st) :=
  lengthsAgree_of_view (processBlock_lengths h.2.1)

/-- Along a chain run, the four lists that the spec indexes by validator keep the length of
`validators`, when they have it at the start. -/
theorem ChainRun.listLengths {hi : Nat} {steps : List ChainStep} {st st' : BeaconState}
    (h : ChainRun hi steps st st') (h0 : lengthsAgree (pureState st) = true) :
    lengthsAgree (pureState st') = true := by
  induction h with
  | nil => exact h0
  | slot _ hstep _ ih => exact ih (hstep.lengths h0)
  | block _ _ hstep _ ih => exact ih (hstep.lengths.trans h0)

end

end EthCLSpecs.Proofs.Heze
