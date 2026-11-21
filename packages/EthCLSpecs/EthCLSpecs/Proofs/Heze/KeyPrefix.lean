import EthCLSpecs.Proofs.Heze.StakeFrame
import EthCLSpecs.Proofs.Heze.HeaderFrame
import EthCLSpecs.Proofs.Heze.DriftEpoch
import EthCLSpecs.Proofs.Heze.EbUpdates
import EthCLSpecs.Proofs.Heze.ParticipationRotate

/-!
# `EthCLSpecs.Proofs.Heze.KeyPrefix`: a registry index names one key on every run

An attestation counts for the validator at an index of the registry of the state that
processes it. `is_valid_indexed_attestation` checks the signature against the public key at that
index. So a statement about "the honest validator `i`" on two runs means one key only when index
`i` holds one public key on both runs.

The state transition never writes a public key and never removes a validator. A new validator
takes the index `len(state.validators)` (`get_index_for_new_validator`), so it is appended. So
the first `n` public keys of a registry with at least `n` validators stay along a run:

- a block step and a slot step keep the public keys (`processBlock_frame_key`,
  `processSlot_frame_key`);
- the epoch step writes validators only through `modValidator`, which keeps the public key, and
  appends through `addValidatorToRegistry`.

`pkView n` holds the flag `n ≤ len(validators)` and the first `n` public keys. Each epoch
function keeps a `pkView` of `true` (`processEpoch_frame_pk`). Along a run, `pkView` stays
(`ChainRun.pkView_eq`). So two runs from one state agree on the public keys of its indices
(`ChainRun.pubkey_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState pureState_inj run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_ite_eq_ok run_pure_state_eq)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState Epoch Gwei ValidatorIndex
  Validator getValidatorFromDeposit)

section
variable [Preset] [HasherTag]

/-! ## The view -/

/-- The first `n` public keys of a registry. The definition is irreducible, so `frame_invert`
compares two such values by their registries. -/
@[irreducible] def keysOf (n : Nat) (vs : Array Validator) : List EthCLSpecs.Heze.BLSPubkey :=
  (vs.toList.take n).map (·.pubkey)

/-- The flag `n ≤ len(validators)` and the first `n` public keys. -/
def pkView (n : Nat) (st : State) : Bool × List EthCLSpecs.Heze.BLSPubkey :=
  (decide (n ≤ (sszGet st validators).val.size), keysOf n (sszGet st validators).val)

/-- The registry and the slot. -/
def vsView (st : State) := (sszGet st validators, sszGet st slot)

/-- Two states with one `keyView` have one `pkView`. -/
theorem pkView_of_key {n : Nat} {s u : BeaconState}
    (h : keyView (pureState s) = keyView (pureState u)) :
    pkView n (pureState s) = pkView n (pureState u) := by
  have hm : s.validators.val.map (·.pubkey) = u.validators.val.map (·.pubkey) :=
    congrArg (fun x => x.1) h
  have hsz : s.validators.val.size = u.validators.val.size := by
    simpa using congrArg Array.size hm
  simp only [pkView, Prod.mk.injEq]
  refine ⟨by show decide (n ≤ s.validators.val.size) = decide (n ≤ u.validators.val.size); rw [hsz],
    ?_⟩
  show keysOf n s.validators.val = keysOf n u.validators.val
  unfold keysOf
  rw [List.map_take, List.map_take, ← Array.toList_map, ← Array.toList_map, hm]

/-- Two states with one registry and one slot have one `pkView`. -/
theorem pkView_of_vs {n : Nat} {s u : BeaconState} (h : vsView (pureState s) = vsView (pureState u)) :
    pkView n (pureState s) = pkView n (pureState u) := by
  simp only [vsView, Prod.mk.injEq] at h
  simp only [pkView, h.1]

/-- A write that keeps the public key keeps `pkView`. -/
theorem pkView_setValidator {n : Nat} (a : BeaconState) (j : Nat) (v' : Validator)
    (hv : v'.pubkey = a.validators[j]!.pubkey) :
    pkView n (pureState { a with validators := a.validators.set! j v' }) =
      pkView n (pureState a) :=
  pkView_of_key (keyView_setValidator a j v' hv)

/-- An append keeps a `pkView` of `true`: the first `n` validators stay. -/
theorem pkView_push {n : Nat} (a : BeaconState) (v : Validator)
    (hn : n ≤ a.validators.val.size) :
    pkView n (pureState { a with validators := a.validators.push v }) =
      pkView n (pureState a) := by
  simp only [pkView, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · show decide (n ≤ (a.validators.val.push v).size) = decide (n ≤ a.validators.val.size)
    rw [Array.size_push]
    simp only [decide_eq_decide]
    omega
  · show keysOf n (a.validators.val.push v) = keysOf n a.validators.val
    unfold keysOf
    rw [Array.toList_push, List.take_append_of_le_length (by simpa using hn)]

/-- A write of one validator that keeps its public key keeps `pkView`. -/
@[frame_close] theorem pkView_modValidator {n : Nat} {acc : BeaconState} {i : ValidatorIndex}
    {wc : Validator → EthCLSpecs.Heze.Bytes32} {eb : Validator → Gwei} {sl : Validator → Bool}
    {aee ae ee we : Validator → EthCLSpecs.Heze.Epoch} {v : _}
    (hacc : pkView n (pureState acc) = v) :
    pkView n (EthCLSpecs.Heze.modValidator (pureState acc) i fun w =>
      { pubkey := w.pubkey, withdrawalCredentials := wc w, effectiveBalance := eb w,
        slashed := sl w, activationEligibilityEpoch := aee w, activationEpoch := ae w,
        exitEpoch := ee w, withdrawableEpoch := we w }) = v := by
  rw [← hacc, modValidator_pureState]
  exact pkView_setValidator acc _ _ rfl

/-- `pkView_modValidator` for a write at a list position (`modValidatorAt`). -/
@[frame_close] theorem pkView_modValidatorAt {n : Nat} {acc : BeaconState} {i : Nat}
    {wc : Validator → EthCLSpecs.Heze.Bytes32} {eb : Validator → Gwei} {sl : Validator → Bool}
    {aee ae ee we : Validator → EthCLSpecs.Heze.Epoch} {v : _}
    (hacc : pkView n (pureState acc) = v) :
    pkView n (EthCLSpecs.Heze.modValidatorAt (pureState acc) i fun w =>
      { pubkey := w.pubkey, withdrawalCredentials := wc w, effectiveBalance := eb w,
        slashed := sl w, activationEligibilityEpoch := aee w, activationEpoch := ae w,
        exitEpoch := ee w, withdrawableEpoch := we w }) = v := by
  rw [← hacc, modValidatorAt_pureState]
  exact pkView_setValidator acc _ _ rfl

/-- A flag of `true` in a `pkView` value gives `n ≤ len(validators)`. -/
theorem le_of_pkView {n : Nat} {t : BeaconState} {c : List EthCLSpecs.Heze.BLSPubkey}
    (hs : pkView n (pureState t) = (true, c)) : n ≤ t.validators.val.size := by
  have := congrArg Prod.fst hs
  exact of_decide_eq_true this

/-- The public key at an index below `n` is entry `i` of the first `n` public keys. -/
theorem pubkey_of_keysOf {n i : Nat} {vs : Array Validator} (hn : n ≤ vs.size) (hi : i < n) :
    (keysOf n vs)[i]? = some (vs[i]!).pubkey := by
  unfold keysOf
  rw [List.getElem?_map, List.getElem?_take_of_lt hi, Array.getElem?_toList,
    Array.getElem?_eq_getElem (by omega), getElem!_pos vs i (by omega)]
  rfl

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The epoch functions -/

/-- `processJustificationAndFinalization` keeps `pkView`. -/
@[frame] theorem processJustificationAndFinalization_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) :=
  pkView_of_key (processJustificationAndFinalization_frame_key h)

/-- `processInactivityUpdates` keeps `pkView`. -/
@[frame] theorem processInactivityUpdates_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processInactivityUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) :=
  pkView_of_key (processInactivityUpdates_frame_key h)

/-- `processRewardsAndPenalties` keeps `pkView`. -/
@[frame] theorem processRewardsAndPenalties_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRewardsAndPenalties (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) :=
  pkView_of_key (processRewardsAndPenalties_frame_key h)

/-- `processRegistryUpdates` keeps `pkView`. -/
@[frame] theorem processRegistryUpdates_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRegistryUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) :=
  pkView_of_key (processRegistryUpdates_frame_key h)

/-- `processSlashings` keeps `pkView`. -/
@[frame] theorem processSlashings_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashings (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) :=
  pkView_of_key (processSlashings_frame_key h)

/-- `processSlashingsReset` keeps `pkView`. -/
@[frame] theorem processSlashingsReset_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processRandaoMixesReset` keeps `pkView`. -/
@[frame] theorem processRandaoMixesReset_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processRandaoMixesReset (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processHistoricalSummariesUpdate` keeps `pkView`. -/
@[frame] theorem processHistoricalSummariesUpdate_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processHistoricalSummariesUpdate (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processParticipationFlagUpdates` keeps `pkView`. -/
@[frame] theorem processParticipationFlagUpdates_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processParticipationFlagUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processSyncCommitteeUpdates` keeps `pkView`. -/
@[frame] theorem processSyncCommitteeUpdates_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processSyncCommitteeUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processProposerLookahead` keeps `pkView`. -/
@[frame] theorem processProposerLookahead_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processProposerLookahead (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processPtcWindow` keeps `pkView`. -/
@[frame] theorem processPtcWindow_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processPtcWindow (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- One step of the effective-balance loop keeps `pkView`. It writes an effective balance. -/
theorem ebuBody_pk (n : Nat) (b : BeaconState) (i : Nat) :
    pkView n (pureState (ebuBody b i)) = pkView n (pureState b) := by
  unfold ebuBody
  dsimp only
  split
  · exact pkView_setValidator b i _ rfl
  · rfl

/-- A fold of `ebuBody` keeps `pkView`. -/
theorem ebuFold_pk (n : Nat) :
    ∀ (l : List Nat) (b : BeaconState),
      pkView n (pureState (l.foldl ebuBody b)) = pkView n (pureState b)
  | [], _ => rfl
  | i :: rest, b => by rw [List.foldl_cons, ebuFold_pk n rest (ebuBody b i), ebuBody_pk]

/-- `processEffectiveBalanceUpdates` keeps `pkView`. -/
@[frame] theorem processEffectiveBalanceUpdates_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processEffectiveBalanceUpdates (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  cases a
  rw [processEffectiveBalanceUpdates_run t t' h]
  exact ebuFold_pk n _ t

/-- `processPendingConsolidations` keeps `pkView`. -/
@[frame] theorem processPendingConsolidations_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processPendingConsolidations (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- `processBuilderPendingPayments` keeps `pkView`. -/
@[frame] theorem processBuilderPendingPayments_frame_pk {n : Nat} {t t' : BeaconState}
    {a : PUnit}
    (h : (EthCLSpecs.Heze.processBuilderPendingPayments (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t')) :
    pkView n (pureState t') = pkView n (pureState t) := by
  frame_invert h

/-- **A deposit of a new validator keeps a `pkView` of `true`.** It appends the validator at
index `len(validators)`, after the first `n`. The four writes after the append keep the
registry. -/
@[frame] theorem addValidatorToRegistry_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {wc : EthCLSpecs.Heze.Bytes32} {amount : Gwei}
    {c : List EthCLSpecs.Heze.BLSPubkey}
    (h : (EthCLSpecs.Heze.addValidatorToRegistry (StateTransition := HezeRun) pk wc amount).run
      (pureState t) = .ok (a, pureState t'))
    (hs : pkView n (pureState t) = (true, c)) : pkView n (pureState t') = (true, c) := by
  have hn := le_of_pkView hs
  cases a
  unfold EthCLSpecs.Heze.addValidatorToRegistry at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨_, s0, h0, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, -, -⟩ := checkedIndex_run_ok h0
  try dsimp only at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  have h1 := run_get_bind_eq_ok _ _ _ h1
  try dsimp only at h1
  rcases run_ite_eq_ok h1 with ⟨-, h1⟩ | ⟨hne, -⟩
  · have e1 := appendValidator_run _ _ h1
    cases pureState_inj e1
    have hv : vsView (pureState t') = vsView (pureState
        { t with validators := t.validators.push (getValidatorFromDeposit pk wc amount) }) := by
      frame_invert h
    rw [pkView_of_vs hv, pkView_push _ _ hn]
    exact hs
  · simp at hne

/-- `applyPendingDeposit` keeps a `pkView` of `true`. -/
@[frame] theorem applyPendingDeposit_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    {d : EthCLSpecs.Heze.PendingDeposit} {c : List EthCLSpecs.Heze.BLSPubkey}
    (h : (EthCLSpecs.Heze.applyPendingDeposit (StateTransition := HezeRun) d).run
      (pureState t) = .ok (a, pureState t'))
    (hs : pkView n (pureState t) = (true, c)) : pkView n (pureState t') = (true, c) := by
  frame_invert h

/-- The deposit scan `ppdLoop` keeps a `pkView` of `true`. -/
@[frame] theorem ppdLoop_frame_pk {n : Nat} {t t' : BeaconState} {a : _}
    {d : Array EthCLSpecs.Heze.PendingDeposit} {finalizedSlot avail : Gwei}
    {nextEpoch : EthCLSpecs.Heze.Epoch} {c : List EthCLSpecs.Heze.BLSPubkey}
    (h : (EthCLSpecs.Heze.ppdLoop (StateTransition := HezeRun) d finalizedSlot avail
      nextEpoch).run (pureState t) = .ok (a, pureState t'))
    (hs : pkView n (pureState t) = (true, c)) : pkView n (pureState t') = (true, c) := by
  frame_invert h

/-- `processPendingDeposits` keeps a `pkView` of `true`. -/
@[frame] theorem processPendingDeposits_frame_pk {n : Nat} {t t' : BeaconState} {a : PUnit}
    {c : List EthCLSpecs.Heze.BLSPubkey}
    (h : (EthCLSpecs.Heze.processPendingDeposits (StateTransition := HezeRun)).run
      (pureState t) = .ok (a, pureState t'))
    (hs : pkView n (pureState t) = (true, c)) : pkView n (pureState t') = (true, c) := by
  frame_invert h

/-- **`processEpoch` keeps a `pkView` of `true`.** -/
theorem processEpoch_frame_pk {n : Nat} {t t' : BeaconState} {a : Unit}
    {c : List EthCLSpecs.Heze.BLSPubkey}
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t'))
    (hs : pkView n (pureState t) = (true, c)) : pkView n (pureState t') = (true, c) := by
  rw [processEpoch_eq_jf] at h
  frame_invert h

/-! ## Along a run -/

/-- A slot step keeps a `pkView` of `true`. -/
theorem SlotStep.pkView_eq {u u' : BeaconState} (h : SlotStep u u') {n : Nat}
    {c : List EthCLSpecs.Heze.BLSPubkey} (hs : pkView n (pureState u) = (true, c)) :
    pkView n (pureState u') = (true, c) := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := processSlot_run_eq h1
  subst e1
  have hs1 : pkView n (pureState (slotWrite u)) = (true, c) := by
    rw [← hs]
    exact pkView_of_vs rfl
  have hs2 : pkView n (pureState st2) = (true, c) := by
    split at h2
    · exact processEpoch_frame_pk h2 hs1
    · subst h2
      exact hs1
  rw [← hs2]
  have hv : u'.validators = st2.validators := congrArg (fun s : State => s.view.validators) hst'
  simp only [pkView]
  show (decide (n ≤ u'.validators.val.size), keysOf n u'.validators.val) = _
  rw [hv]
  rfl

/-- **Along a run, the first `n` public keys stay**, for `n` at most the size of the registry
at the start. -/
theorem ChainRun.pkView_eq {hi : Nat} {q : List ChainStep} {s z : BeaconState}
    (h : ChainRun hi q s z) {n : Nat} {c : List EthCLSpecs.Heze.BLSPubkey}
    (hs : pkView n (pureState s) = (true, c)) : pkView n (pureState z) = (true, c) := by
  induction h with
  | nil => exact hs
  | slot _ hstep _ ih => exact ih (hstep.pkView_eq hs)
  | block sb v hstep _ ih =>
    exact ih ((pkView_of_key (processBlock_frame_key hstep.2.1)).trans hs)

/-- **An index of a state names one public key on every run from it.** Take two runs from `s`,
and an index `i` of the registry of `s`. Both end states hold `i`, with the public key that `s`
holds at `i`. -/
theorem ChainRun.pubkey_eq {hi : Nat} {q : List ChainStep} {s z : BeaconState}
    (h : ChainRun hi q s z) {i : Nat} (hi' : i < s.validators.val.size) :
    i < z.validators.val.size ∧ (z.validators.val[i]!).pubkey = (s.validators.val[i]!).pubkey := by
  have hs : pkView s.validators.val.size (pureState s) =
      (true, keysOf s.validators.val.size s.validators.val) := by
    show (decide (s.validators.val.size ≤ s.validators.val.size),
      keysOf s.validators.val.size s.validators.val) = _
    rw [decide_eq_true (Nat.le_refl _)]
  have hz := h.pkView_eq hs
  have hn := le_of_pkView hz
  refine ⟨by omega, ?_⟩
  have e := congrArg Prod.snd hz
  simp only [pkView] at e
  have e1 := pubkey_of_keysOf (vs := z.validators.val) hn hi'
  have e2 := pubkey_of_keysOf (vs := s.validators.val) (Nat.le_refl _) hi'
  change keysOf s.validators.val.size z.validators.val = _ at e
  rw [e, e2] at e1
  exact (Option.some.inj e1).symm

end

end EthCLSpecs.Proofs.Heze
