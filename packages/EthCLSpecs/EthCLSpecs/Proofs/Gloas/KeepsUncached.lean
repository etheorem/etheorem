import EthCLLib.Spec
import EthCLLib.Proofs.KeepsUncached
import EthCLSpecs.Proofs.Fulu.Balances
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Gloas.Operations
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.KeepsUncached`: the Gloas handlers never leave the uncached box

`KeepsUncached` (`EthCLLib/Proofs/KeepsUncached.lean`) is the property behind `runPure`'s
conditional bind law: a successful run that starts on `pureState preState` ends on an
uncached box. This file discharges it for the Gloas handlers the per-step split
of `processOperations_run_ok_iff` builds on. All six `processOperations`
handlers have lemmas: the spike set (`computeExitEpochAndUpdateChurn`,
`initiateValidatorExit`, `processVoluntaryExit`), the readers
(`processProposerSlashing`, `processBlsToExecutionChange`,
`processPayloadAttestation`, with `getPtc` and `getIndexedPayloadAttestation`
as callees), and the two handlers with loops
(`processAttesterSlashing`, `processAttestation`) through the per-start lemmas
(`KeepsUncachedFrom`, `ReturnsUncached`, the invariant-loop facts, and the
`get`/`set` splice). The read helpers those two loop proofs call
(`getBlockRootAtSlot`, `getBlockRoot`, `isAttestationSameSlot`,
`getAttestationParticipationFlagIndices`) have lemmas of their own.

Each lemma is a construction over the generic closure lemmas, one bind per
`←`-binding in the source, and the state writes discharge
`keepsUncached_modify`'s writer hypothesis by `rfl` (the `sszUpdate` expansion on
`pureState state` reduces to the record update on `state`). The handlers are the Gloas
constants: `inherit` re-elaborates the Fulu bodies at `Gloas.State`, so
`EthCLSpecs.Gloas.processVoluntaryExit` calls `EthCLSpecs.Gloas.initiateValidatorExit`
and the Gloas `computeExitEpochAndUpdateChurn`, and the lemmas name those
constants. All of them are supporting lemmas, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag CryptoBackend sszGetIdx checkedAdd ErrorConv Checked liftErr
  StateTransitionError)
open EthCLSpecs.Gloas (Preset Config ValidatorIndex Gwei Epoch Slot Attestation AttestationData
  Validator SignedVoluntaryExit ProposerSlashing AttesterSlashing SignedBLSToExecutionChange
  PayloadAttestation BeaconState
  processVoluntaryExit initiateValidatorExit computeExitEpochAndUpdateChurn
  processProposerSlashing processAttesterSlashing processAttestation
  processBlsToExecutionChange processPayloadAttestation
  getIndexedPayloadAttestation getPtc increaseBalance decreaseBalance slashValidator
  modBalance getBlockRootAtSlot getBlockRoot isAttestationSameSlot
  getAttestationParticipationFlagIndices builderPaymentIndex)
open EthCLLib.Proofs (pureState KeepsUncached ReturnsUncached KeepsUncachedFrom
  keepsUncached_pure keepsUncached_throw keepsUncached_bind keepsUncached_modify
  keepsUncached_get keepsUncachedFrom_bind
  keepsUncached_liftChecked keepsUncachedFrom_liftChecked
  keepsUncached_liftErr keepsUncached_dite keepsUncached_forIn_range
  keepsUncached_ite keepsUncachedFrom_ite keepsUncachedFrom_pure keepsUncachedFrom_throw
  keepsUncachedFrom_liftErr keepsUncachedFrom_sszOfArrayM keepsUncachedFrom_dite
  keepsUncachedFrom_set keepsUncachedFrom_get
  keepsUncachedFrom_get_bind keepsUncachedFrom_throw_bind keepsUncachedFrom_forIn_array_of_keeps
  keepsUncachedFrom_forIn_array_bind_P keepsUncachedFrom_forIn_range_bind_run_inv
  returnsUncached_bind returnsUncachedFrom_bind keepsUncached_iff_forall_from
  keepsUncachedFrom_forIn_array_inv
  run_bind run_pure run_throw except_bind_ok except_bind_error
  run_ofExcept_ok run_ofExcept_error run_liftErr_of_ok run_liftErr_of_error
  run_sszGetIdx_some run_sszGetIdx_none keepsUncached_sszGetIdx keepsUncached_sszOfArrayM
  getAt_progressiveList_clUint64
  run_bind_inv ite_bind
  pureState_forIn_range_id)

open SizzLean (SSZRepr)
open SizzLean.Proofs (view_uncachedBox)
open SizzLean.Cache

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The run of a lifted checked value is the identity on the state: the success
value passes through, so a `liftM` bind in a run equation peels with the bind
law and this fact. The claim quantifies over an arbitrary box, so it is a box
fact and no plain-value restatement replaces it: a caller reaches it mid-run,
where the threaded box is only known to be `pureState` of some value through the
surrounding invariant, not in the lemma's own statement. -/
@[box_generic "the run equation is a claim about the box: it says the run's
post-state box is the start box itself, unchanged by the lifted checked value"]
private theorem run_liftChecked_ok {α : Type} (v : α)
    (s : SSZ.Box HasherTag.H BeaconState) :
    ((liftM (Except.ok v : Checked α) : GloasRun α).run s) = .ok (v, s) :=
  rfl

@[box_generic "the run equation is a claim about the box: the run rejects, so
the post-state box is the start box itself, unchanged by the faulted value"]
private theorem run_liftChecked_error {α : Type} (e : EthCLLib.Spec.ArithFault)
    (s : SSZ.Box HasherTag.H BeaconState) :
    ((liftM (Except.error e : Checked α) : GloasRun α).run s)
      = .error (StateTransitionError.ofArithFault e) :=
  rfl

/-- The flavour of a `liftM` of a pure checked value, proven over the run
equations. Some body-elaborated operator chains stall the leaf lemma's
conclusion unification, so the ladders state the fact at the site's own term
and cite this. -/
private theorem liftCheckedViaRun {α : Type} (_v : BeaconState) (x : Checked α) :
    KeepsUncached (liftM x : GloasRun α) := by
  intro v' a s h
  revert h
  cases hx : x with
  | ok w =>
    intro h
    rw [run_liftChecked_ok] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hs⟩ := h
    subst hs
    rfl
  | error e =>
    intro h
    rw [run_liftChecked_error] at h
    exact absurd h (by simp)

/-- `computeExitEpochAndUpdateChurn` keeps the flavour: one read of the state,
four lifted checked binds (the activation-exit sum, the churn limit, the churn
reservation, and the remaining-balance subtraction), and the two-clause write. -/
theorem keepsUncached_computeExitEpochAndUpdateChurn (exitBalance : Gwei) :
    KeepsUncached (computeExitEpochAndUpdateChurn
      (StateTransition := GloasRun) exitBalance) := by
  unfold computeExitEpochAndUpdateChurn
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_bind (keepsUncached_liftChecked (T := BeaconState)
      (ε := EthCLLib.Spec.StateTransitionError)
      (x := EthCLSpecs.Gloas.computeActivationExitEpoch
        (EthCLSpecs.Gloas.computeEpochAtSlot (sszGet state slot)))) (fun exitEpoch => ?_)
  refine keepsUncached_bind (keepsUncached_liftErr (T := BeaconState)
      (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.StateTransitionError)
      (EthCLSpecs.Gloas.getExitChurnLimit state)) (fun perEpochChurn => ?_)
  refine keepsUncached_bind (keepsUncached_liftChecked (T := BeaconState)
      (ε := EthCLLib.Spec.StateTransitionError)
      (x := EthCLSpecs.Gloas.reserveChurn exitBalance
        (if (sszGet state earliestExitEpoch) < max
            (sszGet state earliestExitEpoch) exitEpoch then perEpochChurn
          else (sszGet state exitBalanceToConsume)) perEpochChurn
        (max (sszGet state earliestExitEpoch) exitEpoch))) (fun p => ?_)
  refine keepsUncached_bind (keepsUncached_liftChecked (T := BeaconState)
      (ε := EthCLLib.Spec.StateTransitionError) (x := p.snd - exitBalance)) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_modify _ (fun v => ⟨_, by rfl⟩)) (fun _ => ?_)
  exact keepsUncached_pure _

/-- `initiateValidatorExit` keeps the flavour: the validator read and the
checked withdrawability sum are `liftErr`-shaped, the early-return gate is an
`if`, and the write is `modValidator` through the record update. -/
theorem keepsUncached_initiateValidatorExit (i : ValidatorIndex) :
    KeepsUncached (initiateValidatorExit (StateTransition := GloasRun) i) := by
  unfold initiateValidatorExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_bind (keepsUncached_sszGetIdx _ _) (fun validator => ?_)
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_computeExitEpochAndUpdateChurn validator.effectiveBalance)
    (fun exitEpoch => ?_)
  refine keepsUncached_bind
    (keepsUncached_liftChecked (x := exitEpoch + EthCLSpecs.Gloas.Const.minValidatorWithdrawabilityDelay))
    (fun withdrawableEpoch => ?_)
  (apply keepsUncached_modify; intro v; exact ⟨_, by rfl⟩)

/-- The Gloas copy of `processVoluntaryExit` keeps the flavour: the `assertH`
gate, six validation gates, two checked reads (`passedShardCommitteePeriod`'s
sum and the pending-withdrawal fold), and `initiateValidatorExit`, whose own
lemma carries the write. -/
theorem keepsUncached_processVoluntaryExit (sve : SignedVoluntaryExit) :
    KeepsUncached (processVoluntaryExit (StateTransition := GloasRun) sve) := by
  unfold processVoluntaryExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_bind (keepsUncached_sszGetIdx _ _) (fun validator => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  refine keepsUncached_bind ?h1 (fun _ => ?_)
  · exact keepsUncached_liftChecked (T := BeaconState)
      (ε := EthCLLib.Spec.StateTransitionError)
      (x := EthCLSpecs.Gloas.passedShardCommitteePeriod validator
        (EthCLSpecs.Gloas.currentEpochOf state))
  · refine keepsUncached_bind
      (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
      (fun _ => ?_)
    refine keepsUncached_bind ?h2 (fun _ => ?_)
    · exact keepsUncached_liftChecked (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (x := EthCLSpecs.Gloas.getPendingBalanceToWithdraw state sve.message.validatorIndex)
    · refine keepsUncached_bind
        (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
        (fun _ => ?_)
      refine keepsUncached_bind
        (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
        (fun _ => ?_)
      exact keepsUncached_initiateValidatorExit sve.message.validatorIndex

set_option maxRecDepth 40000 in
/-- `getPtc` keeps the flavour: it takes the state as an explicit argument, and
its body reads and gates only, through checked ops and asserts. The ladder is
explicit, and the declaration carries a local `maxRecDepth` raise for the
re-elaborated checked-operator terms (Stage 5.1 repair record). -/
theorem keepsUncached_getPtc (state : BeaconState) (slot : EthCLSpecs.Gloas.Slot) :
    KeepsUncached (getPtc (StateTransition := GloasRun) (pureState state) slot) := by
  unfold getPtc
  simp only []
  -- `split` peels the fork-epoch assert (the ite leaf's `Decidable` premise
  -- stalls on the re-elaborated epoch comparison); each branch continues with
  -- its own binds.
  split
  · refine keepsUncached_bind (keepsUncached_pure (T := BeaconState) PUnit.unit) (fun _ => ?_)
    refine keepsUncached_ite (T := BeaconState)
      (ε := EthCLLib.Spec.StateTransitionError)
      (c := (EthCLSpecs.Gloas.computeEpochAtSlot slot <
        EthCLSpecs.Gloas.currentEpochOf (pureState state)))
      (fun _ => ?_) (fun _ => ?_)
    · refine keepsUncached_bind (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (liftCheckedViaRun state
          (x := EthCLSpecs.Gloas.computeEpochAtSlot slot + 1)) (fun _ => ?_)
      refine keepsUncached_bind
        (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
        (fun _ => ?_)
      exact keepsUncached_pure _
    · refine keepsUncached_bind (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (liftCheckedViaRun state
          (x := EthCLSpecs.Gloas.currentEpochOf (pureState state) +
            EthCLSpecs.Gloas.Const.minSeedLookahead)) (fun _ => ?_)
      refine keepsUncached_bind
        (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
        (fun _ => ?_)
      refine keepsUncached_bind (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (liftCheckedViaRun state
          (x := EthCLSpecs.Gloas.computeEpochAtSlot slot -
            EthCLSpecs.Gloas.currentEpochOf (pureState state))) (fun diff => ?_)
      refine keepsUncached_bind (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (liftCheckedViaRun state (x := diff + 1)) (fun offset => ?_)
      refine keepsUncached_bind (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (liftCheckedViaRun state
          (x := offset * EthCLSpecs.Gloas.Const.slotsPerEpochC)) (fun scaled => ?_)
      -- `slotIdx` is the proved-total divisor-view remainder, a pure value with no
      -- bind of its own; the last checked bind is the index sum.
      refine keepsUncached_bind (T := BeaconState)
        (ε := EthCLLib.Spec.StateTransitionError)
        (liftCheckedViaRun state
          (x := scaled +
            (slot % EthCLSpecs.Gloas.Const.slotsPerEpochDiv))) (fun _ => ?_)
      exact keepsUncached_pure _
  · intro a s' s hrun
    rw [run_bind, run_throw, except_bind_error] at hrun
    exact absurd hrun (by simp)

/-- `getIndexedPayloadAttestation` keeps the flavour: the `getPtc` read, whose
own lemma carries the flavour, then a pure fold and the `sszOfArrayM` list
constructor. -/
theorem keepsUncached_getIndexedPayloadAttestation (state : BeaconState)
    (pa : PayloadAttestation) :
    KeepsUncached (getIndexedPayloadAttestation (StateTransition := GloasRun) (pureState state) pa) := by
  unfold getIndexedPayloadAttestation
  refine keepsUncached_bind (keepsUncached_getPtc state pa.data.slot) (fun ptc => ?_)
  refine keepsUncached_bind (keepsUncached_sszOfArrayM "attestingIndices" _) (fun _ => ?_)
  exact keepsUncached_pure _

/-- `processBlsToExecutionChange` keeps the flavour: the range assert, the
registry read, three pure validation gates, and one `modValidator` write through
the record update. -/
theorem keepsUncached_processBlsToExecutionChange
    (sbc : SignedBLSToExecutionChange) :
    KeepsUncached (processBlsToExecutionChange (StateTransition := GloasRun) sbc) := by
  unfold processBlsToExecutionChange
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_sszGetIdx _ _) (fun validator => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  refine keepsUncached_bind
    (keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _))
    (fun _ => ?_)
  apply keepsUncached_modify
  intro v
  exact ⟨_, by rfl⟩

set_option maxRecDepth 1000000 in
/-- `processPayloadAttestation` keeps the flavour: three pure gates, the
checked slot increment, and `getIndexedPayloadAttestation`, whose own lemma
carries the flavour. The `get` peels through `keepsUncachedFrom_get_bind`, so
the continuation starts on `pureState state` and the rebound callee lemma applies. -/
theorem keepsUncached_processPayloadAttestation (pa : PayloadAttestation) :
    KeepsUncached (processPayloadAttestation (StateTransition := GloasRun) pa) := by
  intro preState
  unfold processPayloadAttestation
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_bind ?g1 (fun _ midState₁ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  · -- The checked slot increment binds before its assert. The lemma's abstract
    -- `x` unifies with the goal's own elaborated body term.
    refine keepsUncachedFrom_bind ?add (fun attestedSlot midState₁b => ?_)
    · -- The literal stays a `Nat` in the body's `HAdd CLUint64 Nat` instance;
      -- spelling it at `Slot` would hand the unifier a different instance pair.
      exact keepsUncachedFrom_liftChecked (T := BeaconState)
        (ε := StateTransitionError) midState₁ (x := pa.data.slot + (1 : Nat))
    · -- The bind's continuation is the attested-slot assert itself, so the
      -- assert peels as the next bind's action.
      refine keepsUncachedFrom_bind
        (T := BeaconState)
        (keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
          (fun _ => keepsUncachedFrom_throw _ _))
        (fun _ midState₁c => ?_)
      · refine keepsUncachedFrom_bind ?gi (fun indexed midState₃ => ?_)
        · exact keepsUncached_iff_forall_from.mp (keepsUncached_getIndexedPayloadAttestation state pa) _
        · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)

/-- `sszGetIdx`'s in-range read is the identity action at the Gloas runner, the
same `rfl` fact the Fulu balances proofs use, so the body's bind on it
substitutes the element. -/
private theorem bind_liftErr_ok_gloas {α β : Type} (v : α) (k : α → GloasRun β) :
    bind (liftErr (Except.ok v : Except IndexError α)) k = k v :=
  rfl

/-- `increaseBalance`, at its Gloas copy, returns `pureState` of the written
value and leaves the threaded state uncached: the run reduces to the same match
the Fulu contract states. The claims here are about the box, so the
checked-chain value laws (`add_eq_ok`, `add_value`) do not reach: the matches on
`balance + d` need only the `Except` shape, and the add's value is never read. -/
theorem returnsUncached_increaseBalance (state : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    ReturnsUncached (increaseBalance (StateTransition := GloasRun) (pureState state) i d) := by
  intro preState b s h
  have hrun : (increaseBalance (StateTransition := GloasRun) (pureState state) i d).run
      (pureState preState)
      = (match state.balances.val[i.toPlainNat]? with
        | none => .error (.outOfBounds i.toPlainNat state.balances.size)
        | some balance =>
          match balance + d with
          | .error f => .error (StateTransitionError.ofArithFault f)
          | .ok sum => .ok (modBalance (pureState state) i (fun _ => sum), pureState preState)) := by
    unfold increaseBalance sszGetIdx
    rw [getAt_progressiveList_clUint64]
    simp only [view_uncachedBox]
    cases state.balances.val[i.toPlainNat]? with
    | none => simp; rfl
    | some balance =>
      -- The read succeeded, so the body's first bind discharges; the checked add
      -- rides the monad lift, whose fault arm is `ofArithFault`.
      have hlift : ∀ x : Checked Gwei, (liftM x : GloasRun Gwei)
          = MonadExcept.ofExcept (x.mapError StateTransitionError.ofArithFault) := by
        intro x
        cases x with
        | ok v => rfl
        | error e => rfl
      rw [bind_liftErr_ok_gloas, hlift]
      cases hc : balance + d with
      | error f => simp only [hc, Except.mapError]; rfl
      | ok sum => simp only [hc, Except.mapError]; rfl
  cases hu : state.balances.val[i.toPlainNat]? with
  | none => rw [hrun, hu] at h; simp at h
  | some balance =>
    rw [hrun, hu] at h
    dsimp only at h
    cases hc : balance + d with
    | error f => rw [hc] at h; simp at h
    | ok sum =>
      rw [hc] at h
      injection h with h1
      injection h1 with h1a h1b
      subst h1a
      subst h1b
      exact ⟨⟨_, rfl⟩, rfl⟩

/-- `decreaseBalance`, at its Gloas copy: the same shape, with the saturating
difference written. -/
theorem returnsUncached_decreaseBalance (state : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    ReturnsUncached (decreaseBalance (StateTransition := GloasRun) (pureState state) i d) := by
  intro preState b s h
  have hrun : (decreaseBalance (StateTransition := GloasRun) (pureState state) i d).run
      (pureState preState)
      = (match state.balances.val[i.toPlainNat]? with
        | none => .error (.outOfBounds i.toPlainNat state.balances.size)
        | some balance =>
          .ok (modBalance (pureState state) i
            (fun _ => balance.saturatingSub d), pureState preState)) := by
    unfold decreaseBalance sszGetIdx
    rw [getAt_progressiveList_clUint64]
    simp only [view_uncachedBox]
    cases state.balances.val[i.toPlainNat]? with
    | none => simp; rfl
    | some balance =>
      simp only [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl
  cases hu : state.balances.val[i.toPlainNat]? with
  | none => rw [hrun, hu] at h; simp at h
  | some balance =>
    rw [hrun, hu] at h
    dsimp only at h
    injection h with h1
    injection h1 with h1a h1b
    subst h1a
    subst h1b
    exact ⟨⟨_, rfl⟩, rfl⟩

set_option maxHeartbeats 4000000 in
/-- `slashValidator` keeps the flavour: the reads and the exit write keep it as
the spike lemmas do, and the threaded states, the local write chain, the checked
`Gwei` binds, and the two balance returns stay uncached. The closing EIP-7732
loop over the payment window is a pure `modifyState` writer, and
`pureState_forIn_range_id` carries the flavour through its steps. -/
theorem keepsUncached_slashValidator (i : ValidatorIndex) :
    KeepsUncached (slashValidator (StateTransition := GloasRun) i) := by
  intro preState
  unfold slashValidator
  -- The pure `let epoch := …` at the head of the body leaves a redex around the
  -- rest, which stalls the `liftM`-leaf unifications below; clean it once.
  simp only []
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun epochState midState₁ => ?_)
  refine keepsUncachedFrom_bind
    ((keepsUncached_iff_forall_from.mp (keepsUncached_initiateValidatorExit i)) midState₁)
    (fun _ midState₂ => ?_)
  refine keepsUncachedFrom_get_bind (fun state => ?_)
  refine keepsUncachedFrom_bind
    (keepsUncachedFrom_liftErr (T := BeaconState) (ε := EthCLLib.Spec.StateTransitionError)
      (ε' := EthCLLib.Spec.IndexError) (α := Validator) state _)
    (fun validator midState₃ => ?_)
  -- The checked `Epoch` binds the migration added (the ring index and the
  -- withdrawability extension) are `liftM`s of pure values, as are the checked
  -- `Gwei` binds (the slashings ring add, the slashing penalty, and the
  -- whistleblower chain): each passes the box through unchanged, by
  -- `keepsUncachedFrom_liftChecked`.
  refine keepsUncachedFrom_bind ?si (fun _ midState₃a => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₃ _
  refine keepsUncachedFrom_bind ?ex (fun _ midState₃b => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₃a _
  refine keepsUncachedFrom_bind ?ring (fun _ midState₄ => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₃b _
  refine keepsUncachedFrom_bind ?pen (fun _ midState₅ => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₄ _
  refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ i _)
    (fun afterDecrease midState₆ => ?_)
  refine keepsUncachedFrom_bind (v := midState₆) (keepsUncachedFrom_set midState₆ afterDecrease)
    (fun _ midState₇ => ?_)
  refine keepsUncachedFrom_get_bind (fun state' => ?_)
  refine keepsUncachedFrom_bind ?wr (fun whistleblowerReward midState₇a => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) state' _
  -- The numerator chain is the one `liftM` whose leaf unification stalls the
  -- unifier, so state the flavour by hand over the run equations.
  have hpr : KeepsUncachedFrom midState₇a
      (liftM (whistleblowerReward * Gloas.Const.proposerWeight /
        Gloas.Const.weightDenominator) : GloasRun Gwei) := by
    intro a s h
    cases hx : (whistleblowerReward * Gloas.Const.proposerWeight /
        Gloas.Const.weightDenominator) with
    | ok w =>
      rw [hx] at h; rw [run_liftChecked_ok] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hs⟩ := h
      subst hs
      rfl
    | error e =>
      rw [hx] at h; rw [run_liftChecked_error] at h
      exact absurd h (by simp)
  refine keepsUncachedFrom_bind hpr (fun proposerReward midState₇b => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterProposerReward midState₈ => ?_)
  have hrem : KeepsUncachedFrom midState₈
      (liftM (whistleblowerReward - proposerReward) : GloasRun Gwei) := by
    intro a s h
    cases hx : (whistleblowerReward - proposerReward) with
    | ok w =>
      rw [hx] at h; rw [run_liftChecked_ok] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hs⟩ := h
      subst hs
      rfl
    | error e =>
      rw [hx] at h; rw [run_liftChecked_error] at h
      exact absurd h (by simp)
  refine keepsUncachedFrom_bind hrem (fun _ midState₈a => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterWhistleblowerReward midState₉ => ?_)
  refine keepsUncachedFrom_bind (keepsUncachedFrom_set midState₉ afterWhistleblowerReward)
    (fun _ midState₁₀ => ?_)
  -- The payment loop: each step either rebuilds the record (an uncached box) or passes
  -- the box through, so the whole writer maps `pureState` to `pureState`.
  refine keepsUncached_iff_forall_from.mp (keepsUncached_modify _ (fun v => ?_)) midState₁₀
  -- `Id.run do … return state` is the loop followed by `pure`, which `bind_pure` drops.
  simp only [bind_pure]
  exact pureState_forIn_range_id _ (fun paymentIndex v => by
    try dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨v, rfl⟩) _ v

/-! ## The read helpers the two loop handlers call

`getBlockRootAtSlot` and its callers take the state as an explicit argument, so
their lemmas state the claim on `pureState state`, the same form `keepsUncached_getPtc`
takes. Their bodies gate and read only: the monadic state passes through
unchanged. -/

set_option maxRecDepth 400000 in
/-- `getBlockRootAtSlot` gates on two asserts and the recency bound's checked add;
the monadic state passes through unchanged. -/
theorem keepsUncached_getBlockRootAtSlot (state : BeaconState) (s : EthCLSpecs.Gloas.Slot) :
    KeepsUncached (getBlockRootAtSlot (StateTransition := GloasRun) (pureState state) s) := by
  unfold getBlockRootAtSlot
  refine keepsUncached_bind ?g1 (fun _ => ?_)
  · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
  · -- The recency bound is the pyspec's checked `Slot` add, bound before its assert.
    refine keepsUncached_bind
      (T := BeaconState) (ε := EthCLLib.Spec.StateTransitionError)
      (liftCheckedViaRun state
        (x := s + EthCLSpecs.Gloas.Const.slotsPerHistoricalRootC)) (fun bound => ?_)
    · refine keepsUncached_bind ?g2 (fun _ => ?_)
      · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
      · exact keepsUncached_pure _

theorem keepsUncached_getBlockRoot (state : BeaconState) (epoch : EthCLSpecs.Gloas.Epoch) :
    KeepsUncached (getBlockRoot (StateTransition := GloasRun) (pureState state) epoch) := by
  unfold getBlockRoot
  -- The start slot is the checked `computeStartSlotAtEpoch` product, a `liftM`
  -- of a pure value that passes the box through.
  refine keepsUncached_bind (keepsUncached_liftChecked _) (fun startSlot => ?_)
  exact keepsUncached_getBlockRootAtSlot state startSlot

theorem keepsUncached_isAttestationSameSlot (state : BeaconState) (data : EthCLSpecs.Gloas.AttestationData) :
    KeepsUncached (isAttestationSameSlot (StateTransition := GloasRun) (pureState state) data) := by
  unfold isAttestationSameSlot
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind ?sr (fun _ => ?_)
  · exact keepsUncached_getBlockRootAtSlot state _
  · refine keepsUncached_bind ?ps (fun _ => ?_)
    · exact keepsUncached_liftChecked _
    · refine keepsUncached_bind ?pr (fun _ => ?_)
      · exact keepsUncached_getBlockRootAtSlot state _
      · exact keepsUncached_pure _

theorem keepsUncached_getAttestationParticipationFlagIndices (state : BeaconState) (data : EthCLSpecs.Gloas.AttestationData)
    (inclusionDelay : Slot) (parentSlot : Slot) :
    KeepsUncached (getAttestationParticipationFlagIndices
      (StateTransition := GloasRun) (pureState state) data inclusionDelay parentSlot) := by
  unfold getAttestationParticipationFlagIndices
  refine keepsUncached_bind ?br (fun _ => ?_)
  · exact keepsUncached_getBlockRoot state _
  · refine keepsUncached_bind ?ss (fun _ => ?_)
    · exact keepsUncached_isAttestationSameSlot state _
    · refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
      refine keepsUncached_bind ?hr (fun _ => ?_)
      · exact keepsUncached_getBlockRootAtSlot state _
      · repeat' first
          | refine keepsUncached_ite (fun _ => ?_) (fun _ => ?_)
          | refine keepsUncached_bind (keepsUncached_pure _) (fun _a => ?_)
          | exact keepsUncached_pure _



/-! ## `processProposerSlashing` and the two loop handlers

The three remaining handlers peel per statement. The peel steps name their own
closure lemma, so the unifier never searches: a failed leaf trial whnfs the goal
action, and past the first gate that walk reaches the `sszUpdate` expansions of
the cached-box branch, which is where the naive tactic pass stalls. -/

theorem keepsUncached_processProposerSlashing (ps : ProposerSlashing) :
    KeepsUncached (processProposerSlashing (StateTransition := GloasRun) ps) := by
  intro preState
  unfold processProposerSlashing
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun box midState₁ => ?_)
  refine keepsUncachedFrom_bind ?g1 (fun _ midState₂ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  · refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
    · refine keepsUncachedFrom_bind ?g3 (fun _ midState₄ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
      · refine keepsUncachedFrom_bind ?g4 (fun _ midState₅ => ?_)
        · -- The proposer read is the raising registry read.
          exact keepsUncached_iff_forall_from.mp (keepsUncached_sszGetIdx _ _) _
        · refine keepsUncachedFrom_bind ?g5 (fun _ midState₆ => ?_)
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
          · refine keepsUncachedFrom_bind ?g6 (fun _ midState₇ => ?_)
            · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
            · refine keepsUncachedFrom_bind ?g7 (fun _ midState₈ => ?_)
              · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
              · exact keepsUncached_iff_forall_from.mp
                  (keepsUncached_slashValidator (i := ps.signedHeader1.message.proposerIndex)) _

theorem keepsUncached_processAttesterSlashing (asl : AttesterSlashing) :
    KeepsUncached (processAttesterSlashing (StateTransition := GloasRun) asl) := by
  intro preState
  unfold processAttesterSlashing
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun state midState₁ => ?_)
  refine keepsUncachedFrom_bind ?g1 (fun _ midState₂ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  · refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
    · refine keepsUncachedFrom_bind ?g3 (fun _ midState₄ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
      · refine keepsUncachedFrom_bind ?loop (fun r midState₅ => ?_)
        · refine keepsUncachedFrom_forIn_array_of_keeps _ ?hf _ _
          · intro x b midState₆
            refine keepsUncachedFrom_bind (keepsUncachedFrom_get midState₆) (fun state midState₇ => ?_)
            -- The registry read raises past the end and never writes.
            refine keepsUncachedFrom_bind
              (keepsUncached_iff_forall_from.mp (keepsUncached_sszGetIdx _ _) _)
              (fun validator midState₇b => ?_)
            refine keepsUncachedFrom_ite (fun _ => ?ht) (fun _ => ?he)
            · refine keepsUncachedFrom_bind ?sv (fun _ midState₈ => ?_)
              · exact keepsUncached_iff_forall_from.mp (keepsUncached_slashValidator _) _
              · exact keepsUncachedFrom_pure _ _
            · exact keepsUncachedFrom_pure _ _
        · refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)

/-- The current-field record write of an uncached box is again uncached. `j`
is the validator (record) index; the written value is the checked-8 `addFlag`
result the walk bound before the write. -/
private theorem keepsUncached_writeParticipationCurr (stC : BeaconState) (j : Nat)
    (fl' : EthCLSpecs.Gloas.ParticipationFlags) :
    ∃ w : BeaconState,
      (sszUpdate (pureState stC) with currentEpochParticipation[j]! := fl') = pureState w :=
  ⟨_, rfl⟩

/-- The previous-field record write of an uncached box is again uncached. `j`
is the validator (record) index; the written value is the checked-8 `addFlag`
result the walk bound before the write. -/
private theorem keepsUncached_writeParticipationPrev (stC : BeaconState) (j : Nat)
    (fl' : EthCLSpecs.Gloas.ParticipationFlags) :
    ∃ w : BeaconState,
      (sszUpdate (pureState stC) with previousEpochParticipation[j]! := fl') = pureState w :=
  ⟨_, rfl⟩

/-- One concrete field choice of `processAttestation`'s per-validator walk, the
current-epoch one. The elaborator hoists the `current_epoch_target` ite around
the whole body, the inner flag read around the inner-loop body, and reduces
every same-condition ite at once, so `keepsUncached_processAttestation` splits
the body into the two (field) branches; this lemma is the run-level proof of
one branch. The flag test and the flag write are the checked-8 `hasFlag` /
`addFlag` binds, restated through the mask laws (`SPEC_ARITHMETIC.md` §5.1):
each raise discards the walk's writes, and each success threads the box. -/
@[box_generic "the lemma is box infrastructure: it says the walk's successful runs
thread the uncached box, the property KeepsUncached is about, and its statement
runs the action at pureState v the same way the closure lemmas do"]
private theorem keepsUncached_attLoopCurr (state : BeaconState) (vi : ValidatorIndex)
    (att : Attestation) (flagIndices : Array EthCLLib.Spec.CLUint64) (sameSlot : Bool) :
    ∀ (b : EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei) (v : BeaconState)
        (r : ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei))
        (s : SSZ.Box HasherTag.H BeaconState),
      (∃ st : BeaconState, b.fst = pureState st) →
      (do
        let flags0 ← sszGetIdx b.fst.view.currentEpochParticipation vi
        let __s ←
          forIn [:3] (b.fst, b.snd.fst, false) fun flagIndex __s =>
            if (!flagIndices.any fun x => x.toPlainNat == flagIndex) = true then
              pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd))
            else do
            let flag ← sszGetIdx __s.fst.view.currentEpochParticipation vi
            let __do_lift ← liftM (EthCLLib.Spec.CLUint8.hasFlag flag flagIndex)
            if (!__do_lift) = true then do
              let flag' ← liftM (EthCLLib.Spec.CLUint8.addFlag flag flagIndex)
              let base ← liftErr (EthCLSpecs.Gloas.getBaseReward (pureState state) vi)
              let weighted ← liftM (base * Gloas.Const.participationFlagWeights[flagIndex]!)
              let __do_lift ← liftM (__s.snd.fst + weighted)
              pure
                (ForInStep.yield
                  ((sszUpdate __s.fst with currentEpochParticipation[vi.toPlainNat]! := flag'),
                    __do_lift, true))
            else pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd))
        if
            (__s.snd.snd && flags0 == 0 && sameSlot &&
                decide
                  ((EthCLLib.Spec.vget (pureState state).view.builderPendingPayments
                      (builderPaymentIndex att.data.slot
                        (att.data.target.epoch ==
                          EthCLSpecs.Gloas.currentEpochOf (pureState state)))).withdrawal.amount >
                    0)) =
              true then
          do
            let attester ← sszGetIdx (pureState state).view.validators vi
            let __do_lift ← liftM (b.snd.snd + attester.effectiveBalance)
            pure (ForInStep.yield (__s.fst, __s.snd.fst, __do_lift))
        else pure (ForInStep.yield (__s.fst, __s.snd.fst, b.snd.snd)) :
          GloasRun (ForInStep
            (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei))).run
            (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ (∃ st : BeaconState, r.value.1 = pureState st) := by
  intro b v r s hb hrun
  -- Peel the flags0 read: it never writes.
  refine run_bind_inv (T := BeaconState)
    (α := EthCLSpecs.Gloas.ParticipationFlags)
    (γ := ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei))
    (P := fun _ => True)
    (Q := fun stp => ∃ st : BeaconState, stp.value.1 = pureState st)
    (hx := fun r0 s0 h0 => ⟨keepsUncached_sszGetIdx _ _ v r0 s0 h0, trivial⟩)
    (hk := fun flags0 sA _ a s h1 => ?_) v r s hrun
  · -- The inner `[:3]` loop, then the payment gate.
    refine keepsUncachedFrom_forIn_range_bind_run_inv (T := BeaconState) (α := Nat)
      (P := fun acc => ∃ st : BeaconState, acc.1 = pureState st)
      (Q := fun stp => ∃ st : BeaconState, stp.value.1 = pureState st)
      _ _ ?hf ?hk 3 (b.fst, b.2.1, false) sA hb a s h1
    · -- inner hf: the flag walk
      rename_i f k
      intro flagIndex acc3 v2 r2 s2 hb2 hrun2
      -- The `continue` for a flag the attestation does not earn: no read, no write.
      split at hrun2
      · rw [run_pure] at hrun2
        injection hrun2 with hp
        injection hp with hpa hpb
        subst hpb
        subst hpa
        exact ⟨rfl, hb2⟩
      refine run_bind_inv (T := BeaconState)
        (α := EthCLSpecs.Gloas.ParticipationFlags)
        (γ := ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × Bool))
        (P := fun _ => True)
        (Q := fun stp => ∃ st : BeaconState, stp.value.1 = pureState st)
        (hx := fun r0 s0 h0 => ⟨keepsUncached_sszGetIdx _ _ v2 r0 s0 h0, trivial⟩)
        (hk := fun flag sC _ a s h3 => ?_) v2 r2 s2 hrun2
      · -- The `has_flag` mask test binds after the read: its raise discards the
        -- walk, its success splits on the `not` gate.
        rw [run_bind] at h3
        cases hh : (EthCLLib.Spec.CLUint8.hasFlag flag flagIndex) with
        | error ef =>
          rw [hh, run_liftChecked_error] at h3
          rw [except_bind_error] at h3
          simp at h3
        | ok hb' =>
          rw [hh, run_liftChecked_ok _ _] at h3
          rw [except_bind_ok] at h3
          split at h3
          · -- the flag-set branch: the `add_flag` mask binds before the write,
            -- then base reward, weighted reward, the checked accumulator add,
            -- and the field write
            rw [run_bind] at h3
            cases hf' : (EthCLLib.Spec.CLUint8.addFlag flag flagIndex) with
            | error ef =>
              rw [hf', run_liftChecked_error] at h3
              rw [except_bind_error] at h3
              simp at h3
            | ok flag' =>
              rw [hf', run_liftChecked_ok _ _] at h3
              rw [except_bind_ok] at h3
              rw [run_bind] at h3
              cases hm : (EthCLSpecs.Gloas.getBaseReward (pureState state) vi).mapError
                  (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
              | error e =>
                rw [run_liftErr_of_error _ _ hm, except_bind_error] at h3
                simp at h3
              | ok rw' =>
                rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at h3
                rw [run_bind] at h3
                cases hw : ((rw' * Gloas.Const.participationFlagWeights[flagIndex]! : Checked Gwei)) with
                | ok weighted =>
                  rw [hw] at h3
                  rw [run_liftChecked_ok _ _] at h3
                  rw [except_bind_ok] at h3
                  rw [run_bind] at h3
                  cases hw2 : ((acc3.2.1 + weighted : Checked Gwei)) with
                  | ok total =>
                    rw [hw2] at h3
                    rw [run_liftChecked_ok _ _] at h3
                    rw [except_bind_ok, run_pure] at h3
                    injection h3 with h3p
                    injection h3p with h3a h3b
                    subst h3b
                    subst h3a
                    refine ⟨rfl, ?_⟩
                    obtain ⟨stC, hstC⟩ := hb2
                    simp only [hstC]
                    exact keepsUncached_writeParticipationCurr stC vi.toPlainNat flag'
                  | error e =>
                    rw [hw2] at h3
                    rw [run_liftChecked_error] at h3
                    rw [except_bind_error] at h3
                    simp at h3
                | error e =>
                  rw [hw] at h3
                  rw [run_liftChecked_error] at h3
                  rw [except_bind_error] at h3
                  simp at h3
          · rw [run_pure] at h3
            injection h3 with h3p
            injection h3p with h3a h3b
            subst h3b
            subst h3a
            exact ⟨rfl, hb2⟩
    · -- the payment gate
      intro acc3 sB hb2 a s h4
      split at h4
      · rw [run_bind] at h4
        cases hq : (EthCLLib.Spec.getAt (pureState state).view.validators vi :
            Except IndexError EthCLSpecs.Gloas.Validator) with
        | ok yv =>
          rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at h4
          rw [run_bind] at h4
          cases hw : ((b.2.2 + yv.effectiveBalance : Checked Gwei)) with
          | ok wsum =>
            rw [hw] at h4
            rw [run_liftChecked_ok _ _] at h4
            rw [except_bind_ok, run_pure] at h4
            injection h4 with h4p
            injection h4p with h4a h4b
            subst h4b
            subst h4a
            exact ⟨rfl, hb2⟩
          | error e =>
            rw [hw] at h4
            rw [run_liftChecked_error] at h4
            rw [except_bind_error] at h4
            simp at h4
        | error ie =>
          rw [run_sszGetIdx_none _ _ _ _ hq, except_bind_error] at h4
          simp at h4
      · rw [run_pure] at h4
        injection h4 with h4p
        injection h4p with h4a h4b
        subst h4b
        subst h4a
        exact ⟨rfl, hb2⟩

/-- The previous-epoch field choice of the same walk; the proof is the
current-field one with the field renamed, including the checked-8 `hasFlag` /
`addFlag` binds. -/
@[box_generic "the lemma is box infrastructure: it says the walk's successful runs
thread the uncached box, the property KeepsUncached is about, and its statement
runs the action at pureState v the same way the closure lemmas do"]
private theorem keepsUncached_attLoopPrev (state : BeaconState) (vi : ValidatorIndex)
    (att : Attestation) (flagIndices : Array EthCLLib.Spec.CLUint64) (sameSlot : Bool) :
    ∀ (b : EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei) (v : BeaconState)
        (r : ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei))
        (s : SSZ.Box HasherTag.H BeaconState),
      (∃ st : BeaconState, b.fst = pureState st) →
      (do
        let flags0 ← sszGetIdx b.fst.view.previousEpochParticipation vi
        let __s ←
          forIn [:3] (b.fst, b.snd.fst, false) fun flagIndex __s =>
            if (!flagIndices.any fun x => x.toPlainNat == flagIndex) = true then
              pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd))
            else do
            let flag ← sszGetIdx __s.fst.view.previousEpochParticipation vi
            let __do_lift ← liftM (EthCLLib.Spec.CLUint8.hasFlag flag flagIndex)
            if (!__do_lift) = true then do
              let flag' ← liftM (EthCLLib.Spec.CLUint8.addFlag flag flagIndex)
              let base ← liftErr (EthCLSpecs.Gloas.getBaseReward (pureState state) vi)
              let weighted ← liftM (base * Gloas.Const.participationFlagWeights[flagIndex]!)
              let __do_lift ← liftM (__s.snd.fst + weighted)
              pure
                (ForInStep.yield
                  ((sszUpdate __s.fst with previousEpochParticipation[vi.toPlainNat]! := flag'),
                    __do_lift, true))
            else pure (ForInStep.yield (__s.fst, __s.snd.fst, __s.snd.snd))
        if
            (__s.snd.snd && flags0 == 0 && sameSlot &&
                decide
                  ((EthCLLib.Spec.vget (pureState state).view.builderPendingPayments
                      (builderPaymentIndex att.data.slot
                        (att.data.target.epoch ==
                          EthCLSpecs.Gloas.currentEpochOf (pureState state)))).withdrawal.amount >
                    0)) =
              true then
          do
            let attester ← sszGetIdx (pureState state).view.validators vi
            let __do_lift ← liftM (b.snd.snd + attester.effectiveBalance)
            pure (ForInStep.yield (__s.fst, __s.snd.fst, __do_lift))
        else pure (ForInStep.yield (__s.fst, __s.snd.fst, b.snd.snd)) :
          GloasRun (ForInStep
            (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei))).run
            (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ (∃ st : BeaconState, r.value.1 = pureState st) := by
  intro b v r s hb hrun
  -- Peel the flags0 read: it never writes.
  refine run_bind_inv (T := BeaconState)
    (α := EthCLSpecs.Gloas.ParticipationFlags)
    (γ := ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei))
    (P := fun _ => True)
    (Q := fun stp => ∃ st : BeaconState, stp.value.1 = pureState st)
    (hx := fun r0 s0 h0 => ⟨keepsUncached_sszGetIdx _ _ v r0 s0 h0, trivial⟩)
    (hk := fun flags0 sA _ a s h1 => ?_) v r s hrun
  · -- The inner `[:3]` loop, then the payment gate.
    refine keepsUncachedFrom_forIn_range_bind_run_inv (T := BeaconState) (α := Nat)
      (P := fun acc => ∃ st : BeaconState, acc.1 = pureState st)
      (Q := fun stp => ∃ st : BeaconState, stp.value.1 = pureState st)
      _ _ ?hf ?hk 3 (b.fst, b.2.1, false) sA hb a s h1
    · -- inner hf: the flag walk
      rename_i f k
      intro flagIndex acc3 v2 r2 s2 hb2 hrun2
      -- The `continue` for a flag the attestation does not earn: no read, no write.
      split at hrun2
      · rw [run_pure] at hrun2
        injection hrun2 with hp
        injection hp with hpa hpb
        subst hpb
        subst hpa
        exact ⟨rfl, hb2⟩
      refine run_bind_inv (T := BeaconState)
        (α := EthCLSpecs.Gloas.ParticipationFlags)
        (γ := ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × Bool))
        (P := fun _ => True)
        (Q := fun stp => ∃ st : BeaconState, stp.value.1 = pureState st)
        (hx := fun r0 s0 h0 => ⟨keepsUncached_sszGetIdx _ _ v2 r0 s0 h0, trivial⟩)
        (hk := fun flag sC _ a s h3 => ?_) v2 r2 s2 hrun2
      · -- The `has_flag` mask test binds after the read: its raise discards the
        -- walk, its success splits on the `not` gate.
        rw [run_bind] at h3
        cases hh : (EthCLLib.Spec.CLUint8.hasFlag flag flagIndex) with
        | error ef =>
          rw [hh, run_liftChecked_error] at h3
          rw [except_bind_error] at h3
          simp at h3
        | ok hb' =>
          rw [hh, run_liftChecked_ok _ _] at h3
          rw [except_bind_ok] at h3
          split at h3
          · -- the flag-set branch: the `add_flag` mask binds before the write,
            -- then base reward, weighted reward, the checked accumulator add,
            -- and the field write
            rw [run_bind] at h3
            cases hf' : (EthCLLib.Spec.CLUint8.addFlag flag flagIndex) with
            | error ef =>
              rw [hf', run_liftChecked_error] at h3
              rw [except_bind_error] at h3
              simp at h3
            | ok flag' =>
              rw [hf', run_liftChecked_ok _ _] at h3
              rw [except_bind_ok] at h3
              rw [run_bind] at h3
              cases hm : (EthCLSpecs.Gloas.getBaseReward (pureState state) vi).mapError
                  (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
              | error e =>
                rw [run_liftErr_of_error _ _ hm, except_bind_error] at h3
                simp at h3
              | ok rw' =>
                rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at h3
                rw [run_bind] at h3
                cases hw : ((rw' * Gloas.Const.participationFlagWeights[flagIndex]! : Checked Gwei)) with
                | ok weighted =>
                  rw [hw] at h3
                  rw [run_liftChecked_ok _ _] at h3
                  rw [except_bind_ok] at h3
                  rw [run_bind] at h3
                  cases hw2 : ((acc3.2.1 + weighted : Checked Gwei)) with
                  | ok total =>
                    rw [hw2] at h3
                    rw [run_liftChecked_ok _ _] at h3
                    rw [except_bind_ok, run_pure] at h3
                    injection h3 with h3p
                    injection h3p with h3a h3b
                    subst h3b
                    subst h3a
                    refine ⟨rfl, ?_⟩
                    obtain ⟨stC, hstC⟩ := hb2
                    simp only [hstC]
                    exact keepsUncached_writeParticipationPrev stC vi.toPlainNat flag'
                  | error e =>
                    rw [hw2] at h3
                    rw [run_liftChecked_error] at h3
                    rw [except_bind_error] at h3
                    simp at h3
                | error e =>
                  rw [hw] at h3
                  rw [run_liftChecked_error] at h3
                  rw [except_bind_error] at h3
                  simp at h3
          · rw [run_pure] at h3
            injection h3 with h3p
            injection h3p with h3a h3b
            subst h3b
            subst h3a
            exact ⟨rfl, hb2⟩
    · -- the payment gate
      intro acc3 sB hb2 a s h4
      split at h4
      · rw [run_bind] at h4
        cases hq : (EthCLLib.Spec.getAt (pureState state).view.validators vi :
            Except IndexError EthCLSpecs.Gloas.Validator) with
        | ok yv =>
          rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at h4
          rw [run_bind] at h4
          cases hw : ((b.2.2 + yv.effectiveBalance : Checked Gwei)) with
          | ok wsum =>
            rw [hw] at h4
            rw [run_liftChecked_ok _ _] at h4
            rw [except_bind_ok, run_pure] at h4
            injection h4 with h4p
            injection h4p with h4a h4b
            subst h4b
            subst h4a
            exact ⟨rfl, hb2⟩
          | error e =>
            rw [hw] at h4
            rw [run_liftChecked_error] at h4
            rw [except_bind_error] at h4
            simp at h4
        | error ie =>
          rw [run_sszGetIdx_none _ _ _ _ hq, except_bind_error] at h4
          simp at h4
      · rw [run_pure] at h4
        injection h4 with h4p
        injection h4p with h4a h4b
        subst h4b
        subst h4a
        exact ⟨rfl, hb2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem keepsUncached_processAttestation (att : EthCLSpecs.Gloas.Attestation) (parentSlot : Slot) :
    KeepsUncached (EthCLSpecs.Gloas.processAttestation (StateTransition := GloasRun) att parentSlot) := by
  intro preState
  unfold EthCLSpecs.Gloas.processAttestation
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_bind ?gA (fun _ midState₁ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  · refine keepsUncachedFrom_bind ?gB (fun _ midState₂ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
    · -- The inclusion slot is the pyspec's checked `data.slot + MIN_ATTESTATION_INCLUSION_DELAY`,
      -- bound between the epoch assert and its own assert. The lemma's abstract
      -- `x` unifies with the goal's own elaborated body term.
      refine keepsUncachedFrom_bind
        (T := BeaconState)
        (keepsUncachedFrom_liftChecked midState₂ _) (fun inclusionSlot midState₂b => ?_)
      · -- The bind's continuation is the inclusion-slot assert itself, so the
        -- assert peels as the next bind's action.
        refine keepsUncachedFrom_bind
          (T := BeaconState)
          (keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _))
          (fun _ midState₂c => ?_)
        · refine keepsUncachedFrom_bind ?gC (fun _ midState₄ => ?_)
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
          · simp only []
            -- The coverage read is `liftErr`-shaped: the fault propagates and the
            -- success pair passes the box through.
            refine keepsUncachedFrom_bind (T := BeaconState)
              (keepsUncachedFrom_liftErr midState₄ _) (fun _ midState₆ => ?_)
            refine keepsUncachedFrom_bind (T := BeaconState) ?gF (fun _ midState₇ => ?_)
            · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                (fun _ => keepsUncachedFrom_throw _ _)
            · refine keepsUncachedFrom_bind (T := BeaconState) ?gG (fun _ midState₇b => ?_)
              · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                  (fun _ => keepsUncachedFrom_throw _ _)
              · -- The inclusion delay is the pyspec's checked `state.slot - data.slot`,
                -- bound at the argument position the flag-indices call reads it.
                refine keepsUncachedFrom_bind (T := BeaconState) ?gid
                  (fun inclusionDelay midState₇c => ?_)
                · exact keepsUncachedFrom_liftChecked midState₇b _
                · refine keepsUncachedFrom_bind (T := BeaconState) ?gf
                    (fun flagIndices midState₈ => ?_)
                  · exact keepsUncached_iff_forall_from.mp
                      (keepsUncached_getAttestationParticipationFlagIndices state att.data
                        inclusionDelay parentSlot) _
                  · -- The participation-flag `match` peels into its `some` branch and a
                    -- `throw` continuation that never runs.
                    split
                    · refine keepsUncachedFrom_bind (keepsUncachedFrom_pure _ _)
                        (fun _ midState₉ => ?_)
                      refine keepsUncachedFrom_bind ?li (fun idxs midState₁₀ => ?_)
                      · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₉)
                          (ε := EthCLLib.Spec.StateTransitionError)
                          (ε' := EthCLLib.Spec.StateTransitionError)
                          (α := Array EthCLSpecs.Gloas.ValidatorIndex) _
                      · -- The attesting-index list is built purely (a progressive list wraps
                        -- the sorted array), so the next effect is the validity assert.
                        refine keepsUncachedFrom_bind (T := BeaconState)
                          (keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                            (fun _ => keepsUncachedFrom_throw _ _))
                          (fun _ midState₁₁ => ?_)
                        · refine keepsUncachedFrom_bind ?ssL (fun sameSlot midState₁₂ => ?_)
                          · exact keepsUncached_iff_forall_from.mp
                              (keepsUncached_isAttestationSameSlot state att.data) _
                          · refine keepsUncachedFrom_bind ?li2 (fun idxs2 midState₁₃ => ?_)
                            · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₁₂)
                                (ε := EthCLLib.Spec.StateTransitionError)
                                (ε' := EthCLLib.Spec.StateTransitionError)
                                (α := Array EthCLSpecs.Gloas.ValidatorIndex) _
                            · -- ===== the two nested flag/reward loops, then the tail =====
                              apply keepsUncachedFrom_forIn_array_bind_P (T := BeaconState)
                                (P := fun (acc : EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei) =>
                                  ∃ accState : BeaconState, Prod.fst acc = pureState accState)
                              · -- **hf**: the per-validator body. The elaborator hoists the
                                -- `current_epoch_target` ite around the whole body, the
                                -- inner flag read around the inner-loop body, and the write
                                -- around its two record updates; one `split` reduces all
                                -- three to the concrete field, and
                                -- `keepsUncached_attLoopBranch` covers the walk. The flag
                                -- indices term is inaccessible after the `split`, so the
                                -- applications hand it to unification.
                                intro vi b v r s hb hrun
                                split at hrun
                                · exact keepsUncached_attLoopCurr state vi att _ sameSlot
                                    b v r s hb hrun
                                · exact keepsUncached_attLoopPrev state vi att _ sameSlot
                                    b v r s hb hrun
                              · -- **hk**: the proposer-payment tail
                                intro b w' hbp
                                obtain ⟨saS, hsa⟩ := hbp
                                rw [hsa]
                                -- The denominator binds first: every operand is a
                                -- checked `Uint64` constant at the pin, so the chain
                                -- is checked arithmetic.
                                refine keepsUncachedFrom_bind (T := BeaconState)
                                  (keepsUncachedFrom_liftChecked w' _)
                                  (fun proposerDenom w'' => ?_)
                                refine keepsUncachedFrom_bind (T := BeaconState)
                                  (keepsUncachedFrom_liftChecked w'' _)
                                  (fun proposerReward w''' => ?_)
                                refine returnsUncachedFrom_bind (T := BeaconState)
                                  (returnsUncached_increaseBalance saS
                                    (EthCLSpecs.Gloas.getBeaconProposerIndex (pureState saS))
                                    proposerReward) (fun w w'' => ?_)
                                intro a s h
                                -- `set` always succeeds with the box it was handed, and the
                                -- `sszUpdate` match on `pureState w` reduces to the uncached
                                -- record update, which is `pureState` of its own view.
                                have hset : ∀ (B sb : SSZ.Box HasherTag.H BeaconState),
                                    (set (B) : StateT (SSZ.Box HasherTag.H BeaconState)
                                      (Except EthCLLib.Spec.StateTransitionError) PUnit).run sb
                                      = .ok ((), B) := fun B sb => rfl
                                rw [hset] at h
                                injection h with hp
                                injection hp with h1 h2
                                subst h2
                                rfl
                              · -- **hinit**: the loop starts on `state` itself.
                                exact ⟨state, rfl⟩
                    · exact keepsUncachedFrom_throw_bind _ _

end

end EthCLSpecs.Proofs.Gloas
