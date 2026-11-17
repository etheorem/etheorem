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
  keepsUncached_liftErr keepsUncached_dite keepsUncached_forIn_range
  keepsUncached_ite keepsUncachedFrom_ite keepsUncachedFrom_pure keepsUncachedFrom_throw
  keepsUncachedFrom_liftErr keepsUncachedFrom_sszOfArrayM keepsUncachedFrom_dite
  keepsUncachedFrom_set keepsUncachedFrom_get
  keepsUncachedFrom_get_bind keepsUncachedFrom_throw_bind keepsUncachedFrom_forIn_array_of_keeps
  keepsUncachedFrom_forIn_array_bind_P keepsUncachedFrom_forIn_range_bind_run_inv
  returnsUncached_bind returnsUncachedFrom_bind keepsUncached_iff_forall_from
  keepsUncachedFrom_forIn_array_inv
  run_bind run_pure except_bind_ok except_bind_error
  run_ofExcept_ok run_ofExcept_error run_liftErr_of_ok run_liftErr_of_error
  run_sszGetIdx_some run_sszGetIdx_none keepsUncached_sszGetIdx run_bind_inv ite_bind
  pureState_forIn_range_id)

open SizzLean (SSZRepr)
open SizzLean.Proofs (view_uncachedBox)
open SizzLean.Cache

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `computeExitEpochAndUpdateChurn` keeps the flavour: one read of the state,
one two-clause write, and the return of the epoch it computed. -/
theorem keepsUncached_computeExitEpochAndUpdateChurn (exitBalance : Gwei) :
    KeepsUncached (computeExitEpochAndUpdateChurn
      (StateTransition := GloasRun) exitBalance) := by
  unfold computeExitEpochAndUpdateChurn
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- `initiateValidatorExit` keeps the flavour: the validator read and the
checked withdrawability sum are `liftErr`-shaped, the early-return gate is an
`if`, and the write is `modValidator` through the record update. -/
theorem keepsUncached_initiateValidatorExit (i : ValidatorIndex) :
    KeepsUncached (initiateValidatorExit (StateTransition := GloasRun) i) := by
  unfold initiateValidatorExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- The Gloas copy of `processVoluntaryExit` keeps the flavour: six pure
validation gates, one checked read, and `initiateValidatorExit`, whose own
lemma carries the write. -/
theorem keepsUncached_processVoluntaryExit (sve : SignedVoluntaryExit) :
    KeepsUncached (processVoluntaryExit (StateTransition := GloasRun) sve) := by
  unfold processVoluntaryExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- `getPtc` keeps the flavour: it takes the state as an explicit argument, and
its body reads and gates only, through checked ops and asserts. -/
theorem keepsUncached_getPtc (state : BeaconState) (slot : EthCLSpecs.Gloas.Slot) :
    KeepsUncached (getPtc (StateTransition := GloasRun) (pureState state) slot) := by
  unfold getPtc
  keeps_uncached

/-- `getIndexedPayloadAttestation` keeps the flavour: the `getPtc` read, whose
own lemma carries the flavour, then a pure fold and a pure return. -/
theorem keepsUncached_getIndexedPayloadAttestation (state : BeaconState)
    (pa : PayloadAttestation) :
    KeepsUncached (getIndexedPayloadAttestation (StateTransition := GloasRun) (pureState state) pa) := by
  unfold getIndexedPayloadAttestation
  refine keepsUncached_bind (keepsUncached_getPtc state pa.data.slot) (fun ptc => ?_)
  keeps_uncached

/-- `processBlsToExecutionChange` keeps the flavour: the validator read and its
gate, pure digest checks, and one `modValidator` write through the record
update. -/
theorem keepsUncached_processBlsToExecutionChange
    (sbc : SignedBLSToExecutionChange) :
    KeepsUncached (processBlsToExecutionChange (StateTransition := GloasRun) sbc) := by
  unfold processBlsToExecutionChange
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

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
  · refine keepsUncachedFrom_bind ?ca (fun _ midState₂ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _) (fun _ => keepsUncachedFrom_pure _ _)
    · refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
      · refine keepsUncachedFrom_bind ?gi (fun indexed midState₄ => ?_)
        · exact keepsUncached_iff_forall_from.mp (keepsUncached_getIndexedPayloadAttestation state pa) _
        · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)

/-- A checked value lifted into the runner is the identity on the state: the
lift maps the fault through `ofArithFault` and the success value through
`pure`, so the box never leaves `pureState v`. The same fact the framework's
`keepsUncachedFrom_liftErr` states for `liftErr`, at the operator surface's
`liftM`. -/
private theorem keepsUncachedFrom_liftChecked {T α : Type} [SSZRepr T] [HasherTag] (v : T)
    (x : Checked α) :
    KeepsUncachedFrom v (liftM x :
      StateT (SSZ.Box HasherTag.H T) (Except EthCLLib.Spec.StateTransitionError) α) := by
  cases x with
  | ok b =>
    intro a s h
    have hrun : ((liftM (Except.ok b : Checked α) :
          StateT (SSZ.Box HasherTag.H T)
            (Except EthCLLib.Spec.StateTransitionError) α).run (pureState v))
        = .ok (b, pureState v) := rfl
    rw [hrun] at h
    injection h with h1
    injection h1 with _ h2
    subst h2
    rfl
  | error e =>
    intro a s h
    have hrun : ((liftM (Except.error e : Checked α) :
          StateT (SSZ.Box HasherTag.H T)
            (Except EthCLLib.Spec.StateTransitionError) α).run (pureState v))
        = .error (StateTransitionError.ofArithFault e) := rfl
    rw [hrun] at h
    exact absurd h (by simp)

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
      = (match state.balances.val[i.toNat]? with
        | none => .error (.outOfBounds i.toNat state.balances.size)
        | some balance =>
          match balance + d with
          | .error f => .error (StateTransitionError.ofArithFault f)
          | .ok sum => .ok (modBalance (pureState state) i (fun _ => sum), pureState preState)) := by
    unfold increaseBalance sszGetIdx EthCLLib.Spec.IdxRead.get? EthCLLib.Spec.IdxRead.size
    simp only [view_uncachedBox]
    cases state.balances.val[i.toNat]? with
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
  cases hu : state.balances.val[i.toNat]? with
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
      = (match state.balances.val[i.toNat]? with
        | none => .error (.outOfBounds i.toNat state.balances.size)
        | some balance =>
          .ok (modBalance (pureState state) i
            (fun _ => balance.saturatingSub d), pureState preState)) := by
    unfold decreaseBalance sszGetIdx EthCLLib.Spec.IdxRead.get? EthCLLib.Spec.IdxRead.size
    simp only [view_uncachedBox]
    cases state.balances.val[i.toNat]? with
    | none => simp; rfl
    | some balance =>
      simp only [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl
  cases hu : state.balances.val[i.toNat]? with
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
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun epochState midState₁ => ?_)
  refine keepsUncachedFrom_bind
    ((keepsUncached_iff_forall_from.mp (keepsUncached_initiateValidatorExit i)) midState₁)
    (fun _ midState₂ => ?_)
  refine keepsUncachedFrom_get_bind (fun state => ?_)
  refine keepsUncachedFrom_bind
    (keepsUncachedFrom_liftErr (T := BeaconState) (ε := EthCLLib.Spec.StateTransitionError)
      (ε' := EthCLLib.Spec.IndexError) (α := Validator) state _)
    (fun validator midState₃ => ?_)
  -- The checked `Gwei` binds (the slashings ring add, the slashing penalty, and
  -- the whistleblower chain) are `liftM`s of pure values: each passes the box
  -- through unchanged, by `keepsUncachedFrom_liftChecked`.
  refine keepsUncachedFrom_bind ?ring (fun _ midState₄ => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₃ _
  refine keepsUncachedFrom_bind ?pen (fun _ midState₅ => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₄ _
  refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ i _)
    (fun afterDecrease midState₆ => ?_)
  refine keepsUncachedFrom_bind (v := midState₆) (keepsUncachedFrom_set midState₆ afterDecrease)
    (fun _ midState₇ => ?_)
  refine keepsUncachedFrom_get_bind (fun state' => ?_)
  refine keepsUncachedFrom_bind ?wr (fun whistleblowerReward midState₇a => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) state' _
  refine keepsUncachedFrom_bind ?pr (fun proposerReward midState₇b => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₇a _
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterProposerReward midState₈ => ?_)
  refine keepsUncachedFrom_bind ?rem (fun _ midState₈a => ?_)
  · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₈ _
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

theorem keepsUncached_getBlockRootAtSlot (state : BeaconState) (s : EthCLSpecs.Gloas.Slot) :
    KeepsUncached (getBlockRootAtSlot (StateTransition := GloasRun) (pureState state) s) := by
  unfold getBlockRootAtSlot
  refine keepsUncached_bind ?g1 (fun _ => ?_)
  · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
  · refine keepsUncached_bind ?ca (fun _ => ?_)
    · exact keepsUncached_ite (fun _ => keepsUncached_throw _) (fun _ => keepsUncached_pure _)
    · refine keepsUncached_bind ?g2 (fun _ => ?_)
      · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
      · exact keepsUncached_pure _

theorem keepsUncached_getBlockRoot (state : BeaconState) (epoch : EthCLSpecs.Gloas.Epoch) :
    KeepsUncached (getBlockRoot (StateTransition := GloasRun) (pureState state) epoch) := by
  unfold getBlockRoot
  exact keepsUncached_getBlockRootAtSlot state _

theorem keepsUncached_isAttestationSameSlot (state : BeaconState) (data : EthCLSpecs.Gloas.AttestationData) :
    KeepsUncached (isAttestationSameSlot (StateTransition := GloasRun) (pureState state) data) := by
  unfold isAttestationSameSlot
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind ?sr (fun _ => ?_)
  · exact keepsUncached_getBlockRootAtSlot state _
  · refine keepsUncached_bind ?pr (fun _ => ?_)
    · exact keepsUncached_getBlockRootAtSlot state _
    · exact keepsUncached_pure _

theorem keepsUncached_getAttestationParticipationFlagIndices (state : BeaconState) (data : EthCLSpecs.Gloas.AttestationData)
    (inclusionDelay : UInt64) (parentSlot : Slot) :
    KeepsUncached (getAttestationParticipationFlagIndices
      (StateTransition := GloasRun) (pureState state) data inclusionDelay parentSlot) := by
  unfold getAttestationParticipationFlagIndices
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
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
        · exact keepsUncachedFrom_dite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)
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
            refine keepsUncachedFrom_ite (fun _ => ?ht) (fun _ => ?he)
            · refine keepsUncachedFrom_bind ?sv (fun _ midState₈ => ?_)
              · exact keepsUncached_iff_forall_from.mp (keepsUncached_slashValidator _) _
              · exact keepsUncachedFrom_pure _ _
            · exact keepsUncachedFrom_pure _ _
        · refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)

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
    · refine keepsUncachedFrom_bind ?ca (fun _ midState₃ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _) (fun _ => keepsUncachedFrom_pure _ _)
      · refine keepsUncachedFrom_bind ?gC (fun _ midState₄ => ?_)
        · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
        · refine keepsUncachedFrom_bind ?gD (fun _ midState₅ => ?_)
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
          · simp only []
            split
            · refine keepsUncachedFrom_bind (keepsUncachedFrom_pure _ _) (fun _ midState₆ => ?_)
              refine keepsUncachedFrom_bind (T := BeaconState) ?gF (fun _ midState₇ => ?_)
              · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                  (fun _ => keepsUncachedFrom_throw _ _)
              · refine keepsUncachedFrom_bind (T := BeaconState) ?gf (fun flagIndices midState₈ => ?_)
                · exact keepsUncached_iff_forall_from.mp
                    (keepsUncached_getAttestationParticipationFlagIndices state _ _ _) _
                · split
                  · refine keepsUncachedFrom_bind (keepsUncachedFrom_pure _ _) (fun _ midState₉ => ?_)
                    refine keepsUncachedFrom_bind ?li (fun idxs midState₁₀ => ?_)
                    · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₉)
                        (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.IndexError)
                        (α := Array EthCLSpecs.Gloas.ValidatorIndex) _
                    · -- The attesting-index list is built purely (a progressive list wraps
                      -- the sorted array), so the next effect is the validity assert.
                      refine keepsUncachedFrom_bind ?gG (fun _ midState₁₁ => ?_)
                      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                          (fun _ => keepsUncachedFrom_throw _ _)
                      · refine keepsUncachedFrom_bind ?ssL (fun sameSlot midState₁₂ => ?_)
                        · exact keepsUncached_iff_forall_from.mp
                            (keepsUncached_isAttestationSameSlot state att.data) _
                        · refine keepsUncachedFrom_bind ?li2 (fun idxs2 midState₁₃ => ?_)
                          · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₁₂)
                              (ε := EthCLLib.Spec.StateTransitionError)
                              (ε' := EthCLLib.Spec.IndexError)
                              (α := Array EthCLSpecs.Gloas.ValidatorIndex) _
                          · refine keepsUncachedFrom_forIn_array_bind_P (T := BeaconState) (v := midState₁₃)
                              ?ob ?kt
                              (P := fun (acc : EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei) =>
                                ∃ accState : BeaconState, acc.1 = pureState accState) ?hf ?hk idxs2
                              (pureState state, (0 : EthCLSpecs.Gloas.Gwei),
                                (EthCLLib.Spec.vget (pureState state).view.builderPendingPayments
                                  (EthCLSpecs.Gloas.builderPaymentIndex att.data.slot
                                    (att.data.target.epoch ==
                                      EthCLSpecs.Gloas.currentEpochOf (pureState state)))).weight)
                              ⟨state, rfl⟩
                            · intro vi b midState₁₄ r s hb hrun
                              obtain ⟨accState, hu⟩ := hb
                              rcases b with ⟨sa, pn, ws⟩
                              rw [hu] at hrun
                              simp only [] at hrun
                              -- The `had_no_participation` read (beta.4) comes first: a gated
                              -- `sszGetIdx`, which passes the start box through. The do-notation
                              -- copies the rest of the body into both read branches, and
                              -- `ite_bind` folds the copies back into one bind.
                              rw [← ite_bind] at hrun
                              refine run_bind_inv (T := BeaconState) (γ := Unit) midState₁₄ (fun _ => True)
                                (fun (acc : ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei)) =>
                                  ∃ accState : BeaconState, acc.value.1 = pureState accState)
                                (fun r0 s0 h0 => ⟨keepsUncached_ite
                                  (fun _ => keepsUncached_sszGetIdx _ _)
                                  (fun _ => keepsUncached_sszGetIdx _ _) midState₁₄ r0 s0 h0, trivial⟩)
                                ?hrest r s hrun
                              intro flags0 midState₁₄ _ r s hrun
                              refine keepsUncachedFrom_forIn_range_bind_run_inv
                                (T := BeaconState) (v := midState₁₄)
                                (P := fun (acc : EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × Bool) =>
                                  ∃ flagAccState : BeaconState, acc.1 = pureState flagAccState)
                                (Q := fun (acc : ForInStep (EthCLSpecs.Gloas.State × EthCLSpecs.Gloas.Gwei × EthCLSpecs.Gloas.Gwei)) =>
                                  ∃ accState : BeaconState, acc.value.1 = pureState accState)
                                (α := EthCLSpecs.Gloas.ValidatorIndex) (f := _) (k := _) ?hfin ?hkt 3
                                (pureState accState, pn, false) ⟨accState, rfl⟩ r s hrun
                              · intro cIdx b2 midState₁₅ r2 s2 hb2 hrun2
                                obtain ⟨flagAccState, hu2⟩ := hb2
                                rcases b2 with ⟨sa2, p2, ws2⟩
                                rw [hu2] at hrun2
                                simp only [] at hrun2
                                split at hrun2
                                · rw [run_bind] at hrun2
                                  cases hq : ((SSZ.Box.view (pureState flagAccState)).currentEpochParticipation).val[(UInt64.toNat vi)]? with
                                  | some y =>
                                    rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at hrun2
                                    split at hrun2
                                    · rw [run_bind] at hrun2
                                      cases hm : (EthCLSpecs.Gloas.getBaseReward (pureState state) vi).mapError
                                        (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
                                      | error e =>
                                        rw [run_liftErr_of_error _ _ hm, except_bind_error] at hrun2
                                        simp at hrun2
                                      | ok rw =>
                                        rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at hrun2
                                        -- The weighted reward and the numerator add are
                                        -- `liftM`s of pure checked values: each peels with
                                        -- the bind law and `run_liftChecked_ok`.
                                        rw [run_bind] at hrun2
                                        cases hw : ((rw * Gloas.Const.participationFlagWeights[cIdx]! : Checked Gwei)) with
                                        | ok weighted =>
                                          rw [hw] at hrun2
                                          rw [run_liftChecked_ok _ _] at hrun2
                                          rw [except_bind_ok] at hrun2
                                          rw [run_bind] at hrun2
                                          cases hw2 : ((p2 + weighted : Checked Gwei)) with
                                          | ok total =>
                                            rw [hw2] at hrun2
                                            rw [run_liftChecked_ok _ _] at hrun2
                                            rw [except_bind_ok, run_pure] at hrun2
                                            injection hrun2 with h1
                                            injection h1 with h1a h1b
                                            subst h1a
                                            subst h1b
                                            refine ⟨rfl, ⟨({ flagAccState with
                                              currentEpochParticipation :=
                                                (SSZ.Box.view (pureState flagAccState)).currentEpochParticipation.set!
                                                  (UInt64.toNat vi) (EthCLLib.Spec.addFlag y cIdx) }), rfl⟩⟩
                                          | error e =>
                                            rw [hw2] at hrun2
                                            rw [run_liftChecked_error] at hrun2
                                            rw [except_bind_error] at hrun2
                                            simp at hrun2
                                        | error e =>
                                          rw [hw] at hrun2
                                          rw [run_liftChecked_error] at hrun2
                                          rw [except_bind_error] at hrun2
                                          simp at hrun2
                                    · rw [run_pure] at hrun2
                                      injection hrun2 with h1
                                      injection h1 with h1a h1b
                                      subst h1a
                                      subst h1b
                                      exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                                  | none =>
                                    rw [run_sszGetIdx_none _ _ _ hq, except_bind_error] at hrun2
                                    simp at hrun2
                                · rw [run_bind] at hrun2
                                  cases hq : ((SSZ.Box.view (pureState flagAccState)).previousEpochParticipation).val[(UInt64.toNat vi)]? with
                                  | some y =>
                                    rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at hrun2
                                    split at hrun2
                                    · rw [run_bind] at hrun2
                                      cases hm : (EthCLSpecs.Gloas.getBaseReward (pureState state) vi).mapError
                                        (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
                                      | error e =>
                                        rw [run_liftErr_of_error _ _ hm, except_bind_error] at hrun2
                                        simp at hrun2
                                      | ok rw =>
                                        rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at hrun2
                                        -- The weighted reward and the numerator add are
                                        -- `liftM`s of pure checked values: each peels with
                                        -- the bind law and `run_liftChecked_ok`.
                                        rw [run_bind] at hrun2
                                        cases hw : ((rw * Gloas.Const.participationFlagWeights[cIdx]! : Checked Gwei)) with
                                        | ok weighted =>
                                          rw [hw] at hrun2
                                          rw [run_liftChecked_ok _ _] at hrun2
                                          rw [except_bind_ok] at hrun2
                                          rw [run_bind] at hrun2
                                          cases hw2 : ((p2 + weighted : Checked Gwei)) with
                                          | ok total =>
                                            rw [hw2] at hrun2
                                            rw [run_liftChecked_ok _ _] at hrun2
                                            rw [except_bind_ok, run_pure] at hrun2
                                            injection hrun2 with h1
                                            injection h1 with h1a h1b
                                            subst h1a
                                            subst h1b
                                            refine ⟨rfl, ⟨({ flagAccState with
                                              previousEpochParticipation :=
                                                (SSZ.Box.view (pureState flagAccState)).previousEpochParticipation.set!
                                                  (UInt64.toNat vi) (EthCLLib.Spec.addFlag y cIdx) }), rfl⟩⟩
                                          | error e =>
                                            rw [hw2] at hrun2
                                            rw [run_liftChecked_error] at hrun2
                                            rw [except_bind_error] at hrun2
                                            simp at hrun2
                                        | error e =>
                                          rw [hw] at hrun2
                                          rw [run_liftChecked_error] at hrun2
                                          rw [except_bind_error] at hrun2
                                          simp at hrun2
                                    · rw [run_pure] at hrun2
                                      injection hrun2 with h1
                                      injection h1 with h1a h1b
                                      subst h1a
                                      subst h1b
                                      exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                                  | none =>
                                    rw [run_sszGetIdx_none _ _ _ hq, except_bind_error] at hrun2
                                    simp at hrun2
                              · intro r1 midState₁₆ hP1 a s3 hrun3
                                obtain ⟨flagAccState, hu1⟩ := hP1
                                rw [hu1] at hrun3
                                split at hrun3
                                · rw [run_bind] at hrun3
                                  cases hq : ((SSZ.Box.view (pureState state)).validators).val[(UInt64.toNat vi)]? with
                                  | some yv =>
                                    rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at hrun3
                                    -- The payment-weight add is a `liftM` of a pure
                                    -- checked value: peel it as above.
                                    rw [run_bind] at hrun3
                                    cases hw : ((ws + (yv, pureState midState₁₆).fst.effectiveBalance : Checked Gwei)) with
                                    | ok wsum =>
                                      rw [hw] at hrun3
                                      rw [run_liftChecked_ok _ _] at hrun3
                                      rw [except_bind_ok, run_pure] at hrun3
                                      injection hrun3 with h1
                                      injection h1 with h1a h1b
                                      subst h1a
                                      subst h1b
                                      exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                                    | error e =>
                                      rw [hw] at hrun3
                                      rw [run_liftChecked_error] at hrun3
                                      rw [except_bind_error] at hrun3
                                      simp at hrun3
                                  | none =>
                                    rw [run_sszGetIdx_none _ _ _ hq, except_bind_error] at hrun3
                                    simp at hrun3
                                · rw [run_pure] at hrun3
                                  injection hrun3 with h1
                                  injection h1 with h1a h1b
                                  subst h1a
                                  subst h1b
                                  exact ⟨rfl, ⟨flagAccState, rfl⟩⟩

                            · intro b midState₁₇ hb
                              obtain ⟨accState, hu⟩ := hb
                              rcases b with ⟨sa, pn, wt⟩
                              rw [hu]
                              -- The proposer reward is the checked `proposerNum /
                              -- proposerDenominator` division, a `liftM` of a pure
                              -- value: it passes the box through unchanged.
                              refine keepsUncachedFrom_bind ?prr
                                (fun proposerReward midState₁₇b => ?_)
                              · exact keepsUncachedFrom_liftChecked (T := BeaconState) midState₁₇ _
                              refine returnsUncachedFrom_bind
                                (returnsUncached_increaseBalance _ _ _) (fun afterIncrease midState₁₈ =>
                                  -- The payment write-back on `pureState afterIncrease` reduces to
                                  -- `pureState` of the record update, so the value is inferred.
                                  keepsUncachedFrom_set midState₁₈ _)
                  · exact keepsUncachedFrom_throw_bind _ _
            · exact keepsUncachedFrom_throw_bind _ _

end

end EthCLSpecs.Proofs.Gloas
