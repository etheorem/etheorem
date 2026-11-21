import EthCLLib.Spec
import EthCLLib.Proofs.KeepsUncached
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Heze.Operations
import EthCLSpecs.Heze.Transition
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Heze.KeepsUncached`: the Heze handlers never leave the uncached box

`KeepsUncached` (`EthCLLib/Proofs/KeepsUncached.lean`) is the property behind `runPure`'s
conditional bind law: a successful run that starts on `pureState preState` ends on an
uncached box. This file discharges it for the Heze operation handlers and for
`processOperations`, the block substep that runs them.

`inherit` re-elaborates each Gloas and Fulu body at `Heze.State`, so every handler here is
a Heze constant of its own, and a Gloas lemma says nothing about it. The proofs are the
proofs of `Proofs/Gloas/KeepsUncached.lean`, restated at `HezeRun`: the re-elaborated
bodies have the same shape, so each script carries over. `processOperations` is a Heze
body of its own.

The lemmas fall into four groups:

* the exit path: `computeExitEpochAndUpdateChurn`, `initiateValidatorExit`,
  `processVoluntaryExit`.
* the readers: `processBlsToExecutionChange`, `processPayloadAttestation`, with
  `getPtc` and `getIndexedPayloadAttestation` as callees, and the read helpers of
  the attestation handler (`getBlockRootAtSlot`, `getBlockRoot`,
  `isAttestationSameSlot`, `getAttestationParticipationFlagIndices`).
* the balance writers that return a box (`increaseBalance`, `decreaseBalance`,
  as `ReturnsUncached`) and `slashValidator`, which threads both.
* the handlers with a local state or a loop (`processProposerSlashing`,
  `processAttesterSlashing`, `processAttestation`), and `processOperations`, whose six
  `for` loops run over progressive lists. A progressive list loops over its array, so
  `keepsUncached_forIn_array` carries each handler through its loop.

Each lemma is a construction over the generic closure lemmas, one bind per
`←`-binding in the source. A state write discharges `keepsUncached_modify`'s writer
hypothesis by `rfl`: the `sszUpdate` expansion on `pureState state` reduces to the
record update on `state`. All of them are supporting lemmas, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend sszGetIdx checkedAdd ErrorConv)
open EthCLSpecs.Heze (Preset Config ValidatorIndex Gwei Epoch Slot Attestation AttestationData
  Validator SignedVoluntaryExit ProposerSlashing AttesterSlashing SignedBLSToExecutionChange
  PayloadAttestation BeaconState BeaconBlockBody
  processVoluntaryExit initiateValidatorExit computeExitEpochAndUpdateChurn
  processProposerSlashing processAttesterSlashing processAttestation
  processBlsToExecutionChange processPayloadAttestation processOperations
  getIndexedPayloadAttestation getPtc increaseBalance decreaseBalance slashValidator
  modBalance getBlockRootAtSlot getBlockRoot isAttestationSameSlot
  getAttestationParticipationFlagIndices builderPaymentIndex)
open EthCLLib.Proofs (pureState KeepsUncached ReturnsUncached KeepsUncachedFrom
  keepsUncached_pure keepsUncached_throw keepsUncached_bind keepsUncached_modify
  keepsUncached_get keepsUncachedFrom_bind
  keepsUncached_liftErr keepsUncached_dite
  keepsUncached_ite keepsUncachedFrom_ite keepsUncachedFrom_pure keepsUncachedFrom_throw
  keepsUncachedFrom_liftErr keepsUncachedFrom_dite
  keepsUncachedFrom_set keepsUncachedFrom_get
  keepsUncachedFrom_get_bind keepsUncachedFrom_throw_bind keepsUncachedFrom_forIn_array_of_keeps
  keepsUncachedFrom_forIn_array_bind_P keepsUncachedFrom_forIn_range_bind_run_inv
  keepsUncached_forIn_array
  returnsUncachedFrom_bind keepsUncached_iff_forall_from
  run_bind run_pure except_bind_ok except_bind_error
  run_liftErr_of_ok run_liftErr_of_error
  run_sszGetIdx_some run_sszGetIdx_none keepsUncached_sszGetIdx run_bind_inv ite_bind
  pureState_forIn_range_id)

open SizzLean.Proofs (view_uncachedBox)
open SizzLean.Cache

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A checked `uint64` sum keeps the flavour. It is an `if` with two branches: the
`.arithmetic` fault through `liftErr`, and `pure`. -/
theorem keepsUncached_checkedAdd (a b : UInt64) (descr : String) :
    KeepsUncached (checkedAdd (m := HezeRun) a b descr) := by
  unfold checkedAdd EthCLLib.Spec.throwArithmetic
  exact keepsUncached_ite (fun _ => keepsUncached_liftErr _) (fun _ => keepsUncached_pure _)

/-- The checked `ValidatorIndex(...)` cast keeps the flavour, as `keepsUncached_checkedAdd`. -/
theorem keepsUncached_checkedIndex (i : Nat) (descr : String) :
    KeepsUncached (EthCLLib.Spec.checkedIndex (m := HezeRun) i descr) := by
  unfold EthCLLib.Spec.checkedIndex EthCLLib.Spec.throwArithmetic
  exact keepsUncached_ite (fun _ => keepsUncached_liftErr _) (fun _ => keepsUncached_pure _)

/-- A checked `uint64` difference keeps the flavour, as `keepsUncached_checkedAdd`. -/
theorem keepsUncached_checkedSub (a b : UInt64) (descr : String) :
    KeepsUncached (EthCLLib.Spec.checkedSub (m := HezeRun) a b descr) := by
  unfold EthCLLib.Spec.checkedSub EthCLLib.Spec.throwArithmetic
  exact keepsUncached_ite (fun _ => keepsUncached_liftErr _) (fun _ => keepsUncached_pure _)

/-- A checked `uint64` product keeps the flavour, as `keepsUncached_checkedAdd`. -/
theorem keepsUncached_checkedMul (a b : UInt64) (descr : String) :
    KeepsUncached (EthCLLib.Spec.checkedMul (m := HezeRun) a b descr) := by
  unfold EthCLLib.Spec.checkedMul EthCLLib.Spec.throwArithmetic
  exact keepsUncached_ite (fun _ => keepsUncached_liftErr _) (fun _ => keepsUncached_pure _)

/-- `computeExitEpochAndUpdateChurn` keeps the flavour: one read of the state,
one two-clause write, and the return of the epoch it computed. -/
theorem keepsUncached_computeExitEpochAndUpdateChurn (exitBalance : Gwei) :
    KeepsUncached (computeExitEpochAndUpdateChurn
      (StateTransition := HezeRun) exitBalance) := by
  unfold computeExitEpochAndUpdateChurn
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- `initiateValidatorExit` keeps the flavour: the validator read and the
checked withdrawability sum are `liftErr`-shaped, the early-return gate is an
`if`, and the write is `modValidator` through the record update. -/
theorem keepsUncached_initiateValidatorExit (i : ValidatorIndex) :
    KeepsUncached (initiateValidatorExit (StateTransition := HezeRun) i) := by
  unfold initiateValidatorExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- `processVoluntaryExit` keeps the flavour: six pure validation gates, one checked
read, and `initiateValidatorExit`, whose own lemma carries the write. -/
theorem keepsUncached_processVoluntaryExit (sve : SignedVoluntaryExit) :
    KeepsUncached (processVoluntaryExit (StateTransition := HezeRun) sve) := by
  unfold processVoluntaryExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- `getPtc` keeps the flavour: it takes the state as an explicit argument, and
its body reads and gates only, through checked ops and asserts. -/
theorem keepsUncached_getPtc (state : BeaconState) (slot : Slot) :
    KeepsUncached (getPtc (StateTransition := HezeRun) (pureState state) slot) := by
  unfold getPtc
  keeps_uncached

/-- `getIndexedPayloadAttestation` keeps the flavour: the `getPtc` read, whose
own lemma carries the flavour, then a pure fold and a pure return. -/
theorem keepsUncached_getIndexedPayloadAttestation (state : BeaconState)
    (pa : PayloadAttestation) :
    KeepsUncached (getIndexedPayloadAttestation (StateTransition := HezeRun)
      (pureState state) pa) := by
  unfold getIndexedPayloadAttestation
  refine keepsUncached_bind (keepsUncached_getPtc state pa.data.slot) (fun ptc => ?_)
  keeps_uncached

/-- `processBlsToExecutionChange` keeps the flavour: the validator read and its
gate, pure digest checks, and one `modValidator` write through the record
update. -/
theorem keepsUncached_processBlsToExecutionChange
    (sbc : SignedBLSToExecutionChange) :
    KeepsUncached (processBlsToExecutionChange (StateTransition := HezeRun) sbc) := by
  unfold processBlsToExecutionChange
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached

/-- `processPayloadAttestation` keeps the flavour: three pure gates, the
checked slot increment, and `getIndexedPayloadAttestation`, whose own lemma
carries the flavour. The `get` peels through `keepsUncachedFrom_get_bind`, so
the continuation starts on `pureState state` and the callee lemma applies at that
box. -/
theorem keepsUncached_processPayloadAttestation (pa : PayloadAttestation) :
    KeepsUncached (processPayloadAttestation (StateTransition := HezeRun) pa) := by
  intro preState
  unfold processPayloadAttestation
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_bind ?g1 (fun _ midState₁ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
      (fun _ => keepsUncachedFrom_throw _ _)
  · refine keepsUncachedFrom_bind ?ca (fun _ midState₂ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
        (fun _ => keepsUncachedFrom_pure _ _)
    · refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
          (fun _ => keepsUncachedFrom_throw _ _)
      · refine keepsUncachedFrom_bind ?gi (fun indexed midState₄ => ?_)
        · exact keepsUncached_iff_forall_from.mp
            (keepsUncached_getIndexedPayloadAttestation state pa) _
        · -- The validity check is an `Except` read, then its gate.
          refine keepsUncachedFrom_bind ?lv (fun _ midState₅ => ?_)
          · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₄)
              (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.StateTransitionError)
              (α := Bool) _
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
              (fun _ => keepsUncachedFrom_throw _ _)

/-- `increaseBalance` returns `pureState` of the written value and leaves the threaded
state uncached. The run reduces to the match that the Fulu contract states: a missing
index rejects, an overflow rejects, and otherwise the run returns the `modBalance`
write. -/
theorem returnsUncached_increaseBalance (state : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    ReturnsUncached (increaseBalance (StateTransition := HezeRun) (pureState state) i d) := by
  intro preState b s h
  have hrun : (increaseBalance (StateTransition := HezeRun) (pureState state) i d).run
      (pureState preState)
      = (match state.balances.val[i.toNat]? with
        | none => .error (.outOfBounds i.toNat state.balances.size)
        | some balance =>
          if balance + d < balance then
            .error (.arithmetic "increase_balance: balances[index] + delta")
          else
            .ok (modBalance (pureState state) i (fun _ => balance + d), pureState preState)) := by
    unfold increaseBalance sszGetIdx EthCLLib.Spec.IdxRead.get? EthCLLib.Spec.IdxRead.size checkedAdd
    simp only [view_uncachedBox]
    cases state.balances.val[i.toNat]? with
    | none => simp; rfl
    | some balance =>
      by_cases hc : balance + d < balance
      · simp [hc, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
        rfl
      · simp [hc, EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
        rfl
  cases hu : state.balances.val[i.toNat]? with
  | none => rw [hrun, hu] at h; simp at h
  | some balance =>
    rw [hrun, hu] at h
    dsimp only at h
    by_cases hc : balance + d < balance
    · rw [ite_eq_left hc] at h
      simp at h
    · rw [ite_eq_right hc] at h
      injection h with h1
      injection h1 with h1a h1b
      subst h1a
      subst h1b
      exact ⟨⟨_, rfl⟩, rfl⟩

/-- `decreaseBalance` has the shape of `increaseBalance`, and writes the saturating
difference. -/
theorem returnsUncached_decreaseBalance (state : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    ReturnsUncached (decreaseBalance (StateTransition := HezeRun) (pureState state) i d) := by
  intro preState b s h
  have hrun : (decreaseBalance (StateTransition := HezeRun) (pureState state) i d).run
      (pureState preState)
      = (match state.balances.val[i.toNat]? with
        | none => .error (.outOfBounds i.toNat state.balances.size)
        | some balance =>
          .ok (modBalance (pureState state) i
            (fun _ => EthCLLib.Spec.saturatingSub balance d), pureState preState)) := by
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

/-- `slashValidator` keeps the flavour. The reads and the exit write keep it, as in
the exit path lemmas. Two threaded states, the local write chain and the two balance
returns, stay uncached through `ReturnsUncached` and `keepsUncachedFrom_set`. The closing
EIP-7732 loop over the payment window is a pure `modifyState` writer, and
`pureState_forIn_range_id` carries the flavour through its steps. -/
theorem keepsUncached_slashValidator (i : ValidatorIndex) :
    KeepsUncached (slashValidator (StateTransition := HezeRun) i) := by
  intro preState
  unfold slashValidator
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun _ midState₁ => ?_)
  refine keepsUncachedFrom_bind
    ((keepsUncached_iff_forall_from.mp (keepsUncached_initiateValidatorExit i)) midState₁)
    (fun _ midState₂ => ?_)
  refine keepsUncachedFrom_get_bind (fun state => ?_)
  refine keepsUncachedFrom_bind
    (keepsUncachedFrom_liftErr (T := BeaconState) (ε := EthCLLib.Spec.StateTransitionError)
      (ε' := EthCLLib.Spec.IndexError) (α := Validator) state _)
    (fun validator midState₃ => ?_)
  -- The two checked sums, the withdrawable epoch and the slashings entry.
  refine keepsUncachedFrom_bind ?ce (fun _ midState₃a => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
      (fun _ => keepsUncachedFrom_pure _ _)
  refine keepsUncachedFrom_bind ?cs (fun _ midState₃b => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
      (fun _ => keepsUncachedFrom_pure _ _)
  refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ i _)
    (fun afterDecrease midState₄ => ?_)
  refine keepsUncachedFrom_bind (v := midState₄) (keepsUncachedFrom_set midState₄ afterDecrease)
    (fun _ midState₅ => ?_)
  refine keepsUncachedFrom_get_bind (fun state' => ?_)
  -- The checked product `whistleblower_reward * PROPOSER_WEIGHT`.
  refine keepsUncachedFrom_bind ?cm (fun _ midState₅a => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
      (fun _ => keepsUncachedFrom_pure _ _)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterProposerReward midState₆ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterWhistleblowerReward midState₇ => ?_)
  refine keepsUncachedFrom_bind (keepsUncachedFrom_set midState₇ afterWhistleblowerReward)
    (fun _ midState₈ => ?_)
  -- The payment loop: each step either rebuilds the record (an uncached box) or passes
  -- the box through, so the whole writer maps `pureState` to `pureState`.
  refine keepsUncached_iff_forall_from.mp (keepsUncached_modify _ (fun v => ?_)) midState₈
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

/-- `getBlockRootAtSlot` keeps the flavour: three gates, then a pure read of the root
vector. -/
theorem keepsUncached_getBlockRootAtSlot (state : BeaconState) (s : Slot) :
    KeepsUncached (getBlockRootAtSlot (StateTransition := HezeRun) (pureState state) s) := by
  unfold getBlockRootAtSlot
  refine keepsUncached_bind ?g1 (fun _ => ?_)
  · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
  · refine keepsUncached_bind ?ca (fun _ => ?_)
    · exact keepsUncached_ite (fun _ => keepsUncached_throw _) (fun _ => keepsUncached_pure _)
    · refine keepsUncached_bind ?g2 (fun _ => ?_)
      · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
      · exact keepsUncached_pure _

/-- `getBlockRoot` is `getBlockRootAtSlot` at the first slot of the epoch. -/
theorem keepsUncached_getBlockRoot (state : BeaconState) (epoch : Epoch) :
    KeepsUncached (getBlockRoot (StateTransition := HezeRun) (pureState state) epoch) := by
  unfold getBlockRoot
  -- The epoch's start slot comes from the checked multiply, lifted into the run.
  exact keepsUncached_bind (keepsUncached_liftErr _)
    (fun _ => keepsUncached_getBlockRootAtSlot state _)

/-- `isAttestationSameSlot` keeps the flavour: an early `pure` at slot zero, else two
`getBlockRootAtSlot` reads and a pure comparison. -/
theorem keepsUncached_isAttestationSameSlot (state : BeaconState) (data : AttestationData) :
    KeepsUncached (isAttestationSameSlot (StateTransition := HezeRun) (pureState state) data) := by
  unfold isAttestationSameSlot
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind ?sr (fun _ => ?_)
  · exact keepsUncached_getBlockRootAtSlot state _
  · refine keepsUncached_bind ?pr (fun _ => ?_)
    · exact keepsUncached_getBlockRootAtSlot state _
    · exact keepsUncached_pure _

/-- `getAttestationParticipationFlagIndices` keeps the flavour: its body is gates, the
three root reads above, and pure flag pushes. -/
theorem keepsUncached_getAttestationParticipationFlagIndices (state : BeaconState)
    (data : AttestationData) (inclusionDelay : UInt64) (parentSlot : Slot) :
    KeepsUncached (getAttestationParticipationFlagIndices
      (StateTransition := HezeRun) (pureState state) data inclusionDelay parentSlot) := by
  unfold getAttestationParticipationFlagIndices
  -- The three root reads carry their own lemmas. The gates and the flag list are closure
  -- steps.
  repeat' first
    | exact keepsUncached_getBlockRoot state _
    | exact keepsUncached_getBlockRootAtSlot state _
    | exact keepsUncached_isAttestationSameSlot state _
    | exact keepsUncached_pure _
    | exact keepsUncached_throw _
    | refine keepsUncached_ite (fun _ => ?_) (fun _ => ?_)
    | refine keepsUncached_bind ?_ (fun _a => ?_)

/-! ## `processProposerSlashing` and the two loop handlers

The three remaining handlers peel per statement. The peel steps name their own
closure lemma, so the unifier never searches: a failed leaf trial whnfs the goal
action, and past the first gate that walk reaches the `sszUpdate` expansions of
the cached-box branch, which is where the naive tactic pass stalls. -/

/-- `processProposerSlashing` keeps the flavour: seven gates on the two headers, then
`slashValidator`, which voids the payments of the slashed proposer. -/
theorem keepsUncached_processProposerSlashing (ps : ProposerSlashing) :
    KeepsUncached (processProposerSlashing (StateTransition := HezeRun) ps) := by
  intro preState
  unfold processProposerSlashing
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun box midState₁ => ?_)
  refine keepsUncachedFrom_bind ?g1 (fun _ midState₂ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
      (fun _ => keepsUncachedFrom_throw _ _)
  · refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
        (fun _ => keepsUncachedFrom_throw _ _)
    · refine keepsUncachedFrom_bind ?g3 (fun _ midState₄ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
          (fun _ => keepsUncachedFrom_throw _ _)
      · refine keepsUncachedFrom_bind ?g4 (fun _ midState₅ => ?_)
        · -- The proposer read through `sszGetIdx`.
          exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₄)
            (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.IndexError)
            (α := Validator) _
        · refine keepsUncachedFrom_bind ?g5 (fun _ midState₆ => ?_)
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
              (fun _ => keepsUncachedFrom_throw _ _)
          · refine keepsUncachedFrom_bind ?g6 (fun _ midState₇ => ?_)
            · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                (fun _ => keepsUncachedFrom_throw _ _)
            · refine keepsUncachedFrom_bind ?g7 (fun _ midState₈ => ?_)
              · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                  (fun _ => keepsUncachedFrom_throw _ _)
              · exact keepsUncached_iff_forall_from.mp
                  (keepsUncached_slashValidator (i := ps.signedHeader1.message.proposerIndex)) _

/-- `processAttesterSlashing` keeps the flavour: three gates, then a loop over the
slashable indices whose body calls `slashValidator`. The loop accumulator carries no
box, so `keepsUncachedFrom_forIn_array_of_keeps` applies. -/
theorem keepsUncached_processAttesterSlashing (asl : AttesterSlashing) :
    KeepsUncached (processAttesterSlashing (StateTransition := HezeRun) asl) := by
  intro preState
  unfold processAttesterSlashing
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun state midState₁ => ?_)
  refine keepsUncachedFrom_bind ?g1 (fun _ midState₂ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
      (fun _ => keepsUncachedFrom_throw _ _)
  · -- Each validity check is an `Except` read, then its gate.
    refine keepsUncachedFrom_bind ?l2 (fun _ midState₂a => ?_)
    · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₂)
        (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.StateTransitionError)
        (α := Bool) _
    refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
        (fun _ => keepsUncachedFrom_throw _ _)
    · refine keepsUncachedFrom_bind ?l3 (fun _ midState₃a => ?_)
      · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₃)
          (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.StateTransitionError)
          (α := Bool) _
      refine keepsUncachedFrom_bind ?g3 (fun _ midState₄ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
          (fun _ => keepsUncachedFrom_throw _ _)
      · refine keepsUncachedFrom_bind ?loop (fun r midState₅ => ?_)
        · refine keepsUncachedFrom_forIn_array_of_keeps _ ?hf _ _
          · intro x b midState₆
            refine keepsUncachedFrom_bind (keepsUncachedFrom_get midState₆)
              (fun state midState₇ => ?_)
            refine keepsUncachedFrom_ite (fun _ => ?ht) (fun _ => ?he)
            · refine keepsUncachedFrom_bind ?sv (fun _ midState₈ => ?_)
              · exact keepsUncached_iff_forall_from.mp (keepsUncached_slashValidator _) _
              · exact keepsUncachedFrom_pure _ _
            · exact keepsUncachedFrom_pure _ _
        · refine keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)

/-- `processAttestation` keeps the flavour. After the gates and the attesting-index
reads, a loop runs over the attesting indices, with an inner range loop over the three
flags. The invariant of both loops says that the box component of the accumulator is
`pureState` of some value (`keepsUncachedFrom_forIn_array_bind_P`,
`keepsUncachedFrom_forIn_range_bind_run_inv`). The `had_no_participation` read before the
inner loop is a gated `sszGetIdx`, which passes the start box through. The final proposer
reward returns a box through `ReturnsUncached`. -/
theorem keepsUncached_processAttestation (att : Attestation) (parentSlot : Slot) :
    KeepsUncached (processAttestation (StateTransition := HezeRun) att parentSlot) := by
  intro preState
  unfold processAttestation
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_bind ?gA (fun _ midState₁ => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
      (fun _ => keepsUncachedFrom_throw _ _)
  · refine keepsUncachedFrom_bind ?gB (fun _ midState₂ => ?_)
    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
        (fun _ => keepsUncachedFrom_throw _ _)
    · refine keepsUncachedFrom_bind ?ca (fun _ midState₃ => ?_)
      · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
          (fun _ => keepsUncachedFrom_pure _ _)
      · refine keepsUncachedFrom_bind ?gC (fun _ midState₄ => ?_)
        · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
            (fun _ => keepsUncachedFrom_throw _ _)
        · refine keepsUncachedFrom_bind ?gD (fun _ midState₅ => ?_)
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
              (fun _ => keepsUncachedFrom_throw _ _)
          · refine keepsUncachedFrom_bind ?co (fun _ midState₆ => ?_)
            · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₅)
                (ε := EthCLLib.Spec.StateTransitionError) (ε' := EthCLLib.Spec.StateTransitionError)
                (α := Nat) _
            · refine keepsUncachedFrom_bind (T := BeaconState) ?gF (fun _ midState₇ => ?_)
              · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                  (fun _ => keepsUncachedFrom_throw _ _)
              · refine keepsUncachedFrom_bind (T := BeaconState) ?gf
                  (fun flagIndices midState₈ => ?_)
                · exact keepsUncached_iff_forall_from.mp
                    (keepsUncached_getAttestationParticipationFlagIndices state _ _ _) _
                · refine keepsUncachedFrom_bind ?li (fun idxs midState₁₀ => ?_)
                  · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₈)
                      (ε := EthCLLib.Spec.StateTransitionError)
                      (ε' := EthCLLib.Spec.StateTransitionError)
                      (α := Array ValidatorIndex) _
                  · -- The attesting-index list is built purely (a progressive list wraps
                    -- the sorted array). The signature check is an `Except` read, then its
                    -- gate.
                    refine keepsUncachedFrom_bind ?lv (fun _ midStateV => ?_)
                    · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₁₀)
                        (ε := EthCLLib.Spec.StateTransitionError)
                        (ε' := EthCLLib.Spec.StateTransitionError) (α := Bool) _
                    refine keepsUncachedFrom_bind ?gG (fun _ midState₁₁ => ?_)
                    · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
                        (fun _ => keepsUncachedFrom_throw _ _)
                    focus
                      · refine keepsUncachedFrom_bind ?ssL (fun sameSlot midState₁₂ => ?_)
                        · exact keepsUncached_iff_forall_from.mp
                            (keepsUncached_isAttestationSameSlot state att.data) _
                        · refine keepsUncachedFrom_bind ?li2 (fun idxs2 midState₁₃ => ?_)
                          · exact keepsUncachedFrom_liftErr (T := BeaconState) (v := midState₁₂)
                              (ε := EthCLLib.Spec.StateTransitionError)
                              (ε' := EthCLLib.Spec.StateTransitionError)
                              (α := Array ValidatorIndex) _
                          · refine keepsUncachedFrom_forIn_array_bind_P (T := BeaconState)
                              (v := midState₁₃) ?ob ?kt
                              (P := fun (acc : EthCLSpecs.Heze.State × Gwei × Gwei) =>
                                ∃ accState : BeaconState, acc.1 = pureState accState)
                              ?hf ?hk idxs2
                              (pureState state, 0,
                                (EthCLLib.Spec.vget (pureState state).view.builderPendingPayments
                                  (builderPaymentIndex att.data.slot
                                    (att.data.target.epoch ==
                                      EthCLSpecs.Heze.currentEpochOf (pureState state)))).weight)
                              ⟨state, rfl⟩
                            · intro vi b midState₁₄ r s hb hrun
                              obtain ⟨accState, hu⟩ := hb
                              rcases b with ⟨sa, pn, ws⟩
                              rw [hu] at hrun
                              simp only [] at hrun
                              -- The `had_no_participation` read comes first: a gated
                              -- `sszGetIdx`, which passes the start box through. The
                              -- do-notation copies the rest of the body into both read
                              -- branches, and `ite_bind` folds the copies back into one bind.
                              rw [← ite_bind] at hrun
                              refine run_bind_inv (T := BeaconState) (γ := Unit) midState₁₄
                                (fun _ => True)
                                (fun (acc : ForInStep (EthCLSpecs.Heze.State × Gwei × Gwei)) =>
                                  ∃ accState : BeaconState, acc.value.1 = pureState accState)
                                (fun r0 s0 h0 => ⟨keepsUncached_ite
                                  (fun _ => keepsUncached_sszGetIdx _ _)
                                  (fun _ => keepsUncached_sszGetIdx _ _) midState₁₄ r0 s0 h0,
                                  trivial⟩)
                                ?hrest r s hrun
                              intro flags0 midState₁₄ _ r s hrun
                              refine keepsUncachedFrom_forIn_range_bind_run_inv
                                (T := BeaconState) (v := midState₁₄)
                                (P := fun (acc : EthCLSpecs.Heze.State × Gwei × Bool) =>
                                  ∃ flagAccState : BeaconState, acc.1 = pureState flagAccState)
                                (Q := fun (acc : ForInStep (EthCLSpecs.Heze.State × Gwei × Gwei)) =>
                                  ∃ accState : BeaconState, acc.value.1 = pureState accState)
                                (α := ValidatorIndex) (f := _) (k := _) ?hfin ?hkt 3
                                (pureState accState, pn, false) ⟨accState, rfl⟩ r s hrun
                              · intro cIdx b2 midState₁₅ r2 s2 hb2 hrun2
                                obtain ⟨flagAccState, hu2⟩ := hb2
                                rcases b2 with ⟨sa2, p2, ws2⟩
                                rw [hu2] at hrun2
                                simp only [] at hrun2
                                -- Only a flag in the set reads the participation entry.
                                split at hrun2
                                · split at hrun2
                                  · rw [run_bind] at hrun2
                                    cases hq : ((SSZ.Box.view (pureState flagAccState)).currentEpochParticipation).val[(UInt64.toNat vi)]? with
                                    | some y =>
                                      rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at hrun2
                                      split at hrun2
                                      · rw [run_bind] at hrun2
                                        cases hm : (EthCLSpecs.Heze.getBaseReward (pureState state) vi).mapError
                                          (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
                                        | error e =>
                                          rw [run_liftErr_of_error _ _ hm, except_bind_error] at hrun2
                                          simp at hrun2
                                        | ok br =>
                                          rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at hrun2
                                          rw [run_bind] at hrun2
                                          simp only [EthCLLib.Spec.checkedMul] at hrun2
                                          split at hrun2
                                          · unfold EthCLLib.Spec.throwArithmetic at hrun2
                                            rw [run_liftErr_of_error _ _ rfl, except_bind_error] at hrun2
                                            simp at hrun2
                                          · rw [run_pure, except_bind_ok, run_bind] at hrun2
                                            simp only [EthCLLib.Spec.checkedAdd] at hrun2
                                            split at hrun2
                                            · unfold EthCLLib.Spec.throwArithmetic at hrun2
                                              rw [run_liftErr_of_error _ _ rfl, except_bind_error] at hrun2
                                              simp at hrun2
                                            · rw [run_pure, except_bind_ok, run_pure] at hrun2
                                              injection hrun2 with h1
                                              injection h1 with h1a h1b
                                              subst h1a
                                              subst h1b
                                              refine ⟨rfl, ⟨({ flagAccState with
                                                currentEpochParticipation :=
                                                  (SSZ.Box.view (pureState flagAccState)).currentEpochParticipation.set!
                                                    (UInt64.toNat vi) (EthCLLib.Spec.addFlag y cIdx) }), rfl⟩⟩
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
                                        cases hm : (EthCLSpecs.Heze.getBaseReward (pureState state) vi).mapError
                                          (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
                                        | error e =>
                                          rw [run_liftErr_of_error _ _ hm, except_bind_error] at hrun2
                                          simp at hrun2
                                        | ok br =>
                                          rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at hrun2
                                          rw [run_bind] at hrun2
                                          simp only [EthCLLib.Spec.checkedMul] at hrun2
                                          split at hrun2
                                          · unfold EthCLLib.Spec.throwArithmetic at hrun2
                                            rw [run_liftErr_of_error _ _ rfl, except_bind_error] at hrun2
                                            simp at hrun2
                                          · rw [run_pure, except_bind_ok, run_bind] at hrun2
                                            simp only [EthCLLib.Spec.checkedAdd] at hrun2
                                            split at hrun2
                                            · unfold EthCLLib.Spec.throwArithmetic at hrun2
                                              rw [run_liftErr_of_error _ _ rfl, except_bind_error] at hrun2
                                              simp at hrun2
                                            · rw [run_pure, except_bind_ok, run_pure] at hrun2
                                              injection hrun2 with h1
                                              injection h1 with h1a h1b
                                              subst h1a
                                              subst h1b
                                              refine ⟨rfl, ⟨({ flagAccState with
                                                previousEpochParticipation :=
                                                  (SSZ.Box.view (pureState flagAccState)).previousEpochParticipation.set!
                                                    (UInt64.toNat vi) (EthCLLib.Spec.addFlag y cIdx) }), rfl⟩⟩
                                      · rw [run_pure] at hrun2
                                        injection hrun2 with h1
                                        injection h1 with h1a h1b
                                        subst h1a
                                        subst h1b
                                        exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                                    | none =>
                                      rw [run_sszGetIdx_none _ _ _ hq, except_bind_error] at hrun2
                                      simp at hrun2
                                · rw [run_pure] at hrun2
                                  injection hrun2 with h1
                                  injection h1 with h1a h1b
                                  subst h1a
                                  subst h1b
                                  exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                              · intro r1 midState₁₆ hP1 a s3 hrun3
                                obtain ⟨flagAccState, hu1⟩ := hP1
                                rw [hu1] at hrun3
                                split at hrun3
                                · rw [run_bind] at hrun3
                                  cases hq : ((SSZ.Box.view (pureState state)).validators).val[(UInt64.toNat vi)]? with
                                  | some yv =>
                                    rw [run_sszGetIdx_some _ _ _ hq, except_bind_ok] at hrun3
                                    -- The weight add is checked.
                                    rw [run_bind] at hrun3
                                    simp only [EthCLLib.Spec.checkedAdd] at hrun3
                                    split at hrun3
                                    · unfold EthCLLib.Spec.throwArithmetic at hrun3
                                      rw [run_liftErr_of_error _ _ rfl, except_bind_error] at hrun3
                                      simp at hrun3
                                    · rw [run_pure, except_bind_ok, run_pure] at hrun3
                                      injection hrun3 with h1
                                      injection h1 with h1a h1b
                                      subst h1a
                                      subst h1b
                                      exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
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
                              refine returnsUncachedFrom_bind
                                (returnsUncached_increaseBalance _ _ _)
                                (fun afterIncrease midState₁₈ =>
                                  -- The payment write-back on `pureState afterIncrease` reduces
                                  -- to `pureState` of the record update, so the value is
                                  -- inferred.
                                  keepsUncachedFrom_set midState₁₈ _)

/-! ## `processOperations`

The coordinator opens with the six length `assert`s, then runs six `for` loops, one per
operation family. Each loop runs over a progressive list, whose `for` is the `for` over
its array. The body is the handler followed by `pure (.yield ())`.
`keepsUncached_forIn_array` carries each handler's own lemma through its loop. -/

/-- `processOperations` keeps the flavour: the six length gates, then the six operation
loops, each through `keepsUncached_forIn_array` and the handler lemma above. -/
theorem keepsUncached_processOperations (body : BeaconBlockBody) (parentSlot : Slot) :
    KeepsUncached (processOperations (StateTransition := HezeRun) body parentSlot) := by
  unfold processOperations
  repeat' first
    | exact keepsUncached_pure _
    | exact keepsUncached_throw _
    | refine keepsUncached_ite (fun _ => ?_) (fun _ => ?_)
    | exact keepsUncached_forIn_array _ (fun op _ => keepsUncached_bind
        (keepsUncached_processProposerSlashing op) (fun _ => keepsUncached_pure _))
        body.proposerSlashings.val _
    | exact keepsUncached_forIn_array _ (fun op _ => keepsUncached_bind
        (keepsUncached_processAttesterSlashing op) (fun _ => keepsUncached_pure _))
        body.attesterSlashings.val _
    | exact keepsUncached_forIn_array _ (fun op _ => keepsUncached_bind
        (keepsUncached_processAttestation op parentSlot) (fun _ => keepsUncached_pure _))
        body.attestations.val _
    | exact keepsUncached_forIn_array _ (fun op _ => keepsUncached_bind
        (keepsUncached_processVoluntaryExit op) (fun _ => keepsUncached_pure _))
        body.voluntaryExits.val _
    | exact keepsUncached_forIn_array _ (fun op _ => keepsUncached_bind
        (keepsUncached_processBlsToExecutionChange op) (fun _ => keepsUncached_pure _))
        body.blsToExecutionChanges.val _
    | exact keepsUncached_forIn_array _ (fun op _ => keepsUncached_bind
        (keepsUncached_processPayloadAttestation op) (fun _ => keepsUncached_pure _))
        body.payloadAttestations.val _
    | refine keepsUncached_bind ?_ (fun _ => ?_)

end

end EthCLSpecs.Proofs.Heze
