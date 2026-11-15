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

The Stage 2 `Gwei := CLUint64` port moved the churn limits, the churn reservation, and the
balance sums onto checked `Gwei` arithmetic. A checked expression the body binds under `←`
reaches the proof as `liftM c` for one `c : Checked Gwei` value, so the proofs peel it as
one leaf: `.ok` is `pure`, `.error` raises through `liftErr` as the `.arithmetic` fault,
and neither arm writes the state. The four private facts in the first section state that
leaf and its two run equations; they stay private so nothing downstream depends on this
file's tactic surface.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag CryptoBackend sszGetIdx ErrorConv)
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
  run_sszGetIdx_some run_sszGetIdx_none run_sszGetIdx_none_pos keepsUncached_sszGetIdx
  run_bind_inv ite_bind pos?_nat_some pos?_nat_none pos?_sszList_some
  pos?_progressiveList_some pos?_clUint64_some pos?_clUint64_none
  pureState_forIn_range_id)

open SizzLean.Proofs (view_uncachedBox)
open SizzLean (SSZRepr)
open SizzLean.Cache

/-! ## The `liftM (c : Checked …)` leaf

The checked-arithmetic ports turn every bound arithmetic expression into `liftM c` for
one `c : Checked α` value (`CLUint.lean`'s `MonadLift (Except ArithFault) m` instance). At
the pure runner that lift is one leaf: the `.ok` arm is `pure`, the `.error` arm raises
through `liftErr` as the `.arithmetic` fault, and neither arm writes the state. These four
private facts are the leaf pair the closure lemmas cannot see and the two run equations
the loop-body proofs peel with. They stay private so nothing downstream depends on this
file's tactic surface. -/

/-- `.run` of `liftM` on a `Checked` success: the value, with the state passed through. -/
private theorem run_liftM_ok {σ α : Type} (a : α) (s : σ) :
    (liftM (Except.ok a : EthCLLib.Spec.Checked α)
      : StateT σ (Except EthCLLib.Spec.StateTransitionError) α).run s = .ok (a, s) := rfl

/-- `.run` of `liftM` on a `Checked` fault: the `.arithmetic` fault carrying the exact
`reprStr` payload, and no state. -/
private theorem run_liftM_error {σ α : Type} (e : EthCLLib.Spec.ArithFault) (s : σ) :
    (liftM (Except.error e : EthCLLib.Spec.Checked α)
      : StateT σ (Except EthCLLib.Spec.StateTransitionError) α).run s
      = .error (EthCLLib.Spec.StateTransitionError.arithmetic (reprStr e)) :=
  rfl

/-- `KeepsUncached` leaf for a lifted `Checked` value: `.ok` is `pure` and `.error` is a
`liftErr` reject, so neither arm writes the state. The `liftM` is spelled with its
`MonadLift` instance explicit, the spelling the body's `let x ← c` desugars to once the
forkdef's `MonadExceptOf` hypothesis is instantiated at the pure runner. -/
private theorem keepsUncached_liftChecked {T α : Type} [SSZRepr T] [HasherTag]
    (c : EthCLLib.Spec.Checked α) :
    KeepsUncached (act := @liftM (Except EthCLLib.Spec.ArithFault)
      (StateT (SSZ.Box HasherTag.H T) (Except EthCLLib.Spec.StateTransitionError))
      inferInstance α c) := by
  cases c with
  | ok b => exact keepsUncached_pure _
  | error e =>
    exact keepsUncached_liftErr (T := T) (ε := EthCLLib.Spec.StateTransitionError)
      (ε' := EthCLLib.Spec.StateTransitionError)
      (x := Except.error (EthCLLib.Spec.StateTransitionError.arithmetic (reprStr e)))

/-- Per-start leaf for a lifted `Checked` value, the form a locally threaded chain peels
with. -/
private theorem keepsUncachedFrom_liftChecked {T α : Type} [SSZRepr T] [HasherTag]
    (v : T) (c : EthCLLib.Spec.Checked α) :
    KeepsUncachedFrom v (@liftM (Except EthCLLib.Spec.ArithFault)
      (StateT (SSZ.Box HasherTag.H T) (Except EthCLLib.Spec.StateTransitionError))
      inferInstance α c) := by
  cases c with
  | ok b => exact keepsUncachedFrom_pure v b
  | error e =>
    exact keepsUncachedFrom_liftErr (T := T) (ε := EthCLLib.Spec.StateTransitionError)
      (ε' := EthCLLib.Spec.StateTransitionError) v
      (Except.error (EthCLLib.Spec.StateTransitionError.arithmetic (reprStr e)))

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
  -- The checked binds: the churn limit, the reservation pair, the remainder,
  -- each a `liftM` leaf.
  all_goals exact keepsUncached_liftChecked _

/-- `initiateValidatorExit` keeps the flavour: the validator read and the
checked withdrawability sum are `liftErr`-shaped, the early-return gate is an
`if`, and the write is `modValidator` through the record update. -/
theorem keepsUncached_initiateValidatorExit (i : ValidatorIndex) :
    KeepsUncached (initiateValidatorExit (StateTransition := GloasRun) i) := by
  unfold initiateValidatorExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached
  -- The checked leaves are the churn callee's own binds (exit candidate, churn
  -- limit, reservation, remainder) plus the withdrawability sum, each a `liftM`
  -- leaf the unit flip produced.
  all_goals exact keepsUncached_liftChecked _

/-- The Gloas copy of `processVoluntaryExit` keeps the flavour: six pure
validation gates, one checked read, and `initiateValidatorExit`, whose own
lemma carries the write. -/
theorem keepsUncached_processVoluntaryExit (sve : SignedVoluntaryExit) :
    KeepsUncached (processVoluntaryExit (StateTransition := GloasRun) sve) := by
  unfold processVoluntaryExit
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  keeps_uncached
  -- The pending-balance fold and the checked-`Gwei` binds of the exit path.
  all_goals exact keepsUncached_liftChecked _

/-- `getPtc` keeps the flavour: it takes the state as an explicit argument, and
its body reads and gates only, through checked ops and asserts. -/
theorem keepsUncached_getPtc (state : BeaconState) (slot : EthCLSpecs.Gloas.Slot) :
    KeepsUncached (getPtc (StateTransition := GloasRun) (pureState state) slot) := by
  unfold getPtc
  keeps_uncached
  -- The checked `Epoch` binds: the `nextEpoch` add in the `if`-branch, and the
  -- else-branch's five-step offset chain.
  all_goals exact keepsUncached_liftChecked _

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
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind ?ca (fun _ midState₂ => ?_)
  -- `attestedSlot ← data.slot + 1`: one checked-`Slot` leaf.
  exact keepsUncachedFrom_liftChecked midState₁ _
  refine keepsUncachedFrom_bind ?g2 (fun _ midState₃ => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind ?gi (fun indexed midState₄ => ?_)
  exact keepsUncached_iff_forall_from.mp (keepsUncached_getIndexedPayloadAttestation state pa) _
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
      (fun _ => keepsUncachedFrom_throw _ _)

/-- A bind on `liftErr`'s success branch is the continuation: `rfl`, since every layer is
an instance projection, a definition, or a match on a constructor. This is the step that
puts `sszGetIdx`'s read element and the run equation's `some` arm on one variable. -/
private theorem bind_liftErr_ok {α β : Type} (v : α) (k : α → GloasRun β) :
    bind (EthCLLib.Spec.liftErr (Except.ok v : Except IndexError α)) k = k v :=
  rfl

/-- The checked sum of the two balances, exactly as the body computes it: `rfl` against
`CLUint64.add`, so the error arm is that operator's own `ArithFault.range`. The run
equation below states its reject through `EthCLSpecs.Proofs.Fulu.increaseFault`, the
payload that `reprStr` produces. -/
private theorem increaseBalance_checkedSum (balance delta : Gwei) :
    (balance + delta : EthCLLib.Spec.Checked Gwei) =
      if balance.val + delta.val < balance.val
      then .error (EthCLLib.Spec.ArithFault.range "+" balance.toPlainInt delta.toPlainInt)
      else .ok (EthCLLib.Spec.CLUint64.trustedOfUInt64 (balance.val + delta.val)) := by
  show (if balance.val + delta.val < balance.val then _ else _) = _
  split
  · rfl
  · rfl

/-- `increaseBalance`, at its Gloas copy, returns `pureState` of the written
value and leaves the threaded state uncached: the run reduces to the same match
the Fulu contract states, with the checked `Gwei` sum as the one rejecting step. -/
theorem returnsUncached_increaseBalance (state : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    ReturnsUncached (increaseBalance (StateTransition := GloasRun) (pureState state) i d) := by
  intro preState b s h
  have hrun : (increaseBalance (StateTransition := GloasRun) (pureState state) i d).run
      (pureState preState)
      = (match state.balances.val[i.toPlainInt]? with
        | none => .error (.outOfBounds 0 state.balances.size)
        | some balance =>
          if balance.val + d.val < balance.val then
            .error (.arithmetic (EthCLSpecs.Proofs.Fulu.increaseFault balance d))
          else
            .ok (modBalance (pureState state) i
              (fun _ => EthCLLib.Spec.CLUint64.trustedOfUInt64 (balance.val + d.val)),
              pureState preState)) := by
    unfold increaseBalance sszGetIdx EthCLLib.Spec.IdxRead.get? EthCLLib.Spec.IdxRead.size
    simp only [view_uncachedBox]
    by_cases hlt : i.toPlainInt < state.balances.size
    · rw [pos?_clUint64_some hlt]
      simp only []
      cases hq : state.balances.val[i.toPlainInt]? with
      | none =>
        have hle : state.balances.val.size ≤ i.toPlainInt := Array.getElem?_eq_none_iff.mp hq
        have hsz : state.balances.size = state.balances.val.size := rfl
        omega
      | some balance =>
        rw [bind_liftErr_ok]
        simp only [increaseBalance_checkedSum]
        by_cases hc : balance.val + d.val < balance.val
        · simp only [ite_eq_left hc]
          rfl
        · simp only [ite_eq_right hc]
          rfl
    · rw [pos?_clUint64_none (Nat.le_of_not_lt hlt),
        Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hlt)]
      simp
      rfl
  cases hu : state.balances.val[i.toPlainInt]? with
  | none => rw [hrun, hu] at h; simp at h
  | some balance =>
    rw [hrun, hu] at h
    dsimp only at h
    by_cases hc : balance.val + d.val < balance.val
    · rw [ite_eq_left hc] at h
      simp at h
    · rw [ite_eq_right hc] at h
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
      = (match state.balances.val[i.toPlainInt]? with
        | none => .error (.outOfBounds 0 state.balances.size)
        | some balance =>
          .ok (modBalance (pureState state) i
            (fun _ => balance.saturatingSub d), pureState preState)) := by
    unfold decreaseBalance sszGetIdx EthCLLib.Spec.IdxRead.get? EthCLLib.Spec.IdxRead.size
    simp only [view_uncachedBox]
    by_cases hlt : i.toPlainInt < state.balances.size
    · rw [pos?_clUint64_some hlt]
      simp only []
      cases hq : state.balances.val[i.toPlainInt]? with
      | none =>
        have hle : state.balances.val.size ≤ i.toPlainInt := Array.getElem?_eq_none_iff.mp hq
        have hsz : state.balances.size = state.balances.val.size := rfl
        omega
      | some balance =>
        simp only [EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
        rfl
    · rw [pos?_clUint64_none (Nat.le_of_not_lt hlt),
        Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hlt)]
      simp
      rfl
  cases hu : state.balances.val[i.toPlainInt]? with
  | none => rw [hrun, hu] at h; simp at h
  | some balance =>
    rw [hrun, hu] at h
    dsimp only at h
    injection h with h1
    injection h1 with h1a h1b
    subst h1a
    subst h1b
    exact ⟨⟨_, rfl⟩, rfl⟩

/-- `slashValidator` keeps the flavour: the reads and the exit write keep it as
the spike lemmas do, and the two threaded states, the local write chain and the
two balance returns, stay uncached through `ReturnsUncached` and
`keepsUncachedFrom_set`. The checked sums the body binds (the withdrawability
add, `slashings +` effective balance, the penalty and whistleblower quotients,
the reward split) peel as `keepsUncachedFrom_liftChecked` leaves. The closing
EIP-7732 loop over the
payment window is a pure `modifyState` writer, and `pureState_forIn_range_id`
carries the flavour through its steps. -/
theorem keepsUncached_slashValidator (i : ValidatorIndex) :
    KeepsUncached (slashValidator (StateTransition := GloasRun) i) := by
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
  -- `withdrawableAt ← epoch + EPOCHS_PER_SLASHINGS_VECTOR`: one checked-`Epoch` leaf
  -- ahead of the slashed leaf; the local `modValidator` write between them is a pure
  -- `let` the unifier sees through.
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₃ _)
    (fun _ midState₃' => ?_)
  -- `slashed ← vget … slashIdx + validator.effectiveBalance`: one checked-`Gwei` leaf.
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₃' _)
    (fun _ midState₄ => ?_)
  -- `state ← decreaseBalance state i (← effectiveBalance / …)`: the penalty quotient is
  -- one checked-`Gwei` leaf, then the mutator's own lemma.
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₄ _)
    (fun penalty midState₅ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ i penalty)
    (fun afterDecrease midState₆ => ?_)
  refine keepsUncachedFrom_bind (v := midState₆) (keepsUncachedFrom_set midState₆ afterDecrease)
    (fun _ midState₇ => ?_)
  refine keepsUncachedFrom_get_bind (fun state' => ?_)
  -- `whistleblowerReward` and `proposerReward`: two checked-`Gwei` leaves.
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked state' _)
    (fun whistleblowerReward midState₈ => ?_)
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₈ _)
    (fun proposerReward midState₉ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ proposerReward)
    (fun afterProposerReward midState₁₀ => ?_)
  -- `whistleblowerReward - proposerReward`: one more checked-`Gwei` leaf, then the second
  -- mutator and the `set` of its return.
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₁₀ _)
    (fun remainder midState₁₁ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ remainder)
    (fun afterWhistleblowerReward midState₁₂ => ?_)
  refine keepsUncachedFrom_bind (keepsUncachedFrom_set midState₁₂ afterWhistleblowerReward)
    (fun _ midState₁₃ => ?_)
  -- The payment loop: each step either rebuilds the record (an uncached box) or passes
  -- the box through, so the whole writer maps `pureState` to `pureState`.
  refine keepsUncached_iff_forall_from.mp (keepsUncached_modify _ (fun v => ?_)) midState₁₃
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
    · -- `bound ← s + SLOTS_PER_HISTORICAL_ROOT`: one checked-`Slot` leaf.
      exact keepsUncached_liftChecked _
    · refine keepsUncached_bind ?g2 (fun _ => ?_)
      · exact keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => keepsUncached_throw _)
      · exact keepsUncached_pure _

theorem keepsUncached_getBlockRoot (state : BeaconState) (epoch : EthCLSpecs.Gloas.Epoch) :
    KeepsUncached (getBlockRoot (StateTransition := GloasRun) (pureState state) epoch) := by
  unfold getBlockRoot
  exact keepsUncached_bind (keepsUncached_liftChecked _)
    (fun _ => keepsUncached_getBlockRootAtSlot state _)

theorem keepsUncached_isAttestationSameSlot (state : BeaconState) (data : EthCLSpecs.Gloas.AttestationData) :
    KeepsUncached (isAttestationSameSlot (StateTransition := GloasRun) (pureState state) data) := by
  unfold isAttestationSameSlot
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind ?sr (fun _ => ?_)
  · exact keepsUncached_getBlockRootAtSlot state _
  · refine keepsUncached_bind ?ps (fun _ => ?_)
    · -- `prevSlot ← data.slot - 1`: one checked-`Slot` leaf; the `slot == 0`
      -- branch above rules out its underflow.
      exact keepsUncached_liftChecked _
    · refine keepsUncached_bind ?pr (fun _ => ?_)
      · exact keepsUncached_getBlockRootAtSlot state _
      · exact keepsUncached_pure _

theorem keepsUncached_getAttestationParticipationFlagIndices (state : BeaconState) (data : EthCLSpecs.Gloas.AttestationData)
    (inclusionDelay : Slot) (parentSlot : Slot) :
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

theorem keepsUncached_processAttestation (att : EthCLSpecs.Gloas.Attestation) (parentSlot : Slot) :
    KeepsUncached (EthCLSpecs.Gloas.processAttestation (StateTransition := GloasRun) att parentSlot) := by
  intro preState
  unfold EthCLSpecs.Gloas.processAttestation
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_bind ?gA (fun _ midState₁ => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind ?gB (fun _ midState₂ => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind ?ca (fun _ midState₃ => ?_)
  -- `inclusionSlot ← data.slot + MIN_ATTESTATION_INCLUSION_DELAY`: one
  -- checked-`Slot` leaf.
  exact keepsUncachedFrom_liftChecked midState₂ _
  refine keepsUncachedFrom_bind ?gC (fun _ midState₄ => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind ?gD (fun _ midState₅ => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _) (fun _ => keepsUncachedFrom_throw _ _)
  -- `let (ok, offset) ← verifyCommitteeCoverage …`: the coverage fold is a
  -- `Checked (Bool × Nat)` value now, so it peels as one checked leaf, and
  -- its two asserts follow it.
  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₅ _)
    (fun _ midState₆ => ?_)
  refine keepsUncachedFrom_bind (T := BeaconState) ?gF (fun _ midState₇ => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
    (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind (T := BeaconState) ?gF2 (fun _ midState₇' => ?_)
  exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
    (fun _ => keepsUncachedFrom_throw _ _)
  refine keepsUncachedFrom_bind (T := BeaconState) ?id (fun _ midState₇'' => ?_)
  -- `inclusionDelay ← state.slot - data.slot`: one checked-`Slot` leaf; the
  -- inclusion assert above rules out its underflow.
  exact keepsUncachedFrom_liftChecked midState₇' _
  refine keepsUncachedFrom_bind (T := BeaconState) ?gf (fun flagIndices midState₈ => ?_)
  · exact keepsUncached_iff_forall_from.mp
      (keepsUncached_getAttestationParticipationFlagIndices state _ _ _) _
  · cases flagIndices with
    | none => exact keepsUncachedFrom_throw_bind _ _
    | some f =>
      · refine keepsUncachedFrom_bind (keepsUncachedFrom_pure midState₈ f) (fun _ midState₉ => ?_)
        refine keepsUncachedFrom_bind ?li (fun idxs midState₁₀ => ?_)
        · exact keepsUncachedFrom_liftErr (v := midState₉)
            (Gloas.getAttestingIndices (pureState state) att)
        · -- The attesting-index list is built purely (a progressive list wraps
          -- the sorted array), so the next effect is the validity assert.
          refine keepsUncachedFrom_bind ?gG (fun _ midState₁₁ => ?_)
          · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_pure _ _)
              (fun _ => keepsUncachedFrom_throw _ _)
          · refine keepsUncachedFrom_bind ?ssL (fun sameSlot midState₁₂ => ?_)
            · exact keepsUncached_iff_forall_from.mp
                (keepsUncached_isAttestationSameSlot state att.data) _
            · refine keepsUncachedFrom_bind ?li2 (fun idxs2 midState₁₃ => ?_)
              · exact keepsUncachedFrom_liftErr (v := midState₁₂)
                  (Gloas.getAttestingIndices (pureState state) att)
              · refine keepsUncachedFrom_forIn_array_bind_P (T := BeaconState) (v := midState₁₃)
                  ?ob ?kt
                  (P := fun (acc : EthCLSpecs.Gloas.State × Gwei × EthCLSpecs.Gloas.Gwei) =>
                    ∃ accState : BeaconState, acc.1 = pureState accState) ?hf ?hk idxs2
                  (pureState state, (0 : Gwei),
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
                    (fun (acc : ForInStep (EthCLSpecs.Gloas.State × Gwei × EthCLSpecs.Gloas.Gwei)) =>
                      ∃ accState : BeaconState, acc.value.1 = pureState accState)
                    (fun r0 s0 h0 => ⟨keepsUncached_ite
                      (fun _ => keepsUncached_sszGetIdx _ _)
                      (fun _ => keepsUncached_sszGetIdx _ _) midState₁₄ r0 s0 h0, trivial⟩)
                    ?hrest r s hrun
                  intro flags0 midState₁₄ _ r s hrun
                  refine keepsUncachedFrom_forIn_range_bind_run_inv
                    (T := BeaconState) (v := midState₁₄)
                    (P := fun (acc : EthCLSpecs.Gloas.State × Gwei × Bool) =>
                      ∃ flagAccState : BeaconState, acc.1 = pureState flagAccState)
                    (Q := fun (acc : ForInStep (EthCLSpecs.Gloas.State × Gwei × EthCLSpecs.Gloas.Gwei)) =>
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
                      cases hq : ((SSZ.Box.view (pureState flagAccState)).currentEpochParticipation).val[vi.toPlainInt]? with
                      | some y =>
                        have hp : EthCLLib.Spec.ToIndex.pos? (vi.toPlainInt)
                            (EthCLLib.Spec.IdxRead.size
                              (SSZ.Box.view (pureState flagAccState)).currentEpochParticipation)
                              = some (vi.toPlainInt) :=
                          pos?_progressiveList_some hq
                        rw [run_sszGetIdx_some _ _ _ hp hq, except_bind_ok] at hrun2
                        -- The flag test is two steps now: the pure membership gate, then
                        -- the checked `hasFlag` bind inside it (the pinned `and`
                        -- short-circuits, so the model binds in its own branch).
                        split at hrun2
                        · rw [run_bind] at hrun2
                          cases hf : (EthCLLib.Spec.hasFlag y cIdx) with
                          | error e =>
                            rw [hf, run_liftM_error, except_bind_error] at hrun2
                            simp at hrun2
                          | ok isSet =>
                            rw [hf, run_liftM_ok, except_bind_ok] at hrun2
                            split at hrun2
                            · rw [run_bind] at hrun2
                              cases ha : (EthCLLib.Spec.addFlag y cIdx) with
                              | error e =>
                                rw [ha, run_liftM_error, except_bind_error] at hrun2
                                simp at hrun2
                              | ok updated =>
                                rw [ha, run_liftM_ok, except_bind_ok] at hrun2
                                rw [run_bind] at hrun2
                                cases hm : (EthCLSpecs.Gloas.getBaseReward (pureState state) vi).mapError
                                  (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
                                | error e =>
                                  rw [run_liftErr_of_error _ _ hm, except_bind_error] at hrun2
                                  simp at hrun2
                                | ok rw =>
                                  rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at hrun2
                                  -- `proposerNum += baseReward * weight`: one checked-`Gwei`
                                  -- leaf between the base-reward read and the write-back.
                                  rw [run_bind] at hrun2
                                  cases hn : (p2 + rw *
                                      EthCLSpecs.Gloas.Const.participationFlagWeights[cIdx]! :
                                      EthCLLib.Spec.Checked EthCLLib.Spec.CLUint64) with
                                  | ok pn' =>
                                    rw [hn, run_liftM_ok, except_bind_ok] at hrun2
                                    rw [run_pure] at hrun2
                                    injection hrun2 with h1
                                    injection h1 with h1a h1b
                                    subst h1a
                                    subst h1b
                                    refine ⟨rfl, ⟨({ flagAccState with
                                      currentEpochParticipation :=
                                        (SSZ.Box.view (pureState flagAccState)).currentEpochParticipation.set!
                                          (vi.toPlainInt) updated }), rfl⟩⟩
                                  | error e =>
                                    rw [hn, run_liftM_error, except_bind_error] at hrun2
                                    simp at hrun2
                            · rw [run_pure] at hrun2
                              injection hrun2 with h1
                              injection h1 with h1a h1b
                              subst h1a
                              subst h1b
                              exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                        · rw [run_pure] at hrun2
                          injection hrun2 with h1
                          injection h1 with h1a h1b
                          subst h1a
                          subst h1b
                          exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                      | none =>
                        -- A miss at the raw `[i]?` read puts the index past the size, so
                        -- `pos?` rejected it and the fault carries the `0` placeholder.
                        have hge : EthCLLib.Spec.IdxRead.size
                            ((SSZ.Box.view (pureState flagAccState)).currentEpochParticipation) ≤ vi.toPlainInt :=
                          Array.getElem?_eq_none_iff.mp hq
                        rw [run_sszGetIdx_none_pos _ _ _ (pos?_nat_none hge),
                          except_bind_error] at hrun2
                        simp at hrun2
                    · rw [run_bind] at hrun2
                      cases hq : ((SSZ.Box.view (pureState flagAccState)).previousEpochParticipation).val[vi.toPlainInt]? with
                      | some y =>
                        have hp : EthCLLib.Spec.ToIndex.pos? (vi.toPlainInt)
                            (EthCLLib.Spec.IdxRead.size
                              (SSZ.Box.view (pureState flagAccState)).previousEpochParticipation)
                              = some (vi.toPlainInt) :=
                          pos?_progressiveList_some hq
                        rw [run_sszGetIdx_some _ _ _ hp hq, except_bind_ok] at hrun2
                        -- The same two-step flag test, previous-epoch branch.
                        split at hrun2
                        · rw [run_bind] at hrun2
                          cases hf : (EthCLLib.Spec.hasFlag y cIdx) with
                          | error e =>
                            rw [hf, run_liftM_error, except_bind_error] at hrun2
                            simp at hrun2
                          | ok isSet =>
                            rw [hf, run_liftM_ok, except_bind_ok] at hrun2
                            split at hrun2
                            · rw [run_bind] at hrun2
                              cases ha : (EthCLLib.Spec.addFlag y cIdx) with
                              | error e =>
                                rw [ha, run_liftM_error, except_bind_error] at hrun2
                                simp at hrun2
                              | ok updated =>
                                rw [ha, run_liftM_ok, except_bind_ok] at hrun2
                                rw [run_bind] at hrun2
                                cases hm : (EthCLSpecs.Gloas.getBaseReward (pureState state) vi).mapError
                                  (ErrorConv.conv (F := EthCLLib.Spec.StateTransitionError)) with
                                | error e =>
                                  rw [run_liftErr_of_error _ _ hm, except_bind_error] at hrun2
                                  simp at hrun2
                                | ok rw =>
                                  rw [run_liftErr_of_ok _ _ hm, except_bind_ok] at hrun2
                                  -- The same checked-`Gwei` leaf, previous-epoch branch.
                                  rw [run_bind] at hrun2
                                  cases hn : (p2 + rw *
                                      EthCLSpecs.Gloas.Const.participationFlagWeights[cIdx]! :
                                      EthCLLib.Spec.Checked EthCLLib.Spec.CLUint64) with
                                  | ok pn' =>
                                    rw [hn, run_liftM_ok, except_bind_ok] at hrun2
                                    rw [run_pure] at hrun2
                                    injection hrun2 with h1
                                    injection h1 with h1a h1b
                                    subst h1a
                                    subst h1b
                                    refine ⟨rfl, ⟨({ flagAccState with
                                      previousEpochParticipation :=
                                        (SSZ.Box.view (pureState flagAccState)).previousEpochParticipation.set!
                                          (vi.toPlainInt) updated }), rfl⟩⟩
                                  | error e =>
                                    rw [hn, run_liftM_error, except_bind_error] at hrun2
                                    simp at hrun2
                            · rw [run_pure] at hrun2
                              injection hrun2 with h1
                              injection h1 with h1a h1b
                              subst h1a
                              subst h1b
                              exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                        · rw [run_pure] at hrun2
                          injection hrun2 with h1
                          injection h1 with h1a h1b
                          subst h1a
                          subst h1b
                          exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                      | none =>
                        -- A miss at the raw `[i]?` read puts the index past the size, so
                        -- `pos?` rejected it and the fault carries the `0` placeholder.
                        have hge : EthCLLib.Spec.IdxRead.size
                            ((SSZ.Box.view (pureState flagAccState)).previousEpochParticipation) ≤ vi.toPlainInt :=
                          Array.getElem?_eq_none_iff.mp hq
                        rw [run_sszGetIdx_none_pos _ _ _ (pos?_nat_none hge),
                          except_bind_error] at hrun2
                        simp at hrun2
                  · intro r1 midState₁₆ hP1 a s3 hrun3
                    obtain ⟨flagAccState, hu1⟩ := hP1
                    rw [hu1] at hrun3
                    split at hrun3
                    · rw [run_bind] at hrun3
                      cases hq : ((SSZ.Box.view (pureState state)).validators).val[vi.toPlainInt]? with
                      | some yv =>
                        have hp : EthCLLib.Spec.ToIndex.pos? (vi.toPlainInt)
                            (EthCLLib.Spec.IdxRead.size
                              (SSZ.Box.view (pureState state)).validators)
                              = some (vi.toPlainInt) :=
                          pos?_progressiveList_some (xs := (SSZ.Box.view (pureState state)).validators)
                            (i := vi.toPlainInt) hq
                        rw [run_sszGetIdx_some _ _ _ hp hq, except_bind_ok] at hrun3
                        -- `weight += effective_balance`: one checked-`Gwei` leaf.
                        rw [run_bind] at hrun3
                        cases hn : (ws + yv.effectiveBalance :
                          EthCLLib.Spec.Checked EthCLLib.Spec.CLUint64) with
                        | ok w' =>
                          rw [hn, run_liftM_ok, except_bind_ok] at hrun3
                          rw [run_pure] at hrun3
                          injection hrun3 with h1
                          injection h1 with h1a h1b
                          subst h1a
                          subst h1b
                          exact ⟨rfl, ⟨flagAccState, rfl⟩⟩
                        | error e =>
                          rw [hn, run_liftM_error, except_bind_error] at hrun3
                          simp at hrun3
                      | none =>
                        -- A miss at the raw `[i]?` read puts the index past the size, so
                        -- `pos?` rejected it and the fault carries the `0` placeholder.
                        have hge : EthCLLib.Spec.IdxRead.size
                            ((SSZ.Box.view (pureState state)).validators) ≤ vi.toPlainInt :=
                          Array.getElem?_eq_none_iff.mp hq
                        rw [run_sszGetIdx_none_pos _ _ _ (pos?_nat_none hge),
                          except_bind_error] at hrun3
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
                  -- `Gwei(proposerNum / proposerDenom)`: one checked-`Gwei` leaf,
                  -- then the mutator and the write-back of its return.
                  refine keepsUncachedFrom_bind (keepsUncachedFrom_liftChecked midState₁₇ _)
                    (fun delta midState₁₈ => ?_)
                  refine returnsUncachedFrom_bind
                    (returnsUncached_increaseBalance _ _ delta) (fun afterIncrease midState₁₉ =>
                      -- The payment write-back on `pureState afterIncrease` reduces to
                      -- `pureState` of the record update, so the value is inferred.
                      keepsUncachedFrom_set midState₁₉ _)

end

end EthCLSpecs.Proofs.Gloas
