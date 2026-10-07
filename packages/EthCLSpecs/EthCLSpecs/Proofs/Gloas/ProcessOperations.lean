import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Gloas.ProcessOperations`: Gloas coordinator sequencing

Public declarations live in `EthCLSpecs.Proofs.Gloas`. At `GloasRun`, the
runner every Gloas proof here pins to, they establish three facts about Gloas
`processOperations`, the operations coordinator inside `processBlock`:

* `processOperations_eq_seq` equates the coordinator to the opening deposit
  assertion followed by six operation-family folds in implementation order.
* `processOperations_nonempty_deposits_error` shows that non-empty in-block
  deposits fail that assertion immediately, for any pre-state value.
* `processOperations_run_ok_iff` characterizes success as empty deposits plus
  the six folds succeeding as one sequence.

The implementation's `for op in ops do handler op` loops elaborate to `forIn`
over `SSZList`. This module names that fold `processOperationsForM`
(`ForM.forM ops.val handler`) and rewrites each loop to it, so the coordinator
equation and the success characterization speak in named folds rather than raw
`forIn` terms.

Statements bind plain `BeaconState` values and read the runs through `runPure`.
The handlers stay opaque, so the intermediate states between the six folds stay
at the box and no theorem names them: an opaque handler may return any box
flavour, and `runPure` reads only the view, which is exactly what threads
through the coordinator's binds. That is why the success characterization
states the six-fold sequence as the one composite `processOperationsLoops` run
rather than as five intermediate states.

A rejecting run returns the error alone at this monad, with no state attached,
so there is nothing to say about how far a failing run got, and no theorem
here tries to.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag CryptoBackend SpecReject SSZList)
open scoped EthCLLib.Spec
open EthCLSpecs.Gloas (Preset Config)
open EthCLSpecs.Gloas (
  State BeaconState BeaconBlockBody processOperations
  processProposerSlashing processAttesterSlashing processAttestation
  processVoluntaryExit processBlsToExecutionChange processPayloadAttestation)
open EthCLSpecs.Proofs (runPure runPure_eq)

section
variable [Preset] [HasherTag]

/-- Left-to-right monadic fold of a body's operation list through its handler.
Definitionally `ForM.forM ops.val handler`, which is
`ops.val.foldlM (fun _ => handler) ⟨⟩`. This is the `forIn` expression Lean
emits for each `for op in ops do handler op` inside `processOperations` (the
`SSZList` instance delegates to `Array`, and an always-yielding body folds). -/
abbrev processOperationsForM
    {α : Type} {cap : Nat}
    (ops : SSZList α cap) (handler : α → GloasRun Unit) :
    GloasRun Unit :=
  ForM.forM ops.val handler

/-- `(fun _ => a) <$> x` equals `x >>= fun _ => pure a` at `GloasRun`. -/
private theorem map_const_eq_bind_pure :
    ∀ {α β : Type} (x : GloasRun α) (a : β),
      (fun _ => a) <$> x = (x >>= fun _ => pure a) := by
  intro α β x a
  simp [Functor.map]

/-- The elaborated `forIn` body of `for op in ops do handler op` equals
`processOperationsForM`. -/
private theorem forIn_ops_eq_processOperationsForM :
    ∀ {α : Type} {cap : Nat} (ops : SSZList α cap)
      (handler : α → GloasRun Unit),
      forIn ops PUnit.unit (fun op (_ : PUnit) => do
          handler op
          pure (ForInStep.yield PUnit.unit)) =
        processOperationsForM ops handler := by
  intro α cap ops handler
  -- `SSZList.ForIn` delegates to the underlying array.
  show forIn ops.val PUnit.unit
      (fun op (_ : PUnit) =>
        handler op >>= fun _ => pure (ForInStep.yield PUnit.unit)) =
    ForM.forM ops.val handler
  have hbody :
      (fun op (_ : PUnit) =>
        handler op >>= fun _ => pure (ForInStep.yield PUnit.unit)) =
      (fun a (_ : PUnit) =>
        (fun _ => ForInStep.yield PUnit.unit) <$> handler a) := by
    funext op _; rw [map_const_eq_bind_pure]
  rw [hbody, Array.forIn_yield_eq_foldlM
    (f := fun a (_ : PUnit) => handler a)
    (g := fun (_ : α) (_ : PUnit) (_ : PUnit) => PUnit.unit)]
  simp only [ForM.forM, Array.forM, map_const_eq_bind_pure, bind_pure_unit]

section
variable [Config] [CryptoBackend]

/-- Structural coordinator equation: `processOperations` equals the deposit
assert followed by the six operation-family folds in implementation order. The
deposit-gate error and successful-run characterizations follow from this
equation. Handlers stay opaque and may modify state; this theorem does not claim
that other state fields remain unchanged. -/
@[characterizes EthCLSpecs.Gloas.processOperations]
theorem processOperations_eq_seq :
    ∀ (body : BeaconBlockBody),
      processOperations (StateTransition := GloasRun) body = (do
        assert (body.deposits.size == 0)
        processOperationsForM body.proposerSlashings processProposerSlashing
        processOperationsForM body.attesterSlashings processAttesterSlashing
        processOperationsForM body.attestations processAttestation
        processOperationsForM body.voluntaryExits processVoluntaryExit
        processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
        processOperationsForM body.payloadAttestations processPayloadAttestation) := by
  intro body
  unfold processOperations
  simp only [forIn_ops_eq_processOperationsForM, bind_pure_unit]

/-- The six family folds as a single `GloasRun` action. -/
private abbrev processOperationsLoops
    (body : BeaconBlockBody) : GloasRun Unit := do
  processOperationsForM body.proposerSlashings processProposerSlashing
  processOperationsForM body.attesterSlashings processAttesterSlashing
  processOperationsForM body.attestations processAttestation
  processOperationsForM body.voluntaryExits processVoluntaryExit
  processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
  processOperationsForM body.payloadAttestations processPayloadAttestation

/-- After a passing deposit assert, `processOperations` is the six loops, as an
equation between actions: the assert's gate contributes nothing to the state,
so the two actions are equal, not merely equal at each `.run`. -/
private theorem processOperations_eq_loops_of_empty (body : BeaconBlockBody)
    (htrue : (body.deposits.size == 0) = true) :
    (processOperations (StateTransition := GloasRun) body) = processOperationsLoops body := by
  rw [processOperations_eq_seq]
  simp [htrue, processOperationsLoops]

/-- Deposit-gate characterization: non-empty in-block deposits fail the opening
assert immediately, from any pre-state value. The error is an `assert`
constructor; its diagnostic string is existential and unpinned in the statement.

A reject at this monad carries no state. Where the `EStateM` spelling of this
theorem had to *claim* that the gate preserved the pre-state (`EStateM` keeps
whatever state a failing run had reached, and only this opening gate was known
to have reached none), `StateT` over `Except` returns the error alone. So the
statement no longer mentions a post-state, and the same silence covers a later
handler failure, which is why no companion theorem is owed for those. -/
theorem processOperations_nonempty_deposits_error :
    ∀ (v : BeaconState) (body : BeaconBlockBody),
      body.deposits.size ≠ 0 →
      ∃ descr : String,
        runPure (processOperations (StateTransition := GloasRun) body) v
          = .error (.assert descr) := by
  intro v body hne
  have hfalse : (body.deposits.size == 0) = false :=
    beq_eq_false_iff_ne.2 hne
  rw [runPure_eq, processOperations_eq_seq]
  simp only [hfalse, SpecReject.assert]
  refine ⟨_, rfl⟩

/-- Exact success ↔: `processOperations` succeeds on the uncached box of `v`
with post-value `w` iff deposits are empty and the six operation-family loops
succeed as one sequence from `v`. The handlers stay opaque, so the intermediate
states between the folds stay at the box: `runPure` reads only each fold's
post-state view, and the view is all that threads through the coordinator's
binds. This is a coordinator sequencing characterization rather than complete
correctness of operation processing. -/
@[characterizes EthCLSpecs.Gloas.processOperations]
theorem processOperations_run_ok_iff :
    ∀ (v w : BeaconState) (body : BeaconBlockBody),
      runPure (processOperations (StateTransition := GloasRun) body) v = .ok ((), w) ↔
        body.deposits.size = 0 ∧
        runPure (processOperationsLoops body) v = .ok ((), w) := by
  intro v w body
  constructor
  · intro hok
    rw [runPure_eq] at hok
    cases hrun : (processOperations (StateTransition := GloasRun) body).run (pureState v) with
    | error e =>
      rw [hrun] at hok
      simp only [Except.map] at hok
      simp at hok
    | ok p =>
      obtain ⟨_, s⟩ := p
      rw [hrun] at hok
      cases hbeq : body.deposits.size == 0 with
      | false =>
        rw [processOperations_eq_seq, hbeq] at hrun
        simp [run_throw, except_bind_error, SpecReject.assert] at hrun
      | true =>
        refine ⟨beq_iff_eq.mp hbeq, ?_⟩
        rw [runPure_eq, ← processOperations_eq_loops_of_empty body hbeq, hrun]
        exact hok
  · rintro ⟨hsize, hloops⟩
    rw [processOperations_eq_loops_of_empty body (beq_iff_eq.mpr hsize)]
    exact hloops

end
end

end EthCLSpecs.Proofs.Gloas
