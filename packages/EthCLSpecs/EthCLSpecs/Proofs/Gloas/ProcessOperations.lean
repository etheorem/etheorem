import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Proofs.Gloas.KeepsUncached
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
  the six folds succeeding in order over five plain intermediate values.

The implementation's `for op in ops do handler op` loops elaborate to `forIn`
over `SSZList`. This module names that fold `processOperationsForM`
(`ForM.forM ops.val handler`) and rewrites each loop to it, so the coordinator
equation and the success characterization speak in named folds rather than raw
`forIn` terms.

Statements bind plain `BeaconState` values and read the runs through `runPure`.
The success characterization splits over five plain intermediate values
`u1 ... u5`: empty deposits, then one `runPure` fact per operation-family loop,
each loop's post-state a plain value. The fact behind the split is `KeepsUncached`
(`Proofs/Gloas/KeepsUncached.lean`): every one of the six handlers keeps the
flavour, so `runPure_bind_of_keepsUncached` names each fold's post-state as a
plain value, and the six loop facts `keepsUncached_forM_*` carry it to the
folds.

A rejecting run returns the error alone at this monad, with no state attached,
so there is nothing to say about how far a failing run got, and no theorem
here tries to say anything about one.
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
open EthCLSpecs.Proofs (runPure runPure_eq KeepsUncached
  keepsUncached_forM_array runPure_bind_of_keepsUncached)
open SizzLean.Proofs (view_uncachedBox)

section
variable [Preset] [HasherTag]

/-- Left-to-right monadic fold of a body's operation list through its handler.
Definitionally `ForM.forM ops.val handler`, which is
`ops.val.foldlM (fun _ => handler) \</\>`. This is the `forIn` expression Lean
emits for each `for op in ops do handler op` inside `processOperations` (the
`SSZList` instance delegates to `Array`, and an always-yielding body folds). -/
abbrev processOperationsForM
    {α : Type} {cap : Nat}
    (ops : SSZList α cap) (handler : α -> GloasRun Unit) :
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

/-- The six family loops as a single `GloasRun` action. -/
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

set_option linter.unusedSectionVars false in
/-- The six family loops keep the flavour, one fact per loop, each through
`keepsUncached_forM_array` and its handler's own `KeepsUncached` lemma. -/
theorem keepsUncached_forM_proposerSlashings [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) :
    KeepsUncached (processOperationsForM body.proposerSlashings processProposerSlashing) :=
  keepsUncached_forM_array processProposerSlashing
    (fun a => keepsUncached_processProposerSlashing a) body.proposerSlashings

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
theorem keepsUncached_forM_attesterSlashings [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) :
    KeepsUncached (processOperationsForM body.attesterSlashings processAttesterSlashing) :=
  keepsUncached_forM_array processAttesterSlashing
    (fun a => keepsUncached_processAttesterSlashing a) body.attesterSlashings

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
theorem keepsUncached_forM_attestations [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) :
    KeepsUncached (processOperationsForM body.attestations processAttestation) :=
  keepsUncached_forM_array processAttestation
    (fun a => keepsUncached_processAttestation a) body.attestations

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
theorem keepsUncached_forM_voluntaryExits [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) :
    KeepsUncached (processOperationsForM body.voluntaryExits processVoluntaryExit) :=
  keepsUncached_forM_array processVoluntaryExit
    (fun a => keepsUncached_processVoluntaryExit a) body.voluntaryExits

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
theorem keepsUncached_forM_blsToExecutionChanges [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) :
    KeepsUncached (processOperationsForM body.blsToExecutionChanges
      processBlsToExecutionChange) :=
  keepsUncached_forM_array processBlsToExecutionChange
    (fun a => keepsUncached_processBlsToExecutionChange a) body.blsToExecutionChanges

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
theorem keepsUncached_forM_payloadAttestations [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) :
    KeepsUncached (processOperationsForM body.payloadAttestations processPayloadAttestation) :=
  keepsUncached_forM_array processPayloadAttestation
    (fun a => keepsUncached_processPayloadAttestation a) body.payloadAttestations

/-- Exact success ↔: `processOperations` succeeds on the uncached box of `v`
with post-value `w` iff deposits are empty and the six operation-family loops
succeed in order over five plain intermediate values `u1 ... u5`. The forward
direction names each fold's post-box as `pureState` of a plain value through the
loop's `KeepsUncached` fact; the reverse chains `runPure_bind_of_keepsUncached`
over the six folds. This is a coordinator sequencing characterization rather
than complete correctness of operation processing. -/
@[characterizes EthCLSpecs.Gloas.processOperations]
theorem processOperations_run_ok_iff :
    ∀ (v w : BeaconState) (body : BeaconBlockBody),
      runPure (processOperations (StateTransition := GloasRun) body) v = .ok ((), w) ↔
        body.deposits.size = 0 ∧
        ∃ u1 u2 u3 u4 u5 : BeaconState,
          runPure (processOperationsForM body.proposerSlashings
              processProposerSlashing) v = .ok ((), u1) ∧
          runPure (processOperationsForM body.attesterSlashings
              processAttesterSlashing) u1 = .ok ((), u2) ∧
          runPure (processOperationsForM body.attestations processAttestation) u2 = .ok ((), u3) ∧
          runPure (processOperationsForM body.voluntaryExits processVoluntaryExit) u3 = .ok ((), u4) ∧
          runPure (processOperationsForM body.blsToExecutionChanges
              processBlsToExecutionChange) u4 = .ok ((), u5) ∧
          runPure (processOperationsForM body.payloadAttestations
              processPayloadAttestation) u5 = .ok ((), w) := by
  intro v w body
  have hbeq : (body.deposits.size == 0) = true →
      (processOperations (StateTransition := GloasRun) body) = processOperationsLoops body :=
    processOperations_eq_loops_of_empty body
  have H1 := keepsUncached_forM_proposerSlashings body
  have H2 := keepsUncached_forM_attesterSlashings body
  have H3 := keepsUncached_forM_attestations body
  have H4 := keepsUncached_forM_voluntaryExits body
  have H5 := keepsUncached_forM_blsToExecutionChanges body
  have H6 := keepsUncached_forM_payloadAttestations body
  constructor
  · rintro hok
    rw [runPure_eq] at hok
    cases hbeq0 : (body.deposits.size == 0) with
    | false =>
      rw [processOperations_eq_seq, hbeq0] at hok
      simp [Except.map, run_throw, except_bind_error, SpecReject.assert] at hok
    | true =>
      refine ⟨beq_iff_eq.mp hbeq0, ?_⟩
      rw [hbeq hbeq0] at hok
      rw [run_bind] at hok
      cases hr1 : (processOperationsForM body.proposerSlashings processProposerSlashing).run (pureState v) with
      | error e => rw [hr1, except_bind_error] at hok; simp [Except.map] at hok
      | ok p1 =>
        obtain ⟨_, s1⟩ := p1
        have hu1 := H1 v () s1 hr1
        rw [hr1, except_bind_ok, hu1] at hok
        simp only [] at hok
        have hF1 : runPure (processOperationsForM body.proposerSlashings processProposerSlashing) v = .ok ((), s1.view) := by
          rw [runPure_eq, hr1, hu1]
          rfl
        rw [run_bind] at hok
        cases hr2 : (processOperationsForM body.attesterSlashings processAttesterSlashing).run (pureState s1.view) with
        | error e => rw [hr2, except_bind_error] at hok; simp [Except.map] at hok
        | ok p2 =>
          obtain ⟨_, s2⟩ := p2
          have hu2 := H2 s1.view () s2 hr2
          rw [hr2, except_bind_ok, hu2] at hok
          dsimp only at hok
          have hF2 : runPure (processOperationsForM body.attesterSlashings processAttesterSlashing) s1.view = .ok ((), s2.view) := by
            rw [runPure_eq, hr2, hu2]
            rfl
          rw [run_bind] at hok
          cases hr3 : (processOperationsForM body.attestations processAttestation).run (pureState s2.view) with
          | error e => rw [hr3, except_bind_error] at hok; simp [Except.map] at hok
          | ok p3 =>
            obtain ⟨_, s3⟩ := p3
            have hu3 := H3 s2.view () s3 hr3
            rw [hr3, except_bind_ok, hu3] at hok
            dsimp only at hok
            have hF3 : runPure (processOperationsForM body.attestations processAttestation) s2.view = .ok ((), s3.view) := by
              rw [runPure_eq, hr3, hu3]
              rfl
            rw [run_bind] at hok
            cases hr4 : (processOperationsForM body.voluntaryExits processVoluntaryExit).run (pureState s3.view) with
            | error e => rw [hr4, except_bind_error] at hok; simp [Except.map] at hok
            | ok p4 =>
              obtain ⟨_, s4⟩ := p4
              have hu4 := H4 s3.view () s4 hr4
              rw [hr4, except_bind_ok, hu4] at hok
              dsimp only at hok
              have hF4 : runPure (processOperationsForM body.voluntaryExits processVoluntaryExit) s3.view = .ok ((), s4.view) := by
                rw [runPure_eq, hr4, hu4]
                rfl
              rw [run_bind] at hok
              cases hr5 : (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run (pureState s4.view) with
              | error e => rw [hr5, except_bind_error] at hok; simp [Except.map] at hok
              | ok p5 =>
                obtain ⟨_, s5⟩ := p5
                have hu5 := H5 s4.view () s5 hr5
                rw [hr5, except_bind_ok, hu5] at hok
                dsimp only at hok
                have hF5 : runPure (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange) s4.view = .ok ((), s5.view) := by
                  rw [runPure_eq, hr5, hu5]
                  rfl
                cases hr6 : (processOperationsForM body.payloadAttestations processPayloadAttestation).run (pureState s5.view) with
                | error e => rw [hr6] at hok; simp [Except.map] at hok
                | ok p6 =>
                  obtain ⟨_, s6⟩ := p6
                  rw [hr6] at hok
                  have hu6 := H6 s5.view () s6 hr6
                  simp only [Except.map] at hok
                  injection hok with h1
                  injection h1 with _ heq
                  refine ⟨s1.view, s2.view, s3.view, s4.view, s5.view,
                    hF1, hF2, hF3, hF4, hF5, ?_⟩
                  rw [runPure_eq, hr6]
                  simp only [Except.map]
                  rw [heq]
  · rintro ⟨hsize, u1, u2, u3, u4, u5, hu1, hu2, hu3, hu4, hu5, hu6⟩
    rw [hbeq (beq_iff_eq.mpr hsize)]
    rw [runPure_bind_of_keepsUncached H1 v]
    rw [hu1, except_bind_ok]
    simp only []
    rw [runPure_bind_of_keepsUncached H2 u1]
    rw [hu2, except_bind_ok]
    simp only []
    rw [runPure_bind_of_keepsUncached H3 u2]
    rw [hu3, except_bind_ok]
    simp only []
    rw [runPure_bind_of_keepsUncached H4 u3]
    rw [hu4, except_bind_ok]
    simp only []
    rw [runPure_bind_of_keepsUncached H5 u4]
    rw [hu5, except_bind_ok]
    simp only []
    exact hu6
end
end

end EthCLSpecs.Proofs.Gloas
