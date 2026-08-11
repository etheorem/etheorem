import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Proofs.Run

/-!
# `EthCLSpecs.Proofs.ProcessOperations`: Gloas coordinator sequencing

Public declarations live in `EthCLSpecs.Proofs.Gloas`. At `GloasRun`, the
runner every Gloas proof here pins to, they establish three facts about Gloas
`processOperations`, the operations coordinator inside `processBlock`:

* `processOperations_eq_seq` equates the coordinator to the opening deposit
  assertion followed by six operation-family folds in implementation order.
* `processOperations_nonempty_deposits_error` shows that non-empty in-block
  deposits fail that assertion immediately and leave the pre-state unchanged.
* `processOperations_run_ok_iff` characterizes success as empty deposits plus
  those six folds succeeding in sequence.

The implementation's `for op in ops do handler op` loops elaborate to `forIn`
over `SSZList`. This module names that fold `processOperationsForM`
(`ForM.forM ops.val handler`) and rewrites each loop to it, so the coordinator
equation and the success characterization speak in named folds rather than raw
`forIn` terms.

On the success path, each `GloasRun Unit` bind unpacks through
`run_bind_unit_ok_iff` into an intermediate state. The successful-run theorem
threads five such states between the six folds, with the caller's `post` as the
final state.

Handlers stay opaque: the theorems constrain sequencing and the deposit gate,
not per-operation postconditions. Only the opening deposit assertion is proved
to preserve `pre` on failure. Later handler failures leave whatever state
`EStateM` retained after earlier successful steps; this module leaves those
states uncharacterized.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag CryptoBackend SpecReject SSZList)
open scoped EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config)
open EthCLSpecs.Gloas (
  State BeaconBlockBody processOperations
  processProposerSlashing processAttesterSlashing processAttestation
  processVoluntaryExit processBlsToExecutionChange processPayloadAttestation)

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

/-- `(fun _ => a) <$> x` equals `x >>= fun _ => pure a` on `EStateM`. -/
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

/-- Success of `x >>= f` on `GloasRun Unit` unpacks to an intermediate
state where `x` succeeded and `f` continued from there. -/
private theorem run_bind_unit_ok_iff :
    ∀ (x : GloasRun Unit) (f : Unit → GloasRun Unit)
      (s post : State),
      (x >>= f).run s = .ok () post ↔
        ∃ s', x.run s = .ok () s' ∧ (f ()).run s' = .ok () post := by
  intro x f s post
  cases hx : x s with
  | ok u s' =>
    cases u
    simp [EStateM.run, Bind.bind, EStateM.bind, hx]
  | error e s' =>
    simp [EStateM.run, Bind.bind, EStateM.bind, hx]

section
variable [Config] [CryptoBackend]

/-- Structural coordinator equation: `processOperations` equals the deposit
assert followed by the six operation-family folds in implementation order. The
deposit-gate error and successful-run characterizations follow from this
equation. Handlers stay opaque and may modify state; this theorem does not claim
that other state fields remain unchanged. -/
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

/-- Deposit-gate characterization: non-empty in-block deposits fail the opening
assertion immediately. The error is an `assert` constructor; its diagnostic
string is existential and unpinned in the statement. Only this initial gate is
claimed to preserve `pre`. Later handler failure states are not characterized
here; `EStateM` retains state changes made before a failure rather than rolling
them back. -/
theorem processOperations_nonempty_deposits_error :
    ∀ (body : BeaconBlockBody) (pre : State),
      body.deposits.size ≠ 0 →
      ∃ descr : String,
        (processOperations (StateTransition := GloasRun) body).run pre =
          .error (.assert descr) pre := by
  intro body pre hne
  rw [processOperations_eq_seq]
  have hfalse : (body.deposits.size == 0) = false :=
    beq_eq_false_iff_ne.2 hne
  simp [hfalse, EStateM.run, Bind.bind, EStateM.bind, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw, SpecReject.assert]

/-- The six family folds as a single `GloasRun` action. -/
private abbrev processOperationsLoops
    (body : BeaconBlockBody) : GloasRun Unit := do
  processOperationsForM body.proposerSlashings processProposerSlashing
  processOperationsForM body.attesterSlashings processAttesterSlashing
  processOperationsForM body.attestations processAttestation
  processOperationsForM body.voluntaryExits processVoluntaryExit
  processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
  processOperationsForM body.payloadAttestations processPayloadAttestation

/-- `processOperationsLoops` is the six `processOperationsForM` steps in bind form. -/
private theorem processOperationsLoops_eq_binds :
    ∀ (body : BeaconBlockBody),
      processOperationsLoops body =
        (processOperationsForM body.proposerSlashings processProposerSlashing >>= fun _ =>
         processOperationsForM body.attesterSlashings processAttesterSlashing >>= fun _ =>
         processOperationsForM body.attestations processAttestation >>= fun _ =>
         processOperationsForM body.voluntaryExits processVoluntaryExit >>= fun _ =>
         processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange >>= fun _ =>
         processOperationsForM body.payloadAttestations processPayloadAttestation) := by
  intro body
  rfl

/-- Unpack success of the six loops into the five intermediate states plus `post`. -/
private theorem processOperationsLoops_run_ok_iff :
    ∀ (body : BeaconBlockBody) (pre post : State),
      (processOperationsLoops body).run pre = .ok () post ↔
        ∃ afterproposers afterattesters afterattestations afterexits afterchanges : State,
          (processOperationsForM body.proposerSlashings processProposerSlashing).run pre =
            .ok () afterproposers ∧
          (processOperationsForM body.attesterSlashings processAttesterSlashing).run
              afterproposers =
            .ok () afterattesters ∧
          (processOperationsForM body.attestations processAttestation).run
              afterattesters =
            .ok () afterattestations ∧
          (processOperationsForM body.voluntaryExits processVoluntaryExit).run
              afterattestations =
            .ok () afterexits ∧
          (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run
              afterexits =
            .ok () afterchanges ∧
          (processOperationsForM body.payloadAttestations processPayloadAttestation).run
              afterchanges =
            .ok () post := by
  intro body pre post
  rw [processOperationsLoops_eq_binds]
  simp only [run_bind_unit_ok_iff, exists_and_left]


/-- After a successful deposit assert, `processOperations` is the six loops. -/
private theorem processOperations_run_eq_loops :
    ∀ (body : BeaconBlockBody) (pre : State),
      (body.deposits.size == 0) = true →
      (processOperations (StateTransition := GloasRun) body).run pre =
        (processOperationsLoops body).run pre := by
  intro body pre htrue
  rw [processOperations_eq_seq]
  simp [htrue, EStateM.run, Bind.bind, EStateM.bind, pure, EStateM.pure,
    processOperationsLoops]

/-- Exact success ↔: `processOperations` succeeds iff deposits are empty and the
six operation-family loops succeed sequentially, each from the preceding loop's
resulting state. Five existential intermediate states; `post` is the supplied
final state. Handlers stay opaque, so this is a coordinator sequencing
characterization rather than complete correctness of operation processing. -/
theorem processOperations_run_ok_iff :
    ∀ (body : BeaconBlockBody) (pre post : State),
      (processOperations (StateTransition := GloasRun) body).run pre =
          .ok () post ↔
        body.deposits.size = 0 ∧
        ∃ afterproposers afterattesters afterattestations afterexits afterchanges : State,
          (processOperationsForM body.proposerSlashings processProposerSlashing).run pre =
            .ok () afterproposers ∧
          (processOperationsForM body.attesterSlashings processAttesterSlashing).run
              afterproposers =
            .ok () afterattesters ∧
          (processOperationsForM body.attestations processAttestation).run
              afterattesters =
            .ok () afterattestations ∧
          (processOperationsForM body.voluntaryExits processVoluntaryExit).run
              afterattestations =
            .ok () afterexits ∧
          (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run
              afterexits =
            .ok () afterchanges ∧
          (processOperationsForM body.payloadAttestations processPayloadAttestation).run
              afterchanges =
            .ok () post := by
  intro body pre post
  constructor
  · intro hok
    cases hbeq : body.deposits.size == 0 with
    | false =>
      rw [processOperations_eq_seq] at hok
      simp [hbeq, EStateM.run, Bind.bind, EStateM.bind, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw, SpecReject.assert] at hok
    | true =>
      refine ⟨beq_iff_eq.mp hbeq, ?_⟩
      have hloops : (processOperationsLoops body).run pre = .ok () post := by
        rwa [← processOperations_run_eq_loops body pre hbeq]
      exact (processOperationsLoops_run_ok_iff body pre post).mp hloops
  · intro ⟨hsize, hloops⟩
    have htrue : (body.deposits.size == 0) = true := beq_iff_eq.mpr hsize
    have hok : (processOperationsLoops body).run pre = .ok () post :=
      (processOperationsLoops_run_ok_iff body pre post).mpr hloops
    rwa [processOperations_run_eq_loops body pre htrue]

end
end



end EthCLSpecs.Proofs.Gloas
