import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Gloas.ProcessOperations`: Gloas coordinator sequencing

Public declarations live in `EthCLSpecs.Proofs.Gloas`. At `GloasRun`, the
runner every Gloas proof here pins to, they establish three facts about Gloas
`processOperations`, the operations coordinator inside `processBlock`:

* `processOperations_eq_seq` equates the coordinator to the deposit assertion,
  the six progressive-list length assertions, and the six operation-family
  folds in implementation order. The attestation fold passes `parent_slot`
  (the parent block's slot, new at v1.7.0-beta.4) to each `processAttestation`.
* `processOperations_nonempty_deposits_error` shows that non-empty in-block
  deposits fail that assertion immediately, for any pre-state value.
* `processOperations_run_ok_iff` characterizes success as empty deposits, the
  six length bounds, and the six folds succeeding in order over five plain
  intermediate values.

The implementation's `for op in ops do handler op` loops elaborate to `forIn`
over `ProgressiveList`. This module names that fold `processOperationsForM`
(`ForM.forM ops.val handler`) and rewrites each loop to it, so the coordinator
equation and the success characterization speak in named folds rather than raw
`forIn` terms.

Statements bind plain `BeaconState` values and state each run as `.run` on one.
The success characterization splits over five plain intermediate values,
`afterProposerSlashings` through `afterBlsToExecutionChanges`: empty deposits,
the six length bounds, then one `.run` fact per operation-family loop. Gloas
`State` is the plain `BeaconState`, so `run_bind` splits each bind of the loop
chain, and each loop's post-state is already a plain value.

A rejecting run returns the error alone at this monad, with no state attached,
so there is nothing to say about how far a failing run got, and no theorem
here tries to say anything about one.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag CryptoBackend SpecReject ProgressiveList)
open scoped EthCLLib.Spec
open EthCLSpecs.Gloas (Preset Config)
open EthCLSpecs.Gloas.Const (maxProposerSlashings maxAttesterSlashingsElectra
  maxAttestationsElectra maxVoluntaryExits maxBlsToExecutionChanges maxPayloadAttestations)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas (
  State BeaconState BeaconBlockBody processOperations
  processProposerSlashing processAttesterSlashing processAttestation
  processVoluntaryExit processBlsToExecutionChange processPayloadAttestation)
open EthCLLib.Proofs (run_bind run_throw except_bind_ok except_bind_error)

section
variable [Preset]

/-- Left-to-right monadic fold of a body's operation list through its handler.
Definitionally `ForM.forM ops.val handler`. This is the `forIn` expression Lean
emits for each `for op in ops do handler op` inside `processOperations` (the
`ProgressiveList` instance delegates to `Array`, and an always-yielding body folds). -/
abbrev processOperationsForM
    {α : Type}
    (ops : ProgressiveList α) (handler : α -> GloasRun Unit) :
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
    ∀ {α : Type} (ops : ProgressiveList α)
      (handler : α → GloasRun Unit),
      forIn ops PUnit.unit (fun op (_ : PUnit) => do
          handler op
          pure (ForInStep.yield PUnit.unit)) =
        processOperationsForM ops handler := by
  intro α ops handler
  -- `ProgressiveList.ForIn` delegates to the underlying array.
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
variable [HasherTag] [Config] [CryptoBackend]

/-- Structural coordinator equation: `processOperations` equals the deposit
assert, the six progressive-list length asserts, and the six operation-family
folds, in implementation order. Handlers stay opaque and may modify state; this
theorem does not claim that other state fields remain unchanged. -/
@[characterizes EthCLSpecs.Gloas.processOperations]
theorem processOperations_eq_seq :
    ∀ (body : BeaconBlockBody) (parentSlot : Slot),
      processOperations (StateTransition := GloasRun) body parentSlot = (do
        assert (body.deposits.size == 0)
        assert (body.proposerSlashings.size ≤ Const.maxProposerSlashings)
        assert (body.attesterSlashings.size ≤ Const.maxAttesterSlashingsElectra)
        assert (body.attestations.size ≤ Const.maxAttestationsElectra)
        assert (body.voluntaryExits.size ≤ Const.maxVoluntaryExits)
        assert (body.blsToExecutionChanges.size ≤ Const.maxBlsToExecutionChanges)
        assert (body.payloadAttestations.size ≤ Const.maxPayloadAttestations)
        processOperationsForM body.proposerSlashings processProposerSlashing
        processOperationsForM body.attesterSlashings processAttesterSlashing
        processOperationsForM body.attestations (processAttestation · parentSlot)
        processOperationsForM body.voluntaryExits processVoluntaryExit
        processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
        processOperationsForM body.payloadAttestations processPayloadAttestation) := by
  intro body parentSlot
  unfold processOperations
  simp only [forIn_ops_eq_processOperationsForM, bind_pure_unit]

/-- The six family loops as a single `GloasRun` action. -/
private abbrev processOperationsLoops
    (body : BeaconBlockBody) (parentSlot : Slot) : GloasRun Unit := do
  processOperationsForM body.proposerSlashings processProposerSlashing
  processOperationsForM body.attesterSlashings processAttesterSlashing
  processOperationsForM body.attestations (processAttestation · parentSlot)
  processOperationsForM body.voluntaryExits processVoluntaryExit
  processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
  processOperationsForM body.payloadAttestations processPayloadAttestation

/-- After the deposit assert and the six length asserts pass, `processOperations`
is the six loops. Each passing gate is `pure ()`, so the actions are equal. -/
private theorem processOperations_eq_loops_of_bounds (body : BeaconBlockBody) (parentSlot : Slot)
    (hDep : (body.deposits.size == 0) = true)
    (hProp : body.proposerSlashings.size ≤ maxProposerSlashings)
    (hAttSl : body.attesterSlashings.size ≤ maxAttesterSlashingsElectra)
    (hAtt : body.attestations.size ≤ maxAttestationsElectra)
    (hExit : body.voluntaryExits.size ≤ maxVoluntaryExits)
    (hBls : body.blsToExecutionChanges.size ≤ maxBlsToExecutionChanges)
    (hPay : body.payloadAttestations.size ≤ maxPayloadAttestations) :
    (processOperations (StateTransition := GloasRun) body parentSlot) = processOperationsLoops body parentSlot := by
  rw [processOperations_eq_seq]
  simp [hDep, hProp, hAttSl, hAtt, hExit, hBls, hPay, processOperationsLoops]

/-- Deposit-gate characterization: non-empty in-block deposits fail the opening
assert immediately, from any pre-state value. The error is an `assert`
constructor; its diagnostic string is existential and unpinned in the statement.

A reject at this monad carries no state: `StateT` over `Except` returns the error
alone. So the statement mentions no post-state. The same holds for a later handler
failure, which is why no companion theorem is owed for those. -/
theorem processOperations_nonempty_deposits_error :
    ∀ (preState : BeaconState) (body : BeaconBlockBody) (parentSlot : Slot),
      body.deposits.size ≠ 0 →
      ∃ descr : String,
        (processOperations (StateTransition := GloasRun) body parentSlot).run preState
          = .error (.assert descr) := by
  intro preState body parentSlot hne
  have hfalse : (body.deposits.size == 0) = false :=
    beq_eq_false_iff_ne.2 hne
  rw [processOperations_eq_seq]
  simp only [hfalse, SpecReject.assert]
  refine ⟨_, rfl⟩

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- A run of `x >>= fun _ => y`, with `x` a `Unit` action, succeeds iff `x` succeeds
from `s` into some plain value `mid` and `y` succeeds from `mid`. `run_bind` splits the
run. The `Except` bind then succeeds only on the `.ok` branch of `x`. -/
private theorem run_bind_unit_ok_iff {σ ε β : Type}
    (x : StateT σ (Except ε) Unit) (y : StateT σ (Except ε) β) (s : σ) (b : β) (t : σ) :
    (x >>= fun _ => y).run s = .ok (b, t) ↔
      ∃ mid : σ, x.run s = .ok ((), mid) ∧ y.run mid = .ok (b, t) := by
  rw [run_bind]
  cases hx : x.run s with
  | error e => simp [except_bind_error]
  | ok p =>
    obtain ⟨⟨⟩, mid⟩ := p
    simp [except_bind_ok]

/-- Exact success ↔: `processOperations` succeeds on `preState` with post-value
`postState` iff deposits are empty, the six progressive lists meet their length bounds,
and the six operation-family loops succeed in order over five plain intermediate values,
`afterProposerSlashings` through `afterBlsToExecutionChanges`, each named after the loop
that produced it. Once the gates pass, `run_bind_unit_ok_iff` splits the loop chain at
each of its five binds. This is a coordinator sequencing characterization rather than
complete correctness of operation processing. -/
@[characterizes EthCLSpecs.Gloas.processOperations]
theorem processOperations_run_ok_iff :
    ∀ (preState postState : BeaconState) (body : BeaconBlockBody) (parentSlot : Slot),
      (processOperations (StateTransition := GloasRun) body parentSlot).run preState
          = .ok ((), postState) ↔
        body.deposits.size = 0 ∧
        body.proposerSlashings.size ≤ maxProposerSlashings ∧
        body.attesterSlashings.size ≤ maxAttesterSlashingsElectra ∧
        body.attestations.size ≤ maxAttestationsElectra ∧
        body.voluntaryExits.size ≤ maxVoluntaryExits ∧
        body.blsToExecutionChanges.size ≤ maxBlsToExecutionChanges ∧
        body.payloadAttestations.size ≤ maxPayloadAttestations ∧
        ∃ afterProposerSlashings afterAttesterSlashings afterAttestations
            afterVoluntaryExits afterBlsToExecutionChanges : BeaconState,
          (processOperationsForM body.proposerSlashings processProposerSlashing).run
              preState = .ok ((), afterProposerSlashings) ∧
          (processOperationsForM body.attesterSlashings processAttesterSlashing).run
              afterProposerSlashings = .ok ((), afterAttesterSlashings) ∧
          (processOperationsForM body.attestations (processAttestation · parentSlot)).run
              afterAttesterSlashings = .ok ((), afterAttestations) ∧
          (processOperationsForM body.voluntaryExits processVoluntaryExit).run
              afterAttestations = .ok ((), afterVoluntaryExits) ∧
          (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run
              afterVoluntaryExits = .ok ((), afterBlsToExecutionChanges) ∧
          (processOperationsForM body.payloadAttestations processPayloadAttestation).run
              afterBlsToExecutionChanges = .ok ((), postState) := by
  intro preState postState body parentSlot
  -- Once every gate passes, the coordinator is the loop chain, and the five binds of
  -- that chain split into the five named intermediate values.
  have hLoops :
      (processOperationsLoops body parentSlot).run preState = .ok ((), postState) ↔
        ∃ afterProposerSlashings afterAttesterSlashings afterAttestations
            afterVoluntaryExits afterBlsToExecutionChanges : BeaconState,
          (processOperationsForM body.proposerSlashings processProposerSlashing).run
              preState = .ok ((), afterProposerSlashings) ∧
          (processOperationsForM body.attesterSlashings processAttesterSlashing).run
              afterProposerSlashings = .ok ((), afterAttesterSlashings) ∧
          (processOperationsForM body.attestations (processAttestation · parentSlot)).run
              afterAttesterSlashings = .ok ((), afterAttestations) ∧
          (processOperationsForM body.voluntaryExits processVoluntaryExit).run
              afterAttestations = .ok ((), afterVoluntaryExits) ∧
          (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run
              afterVoluntaryExits = .ok ((), afterBlsToExecutionChanges) ∧
          (processOperationsForM body.payloadAttestations processPayloadAttestation).run
              afterBlsToExecutionChanges = .ok ((), postState) := by
    simp only [processOperationsLoops, run_bind_unit_ok_iff, exists_and_left]
  constructor
  · intro hok
    -- Each failing gate is a `throw`, so a successful run rules it out.
    cases hbeq0 : (body.deposits.size == 0) with
    | false =>
      rw [processOperations_eq_seq, hbeq0] at hok
      simp [run_throw, except_bind_error, SpecReject.assert] at hok
    | true =>
      by_cases hProp : body.proposerSlashings.size ≤ maxProposerSlashings
      · by_cases hAttSl : body.attesterSlashings.size ≤ maxAttesterSlashingsElectra
        · by_cases hAtt : body.attestations.size ≤ maxAttestationsElectra
          · by_cases hExit : body.voluntaryExits.size ≤ maxVoluntaryExits
            · by_cases hBls : body.blsToExecutionChanges.size ≤ maxBlsToExecutionChanges
              · by_cases hPay : body.payloadAttestations.size ≤ maxPayloadAttestations
                · rw [processOperations_eq_loops_of_bounds body parentSlot hbeq0 hProp hAttSl
                    hAtt hExit hBls hPay] at hok
                  exact ⟨beq_iff_eq.mp hbeq0, hProp, hAttSl, hAtt, hExit, hBls, hPay,
                    hLoops.mp hok⟩
                · rw [processOperations_eq_seq] at hok
                  simp [hbeq0, hProp, hAttSl, hAtt, hExit, hBls, hPay, run_throw,
                    except_bind_error, SpecReject.assert] at hok
              · rw [processOperations_eq_seq] at hok
                simp [hbeq0, hProp, hAttSl, hAtt, hExit, hBls, run_throw,
                  except_bind_error, SpecReject.assert] at hok
            · rw [processOperations_eq_seq] at hok
              simp [hbeq0, hProp, hAttSl, hAtt, hExit, run_throw,
                except_bind_error, SpecReject.assert] at hok
          · rw [processOperations_eq_seq] at hok
            simp [hbeq0, hProp, hAttSl, hAtt, run_throw,
              except_bind_error, SpecReject.assert] at hok
        · rw [processOperations_eq_seq] at hok
          simp [hbeq0, hProp, hAttSl, run_throw, except_bind_error, SpecReject.assert] at hok
      · rw [processOperations_eq_seq] at hok
        simp [hbeq0, hProp, run_throw, except_bind_error, SpecReject.assert] at hok
  · rintro ⟨hsize, hProp, hAttSl, hAtt, hExit, hBls, hPay, hChain⟩
    rw [processOperations_eq_loops_of_bounds body parentSlot (beq_iff_eq.mpr hsize)
      hProp hAttSl hAtt hExit hBls hPay]
    exact hLoops.mpr hChain
end
end

end EthCLSpecs.Proofs.Gloas
