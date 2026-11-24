import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun

/-!
# Accepting an execution payload envelope

Heze's `onExecutionPayloadEnvelope` (`Heze/ForkChoice.lean:447-468`)
verifies and records a revealed payload envelope. This module proves its
complete compositional `.run` equation at `ForkChoiceStoreRun (Store map)`.

The handler has four levels: block-state lookup, data availability,
verification, and the recorder result. A missing block state or a failed
availability check is an `.assert` error. Verification and recorder errors
propagate unchanged. No handler `set` has executed on those paths, and
`.error err` contains no post-state.

The recorder does not mutate the runner with `set`. On success it returns an
explicitly updated `Store` value with `pure`. The handler uses that returned
value as the base of its final `set`, discarding the recorder-produced runner
state.

The Heze `State` is the plain `BeaconState`, so the store keeps plain block
states and the corollaries bind the block state as a plain value `state`.
The verification returns `Except StoreTransitionError Unit`, as the pyspec
`verify_execution_payload_envelope` returns `None`. On success the handler writes
`payloads` and the recorder's satisfaction map, and leaves `blockStates` as it
was. So the corollaries ask only that the verification succeeds.

Lookup-after-insert, contains-after-insert, `isPayloadVerified`, and
composition with `shouldExtendPayload` remain open. The generic `FcMap`
interface provides no insert/lookup or insert/contains law.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_throw except_bind_error)
open EthCLLib.Spec (HasherTag MapKind FcMap ExecutionEngine DataAvailability CryptoBackend
  StoreTransitionError)
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Slot ExecutionPayload
  ExecutionRequests Transaction SignedExecutionPayloadEnvelope onExecutionPayloadEnvelope
  verifyExecutionPayloadEnvelope recordPayloadInclusionListSatisfaction
  getShufflingDependentRoot getInclusionListTransactions isInclusionListSatisfied
  computeEpochAtSlot isDataAvailable)

variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] [CryptoBackend]

omit [DataAvailability] in
/-- A successful verification is `.ok ()`: `Unit` has one value, so the `isOk`
reading fixes the whole result. -/
private theorem verifyExecutionPayloadEnvelope_eq_ok_of_isOk :
    ∀ (state : BeaconState) (signedEnv : SignedExecutionPayloadEnvelope),
      (verifyExecutionPayloadEnvelope state signedEnv).isOk = true →
      verifyExecutionPayloadEnvelope state signedEnv = .ok () := by
  intro state signedEnv hok
  cases hv : verifyExecutionPayloadEnvelope state signedEnv with
  | error e => simp [hv, Except.isOk, Except.toBool] at hok
  | ok u => rfl

/--
Complete compositional `.run` equation of `onExecutionPayloadEnvelope`.
Lookup and availability failures are `.assert` errors. Verification and
recorder errors propagate unchanged. After recorder success, the handler
performs its final `set` on the returned store, discarding the
recorder-produced runner state. That `set` writes only `payloads`.
`recordPayloadInclusionListSatisfaction_run` characterizes the recorder's
missing-block, slot-zero, walk-error, and successful outcomes.
-/
@[characterizes EthCLSpecs.Heze.onExecutionPayloadEnvelope]
theorem onExecutionPayloadEnvelope_run :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope),
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        =
        match FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot with
        | none =>
            .error (.assert "envelope.beacon_block_root in store.block_states")
        | some state =>
            -- The reject sits next to its guard, in the handler's `assert` order.
            if !isDataAvailable signedEnv.message.beaconBlockRoot then
              .error (.assert "(isDataAvailable envelope.beaconBlockRoot)")
            else
              match verifyExecutionPayloadEnvelope state signedEnv with
              | .error e => .error e
              | .ok () =>
                  match (recordPayloadInclusionListSatisfaction
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store signedEnv.message.beaconBlockRoot
                      signedEnv.message.payload).run store with
                  | .error err => .error err
                  | .ok (recordedStore, _) =>
                      .ok ((),
                        { recordedStore with
                          payloads :=
                            FcMap.insert recordedStore.payloads
                              signedEnv.message.beaconBlockRoot
                              signedEnv.message }) := by
  intro store signedEnv
  simp [onExecutionPayloadEnvelope, FcMap.getOrAssert]
  cases FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot with
  | none =>
    rfl
  | some state =>
    by_cases hda : isDataAvailable signedEnv.message.beaconBlockRoot
    · simp [hda]
      cases verifyExecutionPayloadEnvelope state signedEnv with
      | error e =>
        exact run_throw e store
      | ok u =>
        cases u
        simp
        cases (recordPayloadInclusionListSatisfaction
            (StoreTransition := ForkChoiceStoreRun (Store map))
            store signedEnv.message.beaconBlockRoot
            signedEnv.message.payload).run store with
        | error err =>
          rfl
        | ok p =>
          obtain ⟨recordedStore, _⟩ := p
          rfl
    · simp [hda, run_throw, except_bind_error]
      rfl

/--
The complete `.run` equation of `onExecutionPayloadEnvelope` when the block
state at the root is `state`. It is `onExecutionPayloadEnvelope_run` with the
lookup resolved.
-/
theorem onExecutionPayloadEnvelope_run_of_lookup :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope) (state : BeaconState),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        =
        if !isDataAvailable signedEnv.message.beaconBlockRoot then
          .error (.assert "(isDataAvailable envelope.beaconBlockRoot)")
        else
          match verifyExecutionPayloadEnvelope state signedEnv with
          | .error e => .error e
          | .ok () =>
              match (recordPayloadInclusionListSatisfaction
                  (StoreTransition := ForkChoiceStoreRun (Store map))
                  store signedEnv.message.beaconBlockRoot
                  signedEnv.message.payload).run store with
              | .error err => .error err
              | .ok (recordedStore, _) =>
                  .ok ((),
                    { recordedStore with
                      payloads :=
                        FcMap.insert recordedStore.payloads
                          signedEnv.message.beaconBlockRoot
                          signedEnv.message }) := by
  intro store signedEnv state hlookup
  rw [onExecutionPayloadEnvelope_run]
  simp only [hlookup]

/-- Missing `blockStates` entry is the handler's first `.assert` error. -/
theorem onExecutionPayloadEnvelope_run_error_of_missing_block_state :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = none →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error (.assert "envelope.beacon_block_root in store.block_states") := by
  intro store signedEnv hlookup
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup]

/-- Failed data-availability check is the handler's second `.assert` error.
The availability check does not read the block state, so the hypothesis asks
only that the lookup succeeds. -/
theorem onExecutionPayloadEnvelope_run_error_of_data_unavailable :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope),
      (FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot).isSome = true →
      isDataAvailable signedEnv.message.beaconBlockRoot = false →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error (.assert "(isDataAvailable envelope.beaconBlockRoot)") := by
  intro store signedEnv hlookup hda
  rw [onExecutionPayloadEnvelope_run]
  cases hl : FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot with
  | none => simp [hl] at hlookup
  | some _ => simp [hda]

/-- A verification error is the handler's result. -/
theorem onExecutionPayloadEnvelope_run_error_of_verify :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope)
      (state : BeaconState) (err : StoreTransitionError),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope state signedEnv = .error err →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error err := by
  intro store signedEnv state err hlookup hda hverif
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, hverif]

/-- A recorder error is the handler's result. -/
theorem onExecutionPayloadEnvelope_run_error_of_record :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope)
      (state : BeaconState) (err : StoreTransitionError),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      (verifyExecutionPayloadEnvelope state signedEnv).isOk = true →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store signedEnv.message.beaconBlockRoot
          signedEnv.message.payload).run store
        = .error err →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error err := by
  intro store signedEnv state err hlookup hda hok hrec
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, verifyExecutionPayloadEnvelope_eq_ok_of_isOk state signedEnv hok, hrec]

/--
Successful-path run equation for `onExecutionPayloadEnvelope`. The handler's
lookup and checks succeed, `slot` is the slot before the envelope's block (so that block
sits at a nonzero slot), and the dependent-root walk returns `dependentRoot`. Then the final
store is the original store updated by two same-root `FcMap.insert` expressions: the
envelope in `payloads`, and the inclusion-list result for the timely transactions stored
under `(slot, dependentRoot)`. The inserts may overwrite a prior entry. `blockStates`
keeps its entries.
-/
theorem onExecutionPayloadEnvelope_run_eq_of_successful_checks :
    ∀ (store : Store map)
      (signedEnv : SignedExecutionPayloadEnvelope)
      (state : BeaconState)
      (block : BeaconBlock) (slot : Slot) (dependentRoot : Root)
      (postRunnerStore : Store map),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      (verifyExecutionPayloadEnvelope state signedEnv).isOk = true →
      FcMap.lookup store.blocks signedEnv.message.beaconBlockRoot = some block →
      slot.toPlainNat + 1 = block.slot.toPlainNat →
      (getShufflingDependentRoot
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store signedEnv.message.beaconBlockRoot (computeEpochAtSlot slot)).run store
        = .ok (dependentRoot, postRunnerStore) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .ok ((),
            { store with
              payloads :=
                FcMap.insert store.payloads signedEnv.message.beaconBlockRoot
                  signedEnv.message,
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction
                  signedEnv.message.beaconBlockRoot
                  (isInclusionListSatisfied signedEnv.message.payload
                    (getInclusionListTransactions store.inclusionListStore slot
                      dependentRoot (onlyTimely := true))) }) := by
  intro store signedEnv state block slot dependentRoot postRunnerStore hlookup hda hok
    hblock hprev hdep
  -- `hlookup`, `hda`, and `hok` discharge the handler prefix;
  -- `hblock`, `hprev`, and `hdep` select the recorder's successful branch.
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, verifyExecutionPayloadEnvelope_eq_ok_of_isOk state signedEnv hok,
    recordPayloadInclusionListSatisfaction_run_eq (map := map) store store postRunnerStore
      signedEnv.message.beaconBlockRoot signedEnv.message.payload block slot dependentRoot
      hblock hprev hdep]

end EthCLSpecs.Proofs.Heze
