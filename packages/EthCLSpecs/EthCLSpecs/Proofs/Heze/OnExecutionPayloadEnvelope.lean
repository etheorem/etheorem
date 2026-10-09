import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun

/-!
# Accepting an execution payload envelope

Heze's `onExecutionPayloadEnvelope` (`Heze/ForkChoice.lean:426-448`)
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

The corollaries state the block state as a plain value `state`, stored as
`pureState state` (`SPECS_ARCHITECTURE.md` §11.1). On `pureState state` a successful
verification returns `pureState state` itself
(`verifyExecutionPayloadEnvelope_pureState`): its only box result is the warm
half of `stateRoot state`, and `hashTreeRoot_uncachedBox` hands the uncached box
back unchanged. So the corollaries ask only that the verification succeeds, and
`onExecutionPayloadEnvelope_run_of_pureState` restates the whole `.run`
equation with no box beyond `pureState state`.

Lookup-after-insert, contains-after-insert, `isPayloadVerified`, and
composition with `shouldExtendPayload` remain open. The generic `FcMap`
interface provides no insert/lookup or insert/contains law.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_throw except_bind_error pureState)
open EthCLLib.Spec (HasherTag MapKind FcMap ExecutionEngine DataAvailability CryptoBackend
  StoreTransitionError)
open EthCLSpecs.Heze (Preset Config Store BeaconState ExecutionPayload ExecutionRequests
  Transaction SignedExecutionPayloadEnvelope onExecutionPayloadEnvelope
  verifyExecutionPayloadEnvelope recordPayloadInclusionListSatisfaction
  getInclusionListTransactions isInclusionListSatisfied
  isDataAvailable)

variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] [CryptoBackend]

omit [DataAvailability] in
/-- On the uncached box of a plain value, a successful verification returns that
same box. The verification's only box result is the `warm` half of
`stateRoot state`, and `hashTreeRoot_uncachedBox` hands the uncached box back
unchanged. Stated as a `map` so the statement binds no box: the success value
of the left side is `pureState state` itself. `map_bind` and `map_pure` push the
`map` through every bind, and no assert condition is evaluated. -/
theorem verifyExecutionPayloadEnvelope_pureState :
    ∀ (state : BeaconState) (signedEnv : SignedExecutionPayloadEnvelope),
      verifyExecutionPayloadEnvelope (pureState state) signedEnv
        = (fun _ => pureState state) <$> verifyExecutionPayloadEnvelope (pureState state) signedEnv := by
  intro state signedEnv
  simp only [verifyExecutionPayloadEnvelope, EthCLLib.Spec.stateRoot,
    SizzLean.Proofs.hashTreeRoot_uncachedBox, map_bind, map_pure]

omit [DataAvailability] in
/-- A successful verification on `pureState state` returns `pureState state`: the
`isOk` reading of `verifyExecutionPayloadEnvelope_pureState`. -/
private theorem verifyExecutionPayloadEnvelope_pureState_of_isOk :
    ∀ (state : BeaconState) (signedEnv : SignedExecutionPayloadEnvelope),
      (verifyExecutionPayloadEnvelope (pureState state) signedEnv).isOk = true →
      verifyExecutionPayloadEnvelope (pureState state) signedEnv = .ok (pureState state) := by
  intro state signedEnv hok
  have hmap := verifyExecutionPayloadEnvelope_pureState state signedEnv
  cases hv : verifyExecutionPayloadEnvelope (pureState state) signedEnv with
  | error e => simp [hv, Except.isOk, Except.toBool] at hok
  | ok w =>
    -- `hmap` reads `.ok w = (fun _ => pureState state) <$> .ok w`, and the right side
    -- reduces to `.ok (pureState state)`.
    rw [hv] at hmap
    exact hmap

/--
Complete compositional `.run` equation of `onExecutionPayloadEnvelope`.
Lookup and availability failures are `.assert` errors. Verification and
recorder errors propagate unchanged. After recorder success, the handler
performs its final `set` on the returned store, discarding the
recorder-produced runner state.
`recordPayloadInclusionListSatisfaction_run` characterizes the recorder's
slot-zero, collector-error, and successful outcomes.
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
              | .ok warm =>
                  match (recordPayloadInclusionListSatisfaction
                      (StoreTransition := ForkChoiceStoreRun (Store map))
                      store state signedEnv.message.beaconBlockRoot
                      signedEnv.message.payload).run store with
                  | .error err => .error err
                  | .ok (recordedStore, _) =>
                      .ok ((),
                        { recordedStore with
                          blockStates :=
                            FcMap.insert recordedStore.blockStates
                              signedEnv.message.beaconBlockRoot warm,
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
      | ok warm =>
        simp
        cases (recordPayloadInclusionListSatisfaction
            (StoreTransition := ForkChoiceStoreRun (Store map))
            store state signedEnv.message.beaconBlockRoot
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
state at the root is the uncached box of a plain value `state`. It is
`onExecutionPayloadEnvelope_run` with the lookup resolved and the warm state
replaced by `pureState state` (`verifyExecutionPayloadEnvelope_pureState`), so the
right side names no box beyond `pureState state`.
-/
theorem onExecutionPayloadEnvelope_run_of_pureState :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope) (state : BeaconState),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState state) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        =
        if !isDataAvailable signedEnv.message.beaconBlockRoot then
          .error (.assert "(isDataAvailable envelope.beaconBlockRoot)")
        else
          match verifyExecutionPayloadEnvelope (pureState state) signedEnv with
          | .error e => .error e
          | .ok _ =>
              match (recordPayloadInclusionListSatisfaction
                  (StoreTransition := ForkChoiceStoreRun (Store map))
                  store (pureState state) signedEnv.message.beaconBlockRoot
                  signedEnv.message.payload).run store with
              | .error err => .error err
              | .ok (recordedStore, _) =>
                  .ok ((),
                    { recordedStore with
                      blockStates :=
                        FcMap.insert recordedStore.blockStates
                          signedEnv.message.beaconBlockRoot (pureState state),
                      payloads :=
                        FcMap.insert recordedStore.payloads
                          signedEnv.message.beaconBlockRoot
                          signedEnv.message }) := by
  intro store signedEnv state hlookup
  rw [onExecutionPayloadEnvelope_run]
  simp only [hlookup]
  by_cases hda : isDataAvailable signedEnv.message.beaconBlockRoot
  · simp only [hda]
    cases hv : verifyExecutionPayloadEnvelope (pureState state) signedEnv with
    | error e => rfl
    | ok w =>
      have hw : verifyExecutionPayloadEnvelope (pureState state) signedEnv = .ok (pureState state) :=
        verifyExecutionPayloadEnvelope_pureState_of_isOk state signedEnv (by rw [hv]; rfl)
      rw [hv] at hw
      cases hw
      rfl
  · simp [hda]

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
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState state) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope (pureState state) signedEnv = .error err →
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
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState state) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      (verifyExecutionPayloadEnvelope (pureState state) signedEnv).isOk = true →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store (pureState state) signedEnv.message.beaconBlockRoot
          signedEnv.message.payload).run store
        = .error err →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error err := by
  intro store signedEnv state err hlookup hda hok hrec
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, verifyExecutionPayloadEnvelope_pureState_of_isOk state signedEnv hok, hrec]

/--
Successful-path run equation for `onExecutionPayloadEnvelope`. When the
handler's lookup and checks succeed and timely inclusion-list collection
returns `ilTxs`, the final store is the original store updated by three
same-root `FcMap.insert` expressions: the block state `pureState state` in
`blockStates`, the envelope in `payloads`, and the inclusion-list result.
The inserts may overwrite a prior entry.
-/
theorem onExecutionPayloadEnvelope_run_eq_of_successful_checks :
    ∀ (store : Store map)
      (signedEnv : SignedExecutionPayloadEnvelope)
      (state : BeaconState)
      (ilTxs : Array Transaction)
      (postRunnerStore : Store map),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState state) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      (verifyExecutionPayloadEnvelope (pureState state) signedEnv).isOk = true →
      state.slot ≠ 0 →
      (getInclusionListTransactions
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore (pureState state) (state.slot - 1)
          (onlyTimely := true)).run store
        = .ok (ilTxs, postRunnerStore) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .ok ((),
            { store with
              blockStates :=
                FcMap.insert store.blockStates signedEnv.message.beaconBlockRoot (pureState state),
              payloads :=
                FcMap.insert store.payloads signedEnv.message.beaconBlockRoot
                  signedEnv.message,
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction
                  signedEnv.message.beaconBlockRoot
                  (isInclusionListSatisfied signedEnv.message.payload ilTxs) }) := by
  intro store signedEnv state ilTxs postRunnerStore hlookup hda hok hslot htxs
  -- `hlookup`, `hda`, and `hok` discharge the handler prefix;
  -- `hslot` and `htxs` select the recorder's successful branch.
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, verifyExecutionPayloadEnvelope_pureState_of_isOk state signedEnv hok,
    recordPayloadInclusionListSatisfaction_run_eq (map := map) store store postRunnerStore
      state signedEnv.message.beaconBlockRoot signedEnv.message.payload ilTxs hslot htxs]

end EthCLSpecs.Proofs.Heze
