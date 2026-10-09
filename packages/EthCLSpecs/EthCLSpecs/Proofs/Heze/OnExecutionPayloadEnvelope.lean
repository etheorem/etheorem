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

The corollaries state the block state as a plain value `v`, stored as
`pureState v` (`SPECS_ARCHITECTURE.md` §11.1). On `pureState v` a successful
verification returns `pureState v` itself
(`verifyExecutionPayloadEnvelope_pureState`): its only box result is the warm
half of `stateRoot state`, and `hashTreeRoot_uncachedBox` hands the uncached box
back unchanged. So the corollaries ask only that the verification succeeds, and
`onExecutionPayloadEnvelope_run_of_pureState` restates the whole `.run`
equation with no box beyond `pureState v`.

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
of the left side is `pureState v` itself. `map_bind` and `map_pure` push the
`map` through every bind, and no assert condition is evaluated. -/
theorem verifyExecutionPayloadEnvelope_pureState :
    ∀ (v : BeaconState) (signedEnv : SignedExecutionPayloadEnvelope),
      verifyExecutionPayloadEnvelope (pureState v) signedEnv
        = (fun _ => pureState v) <$> verifyExecutionPayloadEnvelope (pureState v) signedEnv := by
  intro v signedEnv
  simp only [verifyExecutionPayloadEnvelope, EthCLLib.Spec.stateRoot,
    SizzLean.Proofs.hashTreeRoot_uncachedBox, map_bind, map_pure]

omit [DataAvailability] in
/-- A successful verification on `pureState v` returns `pureState v`: the
`isOk` reading of `verifyExecutionPayloadEnvelope_pureState`. -/
theorem verifyExecutionPayloadEnvelope_pureState_of_isOk :
    ∀ (v : BeaconState) (signedEnv : SignedExecutionPayloadEnvelope),
      (verifyExecutionPayloadEnvelope (pureState v) signedEnv).isOk = true →
      verifyExecutionPayloadEnvelope (pureState v) signedEnv = .ok (pureState v) := by
  intro v signedEnv hok
  have hmap := verifyExecutionPayloadEnvelope_pureState v signedEnv
  cases hv : verifyExecutionPayloadEnvelope (pureState v) signedEnv with
  | error e => simp [hv, Except.isOk, Except.toBool] at hok
  | ok w =>
    -- `hmap` reads `.ok w = (fun _ => pureState v) <$> .ok w`, and the right side
    -- reduces to `.ok (pureState v)`.
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
state at the root is the uncached box of a plain value `v`. It is
`onExecutionPayloadEnvelope_run` with the lookup resolved and the warm state
replaced by `pureState v` (`verifyExecutionPayloadEnvelope_pureState`), so the
right side names no box beyond `pureState v`.
-/
theorem onExecutionPayloadEnvelope_run_of_pureState :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope) (v : BeaconState),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState v) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        =
        if !isDataAvailable signedEnv.message.beaconBlockRoot then
          .error (.assert "(isDataAvailable envelope.beaconBlockRoot)")
        else
          match verifyExecutionPayloadEnvelope (pureState v) signedEnv with
          | .error e => .error e
          | .ok _ =>
              match (recordPayloadInclusionListSatisfaction
                  (StoreTransition := ForkChoiceStoreRun (Store map))
                  store (pureState v) signedEnv.message.beaconBlockRoot
                  signedEnv.message.payload).run store with
              | .error err => .error err
              | .ok (recordedStore, _) =>
                  .ok ((),
                    { recordedStore with
                      blockStates :=
                        FcMap.insert recordedStore.blockStates
                          signedEnv.message.beaconBlockRoot (pureState v),
                      payloads :=
                        FcMap.insert recordedStore.payloads
                          signedEnv.message.beaconBlockRoot
                          signedEnv.message }) := by
  intro store signedEnv v hlookup
  rw [onExecutionPayloadEnvelope_run]
  simp only [hlookup]
  by_cases hda : isDataAvailable signedEnv.message.beaconBlockRoot
  · simp only [hda]
    cases hv : verifyExecutionPayloadEnvelope (pureState v) signedEnv with
    | error e => rfl
    | ok w =>
      have hw : verifyExecutionPayloadEnvelope (pureState v) signedEnv = .ok (pureState v) :=
        verifyExecutionPayloadEnvelope_pureState_of_isOk v signedEnv (by rw [hv]; rfl)
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
      (v : BeaconState) (err : StoreTransitionError),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState v) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope (pureState v) signedEnv = .error err →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error err := by
  intro store signedEnv v err hlookup hda hverif
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, hverif]

/-- A recorder error is the handler's result. -/
theorem onExecutionPayloadEnvelope_run_error_of_record :
    ∀ (store : Store map) (signedEnv : SignedExecutionPayloadEnvelope)
      (v : BeaconState) (err : StoreTransitionError),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState v) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      (verifyExecutionPayloadEnvelope (pureState v) signedEnv).isOk = true →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store (pureState v) signedEnv.message.beaconBlockRoot
          signedEnv.message.payload).run store
        = .error err →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .error err := by
  intro store signedEnv v err hlookup hda hok hrec
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, verifyExecutionPayloadEnvelope_pureState_of_isOk v signedEnv hok, hrec]

/--
Successful-path run equation for `onExecutionPayloadEnvelope`. When the
handler's lookup and checks succeed and timely inclusion-list collection
returns `ilTxs`, the final store is the original store updated by three
same-root `FcMap.insert` expressions: the block state `pureState v` in
`blockStates`, the envelope in `payloads`, and the inclusion-list result.
The inserts may overwrite a prior entry.
-/
theorem onExecutionPayloadEnvelope_run_eq_of_successful_checks :
    ∀ (store : Store map)
      (signedEnv : SignedExecutionPayloadEnvelope)
      (v : BeaconState)
      (ilTxs : Array Transaction)
      (postRunnerStore : Store map),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState v) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      (verifyExecutionPayloadEnvelope (pureState v) signedEnv).isOk = true →
      v.slot ≠ 0 →
      (getInclusionListTransactions
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore (pureState v) (v.slot - 1)
          (onlyTimely := true)).run store
        = .ok (ilTxs, postRunnerStore) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .ok ((),
            { store with
              blockStates :=
                FcMap.insert store.blockStates signedEnv.message.beaconBlockRoot (pureState v),
              payloads :=
                FcMap.insert store.payloads signedEnv.message.beaconBlockRoot
                  signedEnv.message,
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction
                  signedEnv.message.beaconBlockRoot
                  (isInclusionListSatisfied signedEnv.message.payload ilTxs) }) := by
  intro store signedEnv v ilTxs postRunnerStore hlookup hda hok hslot htxs
  -- `hlookup`, `hda`, and `hok` discharge the handler prefix;
  -- `hslot` and `htxs` select the recorder's successful branch.
  rw [onExecutionPayloadEnvelope_run]
  simp [hlookup, hda, verifyExecutionPayloadEnvelope_pureState_of_isOk v signedEnv hok,
    recordPayloadInclusionListSatisfaction_run_eq (map := map) store store postRunnerStore
      v signedEnv.message.beaconBlockRoot signedEnv.message.payload ilTxs hslot htxs]

end EthCLSpecs.Proofs.Heze
