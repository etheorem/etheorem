import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLLib.Proofs.LawfulFcMap

/-!
# `EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope`: the stored envelope and its answer

`onExecutionPayloadEnvelope` (`Heze/ForkChoice.lean`) writes three maps at the same
root. `recordPayloadInclusionListSatisfaction` writes the inclusion-list answer to
`payloadInclusionListSatisfaction`. The final `set` writes the envelope to `payloads`
and the warm state to `blockStates`.

`onExecutionPayloadEnvelope_run_eq` gives the store after a successful run. The run
succeeds when the `blockStates` lookup, the data-availability assert, the envelope
verification, and the collection of the inclusion-list transactions succeed, and the
slot of the block state is not zero.
`onExecutionPayloadEnvelope_run_pairing` then uses the `LawfulFcMap` laws. After the
run, a lookup at the root returns the envelope and the EL answer for its payload.

The theorems do not cover a failed run.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Config Store State Root ExecutionPayload ExecutionRequests Transaction
  SignedExecutionPayloadEnvelope onExecutionPayloadEnvelope isDataAvailable
  verifyExecutionPayloadEnvelope
  recordPayloadInclusionListSatisfaction getInclusionListTransactions isInclusionListSatisfied)

/-- The store after a successful `onExecutionPayloadEnvelope`. Let `r` be the block root
of the envelope. The hypotheses are:

1. `blockStates[r]` is `state`;
2. the data at `r` is available;
3. the envelope verification of `state` returns `warm`;
4. `state.slot` is not zero;
5. the collection of the timely inclusion-list transactions for the previous slot
   returns `ilTxs`. It can change the runner state to any `runnerPost`.

Then the run returns the input store with three entries written at `r`. The
inclusion-list answer for the payload goes to `payloadInclusionListSatisfaction`. The
warm state goes to `blockStates`. The envelope goes to `payloads`. The final `set`
replaces the runner state, so `runnerPost` does not appear in the result. -/
theorem onExecutionPayloadEnvelope_run_eq
    {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] :
    ∀ (store runnerPost : Store map) (signedEnv : SignedExecutionPayloadEnvelope)
      (state warm : State) (ilTxs : Array Transaction),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope state signedEnv = .ok warm →
      sszGet state slot ≠ 0 →
      (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore state (sszGet state slot - 1) (onlyTimely := true)).run store
        = .ok (ilTxs, runnerPost) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run store
        = .ok ((),
            { { store with
                payloadInclusionListSatisfaction :=
                  FcMap.insert store.payloadInclusionListSatisfaction
                    signedEnv.message.beaconBlockRoot
                    (isInclusionListSatisfied signedEnv.message.payload ilTxs) } with
              blockStates := FcMap.insert store.blockStates signedEnv.message.beaconBlockRoot warm,
              payloads := FcMap.insert store.payloads signedEnv.message.beaconBlockRoot
                signedEnv.message }) := by
  intro store runnerPost signedEnv state warm ilTxs hstate havail hverify hslot htxs
  have hrecord := recordPayloadInclusionListSatisfaction_run_eq store store runnerPost state
    signedEnv.message.beaconBlockRoot signedEnv.message.payload ilTxs hslot htxs
  -- `simp` runs the handler to the final `set`. The rest is a `map` over `Except.ok`.
  simp [onExecutionPayloadEnvelope, FcMap.getOrAssert, hstate, havail, hverify, hrecord]
  rfl

/-- After a successful `onExecutionPayloadEnvelope`, the store pairs the envelope with its
inclusion-list answer at the block root `r` of the envelope. `payloads[r]` is the envelope.
`payloadInclusionListSatisfaction[r]` is the EL answer for the payload of the envelope.
The hypotheses are the five of `onExecutionPayloadEnvelope_run_eq`. The map must satisfy
`LawfulFcMap`. -/
theorem onExecutionPayloadEnvelope_run_pairing
    {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map] [LawfulFcMap map Root]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] :
    ∀ (store runnerPost : Store map) (signedEnv : SignedExecutionPayloadEnvelope)
      (state warm : State) (ilTxs : Array Transaction),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope state signedEnv = .ok warm →
      sszGet state slot ≠ 0 →
      (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore state (sszGet state slot - 1) (onlyTimely := true)).run store
        = .ok (ilTxs, runnerPost) →
      ∃ post : Store map,
        (onExecutionPayloadEnvelope (map := map)
            (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run store
          = .ok ((), post) ∧
        FcMap.lookup post.payloads signedEnv.message.beaconBlockRoot = some signedEnv.message ∧
        FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
          = some (isInclusionListSatisfied signedEnv.message.payload ilTxs) := by
  intro store runnerPost signedEnv state warm ilTxs hstate havail hverify hslot htxs
  refine ⟨_, onExecutionPayloadEnvelope_run_eq store runnerPost signedEnv state warm ilTxs
    hstate havail hverify hslot htxs, ?_, ?_⟩
  · exact LawfulFcMap.lookup_insert_self _ _ _
  · exact LawfulFcMap.lookup_insert_self _ _ _

end EthCLSpecs.Proofs.Heze
