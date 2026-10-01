import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.StoreRun
import EthCLLib.Proofs.LawfulFcMap

/-!
# Accepting an execution payload envelope

Heze's `onExecutionPayloadEnvelope` (`Heze/ForkChoice.lean:426-448`)
verifies and records a revealed payload envelope. This module proves its
successful-path `ForkChoiceStoreRun` equation.

After the block-state lookup, data-availability check, envelope verification,
and inclusion-list collection succeed, the final runner state is the original
store with three `FcMap.insert` operations at
`signedEnv.message.beaconBlockRoot`:

- `blockStates` receives the warm state returned by verification;
- `payloads` receives `signedEnv.message`;
- `payloadInclusionListSatisfaction` receives
  `isInclusionListSatisfied signedEnv.message.payload ilTxs`.

The inserts may overwrite existing entries. The proof composes
`recordPayloadInclusionListSatisfaction_run_eq`; the handler's final `set`
overwrites the collector's intermediate runner state with the updated explicit
store.

The generic `FcMap` interface has no insert/lookup law, so the run equation
makes no lookup claim. `onExecutionPayloadEnvelope_run_pairing` adds one under
`LawfulFcMap`: after the run, a lookup at the root returns the envelope and the
EL answer for its payload. Rejection paths remain open.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap ExecutionEngine DataAvailability CryptoBackend)
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Config Store State Root ExecutionPayload ExecutionRequests
  Transaction SignedExecutionPayloadEnvelope onExecutionPayloadEnvelope
  verifyExecutionPayloadEnvelope getInclusionListTransactions isInclusionListSatisfied
  isDataAvailable)

/--
Successful-path run equation for `onExecutionPayloadEnvelope`. When the
handler's lookup and checks succeed and timely inclusion-list collection
returns `ilTxs`, the final store contains the three structural same-root
inserts described above.
-/
theorem onExecutionPayloadEnvelope_run_eq_of_successful_checks
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    [DataAvailability] [CryptoBackend] :
    ∀ (store : Store map)
      (signedEnv : SignedExecutionPayloadEnvelope)
      (state warm : State)
      (ilTxs : Array Transaction)
      (postRunnerStore : Store map),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some state →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope state signedEnv = .ok warm →
      sszGet state slot ≠ 0 →
      (getInclusionListTransactions
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore state (sszGet state slot - 1)
          (onlyTimely := true)).run store
        = .ok (ilTxs, postRunnerStore) →
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map))
          signedEnv).run store
        = .ok ((),
            { store with
              blockStates :=
                FcMap.insert store.blockStates signedEnv.message.beaconBlockRoot warm,
              payloads :=
                FcMap.insert store.payloads signedEnv.message.beaconBlockRoot
                  signedEnv.message,
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction
                  signedEnv.message.beaconBlockRoot
                  (isInclusionListSatisfied signedEnv.message.payload ilTxs) }) := by
  intro store signedEnv state warm ilTxs postRunnerStore hlookup hda hverif hslot htxs
  -- Unfold the handler prefix, then rewrite the recorder success equation.
  simp [onExecutionPayloadEnvelope, FcMap.getOrAssert, hlookup, hda, hverif]
  rw [recordPayloadInclusionListSatisfaction_run_eq (map := map) store store postRunnerStore
    state signedEnv.message.beaconBlockRoot signedEnv.message.payload ilTxs hslot htxs]
  rfl

/-- After a successful `onExecutionPayloadEnvelope`, the store pairs the envelope with its
inclusion-list answer at the block root `r` of the envelope. `payloads[r]` is the envelope.
`payloadInclusionListSatisfaction[r]` is the EL answer for the payload of the envelope.
The hypotheses are the five of `onExecutionPayloadEnvelope_run_eq_of_successful_checks`.
The map must satisfy `LawfulFcMap`. -/
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
  refine ⟨_, onExecutionPayloadEnvelope_run_eq_of_successful_checks store signedEnv state warm
    ilTxs runnerPost hstate havail hverify hslot htxs, ?_, ?_⟩
  · exact LawfulFcMap.lookup_insert_self _ _ _
  · exact LawfulFcMap.lookup_insert_self _ _ _

end EthCLSpecs.Proofs.Heze
