import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.StoreRun

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

Because `FcMap` provides neither insert/lookup nor insert/contains laws, the
theorem makes no subsequent-lookup or `isPayloadVerified` claim. Rejection
paths remain open.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap ExecutionEngine DataAvailability CryptoBackend)
open EthCLSpecs.Heze (Preset Config Store State ExecutionPayload ExecutionRequests
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

end EthCLSpecs.Proofs.Heze
