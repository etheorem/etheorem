import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.StoreRun

/-!
# Accepting an execution payload envelope

Heze's `onExecutionPayloadEnvelope` (`Heze/ForkChoice.lean:426-448`) verifies a
revealed payload envelope and records it. After the block-state lookup, the
data-availability check, `verifyExecutionPayloadEnvelope`, and inclusion-list
recording succeed, the handler writes three maps at
`signedEnv.message.beaconBlockRoot`.

This module proves that successful run as one `ForkChoiceStoreRun` equation.
The final store is the original store with:

- `blockStates[root]` updated to the warm state returned by
  `verifyExecutionPayloadEnvelope`;
- `payloads[root]` updated to the envelope;
- `payloadInclusionListSatisfaction[root]` updated to
  `isInclusionListSatisfied envelope.payload ilTxs`.

The three inserts use the same root. That is the structural same-root pairing.
An insert replaces a prior entry at that root when one exists. The theorem
does not claim the key was absent.

`FcMap` has no insert/lookup law and no insert/contains law. The theorem
therefore does not conclude that a later lookup returns the written value, and
it does not conclude `isPayloadVerified` on the final store.
`isPayloadVerified` is `FcMap.contains` on `payloads`.

The proof reuses `recordPayloadInclusionListSatisfaction_run_eq`. The recorder
returns an updated explicit store and a collector runner state. The handler's
final `set` keeps the explicit store and discards that runner state.

Slot zero, a missing block-state entry, a failed data-availability check, a
failed `verifyExecutionPayloadEnvelope`, and a collector error stay open.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap ExecutionEngine DataAvailability CryptoBackend)
open EthCLSpecs.Heze (Preset Config Store State Root ExecutionPayload ExecutionRequests
  Transaction SignedExecutionPayloadEnvelope onExecutionPayloadEnvelope
  verifyExecutionPayloadEnvelope getInclusionListTransactions isInclusionListSatisfied
  isDataAvailable)

/--
If `blockStates` holds `state` at `signedEnv.message.beaconBlockRoot`, data
availability holds at that root,
`verifyExecutionPayloadEnvelope state signedEnv = .ok warm`, `state.slot` is
nonzero, and timely inclusion-list collection succeeds, then
`onExecutionPayloadEnvelope` returns the original store with three same-root
inserts and unit. The root and payload come from `signedEnv.message`.

`warm` is the value of that `verifyExecutionPayloadEnvelope` success premise.
The theorem does not mention `isPayloadVerified` on the resulting store.
-/
theorem onExecutionPayloadEnvelope_run_eq
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
      (getInclusionListTransactions (map := map)
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
