import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.Run
import EthCLSpecs.Proofs.StoreRun
import SizzLean.Proofs.UncachedBox

/-!
# Accepting an execution payload envelope

Heze's `onExecutionPayloadEnvelope` (`Heze/ForkChoice.lean:426-448`)
verifies and records a revealed payload envelope. This module proves its
successful-path `ForkChoiceStoreRun` equation.

After the block-state lookup, data-availability check, envelope verification,
and inclusion-list collection succeed, the final runner state is the original
store with three `FcMap.insert` operations at
`signedEnv.message.beaconBlockRoot`:

- `blockStates` receives the state the handler read at the root, an uncached
  box of a plain value: on `pureState v` the verification's own `stateRoot`
  warms the box, and `hashTreeRoot_uncachedBox` hands back the input box
  unchanged, so the `warm` state the verification returns is `pureState v`
  itself;
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

open EthCLSpecs.Proofs (ForkChoiceStoreRun pureState)
open EthCLLib.Spec (HasherTag MapKind FcMap ExecutionEngine DataAvailability CryptoBackend)
open EthCLSpecs.Heze (Preset Config Store BeaconState ExecutionPayload ExecutionRequests
  Transaction SignedExecutionPayloadEnvelope onExecutionPayloadEnvelope
  verifyExecutionPayloadEnvelope getInclusionListTransactions isInclusionListSatisfied
  isDataAvailable)

/--
Successful-path run equation for `onExecutionPayloadEnvelope`. When the
handler's lookup and checks succeed and timely inclusion-list collection
returns `ilTxs`, the final store contains the three structural same-root
inserts described above. The block state binds as the plain value `v`, and the
statement runs the handler on `pureState v` throughout.
-/
theorem onExecutionPayloadEnvelope_run_eq_of_successful_checks
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
    [DataAvailability] [CryptoBackend] :
    ∀ (store : Store map)
      (signedEnv : SignedExecutionPayloadEnvelope)
      (v : BeaconState)
      (ilTxs : Array Transaction)
      (postRunnerStore : Store map),
      FcMap.lookup store.blockStates signedEnv.message.beaconBlockRoot = some (pureState v) →
      isDataAvailable signedEnv.message.beaconBlockRoot = true →
      verifyExecutionPayloadEnvelope (pureState v) signedEnv = .ok (pureState v) →
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
  intro store signedEnv v ilTxs postRunnerStore hlookup hda hverif hslot htxs
  -- Unfold the handler prefix, then rewrite the recorder success equation.
  simp [onExecutionPayloadEnvelope, FcMap.getOrAssert, hlookup, hda, hverif]
  rw [recordPayloadInclusionListSatisfaction_run_eq (map := map) store store postRunnerStore
    v signedEnv.message.beaconBlockRoot signedEnv.message.payload ilTxs hslot htxs]
  rfl

end EthCLSpecs.Proofs.Heze
