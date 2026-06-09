import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Deneb.Block`: Deneb block hierarchy

Adds `blob_kzg_commitments : List[KZGCommitment,
MAX_BLOB_COMMITMENTS_PER_BLOCK]` to `BeaconBlockBody`, and threads
Deneb's `ExecutionPayload` through. Otherwise carries Capella's
shape forward.

## Caps

* `MAX_BLOB_COMMITMENTS_PER_BLOCK = 4096` (preset-invariant)
* `MAX_BLS_TO_EXECUTION_CHANGES = 16` (preset-invariant)

All Phase 0 operation-list caps unchanged.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Deneb

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Capella (SignedBLSToExecutionChange)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconBlockBody in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  randaoReveal           : BLSSignature,
  eth1Data               : Eth1Data,
  graffiti               : Bytes32,
  proposerSlashings      : SSZList ProposerSlashing 16,
  attesterSlashings      : SSZList AttesterSlashing 2,
  attestations           : SSZList Attestation 128,
  deposits               : SSZList Deposit 16,
  voluntaryExits         : SSZList SignedVoluntaryExit 16,
  syncAggregate          : @%LeanEthCS.Forks.Altair.SyncAggregate,
  executionPayload       : @%LeanEthCS.Forks.Deneb.ExecutionPayload,
  blsToExecutionChanges  : SSZList SignedBLSToExecutionChange 16,
  blobKzgCommitments     : SSZList KZGCommitment @@MAX_BLOB_COMMITMENTS_PER_BLOCK

ssz_struct_for_presets BeaconBlock in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  slot          : Slot,
  proposerIndex : ValidatorIndex,
  parentRoot    : Root,
  stateRoot     : Root,
  body          : @%BeaconBlockBody

ssz_struct_for_presets SignedBeaconBlock in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  message   : @%BeaconBlock,
  signature : BLSSignature

end LeanEthCS.Forks.Deneb
