import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Execution
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Capella.Block`: Capella block hierarchy

Two deltas over Bellatrix:

1. `BeaconBlockBody` carries a `bls_to_execution_changes` list.
2. The `execution_payload` field is now Capella's wider
   `ExecutionPayload` (with `withdrawals`).

The body is preset-variant via both `SyncAggregate` (from Altair) and
`ExecutionPayload` (from this fork); the rest of the chain follows.

## Caps

* `MAX_BLS_TO_EXECUTION_CHANGES = 16`   (mainnet and minimal)

All Phase 0 operation-list caps unchanged.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Capella

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

ssz_struct_for_presets BeaconBlockBody in LeanEthCS.Forks.Capella
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
  executionPayload       : @%ExecutionPayload,
  blsToExecutionChanges  : SSZList SignedBLSToExecutionChange 16

ssz_struct_for_presets BeaconBlock in LeanEthCS.Forks.Capella
    for [minimal, mainnet] where
  slot          : Slot,
  proposerIndex : ValidatorIndex,
  parentRoot    : Root,
  stateRoot     : Root,
  body          : @%BeaconBlockBody

ssz_struct_for_presets SignedBeaconBlock in LeanEthCS.Forks.Capella
    for [minimal, mainnet] where
  message   : @%BeaconBlock,
  signature : BLSSignature

end LeanEthCS.Forks.Capella
