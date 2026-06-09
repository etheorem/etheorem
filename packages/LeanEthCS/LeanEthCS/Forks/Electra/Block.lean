import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.Forks.Electra.Attestation
import LeanEthCS.Forks.Electra.Requests
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Electra.Block`: Electra block hierarchy

Two deltas over Deneb:

1. `attester_slashings` and `attestations` lists use the new Electra
   caps `MAX_ATTESTER_SLASHINGS_ELECTRA = 1` and
   `MAX_ATTESTATIONS_ELECTRA = 8` (both preset-invariant).
2. A new field `execution_requests : ExecutionRequests` appears.

The body's slashings/attestations also become Electra's `Attestation`
/ `AttesterSlashing` types (the Electra variants).
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Electra

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Capella (SignedBLSToExecutionChange)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconBlockBody in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  randaoReveal           : BLSSignature,
  eth1Data               : Eth1Data,
  graffiti               : Bytes32,
  proposerSlashings      : SSZList ProposerSlashing 16,
  attesterSlashings      : SSZList (@%AttesterSlashing) 1,
  attestations           : SSZList (@%Attestation) 8,
  deposits               : SSZList Deposit 16,
  voluntaryExits         : SSZList SignedVoluntaryExit 16,
  syncAggregate          : @%LeanEthCS.Forks.Altair.SyncAggregate,
  executionPayload       : @%LeanEthCS.Forks.Deneb.ExecutionPayload,
  blsToExecutionChanges  : SSZList SignedBLSToExecutionChange 16,
  blobKzgCommitments     : SSZList KZGCommitment @@MAX_BLOB_COMMITMENTS_PER_BLOCK,
  executionRequests      : ExecutionRequests

ssz_struct_for_presets BeaconBlock in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  slot          : Slot,
  proposerIndex : ValidatorIndex,
  parentRoot    : Root,
  stateRoot     : Root,
  body          : @%BeaconBlockBody

ssz_struct_for_presets SignedBeaconBlock in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  message   : @%BeaconBlock,
  signature : BLSSignature

end LeanEthCS.Forks.Electra
