import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Electra.Attestation
import LeanEthCS.Forks.Electra.Requests
import LeanEthCS.Forks.Gloas.Execution
import LeanEthCS.Forks.Gloas.PayloadAttestation
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.Block`: Gloas / EIP-7732 block hierarchy

The Gloas `BeaconBlockBody` is restructured by ePBS:

**Removed** (now in the post-attestation `ExecutionPayloadEnvelope`):
* `execution_payload`
* `blob_kzg_commitments`
* `execution_requests`

**New**:
* `signed_execution_payload_bid : SignedExecutionPayloadBid`, the
  builder's binding commitment, signed before the payload reveal.
* `payload_attestations : List[PayloadAttestation, MAX_PAYLOAD_ATTESTATIONS]`,
  PTC votes carried in the block.
* `parent_execution_requests : ExecutionRequests`, the EL request
  list from the parent slot's payload (Gloas moves request
  processing across the bid/reveal boundary).

`BeaconBlock` and `SignedBeaconBlock` are unchanged from Electra/
Fulu in shape, only the embedded body differs.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Electra (ExecutionRequests)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconBlockBody in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  randaoReveal               : BLSSignature,
  eth1Data                   : Eth1Data,
  graffiti                   : Bytes32,
  proposerSlashings          : SSZList ProposerSlashing 16,
  attesterSlashings          : SSZList (@%LeanEthCS.Forks.Electra.AttesterSlashing) 1,
  attestations               : SSZList (@%LeanEthCS.Forks.Electra.Attestation) 8,
  deposits                   : SSZList Deposit 16,
  voluntaryExits             : SSZList SignedVoluntaryExit 16,
  syncAggregate              : @%LeanEthCS.Forks.Altair.SyncAggregate,
  blsToExecutionChanges      : SSZList LeanEthCS.Forks.Capella.SignedBLSToExecutionChange 16,
  signedExecutionPayloadBid  : @%SignedExecutionPayloadBid,
  payloadAttestations        : SSZList (@%PayloadAttestation) @@MAX_PAYLOAD_ATTESTATIONS,
  parentExecutionRequests    : ExecutionRequests

ssz_struct_for_presets BeaconBlock in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  slot          : Slot,
  proposerIndex : ValidatorIndex,
  parentRoot    : Root,
  stateRoot     : Root,
  body          : @%BeaconBlockBody

ssz_struct_for_presets SignedBeaconBlock in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  message   : @%BeaconBlock,
  signature : BLSSignature

end LeanEthCS.Forks.Gloas
