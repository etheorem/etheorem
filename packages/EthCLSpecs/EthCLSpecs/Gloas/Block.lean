import EthCLSpecs.Gloas.Containers.Execution

/-!
# `EthCLSpecs.Gloas.Block`: the Gloas block containers (EIP-7732)

The ePBS `BeaconBlockBody`, where a `signedExecutionPayloadBid` and
`payloadAttestations` replace the in-block execution payload / blob commitments,
and the `BeaconBlock` / `SignedBeaconBlock` that wrap it. The unchanged operation
containers (`ProposerSlashing`, `Attestation`, `Deposit`, …) are Fulu's.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- The Gloas `BeaconBlockBody` (ePBS): a `signedExecutionPayloadBid` and
`payloadAttestations` in place of the in-block execution payload / blob
commitments; `parentExecutionRequests` carries the parent block's requests. -/
forkcontainer BeaconBlockBody where
  randaoReveal              : BLSSignature
  eth1Data                  : Eth1Data
  graffiti                  : Bytes32
  proposerSlashings         : SSZList ProposerSlashing Const.maxProposerSlashings
  attesterSlashings         : SSZList AttesterSlashing Const.maxAttesterSlashingsElectra
  attestations              : SSZList Attestation Const.maxAttestationsElectra
  deposits                  : SSZList Deposit Const.maxDeposits
  voluntaryExits            : SSZList SignedVoluntaryExit Const.maxVoluntaryExits
  syncAggregate             : SyncAggregate
  blsToExecutionChanges     : SSZList SignedBLSToExecutionChange Const.maxBlsToExecutionChanges
  signedExecutionPayloadBid : SignedExecutionPayloadBid
  payloadAttestations       : SSZList PayloadAttestation Const.maxPayloadAttestations
  parentExecutionRequests   : ExecutionRequests

/-- A Gloas `BeaconBlock` (references the Gloas `BeaconBlockBody`). -/
forkcontainer BeaconBlock where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  body          : BeaconBlockBody

/-- A signed Gloas `BeaconBlock`. -/
signedwrapper SignedBeaconBlock wraps BeaconBlock

end EthCLSpecs.Gloas
