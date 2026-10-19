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

namespace EthCLSpecs.Gloas

/-- The Gloas `BeaconBlockBody` (ePBS, EIP-7688): a progressive container.
`signedExecutionPayloadBid` and `payloadAttestations` stand in place of the
in-block execution payload / blob commitments; `parentExecutionRequests`
carries the parent block's requests. The operation lists are progressive. -/
@[sizzlean_progressive]
forkcontainer BeaconBlockBody where
  randaoReveal              : BLSSignature
  eth1Data                  : Eth1Data
  graffiti                  : Bytes32
  proposerSlashings         : ProgressiveList ProposerSlashing
  attesterSlashings         : ProgressiveList AttesterSlashing
  attestations              : ProgressiveList Attestation
  deposits                  : ProgressiveList Deposit
  voluntaryExits            : ProgressiveList SignedVoluntaryExit
  syncAggregate             : SyncAggregate
  blsToExecutionChanges     : ProgressiveList SignedBLSToExecutionChange
  signedExecutionPayloadBid : SignedExecutionPayloadBid
  payloadAttestations       : ProgressiveList PayloadAttestation
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
