import EthCLSpecs.Heze.Containers.InclusionList

/-!
# `EthCLSpecs.Heze.Block`: the Heze block containers (EIP-8015)

Heze's `BeaconBlockBody` is Gloas's progressive container without `eth1_data` and `deposits`
(EIP-8015, new at v1.7.0-beta.4), whose positions stay as mask gaps,
`active_fields(width=13, gaps=(1, 6))`, so the remaining fields keep their Gloas generalized
indices. `signedExecutionPayloadBid` binds to Heze's bid. `BeaconBlock` / `SignedBeaconBlock`
are Gloas's, `inherit`ed verbatim, and their `body` binds to the body declared here.
The `Containers.InclusionList` import looks unused but is required: it transitively loads
`Heze.Inherited` and the `fork Heze from Gloas` declaration that `inherit` resolves
against. Do not remove it.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

/-- The Heze `BeaconBlockBody` (EIP-8015, `heze/beacon-chain.md:154-172`): Gloas's 13-position
progressive body with `eth1_data` and `deposits` removed and their positions left as mask
gaps. -/
@[sizzlean_progressive, sizzlean_progressive_gaps 1 6]
forkcontainer BeaconBlockBody where
  randaoReveal              : BLSSignature
  -- [Modified in Heze:EIP8015] removed `eth1_data`
  graffiti                  : Bytes32
  proposerSlashings         : ProgressiveList ProposerSlashing
  attesterSlashings         : ProgressiveList AttesterSlashing
  attestations              : ProgressiveList Attestation
  -- [Modified in Heze:EIP8015] removed `deposits`
  voluntaryExits            : ProgressiveList SignedVoluntaryExit
  syncAggregate             : SyncAggregate
  blsToExecutionChanges     : ProgressiveList SignedBLSToExecutionChange
  signedExecutionPayloadBid : SignedExecutionPayloadBid
  payloadAttestations       : ProgressiveList PayloadAttestation
  parentExecutionRequests   : ExecutionRequests

inherit BeaconBlock
inherit SignedBeaconBlock

end EthCLSpecs.Heze
