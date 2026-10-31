import EthCLSpecs.Heze.Constants

/-!
# `EthCLSpecs.Heze.Inherited`: the inherited containers (everything but the new IL family)

EIP-7805 adds the `InclusionList` family and redeclares `ExecutionPayloadBid` with
`inclusion_list_bits`. Every other Heze container keeps Gloas's field block byte for byte,
so each is
`inherit`ed: the ancestor's field block is re-declared in `EthCLSpecs.Heze`, giving a
distinct type with the same SSZ encoding (the inheritance mechanism,
`SPEC_AUTHORING_MODEL.md` §8). The ePBS containers other than the bid come from Gloas;
the component containers resolve through Gloas back to the definitions captured further
up the lineage. `BeaconState` and `BeaconBlockBody` are not inherited: `State` and `Block`
re-declare each as a progressive `forkcontainer` with the EIP-8015 mask gaps (`State` also
runs the `state_preamble` step). Only `BeaconBlock` / `SignedBeaconBlock` are `inherit`ed,
in `Block`, and their `body` binds to the re-declared body.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

-- Component containers. Gloas declared its own copies, so each of these resolves
-- one generation up rather than two.
inherit Checkpoint
inherit AttestationData
inherit Attestation
inherit IndexedAttestation
inherit AttesterSlashing
inherit BLSToExecutionChange
inherit BeaconBlockHeader
inherit ConsolidationRequest
inherit DepositData
inherit DepositMessage
inherit Deposit
inherit DepositRequest
inherit Eth1Data
inherit WithdrawalRequest
inherit Fork
inherit HistoricalSummary
inherit PendingConsolidation
inherit PendingDeposit
inherit PendingPartialWithdrawal
inherit SignedBeaconBlockHeader
inherit ProposerSlashing
inherit SignedBLSToExecutionChange
inherit VoluntaryExit
inherit SignedVoluntaryExit
inherit SyncAggregate
inherit SyncCommittee
inherit Validator
inherit Withdrawal
-- The runner's rewards-vector output container.
inherit Deltas

-- ePBS + EIP-8282 containers declared in Gloas. The bid is redeclared below.
inherit Builder
inherit BuilderDepositRequest
inherit BuilderExitRequest
inherit BuilderPendingWithdrawal
inherit BuilderPendingPayment
inherit ExecutionRequests
inherit PayloadAttestationData
inherit PayloadAttestation
inherit IndexedPayloadAttestation
inherit PayloadAttestationMessage
inherit ExecutionPayload
/-- Heze `ExecutionPayloadBid` (EIP-7805): Gloas's progressive bid plus
`inclusion_list_bits`. -/
@[sizzlean_progressive]
forkcontainer ExecutionPayloadBid where
  parentBlockHash       : Hash32
  parentBlockRoot       : Root
  blockHash             : Hash32
  prevRandao            : Bytes32
  feeRecipient          : ExecutionAddress
  gasLimit              : UInt64
  builderIndex          : BuilderIndex
  slot                  : Slot
  value                 : Gwei
  executionPayment      : Gwei
  blobKzgCommitments    : ProgressiveList KZGCommitment
  executionRequestsRoot : Root
  inclusionListBits     : Bitvector Const.inclusionListCommitteeSize

inherit SignedExecutionPayloadBid
inherit ExecutionPayloadEnvelope
inherit SignedExecutionPayloadEnvelope
inherit NewPayloadRequest

end EthCLSpecs.Heze
