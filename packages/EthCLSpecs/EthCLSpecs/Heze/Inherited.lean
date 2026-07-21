import EthCLSpecs.Heze.Constants
import EthCLSpecs.Gloas.Containers

/-!
# `EthCLSpecs.Heze.Inherited`: the inherited containers (everything but the new IL family)

At alpha.11 EIP-7805 adds only the `InclusionList` family; every other Heze container is
byte-identical to Gloas, so each is `inherit`ed: the ancestor's field block is re-declared
in `EthCLSpecs.Heze`, giving a distinct type with the same SSZ encoding (the inheritance
mechanism, `SPEC_AUTHORING_MODEL.md` §8). The bid, `ExecutionRequests`, and the ePBS
containers come from Gloas; the component containers resolve through Gloas back to the
definitions captured in Fulu. `BeaconState` / `BeaconBlock*` are inherited in
`State` / `Block` (they need the `state_preamble` / signed-wrapper steps).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

-- Component containers (walk to Fulu's captures).
inherit Checkpoint
inherit AttestationData
inherit Attestation
inherit IndexedAttestation
inherit AttesterSlashing
inherit BLSToExecutionChange
inherit BeaconBlockHeader
inherit ConsolidationRequest
inherit DepositData
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

-- ePBS + EIP-8282 containers (declared in Gloas; FOCIL leaves them untouched at alpha.11).
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
inherit ExecutionPayloadBid
inherit SignedExecutionPayloadBid
inherit ExecutionPayloadEnvelope
inherit SignedExecutionPayloadEnvelope

end EthCLSpecs.Heze
