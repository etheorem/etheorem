import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Heze.Operations`: the inherited operation handlers (Gloas over Heze state)

EIP-7805 changes no block operation. Every Gloas operation handler (the inherited
non-ePBS ones and the ePBS-modified / EIP-8282 builder ones) is `inherit`ed over Heze
state, in Gloas's order. `addressOfCred` is a plain `def` in Gloas, and only the capturing
declaration forms (`forkdef` / `forkcontainer` / `forkstruct`, `SPEC_AUTHORING_MODEL.md`
§8.5) are stored for `inherit` to replay, so it is restated here before its first use.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

state_section

/-- `withdrawal_credentials[12:]` as a 20-byte execution address. Restated from Gloas
(a plain `def` rather than an inheritable `forkdef`). -/
private def addressOfCred (wc : Bytes32) : ExecutionAddress := Vector.ofFn (fun i : Fin 20 => wc[12 + i.val])

inherit isSlashableAttestationData
inherit isValidIndexedAttestation
inherit isValidSwitchToCompoundingRequest
inherit getAttestingIndices
inherit processAttesterSlashing
inherit processBlockHeader
inherit processBlsToExecutionChange
inherit processWithdrawalRequest
inherit processConsolidationRequest
inherit processDepositRequest
inherit processVoluntaryExit
inherit processSyncAggregate
inherit isBuilderIndex
inherit toBuilderIndex
inherit isActiveBuilder
inherit getPendingBalanceToWithdrawForBuilder
inherit builderPaymentIndex
inherit isBuilderWithdrawalCredential
inherit isPendingValidator
inherit initiateBuilderExit
inherit getIndexForNewBuilder
inherit addBuilderToRegistry
inherit applyDepositForBuilder
inherit onboardBuildersFromPendingDeposits
inherit isValidBuilderDepositSignature
inherit processBuilderDepositRequest
inherit processBuilderExitRequest
inherit processProposerSlashing
inherit isAttestationSameSlot
inherit getAttestationParticipationFlagIndices
inherit processAttestation
inherit getPtc
inherit getIndexedPayloadAttestation
inherit isValidIndexedPayloadAttestation
inherit processPayloadAttestation
inherit convertBuilderIndexToValidatorIndex
inherit canBuilderCoverBid
inherit verifyExecutionPayloadBidSignature
inherit settleBuilderPayment
inherit processExecutionPayloadBid
inherit applyParentExecutionPayload
inherit processParentExecutionPayload

end

end EthCLSpecs.Heze
