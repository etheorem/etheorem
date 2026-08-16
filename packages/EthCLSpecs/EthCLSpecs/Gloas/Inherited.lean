import EthCLSpecs.Gloas.Constants

/-!
# `EthCLSpecs.Gloas.Inherited`: the inherited component containers

EIP-7732 leaves the consensus component containers (`Validator`, `Checkpoint`,
`Attestation`, the slashing / deposit / exit evidence, the sync structures, the
pending-queue records) byte-identical to Fulu. To keep the fork a *complete, flat
namespace* (`SPECS_ARCHITECTURE.md` §3.4) rather than reaching across the fork
boundary for these types, each is `inherit`ed here: the capture mechanism replays
Fulu's field block in the `EthCLSpecs.Gloas` namespace, so `EthCLSpecs.Gloas.Validator`
is a fresh structure with Fulu's exact fields and therefore Fulu's exact SSZ encoding
and Merkle root. The fork upgrade (`Gloas.Upgrade`) converts a Fulu value to its Gloas
twin field-by-field at the boundary, the price of the flat namespace.

The declarations are in dependency order (a container's field types are inherited
before it), so each replayed body's sibling references late-bind to the Gloas-local
copy: the constants and primitive aliases (`Const.…`, `Root`, `Gwei`, …) are this
fork's own by then (`Gloas/Types.lean`, `Gloas/Constants.lean`), and a bare
`Checkpoint` / `AttestationData` resolves to the copy declared just above. The ePBS
containers that EIP-7732 *changes* (`ExecutionPayload`, `BeaconBlockBody`, `BeaconBlock`,
the bid / envelope / payload-attestation types) are not here; they are this fork's own
(`Gloas.Containers`, `Gloas.Block`, `Gloas.State`).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

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

end EthCLSpecs.Gloas
