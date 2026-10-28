import EthCLSpecs.Gloas.Containers.Execution

/-!
# `EthCLSpecs.Gloas.State`: the Gloas `BeaconState` and its boxed view (EIP-7732)

The Gloas `BeaconState` (v1.7.0-beta.4, 46 fields), then the `State` abbrev that
views it as an SSZ box. The eth1 fields remain; `latestExecutionPayloadHeader` is
dropped (its slot now holds `latestBlockHash`), and the ePBS block is appended
after `proposerLookahead`. The unchanged component containers are this fork's
copies of Fulu's, replayed in `Inherited`; the ePBS containers are its own
(`Containers`).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

/-- The Gloas `BeaconState` (v1.7.0-beta.4, 46 fields). The eth1 fields remain;
`latestExecutionPayloadHeader` is dropped (its slot now holds `latestBlockHash`),
and the ePBS block is appended after `proposerLookahead`. The unchanged component
containers are the replayed copies in `Inherited`. EIP-7688 makes the container
progressive and turns the registry, participation, pending-queue, and builder
lists into `ProgressiveList`s. `historicalRoots`, `eth1DataVotes`, and
`historicalSummaries` stay capped lists. -/
@[sizzlean_progressive]
forkcontainer BeaconState where
  genesisTime                   : UInt64
  genesisValidatorsRoot         : Root
  slot                          : Slot
  forkData                      : Fork
  latestBlockHeader             : BeaconBlockHeader
  blockRoots                    : Vector Root Const.slotsPerHistoricalRoot
  stateRoots                    : Vector Root Const.slotsPerHistoricalRoot
  historicalRoots               : SSZList Root Const.historicalRootsLimit
  eth1Data                      : Eth1Data
  eth1DataVotes                 : SSZList Eth1Data (Const.epochsPerEth1VotingPeriod * Const.slotsPerEpoch)
  eth1DepositIndex              : UInt64
  validators                    : ProgressiveList Validator
  balances                      : ProgressiveList Gwei
  randaoMixes                   : Vector Bytes32 Const.epochsPerHistoricalVector
  slashings                     : Vector Gwei Const.epochsPerSlashingsVector
  previousEpochParticipation    : ProgressiveList ParticipationFlags
  currentEpochParticipation     : ProgressiveList ParticipationFlags
  justificationBits             : Bitvector Const.justificationBitsLength
  previousJustifiedCheckpoint   : Checkpoint
  currentJustifiedCheckpoint    : Checkpoint
  finalizedCheckpoint           : Checkpoint
  inactivityScores              : ProgressiveList UInt64
  currentSyncCommittee          : SyncCommittee
  nextSyncCommittee             : SyncCommittee
  latestBlockHash               : Hash32
  nextWithdrawalIndex           : WithdrawalIndex
  nextWithdrawalValidatorIndex  : ValidatorIndex
  historicalSummaries           : SSZList HistoricalSummary Const.historicalRootsLimit
  depositRequestsStartIndex     : UInt64
  depositBalanceToConsume       : Gwei
  exitBalanceToConsume          : Gwei
  earliestExitEpoch             : Epoch
  consolidationBalanceToConsume : Gwei
  earliestConsolidationEpoch    : Epoch
  pendingDeposits               : ProgressiveList PendingDeposit
  pendingPartialWithdrawals     : ProgressiveList PendingPartialWithdrawal
  pendingConsolidations         : ProgressiveList PendingConsolidation
  proposerLookahead             : Vector ValidatorIndex (2 * Const.slotsPerEpoch)
  builders                      : ProgressiveList Builder
  nextWithdrawalBuilderIndex    : BuilderIndex
  executionPayloadAvailability  : Bitvector Const.slotsPerHistoricalRoot
  builderPendingPayments        : Vector BuilderPendingPayment (2 * Const.slotsPerEpoch)
  builderPendingWithdrawals     : ProgressiveList BuilderPendingWithdrawal
  latestExecutionPayloadBid     : ExecutionPayloadBid
  payloadExpectedWithdrawals    : ProgressiveList Withdrawal
  ptcWindow                     : Vector (Vector ValidatorIndex Const.ptcSize) (3 * Const.slotsPerEpoch)

-- The once-per-fork preamble: declares `State` (the boxed `BeaconState`) and the
-- concrete-domain `modifyState` (`SPEC_AUTHORING_MODEL.md` §6, `EthCLLib.Spec.Header`).
state_preamble BeaconState

end EthCLSpecs.Gloas
