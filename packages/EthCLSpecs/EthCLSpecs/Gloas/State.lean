import EthCLSpecs.Gloas.Containers.Execution

/-!
# `EthCLSpecs.Gloas.State`: the Gloas `BeaconState` and its boxed view (EIP-7732)

The Gloas `BeaconState` (v1.7.0-alpha.10, 46 fields), then the `State` abbrev that
views it as an SSZ box. The eth1 fields remain; `latestExecutionPayloadHeader` is
dropped (its slot now holds `latestBlockHash`), and the ePBS block is appended
after `proposerLookahead`. The unchanged component containers are Fulu's
(`open EthCLSpecs.Fulu`); the ePBS containers are this fork's (`Containers`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- The Gloas `BeaconState` (v1.7.0-alpha.10, 46 fields). The eth1 fields remain;
`latestExecutionPayloadHeader` is dropped (its slot now holds `latestBlockHash`),
and the ePBS block is appended after `proposerLookahead`. The unchanged component
containers are Fulu's. -/
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
  validators                    : SSZList Validator Const.validatorRegistryLimit
  balances                      : SSZList Gwei Const.validatorRegistryLimit
  randaoMixes                   : Vector Bytes32 Const.epochsPerHistoricalVector
  slashings                     : Vector Gwei Const.epochsPerSlashingsVector
  previousEpochParticipation    : SSZList ParticipationFlags Const.validatorRegistryLimit
  currentEpochParticipation     : SSZList ParticipationFlags Const.validatorRegistryLimit
  justificationBits             : Bitvector Const.justificationBitsLength
  previousJustifiedCheckpoint   : Checkpoint
  currentJustifiedCheckpoint    : Checkpoint
  finalizedCheckpoint           : Checkpoint
  inactivityScores              : SSZList UInt64 Const.validatorRegistryLimit
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
  pendingDeposits               : SSZList PendingDeposit Const.pendingDepositsLimit
  pendingPartialWithdrawals     : SSZList PendingPartialWithdrawal Const.pendingPartialWithdrawalsLimit
  pendingConsolidations         : SSZList PendingConsolidation Const.pendingConsolidationsLimit
  proposerLookahead             : Vector ValidatorIndex (2 * Const.slotsPerEpoch)
  builders                      : SSZList Builder Const.builderRegistryLimit
  nextWithdrawalBuilderIndex    : BuilderIndex
  executionPayloadAvailability  : Bitvector Const.slotsPerHistoricalRoot
  builderPendingPayments        : Vector BuilderPendingPayment (2 * Const.slotsPerEpoch)
  builderPendingWithdrawals     : SSZList BuilderPendingWithdrawal Const.builderPendingWithdrawalsLimit
  latestExecutionPayloadBid     : ExecutionPayloadBid
  payloadExpectedWithdrawals    : SSZList Withdrawal Const.maxWithdrawalsPerPayload
  ptcWindow                     : Vector (Vector ValidatorIndex Const.ptcSize) (3 * Const.slotsPerEpoch)

-- The once-per-fork preamble: declares `State` (the boxed `BeaconState`) and the
-- concrete-domain `modifyState` (`SPEC_AUTHORING_MODEL.md` §6, `EthCLLib.Spec.Header`).
state_preamble BeaconState

end EthCLSpecs.Gloas
