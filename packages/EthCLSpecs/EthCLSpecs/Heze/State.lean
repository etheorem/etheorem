import EthCLSpecs.Heze.Containers.InclusionList

/-!
# `EthCLSpecs.Heze.State`: the Heze `BeaconState` (EIP-8015)

Heze's `BeaconState` is Gloas's progressive container with the eth1 deposit machinery removed
(EIP-8015, new at v1.7.0-beta.4): `eth1_data`, `eth1_data_votes`, `eth1_deposit_index`, and
`deposit_requests_start_index` are gone. The container keeps the Gloas width of 46 and leaves
the four positions empty, `active_fields(width=46, gaps=(8, 9, 10, 28))`, so every remaining
field keeps its Gloas generalized index. `@[sizzlean_progressive_gaps 8 9 10 28]` carries that
mask. `latestExecutionPayloadBid` binds to Heze's bid (the extra `inclusionListBits` field).
`state_preamble` declares the boxed `State` and `modifyState`.

The `Containers.InclusionList` import is the load-order entry: it transitively pulls
`Heze.Inherited` (the inherited containers) and the `fork Heze from Gloas` lineage that
`inherit` resolves against. It is required; do not drop it.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

/-- The Heze `BeaconState` (EIP-8015, `heze/beacon-chain.md:178-231`): Gloas's 46-position
progressive container with the four eth1 deposit fields removed and their positions left as
mask gaps. -/
@[sizzlean_progressive, sizzlean_progressive_gaps 8 9 10 28]
forkcontainer BeaconState where
  genesisTime                   : UInt64
  genesisValidatorsRoot         : Root
  slot                          : Slot
  forkData                      : Fork
  latestBlockHeader             : BeaconBlockHeader
  blockRoots                    : Vector Root Const.slotsPerHistoricalRoot
  stateRoots                    : Vector Root Const.slotsPerHistoricalRoot
  historicalRoots               : SSZList Root Const.historicalRootsLimit
  -- [Modified in Heze:EIP8015] removed `eth1_data`, `eth1_data_votes`, `eth1_deposit_index`
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
  -- [Modified in Heze:EIP8015] removed `deposit_requests_start_index`
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

-- The once-per-fork preamble: declares `State` (the boxed `BeaconState`) and `modifyState`.
state_preamble BeaconState

end EthCLSpecs.Heze
