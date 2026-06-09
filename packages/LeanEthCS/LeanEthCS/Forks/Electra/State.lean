import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.Forks.Electra.PendingOperations
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Electra.State`: Electra `BeaconState`

Adds 9 fields over Deneb's state (all EIP-6110 / EIP-7251):

* `deposit_requests_start_index : uint64`
* `deposit_balance_to_consume : Gwei`
* `exit_balance_to_consume : Gwei`
* `earliest_exit_epoch : Epoch`
* `consolidation_balance_to_consume : Gwei`
* `earliest_consolidation_epoch : Epoch`
* `pending_deposits : List[PendingDeposit, PENDING_DEPOSITS_LIMIT]`
* `pending_partial_withdrawals : List[PendingPartialWithdrawal,
   PENDING_PARTIAL_WITHDRAWALS_LIMIT]`
* `pending_consolidations : List[PendingConsolidation,
   PENDING_CONSOLIDATIONS_LIMIT]`

`PENDING_DEPOSITS_LIMIT = 134_217_728` is preset-invariant.
`PENDING_PARTIAL_WITHDRAWALS_LIMIT` (64 / 134_217_728) and
`PENDING_CONSOLIDATIONS_LIMIT` (64 / 262_144) are preset-variant.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Electra

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Capella (HistoricalSummary)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  genesisTime                : UInt64,
  genesisValidatorsRoot      : Root,
  slot                       : Slot,
  fork                       : Fork,
  latestBlockHeader          : BeaconBlockHeader,
  blockRoots                 : Vector Root @@SLOTS_PER_HISTORICAL_ROOT,
  stateRoots                 : Vector Root @@SLOTS_PER_HISTORICAL_ROOT,
  historicalRoots            : SSZList Root 16777216,
  eth1Data                   : Eth1Data,
  eth1DataVotes              : SSZList Eth1Data (@@EPOCHS_PER_ETH1_VOTING_PERIOD * @@SLOTS_PER_EPOCH),
  eth1DepositIndex           : UInt64,
  validators                 : SSZList Validator 1099511627776,
  balances                   : SSZList Gwei 1099511627776,
  randaoMixes                : Vector Bytes32 @@EPOCHS_PER_HISTORICAL_VECTOR,
  slashings                  : Vector Gwei @@EPOCHS_PER_SLASHINGS_VECTOR,
  previousEpochParticipation : SSZList ParticipationFlags 1099511627776,
  currentEpochParticipation  : SSZList ParticipationFlags 1099511627776,
  justificationBits          : Bitvector 4,
  previousJustifiedCheckpoint : Checkpoint,
  currentJustifiedCheckpoint  : Checkpoint,
  finalizedCheckpoint         : Checkpoint,
  inactivityScores           : SSZList UInt64 1099511627776,
  currentSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  nextSyncCommittee          : @%LeanEthCS.Forks.Altair.SyncCommittee,
  latestExecutionPayloadHeader : LeanEthCS.Forks.Deneb.ExecutionPayloadHeader,
  nextWithdrawalIndex          : WithdrawalIndex,
  nextWithdrawalValidatorIndex : ValidatorIndex,
  historicalSummaries          : SSZList HistoricalSummary 16777216,
  depositRequestsStartIndex      : UInt64,
  depositBalanceToConsume        : Gwei,
  exitBalanceToConsume           : Gwei,
  earliestExitEpoch              : Epoch,
  consolidationBalanceToConsume  : Gwei,
  earliestConsolidationEpoch     : Epoch,
  pendingDeposits                : SSZList PendingDeposit 134217728,
  pendingPartialWithdrawals      : SSZList PendingPartialWithdrawal @@PENDING_PARTIAL_WITHDRAWALS_LIMIT,
  pendingConsolidations          : SSZList PendingConsolidation @@PENDING_CONSOLIDATIONS_LIMIT

end LeanEthCS.Forks.Electra
