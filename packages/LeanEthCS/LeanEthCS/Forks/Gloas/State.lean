import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Electra.PendingOperations
import LeanEthCS.Forks.Gloas.Primitives
import LeanEthCS.Forks.Gloas.Builder
import LeanEthCS.Forks.Gloas.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.State`: Gloas `BeaconState`

Tracks the main branch of consensus-specs. Gloas's `BeaconState`
diverges substantially from Fulu's via EIP-7732 (ePBS):

* **Removed:** `latest_execution_payload_header`
* **Added:** `latest_block_hash : Hash32`
* **Added:** `builders : List Builder BUILDER_REGISTRY_LIMIT`
* **Added:** `next_withdrawal_builder_index : BuilderIndex`
* **Added:** `execution_payload_availability : Bitvector SLOTS_PER_HISTORICAL_ROOT`
* **Added:** `builder_pending_payments : Vector BuilderPendingPayment (2 * SLOTS_PER_EPOCH)`
* **Added:** `builder_pending_withdrawals : List BuilderPendingWithdrawal BUILDER_PENDING_WITHDRAWALS_LIMIT`
* **Added:** `latest_execution_payload_bid : ExecutionPayloadBid`
* **Added:** `payload_expected_withdrawals : List Withdrawal MAX_WITHDRAWALS_PER_PAYLOAD`
* **Added:** `ptc_window : Vector (Vector ValidatorIndex PTC_SIZE) ((2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH)`

`MIN_SEED_LOOKAHEAD = 1` is preset-invariant, so `ptc_window`'s
outer length reduces to `3 * SLOTS_PER_EPOCH`, 24 (minimal) /
96 (mainnet). The inner `PTC_SIZE` is preset-sensitive (16 / 512).

The `proposer_lookahead` field carried over from Fulu remains.

Order is taken from `specs/gloas/beacon-chain.md` on the
consensus-specs main branch; SSZ is field-order-sensitive.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Capella (Withdrawal HistoricalSummary)
open LeanEthCS.Forks.Electra (PendingDeposit PendingPartialWithdrawal PendingConsolidation)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Gloas
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
  latestBlockHash              : Hash32,
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
  pendingConsolidations          : SSZList PendingConsolidation @@PENDING_CONSOLIDATIONS_LIMIT,
  proposerLookahead              : Vector ValidatorIndex (2 * @@SLOTS_PER_EPOCH),
  builders                       : SSZList Builder @@BUILDER_REGISTRY_LIMIT,
  nextWithdrawalBuilderIndex     : BuilderIndex,
  executionPayloadAvailability   : Bitvector @@SLOTS_PER_HISTORICAL_ROOT,
  builderPendingPayments         : Vector BuilderPendingPayment (2 * @@SLOTS_PER_EPOCH),
  builderPendingWithdrawals      : SSZList BuilderPendingWithdrawal @@BUILDER_PENDING_WITHDRAWALS_LIMIT,
  latestExecutionPayloadBid      : @%ExecutionPayloadBid,
  payloadExpectedWithdrawals     : SSZList Withdrawal @@MAX_WITHDRAWALS_PER_PAYLOAD,
  ptcWindow                      : Vector (Vector ValidatorIndex @@PTC_SIZE) (3 * @@SLOTS_PER_EPOCH)

end LeanEthCS.Forks.Gloas
