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
# `LeanEthCS.Forks.Fulu.State`: Fulu `BeaconState`

Tracks the main branch of consensus-specs (post-v1.5.0): Fulu's
`BeaconState` is Electra's shape plus one new field,
`proposer_lookahead`, introduced by EIP-7917.

* `proposer_lookahead : Vector ValidatorIndex
    ((MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH)`

  `MIN_SEED_LOOKAHEAD = 1` is preset-invariant, so the vector length
  reduces to `2 * SLOTS_PER_EPOCH`, 16 (minimal) / 64 (mainnet).

The remaining 36 fields are byte-for-byte identical to Electra's
`BeaconState`. We re-declare the full container here rather than
extending Electra's because Lean doesn't have first-class struct
inheritance for `ssz_struct_for_presets`, and the field-order
sensitivity of SSZ makes a "wrap and add" alternative just as long.

Pre-v1.5.0 conformance test vectors (consensus-spec-tests ≤ v1.5.0)
expected Fulu == Electra; the bump to v1.6.0-beta.0 (see
`scripts/run_conformance.py`) brings the upstream vectors in line
with the post-v1.5.0 shape this file declares.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Fulu

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Capella (HistoricalSummary)
open LeanEthCS.Forks.Electra (PendingDeposit PendingPartialWithdrawal PendingConsolidation)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Fulu
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
  pendingConsolidations          : SSZList PendingConsolidation @@PENDING_CONSOLIDATIONS_LIMIT,
  proposerLookahead              : Vector ValidatorIndex (2 * @@SLOTS_PER_EPOCH)

end LeanEthCS.Forks.Fulu
