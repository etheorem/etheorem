import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Execution
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Capella.State`: Capella `BeaconState`

Three fields over Bellatrix's state:

* `next_withdrawal_index : WithdrawalIndex`
* `next_withdrawal_validator_index : ValidatorIndex`
* `historical_summaries : List[HistoricalSummary, HISTORICAL_ROOTS_LIMIT]`

The legacy `historical_roots` list is *frozen* at the fork: new
entries go to `historical_summaries` instead. The
`latest_execution_payload_header` is Capella's wider variant (with
`withdrawals_root`), preset-invariant.

The state is preset-variant via the same field constants as Altair
plus the preset-variant `SyncCommittee` references.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Capella

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Capella
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
  latestExecutionPayloadHeader : ExecutionPayloadHeader,
  nextWithdrawalIndex          : WithdrawalIndex,
  nextWithdrawalValidatorIndex : ValidatorIndex,
  historicalSummaries          : SSZList HistoricalSummary 16777216

end LeanEthCS.Forks.Capella
