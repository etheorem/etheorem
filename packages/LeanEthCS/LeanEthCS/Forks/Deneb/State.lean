import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Deneb.State`: Deneb `BeaconState`

Same field layout as Capella's `BeaconState`, but the
`latest_execution_payload_header` is now Deneb's wider
`ExecutionPayloadHeader` (carrying the new blob-gas fields).
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Deneb

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Forks.Capella (HistoricalSummary)
open LeanEthCS.Macros

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Deneb
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

end LeanEthCS.Forks.Deneb
