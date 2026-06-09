import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Bellatrix.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Bellatrix.State`: Bellatrix `BeaconState`

Adds one field over Altair's `BeaconState`:

* `latest_execution_payload_header : ExecutionPayloadHeader`

Bellatrix's `ExecutionPayloadHeader` is preset-invariant, but the
preceding fields embed `SLOTS_PER_HISTORICAL_ROOT`,
`EPOCHS_PER_HISTORICAL_VECTOR`, `EPOCHS_PER_SLASHINGS_VECTOR`, and
`EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH`, plus the
preset-variant `SyncCommittee` reference, so the whole state is
preset-variant.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Bellatrix

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Bellatrix
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
  latestExecutionPayloadHeader : ExecutionPayloadHeader

end LeanEthCS.Forks.Bellatrix
