import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Altair.State`: Altair `BeaconState`

The Altair `BeaconState` replaces Phase 0's pair of
`PendingAttestation` lists with two `List[ParticipationFlags,
VALIDATOR_REGISTRY_LIMIT]` lists; adds an `inactivity_scores` list;
and threads in two `SyncCommittee` fields (current + next) that drive
the light-client subprotocol.

The container embeds the preset-sensitive constants
`SLOTS_PER_HISTORICAL_ROOT`, `EPOCHS_PER_ETH1_VOTING_PERIOD *
SLOTS_PER_EPOCH`, `EPOCHS_PER_HISTORICAL_VECTOR`, and
`EPOCHS_PER_SLASHINGS_VECTOR` directly in field types, and references
the preset-variant `SyncCommittee`. We emit per-preset structures
via `ssz_struct_for_presets`.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Altair

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

-- `BeaconState` (Altair), 24 fields. Preset-variant in 5 slots:
-- block_roots/state_roots (`SLOTS_PER_HISTORICAL_ROOT`),
-- eth1_data_votes (`EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH`),
-- randao_mixes (`EPOCHS_PER_HISTORICAL_VECTOR`),
-- slashings (`EPOCHS_PER_SLASHINGS_VECTOR`),
-- and the two `SyncCommittee` references.
ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Altair
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
  currentSyncCommittee       : @%SyncCommittee,
  nextSyncCommittee          : @%SyncCommittee

end LeanEthCS.Forks.Altair
