import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Phase0.State`: `HistoricalBatch` and `BeaconState`

The two Phase 0 composites whose SSZ shape varies between presets.
Emitted per-preset via `ssz_struct_for_presets`, which stamps out
matching `Minimal` and `Mainnet` variants from a single declaration.

## Preset-sensitive caps used here

* `SLOTS_PER_HISTORICAL_ROOT`: 64 (minimal) / 8192 (mainnet)
* `EPOCHS_PER_HISTORICAL_VECTOR`: 64 / 65536
* `EPOCHS_PER_SLASHINGS_VECTOR`: 64 / 8192
* `EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH`: 32 / 2048
* `MAX_ATTESTATIONS * SLOTS_PER_EPOCH`: 1024 / 4096
  (cap for `previous/current_epoch_attestations`)

## Preset-invariant caps used here (literal `Nat`s)

* `HISTORICAL_ROOTS_LIMIT = 16_777_216` (= 2^24)
* `VALIDATOR_REGISTRY_LIMIT = 1_099_511_627_776` (= 2^40)
* `JUSTIFICATION_BITS_LENGTH = 4`
* `MAX_ATTESTATIONS = 128`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Phase0

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Macros

ssz_struct_for_presets HistoricalBatch in LeanEthCS.Forks.Phase0
    for [minimal, mainnet] where
  blockRoots : Vector Root @@SLOTS_PER_HISTORICAL_ROOT,
  stateRoots : Vector Root @@SLOTS_PER_HISTORICAL_ROOT

ssz_struct_for_presets BeaconState in LeanEthCS.Forks.Phase0
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
  previousEpochAttestations  : SSZList PendingAttestation (128 * @@SLOTS_PER_EPOCH),
  currentEpochAttestations   : SSZList PendingAttestation (128 * @@SLOTS_PER_EPOCH),
  justificationBits          : Bitvector 4,
  previousJustifiedCheckpoint : Checkpoint,
  currentJustifiedCheckpoint  : Checkpoint,
  finalizedCheckpoint         : Checkpoint

end LeanEthCS.Forks.Phase0
