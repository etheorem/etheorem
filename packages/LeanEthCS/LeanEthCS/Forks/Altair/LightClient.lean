import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Altair.LightClient`: Altair light-client objects

The Altair light client protocol layers on Phase 0's
`BeaconBlockHeader` plus Altair's `SyncCommittee` / `SyncAggregate`.
Four of the five containers reference the preset-variant
`SyncCommittee` or `SyncAggregate`, so they become preset-variant too;
`LightClientHeader` itself is preset-invariant in Altair (it widens
in Capella).

## Merkle-branch depth constants

Global SSZ generalized-index *log₂* values, fixed across both presets:

* `FINALIZED_ROOT_GINDEX_LOG2 = 6`
* `NEXT_SYNC_COMMITTEE_GINDEX_LOG2 = 5`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Altair

open SizzLean

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

/-- `LightClientHeader` (Altair): one-field wrapper around a beacon
block header. Preset-invariant in Altair. -/
structure LightClientHeader where
  beacon : BeaconBlockHeader
  deriving SSZRepr

ssz_struct_for_presets LightClientBootstrap in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  header                     : LightClientHeader,
  currentSyncCommittee       : @%SyncCommittee,
  currentSyncCommitteeBranch : Vector Bytes32 5

ssz_struct_for_presets LightClientUpdate in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  attestedHeader          : LightClientHeader,
  nextSyncCommittee       : @%SyncCommittee,
  nextSyncCommitteeBranch : Vector Bytes32 5,
  finalizedHeader         : LightClientHeader,
  finalityBranch          : Vector Bytes32 6,
  syncAggregate           : @%SyncAggregate,
  signatureSlot           : Slot

ssz_struct_for_presets LightClientFinalityUpdate in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  attestedHeader  : LightClientHeader,
  finalizedHeader : LightClientHeader,
  finalityBranch  : Vector Bytes32 6,
  syncAggregate   : @%SyncAggregate,
  signatureSlot   : Slot

ssz_struct_for_presets LightClientOptimisticUpdate in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  attestedHeader : LightClientHeader,
  syncAggregate  : @%SyncAggregate,
  signatureSlot  : Slot

end LeanEthCS.Forks.Altair
