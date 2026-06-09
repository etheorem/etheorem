import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Electra.LightClient`: Electra light-client objects

Electra inherits Deneb's light-client SSZ shapes verbatim (no field
changes; only Merkle generalized-index numbering shifts, which is a
proof-side concern, not an SSZ-shape concern).

We re-declare them here so the dispatch identifier `electra:LightClientX`
binds cleanly. The implementations are byte-identical to Deneb's.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Electra

open SizzLean

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

/-- `LightClientHeader` (Electra), same as Deneb's. -/
structure LightClientHeader where
  beacon          : BeaconBlockHeader
  execution       : LeanEthCS.Forks.Deneb.ExecutionPayloadHeader
  executionBranch : Vector Bytes32 4
  deriving SSZRepr

-- Electra widens the Altair light-client branches from `floorlog2(gindex)`
-- of the *Altair* `BeaconState` to that of the Electra `BeaconState`,
-- whose gindex values are larger (more state fields) and therefore have
-- deeper Merkle paths. Per the Electra sync-protocol spec at v1.5.0:
--   `FINALIZED_ROOT_GINDEX_ELECTRA = 169`        →  depth 7
--   `CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA = 86` →  depth 6
--   `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA = 87`    →  depth 6

ssz_struct_for_presets LightClientBootstrap in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  header                     : LightClientHeader,
  currentSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  currentSyncCommitteeBranch : Vector Bytes32 6

ssz_struct_for_presets LightClientUpdate in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  attestedHeader          : LightClientHeader,
  nextSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  nextSyncCommitteeBranch : Vector Bytes32 6,
  finalizedHeader         : LightClientHeader,
  finalityBranch          : Vector Bytes32 7,
  syncAggregate           : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot           : Slot

ssz_struct_for_presets LightClientFinalityUpdate in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  attestedHeader  : LightClientHeader,
  finalizedHeader : LightClientHeader,
  finalityBranch  : Vector Bytes32 7,
  syncAggregate   : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot   : Slot

ssz_struct_for_presets LightClientOptimisticUpdate in LeanEthCS.Forks.Electra
    for [minimal, mainnet] where
  attestedHeader : LightClientHeader,
  syncAggregate  : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot  : Slot

end LeanEthCS.Forks.Electra
