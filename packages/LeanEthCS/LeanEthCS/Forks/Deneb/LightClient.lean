import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Deneb.LightClient`: Deneb light-client objects

Same five containers as Capella; `LightClientHeader` is widened to
carry Deneb's `ExecutionPayloadHeader` (with `blob_gas_used` /
`excess_blob_gas` fields). `LightClientHeader` itself remains
preset-invariant; the four downstream containers are preset-variant
via `SyncCommittee` / `SyncAggregate`.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Deneb

open SizzLean

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

/-- `LightClientHeader` (Deneb), Capella's header shape but with
Deneb's `ExecutionPayloadHeader`. Preset-invariant. -/
structure LightClientHeader where
  beacon          : BeaconBlockHeader
  execution       : ExecutionPayloadHeader
  executionBranch : Vector Bytes32 4
  deriving SSZRepr

ssz_struct_for_presets LightClientBootstrap in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  header                     : LightClientHeader,
  currentSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  currentSyncCommitteeBranch : Vector Bytes32 5

ssz_struct_for_presets LightClientUpdate in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  attestedHeader          : LightClientHeader,
  nextSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  nextSyncCommitteeBranch : Vector Bytes32 5,
  finalizedHeader         : LightClientHeader,
  finalityBranch          : Vector Bytes32 6,
  syncAggregate           : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot           : Slot

ssz_struct_for_presets LightClientFinalityUpdate in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  attestedHeader  : LightClientHeader,
  finalizedHeader : LightClientHeader,
  finalityBranch  : Vector Bytes32 6,
  syncAggregate   : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot   : Slot

ssz_struct_for_presets LightClientOptimisticUpdate in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  attestedHeader : LightClientHeader,
  syncAggregate  : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot  : Slot

end LeanEthCS.Forks.Deneb
