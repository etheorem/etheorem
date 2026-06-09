import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Capella.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Capella.LightClient`: Capella light-client objects

Capella widens `LightClientHeader` with two new fields:

* `execution : ExecutionPayloadHeader`: the execution-layer
  header of the same block as `beacon.execution_payload_root`.
* `execution_branch : Vector[Bytes32, EXECUTION_PAYLOAD_GINDEX_LOG2]`:
  Merkle branch proving that header is at the canonical gindex
  inside the body root.

`LightClientHeader` is preset-invariant (its embedded
`ExecutionPayloadHeader` is itself preset-invariant in Capella). The
four downstream containers (`LightClientBootstrap`, `Update`,
`FinalityUpdate`, `OptimisticUpdate`) reference the preset-variant
`SyncCommittee` / `SyncAggregate`, so they become preset-variant too.

## Constants (preset-invariant)

* `EXECUTION_PAYLOAD_GINDEX_LOG2 = 4`
* `FINALIZED_ROOT_GINDEX_LOG2 = 6`
* `NEXT_SYNC_COMMITTEE_GINDEX_LOG2 = 5`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Capella

open SizzLean

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

/-- `LightClientHeader` (Capella): Altair header + execution-payload
header + its Merkle branch. Preset-invariant. -/
structure LightClientHeader where
  beacon          : BeaconBlockHeader
  execution       : ExecutionPayloadHeader
  executionBranch : Vector Bytes32 4
  deriving SSZRepr

ssz_struct_for_presets LightClientBootstrap in LeanEthCS.Forks.Capella
    for [minimal, mainnet] where
  header                     : LightClientHeader,
  currentSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  currentSyncCommitteeBranch : Vector Bytes32 5

ssz_struct_for_presets LightClientUpdate in LeanEthCS.Forks.Capella
    for [minimal, mainnet] where
  attestedHeader          : LightClientHeader,
  nextSyncCommittee       : @%LeanEthCS.Forks.Altair.SyncCommittee,
  nextSyncCommitteeBranch : Vector Bytes32 5,
  finalizedHeader         : LightClientHeader,
  finalityBranch          : Vector Bytes32 6,
  syncAggregate           : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot           : Slot

ssz_struct_for_presets LightClientFinalityUpdate in LeanEthCS.Forks.Capella
    for [minimal, mainnet] where
  attestedHeader  : LightClientHeader,
  finalizedHeader : LightClientHeader,
  finalityBranch  : Vector Bytes32 6,
  syncAggregate   : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot   : Slot

ssz_struct_for_presets LightClientOptimisticUpdate in LeanEthCS.Forks.Capella
    for [minimal, mainnet] where
  attestedHeader : LightClientHeader,
  syncAggregate  : @%LeanEthCS.Forks.Altair.SyncAggregate,
  signatureSlot  : Slot

end LeanEthCS.Forks.Capella
