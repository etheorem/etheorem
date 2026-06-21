import EthCLSpecs.Fulu.Containers.BeaconBlockHeader

/-!
# `EthCLSpecs.Fulu.Containers.Sync`: the Altair sync committee (load order row 12)

The state's `currentSyncCommittee` / `nextSyncCommittee` (`SPECS_ARCHITECTURE.md`
§3.1). The `SyncAggregate` a block carries lives with the block containers.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The Altair sync committee. -/
forkcontainer SyncCommittee where
  pubkeys         : Vector BLSPubkey Const.syncCommitteeSize
  aggregatePubkey : BLSPubkey

end EthCLSpecs.Fulu
