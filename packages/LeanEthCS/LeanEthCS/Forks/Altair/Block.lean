import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Altair.Block`: Altair block hierarchy

The only delta over Phase 0 is the new `sync_aggregate` field on
`BeaconBlockBody`. The operation-list types (`Attestation`,
`AttesterSlashing`, `Deposit`, `SignedVoluntaryExit`,
`ProposerSlashing`) are reused unchanged from Phase 0, their SSZ
shapes are identical.

Because the new `sync_aggregate` field references the preset-variant
`SyncAggregate`, the whole `BeaconBlockBody` becomes preset-variant,
and `BeaconBlock` / `SignedBeaconBlock` follow through their `body`
chain.

## Caps (mainnet *and* minimal agree)

* `MAX_PROPOSER_SLASHINGS = 16`
* `MAX_ATTESTER_SLASHINGS = 2`
* `MAX_ATTESTATIONS = 128`
* `MAX_DEPOSITS = 16`
* `MAX_VOLUNTARY_EXITS = 16`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Altair

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

-- `BeaconBlockBody` (Altair). Preset-variant only via the
-- `syncAggregate` field; everything else has fixed caps shared between
-- presets.
ssz_struct_for_presets BeaconBlockBody in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  randaoReveal      : BLSSignature,
  eth1Data          : Eth1Data,
  graffiti          : Bytes32,
  proposerSlashings : SSZList ProposerSlashing 16,
  attesterSlashings : SSZList AttesterSlashing 2,
  attestations      : SSZList Attestation 128,
  deposits          : SSZList Deposit 16,
  voluntaryExits    : SSZList SignedVoluntaryExit 16,
  syncAggregate     : @%SyncAggregate

ssz_struct_for_presets BeaconBlock in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  slot          : Slot,
  proposerIndex : ValidatorIndex,
  parentRoot    : Root,
  stateRoot     : Root,
  body          : @%BeaconBlockBody

ssz_struct_for_presets SignedBeaconBlock in LeanEthCS.Forks.Altair
    for [minimal, mainnet] where
  message   : @%BeaconBlock,
  signature : BLSSignature

end LeanEthCS.Forks.Altair
