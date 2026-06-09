import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Bellatrix.Execution
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Bellatrix.Block`: Bellatrix block hierarchy

The only delta over Altair is the new `execution_payload` field on
`BeaconBlockBody`. Operation-list types are still reused from Phase 0
unchanged. `SyncAggregate` is reused from Altair (preset-variant);
Bellatrix's `ExecutionPayload` is preset-invariant (no preset
constants in its SSZ shape).

Because of the preset-variant `SyncAggregate` reference, the
`BeaconBlockBody` / `BeaconBlock` / `SignedBeaconBlock` chain becomes
preset-variant.

## Caps (mainnet *and* minimal agree)

* `MAX_PROPOSER_SLASHINGS = 16`
* `MAX_ATTESTER_SLASHINGS = 2`
* `MAX_ATTESTATIONS = 128`
* `MAX_DEPOSITS = 16`
* `MAX_VOLUNTARY_EXITS = 16`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Bellatrix

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0
open LeanEthCS.Macros

ssz_struct_for_presets BeaconBlockBody in LeanEthCS.Forks.Bellatrix
    for [minimal, mainnet] where
  randaoReveal      : BLSSignature,
  eth1Data          : Eth1Data,
  graffiti          : Bytes32,
  proposerSlashings : SSZList ProposerSlashing 16,
  attesterSlashings : SSZList AttesterSlashing 2,
  attestations      : SSZList Attestation 128,
  deposits          : SSZList Deposit 16,
  voluntaryExits    : SSZList SignedVoluntaryExit 16,
  syncAggregate     : @%LeanEthCS.Forks.Altair.SyncAggregate,
  executionPayload  : ExecutionPayload

ssz_struct_for_presets BeaconBlock in LeanEthCS.Forks.Bellatrix
    for [minimal, mainnet] where
  slot          : Slot,
  proposerIndex : ValidatorIndex,
  parentRoot    : Root,
  stateRoot     : Root,
  body          : @%BeaconBlockBody

ssz_struct_for_presets SignedBeaconBlock in LeanEthCS.Forks.Bellatrix
    for [minimal, mainnet] where
  message   : @%BeaconBlock,
  signature : BLSSignature

end LeanEthCS.Forks.Bellatrix
