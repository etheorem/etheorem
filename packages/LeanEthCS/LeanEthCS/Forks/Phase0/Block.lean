import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Phase0.Block`: `BeaconBlockBody`, `BeaconBlock`,
`SignedBeaconBlock`

The block hierarchy. `BeaconBlockBody` is the largest fixed-shape
variable-size container in Phase 0 (5 variable-size lists plus 3
fixed-size fields); `BeaconBlock` wraps it; `SignedBeaconBlock`
adds the BLS signature.

## Phase 0 cap constants (mainnet *and* minimal agree)

* `MAX_PROPOSER_SLASHINGS = 16`
* `MAX_ATTESTER_SLASHINGS = 2`
* `MAX_ATTESTATIONS = 128`
* `MAX_DEPOSITS = 16`
* `MAX_VOLUNTARY_EXITS = 16`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Phase0

open SizzLean

open SizzLean.Repr

open LeanEthCS

/-- `BeaconBlockBody`: the variable-size payload of a beacon block.
Three fixed-size fields (`randao_reveal`, `eth1_data`, `graffiti`)
plus five variable-size `List` fields that carry the
block's slashings, attestations, deposits, and voluntary exits. -/
structure BeaconBlockBody where
  randaoReveal      : BLSSignature
  eth1Data          : Eth1Data
  graffiti          : Bytes32
  proposerSlashings : SSZList ProposerSlashing 16
  attesterSlashings : SSZList AttesterSlashing 2
  attestations      : SSZList Attestation 128
  deposits          : SSZList Deposit 16
  voluntaryExits    : SSZList SignedVoluntaryExit 16
  deriving SSZRepr

/-- `BeaconBlock`: a proposer's block submission. Variable-size
container (the body field is variable). -/
structure BeaconBlock where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  body          : BeaconBlockBody
  deriving SSZRepr

/-- Signed wrapper around `BeaconBlock`. -/
structure SignedBeaconBlock where
  message   : BeaconBlock
  signature : BLSSignature
  deriving SSZRepr

end LeanEthCS.Forks.Phase0
