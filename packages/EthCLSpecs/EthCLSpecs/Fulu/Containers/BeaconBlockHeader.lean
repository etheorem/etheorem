import EthCLSpecs.Fulu.Containers.Eth1Data

/-!
# `EthCLSpecs.Fulu.Containers.BeaconBlockHeader`: the block header (load order row 7)

The header threaded through the state as `latestBlockHeader`
(`SPECS_ARCHITECTURE.md` §3.1).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The block header threaded through the state. -/
forkcontainer BeaconBlockHeader where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  bodyRoot      : Root

end EthCLSpecs.Fulu
