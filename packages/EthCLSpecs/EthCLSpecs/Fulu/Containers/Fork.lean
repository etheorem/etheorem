import EthCLSpecs.Fulu.Constants

/-!
# `EthCLSpecs.Fulu.Containers.Fork`: the fork-version container (load order row 3)

The fork-version pair the state threads, the first container above the
foundations (`SPECS_ARCHITECTURE.md` §3.1).

**Naming note.** SSZ conformance is by field *order*, not field name, so the
consensus `fork` field is named `forkData` where `BeaconState` carries it; the
container type itself is `Fork`. The wire format and root are unchanged.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The fork version pair plus its activation epoch. -/
forkcontainer Fork where
  previousVersion : Version
  currentVersion  : Version
  epoch           : Epoch

end EthCLSpecs.Fulu
