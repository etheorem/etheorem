import LeanEthCS.Forks.Electra.Block
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Fulu.Block`: Fulu block hierarchy

At consensus-spec-tests v1.5.0, Fulu inherits Electra's
`BeaconBlockBody` / `BeaconBlock` / `SignedBeaconBlock` *verbatim*
(SSZ shape unchanged; only execution-payload validation logic
differs). We re-export the Electra variants as `abbrev` aliases so
the CLI's `fulu:BeaconBlock` dispatch path resolves to a Fulu-named
type with the same SSZRepr instance.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Fulu

open SizzLean

abbrev BeaconBlockBody.Minimal := LeanEthCS.Forks.Electra.BeaconBlockBody.Minimal
abbrev BeaconBlockBody.Mainnet := LeanEthCS.Forks.Electra.BeaconBlockBody.Mainnet

abbrev BeaconBlock.Minimal := LeanEthCS.Forks.Electra.BeaconBlock.Minimal
abbrev BeaconBlock.Mainnet := LeanEthCS.Forks.Electra.BeaconBlock.Mainnet

abbrev SignedBeaconBlock.Minimal := LeanEthCS.Forks.Electra.SignedBeaconBlock.Minimal
abbrev SignedBeaconBlock.Mainnet := LeanEthCS.Forks.Electra.SignedBeaconBlock.Mainnet

end LeanEthCS.Forks.Fulu
