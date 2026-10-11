import Lean
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Witness.Base`: the `default` source

The cheapest witness source (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4): serialize `default`
for every input and check. It is the one source that runs on a theorem with
a block input (§1.2), where `initializePtcWindow_lt`'s `i = 0` satisfies the
hypothesis and the vector is written. The command assembles it always, and
alone when the scope walk found a block input.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The `default` source (§9.4): the probe's serialized defaults, checked
like any other candidate. -/
def baseSource : WitnessSource where
  tag := .base
  applies _ _ := true
  search ctx _ _ := return .candidate ctx.probe.defaults

end EthCLLib.TheoremVectors
