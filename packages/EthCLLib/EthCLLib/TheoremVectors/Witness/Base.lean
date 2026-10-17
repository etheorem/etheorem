import Lean
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Witness.Base`: the `default` source

The cheapest witness source (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4): serialize `default`
for every input and check. It is the one source that runs on a theorem with
a block input (§1.2). The command assembles it always, and alone when the
scope walk found a block input.

One exception, from the stage 2 outcome: the source never proposes
`default` for the fork's state. The empty state is not a reachable one, and
on it the spec's own loops run to their fuel bounds, so the candidate
either fails the check or burns the search; a theorem over the state gets
its witness from a manual term, a builder, or a draw instead. §9.4 states
the rule over the statement's input types, so it sits in `applies`, where
the search loop reads it, and `search` proposes the defaults alone.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The `default` source (§9.4): the probe's serialized defaults, checked
like any other candidate, and never over the fork's state. -/
def baseSource : WitnessSource where
  tag := .base
  applies (ctx : SearchCtx) (stmt : Statement) (_ : Case) :=
    !stmt.inputs.any (fun i => isStateType ctx.binding i.type)
  search ctx _ _ := return .candidate ctx.probe.defaults

end EthCLLib.TheoremVectors
