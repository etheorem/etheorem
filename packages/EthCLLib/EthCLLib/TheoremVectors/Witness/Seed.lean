import Lean
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Witness.Seed`: the author-seed source

The seed source (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4): a named line's `with` clause
fixes some inputs to author-written terms, the probe serializes them
(§9.4, through `probe.seeds`), and stage 2 fills the unseeded inputs with
their defaults. §9.4 hands the partial assignment to the bit-vector source
for the rest; that source lands in stage 3, and the plan's stage 3
acceptance revisits the default fill then.

A seed that fails the check is a build error, because the author claimed it
works (§9.4, §18). The source answers `nothing` for a theorem whose line
named no seeds; the loop skips it.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The seed source (§9.4). Applies when the probe holds serialized seeds,
which only a named line's `with` clause puts there. The candidate is the
seeds overlaid, in input order, on the serialized defaults. -/
def seedSource : WitnessSource where
  tag := .seed
  applies _ _ := true
  search ctx stmt c := do
    if ctx.probe.seeds.isEmpty then
      return .nothing
    let a := ctx.probe.seeds.foldl (init := ctx.probe.defaults) fun acc (pos, b) =>
      if h : pos < acc.size then acc.set pos b else acc
    if !ctx.probe.check c.index a then
      -- §9.4: a seed that fails the check is a build error, because the
      -- author claimed it works
      throwError "theorem_vectors: the author seed of `{stmt.thm}` fails \
        the check of case {c.index}; fix the seed or drop the `with` clause"
    return .candidate a

end EthCLLib.TheoremVectors
