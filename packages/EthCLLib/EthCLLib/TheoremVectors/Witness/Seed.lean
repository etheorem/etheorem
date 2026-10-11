import Lean
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Witness.Seed`: the author-seed source

The seed source (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4): a named line's `with` clause
fixes inputs to author-written terms. When the seeds cover every input, the
candidate is the seeds overlaid on the serialized defaults, checked like any
other. When they cover a strict subset, the source answers `nothing` and
the bit-vector source takes the handoff: §9.4 hands the partial assignment
to the solver for the rest.

The build error of §18 (a seed the check rejects) is the command's line-level
call now that theorems split into cases: a seed may satisfy the case it was
written for while another disjunct rejects it. The command errors when a
fully-covering seed wins no case of the run (§18's "the author claimed it
works"), and a case the seed alone fails falls through to the next source.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- Does an unseeded input have the binding's state type? §9.4's seed fill
answers `default` for the unseeded inputs, so a state among them would
take the empty state. -/
private def unseededHaveState (ctx : SearchCtx) (stmt : Statement) : Bool :=
  let seeded := ctx.seedTerms.map (·.1)
  ((Array.range stmt.inputs.size).filter (fun i => !seeded.contains i)).any
    (fun i => isStateType ctx.binding stmt.inputs[i]!.type)

/-- The seed source (§9.4). Applies when the probe holds serialized seeds
and no *unseeded* input is the fork's state: the source overlays the seeds
on the serialized defaults, so an unseeded state input would take
`default`, which §9.4's rule excludes. A seeded state input is the
author's own term and fills the overlay. The cover test (seeds for every
input, or the partial handoff to the bit-vector source) sits in `search`,
which reads the line's seeds against the statement. -/
def seedSource : WitnessSource where
  tag := .seed
  applies (ctx : SearchCtx) (stmt : Statement) (_ : Case) :=
    !ctx.probe.seeds.isEmpty && !unseededHaveState ctx stmt
  search ctx stmt c := do
    unless ctx.seedTerms.size == stmt.inputs.size do
      -- §9.4: a partial seed goes to the bit-vector source's handoff
      return .nothing
    let a := ctx.probe.seeds.foldl (init := ctx.probe.defaults) fun acc (pos, b) =>
      if h : pos < acc.size then acc.set pos b else acc
    if !ctx.probe.check c.index a then
      -- the case rejects the seed; the line-level error is the command's
      return .nothing
    return .candidate a

end EthCLLib.TheoremVectors
