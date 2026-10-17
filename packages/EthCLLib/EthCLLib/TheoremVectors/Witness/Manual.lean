import Lean
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Witness.Manual`: the manual source

The manual source (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4): a named line's
`with` clause fixes inputs to author-written terms. When the manual terms
cover every input, the candidate is the manual bytes overlaid on the
serialized defaults, checked like any other. When they cover a strict
subset, the source answers `nothing` and the bit-vector source takes the
handoff: §9.4 hands the partial assignment to the solver for the rest.

The build error of §18 (a manual term the check rejects) is the command's
line-level call now that theorems split into disjuncts: a term may satisfy
the disjunct it was written for while another disjunct rejects it. The
command errors when a fully-covering set of manual terms wins no disjunct
of the run (§18's "the author claimed it works"), and a disjunct the
manual terms alone fail falls through to the next source.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- Does an input the manual terms do not cover have the binding's state
type? §9.4's manual fill answers `default` for the uncovered inputs, so a
state among them would take the empty state. -/
private def uncoveredHaveState (ctx : SearchCtx) (stmt : Statement) : Bool :=
  let manualPos := ctx.manualTerms.map (·.1)
  ((Array.range stmt.inputs.size).filter (fun i => !manualPos.contains i)).any
    (fun i => isStateType ctx.binding stmt.inputs[i]!.type)

/-- The manual source (§9.4). Applies when the probe holds serialized
manual bytes and no *uncovered* input is the fork's state: the source
overlays the manual bytes on the serialized defaults, so an uncovered
state input would take `default`, which §9.4's rule excludes. A covered
state input is the author's own term and fills the overlay. The cover
test (manual terms for every input, or the partial handoff to the
bit-vector source) sits in `search`, which reads the line's manual terms
against the statement. -/
def manualSource : WitnessSource where
  tag := .manual
  applies (ctx : SearchCtx) (stmt : Statement) (_ : Disjunct) :=
    !ctx.probe.manuals.isEmpty && !uncoveredHaveState ctx stmt
  search ctx stmt d := do
    unless ctx.manualTerms.size == stmt.inputs.size do
      -- §9.4: a partial set of manual terms goes to the bit-vector
      -- source's handoff
      return .nothing
    let a := ctx.probe.manuals.foldl (init := ctx.probe.defaults) fun acc (pos, b) =>
      if h : pos < acc.size then acc.set pos b else acc
    -- §9.4, the stage-4 outcome: the read-bounds gate runs before the
    -- check, so a manual term whose reads run past an end is an honest
    -- no-candidate and no panic prints
    unless (ctx.probe.safe d.index a).all (· == true) do
      return .nothing
    if !ctx.probe.check d.index a then
      -- the disjunct rejects the manual terms; the line-level error is
      -- the command's job
      return .nothing
    return .candidate a

end EthCLLib.TheoremVectors
