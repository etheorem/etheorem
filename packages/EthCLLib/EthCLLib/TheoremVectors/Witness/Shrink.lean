import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe

/-!
# `EthCLLib.TheoremVectors.Witness.Shrink`: the shrink loop

The shrink of §9.6: after a witness from the random source passes, ask
`probe.shrink` for smaller candidates, in `Shrinkable` order, and keep
the ones that pass the check. Repeat until no candidate passes or
`theorem_vectors.shrinkSteps` runs out. The scalars the solver chose are
not shrunk, because a solver value is a boundary point and shrinking
would move it; the probe's `shrink` face varies the container inputs
alone (§9.6), so the loop needs no per-input rule here.

Two cost rules shape the loop around §9.6's sketch, both recorded in
`IMPLEMENTATION_NOTES.md`: one `probe.shrink` call is walked past the
first passing candidate, because the candidates were all built from the
same serialized witness and the call's own cost is one state decode; and
a candidate is accepted whenever its wire size does not exceed the
current witness's, which keeps the walk monotone and drains the step
budget inside one or two calls. Each call's own cost is a full decode of
the drawn state, so a rule that accepts fewer candidates per call only
multiplies the calls. A later candidate of one list can still revert an
earlier round's field cut, since every candidate of a call derives from
the call's own witness; the budget bounds that, and the walk converges.
Length cuts sit first in a container's candidate list, so a smaller
witness is what the budget buys first.

A `!`-read past a shrunken container's end answers its default instead
of raising, and the default fails the check, so the candidate is
rejected and the loop moves on.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The wire size of a whole assignment. -/
private def assignmentSize (a : Assignment) : Nat :=
  a.foldl (fun acc b => acc + b.size) 0

/-- The shrink loop (§9.6). Returns the smallest passing witness found
within the step budget; a witness whose first shrink step fails comes
back unchanged. Each step is one accepted candidate. -/
def shrinkWitness (probe : Probe) (c : Case) (steps : Nat)
    (a : Assignment) : MetaM Assignment := do
  let mut current := a
  let mut size := assignmentSize a
  let mut budget := steps
  let mut progress := true
  while progress && budget > 0 do
    let candidates := probe.shrink current
    progress := false
    for cand in candidates do
      if budget == 0 then break
      let candSize := assignmentSize cand
      if candSize > size then continue
      -- §9.4, the stage-4 outcome: a candidate whose length cuts moved a
      -- collection below a scalar's index fails the bounds gate before
      -- the check, so the shrink's reads never run past an end
      unless (probe.safe c.index cand).all (· == true) do
        continue
      unless probe.check c.index cand do
        continue
      current := cand
      size := candSize
      budget := budget - 1
      progress := true
  return current

end EthCLLib.TheoremVectors
