import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Probe

/-!
# `EthCLLib.TheoremVectors.Witness.Source`: the witness search

The source interface and the search loop (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). A
source proposes one candidate at a time; the probe's `check` (§9.3) is the
single arbiter, and a source whose candidate the check rejects has produced
nothing. The loop walks the sources in §9.2's fixed order, and the command
assembles that order per theorem: the stage-2 list is seed (§9.4) then base
(§9.4), the hint source (§9.8) prepends itself in stage 5, and the
bit-vector, built, and random sources slot in with their stages.

`SearchM` is `MetaM` at this stage. §9.2 gives it a budget counter, which
the random source's redraw loop (§9.4) needs; stage 4 widens the
abbreviation when that lands.

## Lean idioms annotated

- The loop is a fold over the source array with an early return, which the
  `for`/`match` form below states directly; no monad transformer is needed
  while one candidate per source is the whole interface.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- What one source answered (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). -/
inductive SearchStep where
  /-- A candidate; it goes through the probe's `check` before it counts. -/
  | candidate (a : Assignment)
  /-- This source has no candidate; try the next. -/
  | nothing
  /-- The source proved the hypotheses vacuous; stop the loop. -/
  | unsat

/-- One run of the search: the probe, its build-time description, the
binding, and the preset (§9.2's `SearchCtx`; the seed options and the author
seeds ride the probe's `seeds` field, which the command fixes at build
time). -/
structure SearchCtx where
  probe   : Probe
  info    : ProbeInfo
  binding : ForkBinding
  preset  : PresetId

/-- The search monad: `MetaM` with no state of its own yet. The budget
counter of §9.2 arrives with the random source's redraw loop (§9.4), which
is stage 4. -/
abbrev SearchM (α : Type) : Type := MetaM α

/-- One strategy that proposes witnesses (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). -/
structure WitnessSource where
  /-- The wire tag the record names when this source wins. -/
  tag     : WitnessSourceTag
  /-- Can this source try this case at all? -/
  applies : Statement → Case → Bool
  /-- Produce one answer. -/
  search  : SearchCtx → Statement → Case → SearchM SearchStep

/-- The search loop over one case (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). A
candidate the check rejects falls through to the next source; an `unsat`
stops the loop, because no later source can find what does not exist. The
answer carries the winning source's tag, which the record names (§12.2). -/
def searchCase (sources : Array WitnessSource) (ctx : SearchCtx)
    (stmt : Statement) (c : Case) :
    SearchM (Except Failure (Assignment × WitnessSourceTag)) := do
  let mut tried : Array WitnessSourceTag := #[]
  for source in sources do
    unless source.applies stmt c do continue
    match ← source.search ctx stmt c with
    | .candidate a =>
      tried := tried.push source.tag
      if ctx.probe.check c.index a then
        return .ok (a, source.tag)
      -- the check is compiled `decide P`; a failed check falls through to
      -- the next source (§9.3)
    | .nothing => pure ()
    | .unsat =>
      tried := tried.push source.tag
      return .error .unsat
  return .error (.notFound tried)

end EthCLLib.TheoremVectors
