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
assembles that order per theorem: a line with seeds runs seed (§9.4) then
bit-vector (§9.4), a line without seeds runs base (§9.4) then bit-vector,
and a theorem with a block input runs base alone (§1.2). The hint source
(§9.8) prepends itself in stage 5; the built and random sources slot in
with their stages.

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
  /-- This source has no candidate; try the next. `detail` carries what a
  reader of the report should know: the atoms the solver abstracted, an
  input type outside its domain (§9.4). -/
  | nothing (detail : Option String := none)
  /-- The source proved the hypotheses vacuous; stop the loop. -/
  | unsat

/-- One run of the search: the probe, its build-time description, the
binding, the preset, and the telescope's free variables with this line's
seed terms (§9.2's `SearchCtx`; the seed *options* sit in the probe's
`seeds` field, which the command fixes at build time).

The free variables are telescope-local: like the statement's expressions,
they are valid only inside the reader's fold, which the whole search runs
in. The bit-vector source substitutes the instance variables with the
preset's constants when it evaluates a seeded term (§11.2's
substitution), so the context carries both sides of that rewrite. -/
structure SearchCtx where
  probe   : Probe
  info    : ProbeInfo
  binding : ForkBinding
  preset  : PresetId
  /-- One free variable per value input, aligned with `stmt.inputs`. -/
  inputFvars : Array Expr
  /-- One free variable per instance binder, aligned with
  `stmt.instances`. -/
  instFvars  : Array Expr
  /-- The instance constant each instance binder fixes at this preset
  (§10), aligned with `stmt.instances`. -/
  instConsts : Array Name
  /-- The author seed terms of this line, with their input positions
  (§14.3). Empty when the line named none. -/
  seedTerms  : Array (Nat × Expr)

/-- The search monad: `MetaM` with no state of its own yet. The budget
counter of §9.2 arrives with the random source's redraw loop (§9.4), which
is stage 4. -/
abbrev SearchM (α : Type) : Type := MetaM α

/-- One strategy that proposes witnesses (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). -/
structure WitnessSource where
  /-- The wire tag the record names when this source wins. -/
  tag     : WitnessSourceTag
  /-- Can this source try this case at all? The search context is in
  scope, so a rule that reads the binding's state type or the probe's
  seeds sits here (§9.4's state rule). -/
  applies : SearchCtx → Statement → Case → Bool
  /-- Produce one answer. -/
  search  : SearchCtx → Statement → Case → SearchM SearchStep

/-- Is the input type the binding's state container? §9.4's rule: no source
proposes `default` for it, so a source that would fill the input from the
serialized defaults answers `nothing`. -/
def isStateType (binding : ForkBinding) (t : Expr) : Bool :=
  match t.getAppFn with
  | .const c _ => c == binding.stateType
  | _ => false

/-- The search loop over one case (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). A
candidate the check rejects falls through to the next source; an `unsat`
stops the loop, because no later source can find what does not exist. The
answer carries the winning source's tag, which the record names (§12.2). A
`notFound` names every source that ran on the case, whether or not it
proposed a candidate, and carries the details the sources reported. -/
def searchCase (sources : Array WitnessSource) (ctx : SearchCtx)
    (stmt : Statement) (c : Case) :
    SearchM (Except Failure (Assignment × WitnessSourceTag)) := do
  let mut tried : Array WitnessSourceTag := #[]
  let mut details : Array String := #[]
  for source in sources do
    unless source.applies ctx stmt c do continue
    -- §9.2: the reason names every source that ran
    tried := tried.push source.tag
    match ← source.search ctx stmt c with
    | .candidate a =>
      if ctx.probe.check c.index a then
        return .ok (a, source.tag)
      -- the check is compiled `decide P`; a failed check falls through to
      -- the next source (§9.3)
    | .nothing detail =>
      details := details ++ detail.toArray
    | .unsat =>
      return .error .unsat
  return .error (.notFound tried details)

end EthCLLib.TheoremVectors
