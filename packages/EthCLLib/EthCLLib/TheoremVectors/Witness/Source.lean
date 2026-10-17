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
assembles that order per theorem: the hint source (§9.8) runs first on
every list, the reuse source (§10) follows it, then a line with manual
terms runs manual (§9.4) then bit-vector (§9.4), a line without manual
terms runs base (§9.4) then bit-vector, and a theorem with a block input
runs base alone (§1.2).
The built source (§9.9) follows the bit-vector source, and the random
source and the shrink close the list.

`SearchM` is `MetaM`: §9.2's budget counter stayed unnecessary, because
the redraw loop's budget is the `randomDraws` option per disjunct and the
per-run heartbeat budget bounds the whole.

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
  /-- A candidate; it goes through the probe's `check` before it counts.
  `tag?` names the source the record carries when this candidate wins,
  `none` for the proposing source's own tag: the hint source (§9.8)
  proposes under the tag `.hinted orig`, with the origin the committed
  entry recorded. -/
  | candidate (a : Assignment) (tag? : Option WitnessSourceTag := none)
  /-- This source has no candidate; try the next. `detail` carries what a
  reader of the report should know: the atoms the solver abstracted, an
  input type outside its domain (§9.4). -/
  | nothing (detail : Option String := none)
  /-- The source proved the hypotheses vacuous; stop the loop. -/
  | unsat

/-- One disjunct's winning witness from a preset earlier in the line's
preset list (§10), the reuse source's input. The command fills the
search context's table only when the statement passed
`Preset.presetFree`, so a nonempty table implies the type check. -/
structure ReuseWin where
  /-- The zero-based disjunct index the win belongs to. -/
  disjunctIndex  : Nat
  /-- The `.iffTrue` side, when the shape is `.iffTrue`. -/
  side       : Option Bool
  /-- The assignment that passed the check, post-shrink. -/
  assignment : Assignment
  /-- The preset the witness was won at; the record names it in
  `reused-<preset>`. -/
  fromPreset : PresetId

/-- One run of the search: the probe, its build-time description, the
binding, the preset, and the telescope's free variables with this line's
manual terms (§9.2's `SearchCtx`; their serialized bytes sit in the
probe's `manuals` field, which the command fixes at build time).

The free variables are telescope-local: like the statement's expressions,
they are valid only inside the reader's fold, which the whole search runs
in. The bit-vector source substitutes the instance variables with the
preset's constants when it evaluates a manual term (§11.2's
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
  /-- The author's manual terms of this line, with their input positions
  (§14.3). Empty when the line named none. -/
  manualTerms : Array (Nat × Expr)
  /-- The random source's draws, memoized per position: a draw is a
  pure function of the seed, the size, the index, and the position (§9.4),
  so the disjuncts of one theorem at one preset share them. The ref
  holds one slot per draw index. A slot is `none` until a call samples the draw's
  first position. The slot's inner array then holds one `Option ByteArray`
  per input position reached so far, `none` for a position no call has
  requested. A caller that needs a subset of a draw's positions (§9.9's
  built source, the side containers beside the state) samples those
  alone. -/
  drawMemo : IO.Ref (Array (Option (Array (Option ByteArray))))
  /-- The output root, where the built source's cache lives
  (`<outDir>/built/`, §9.9). -/
  outDir : System.FilePath
  /-- The binding module's cache stamp (§9.9): the `.trace` text the
  built source stores beside every cached state and compares before it
  reads one. Computed once per theorem, beside the committed hint
  file. -/
  builtStamp : String
  /-- The fork's first epoch boundary in preset units (§9.9), for the
  built grid's boundary steps. Evaluated once per run from the fork's
  own constant; the default is the upstream minimal value 8, which the
  toy forks' tests take. -/
  epochBoundary : Nat := 8
  /-- One disjunct's winning witness from a preset earlier in the line's
  preset list (§10), the reuse source's input. Every construction site
  names the table. An empty table means no earlier preset won anything,
  or that the statement is preset-bound. The command fills the table
  only when the statement passed `Preset.presetFree`, so a nonempty
  table implies the type check: an entry here says the assignment's
  every byte position is a scalar, free of the preset. -/
  earlierWins : Array ReuseWin

/-- The search monad: `MetaM`. §9.2's budget counter stayed
unnecessary: the redraw loop's budget is `theorem_vectors.randomDraws`
per disjunct, the solver's fragment caps the grid, and the per-run heartbeat
budget (§14.3) bounds the whole. -/
abbrev SearchM (α : Type) : Type := MetaM α

/-- One strategy that proposes witnesses (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). -/
structure WitnessSource where
  /-- The wire tag the record names when this source wins. -/
  tag     : WitnessSourceTag
  /-- Can this source try this disjunct at all? The search context is in
  scope, so a rule that reads the binding's state type or the probe's
  manual bytes sits here (§9.4's state rule). -/
  applies : SearchCtx → Statement → Disjunct → Bool
  /-- Produce one answer. -/
  search  : SearchCtx → Statement → Disjunct → SearchM SearchStep

/-- The search loop over one disjunct (`THEOREM_VECTORS_ARCHITECTURE.md` §9.2). A
candidate the check rejects falls through to the next source; an `unsat`
stops the loop, because no later source can find what does not exist. The
answer carries the winning source's tag, which the record names (§12.2). A
`notFound` names every source that ran on the disjunct, whether or not it
proposed a candidate, and carries the details the sources reported. -/
def searchDisjunct (sources : Array WitnessSource) (ctx : SearchCtx)
    (stmt : Statement) (d : Disjunct) :
    SearchM (Except Failure (Assignment × WitnessSourceTag)) := do
  let mut tried : Array WitnessSourceTag := #[]
  let mut details : Array String := #[]
  for source in sources do
    unless source.applies ctx stmt d do continue
    -- §9.2: the reason names every source that ran
    tried := tried.push source.tag
    match ← source.search ctx stmt d with
    | .candidate a tag? =>
      -- §9.4, the stage-4 outcome: the read-bounds gate runs before the
      -- check, so a candidate whose reads would run past a container's
      -- end never reaches the compiled `decide` and no panic prints
      if (ctx.probe.safe d.index a).all (· == true) then
        if ctx.probe.check d.index a then
          return .ok (a, tag?.getD source.tag)
      -- the check is compiled `decide P`; a failed check falls through to
      -- the next source (§9.3)
    | .nothing detail =>
      details := details ++ detail.toArray
    | .unsat =>
      return .error .unsat
  return .error (.notFound tried details)

end EthCLLib.TheoremVectors
