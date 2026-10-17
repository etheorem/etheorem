import Lean
import EthCLLib.TheoremVectors.Types

/-!
# `EthCLLib.TheoremVectors.Outcome`: the per-theorem outcome lines

One outcome file per theorem under `<outDir>/outcomes/<fork>/<thm>.json`
(`THEOREM_VECTORS_ARCHITECTURE.md` §16.1). The generator command writes the file; the exe's
`report` subcommand folds the files into `report.md` (§16.2). The file is
JSON through `Lean.Json`: the structures here derive `ToJson` and
`FromJson`, and no format code exists for them (§12.3).

The wire shape:

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "target": "EthCLSpecs.Gloas.canBuilderCoverBid",
  "shape": "iffTrue",
  "origin": "named",
  "blockInputs": [],
  "disjuncts": 2,
  "runs": [
    { "preset": "minimal", "status": "written", "records": 2,
      "source": "random", "hint": "replayed", "seconds": 4.1 } ] }
```

`disjuncts` counts the prepared search problems; stage 1 prepares none, so
it writes `0` until the prepare pass lands. The run entries carry one
status per preset; stage 1 writes the placeholder `pending`, or
`unsupported` where the reader gave a reason, and later stages replace
both with real outcomes.

## Lean idioms annotated

- `theorem` is a keyword, so the field carries French quotes: `«theorem»`.
  The derived JSON instances write the field's name, which keeps the wire
  spelling of §16.1.
- `Json.parse` is `Except String`, not `IO`; the file reader lifts it by
  hand.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## Origin and status -/

/-- How the theorem came to the generator's attention (§16.1): a named line,
a `@[theorem_vectors]` tag, a `characterizes` claim, the `survey` clause, or
a `skip` line. -/
inductive OutcomeOrigin where
  | named
  | tagged
  | characterized
  | survey
  | skipped
  deriving DecidableEq, Repr, Inhabited

/-- The wire tag of an origin, as the outcome files write it. -/
def OutcomeOrigin.tag : OutcomeOrigin → String
  | .named         => "named"
  | .tagged        => "tagged"
  | .characterized => "characterized"
  | .survey        => "survey"
  | .skipped       => "skipped"

instance : ToJson OutcomeOrigin where
  toJson o := .str o.tag

instance : FromJson OutcomeOrigin where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "named"         => return .named
    | "tagged"        => return .tagged
    | "characterized" => return .characterized
    | "survey"        => return .survey
    | "skipped"       => return .skipped
    | _ => throw s!"unknown origin '{s}'"

/-- One run's status (§16.1). `written` records exist; `skipped` marks a
run that found no vector, with the reason alongside; `outOfScope`, `unsat`,
and `unsupported` carry their §18 meanings. `unselected` is the `survey`
clause's answer: the theorem was read and listed, and nothing ran. -/
inductive RunStatus where
  | written
  | skipped
  | outOfScope
  | unsat
  | unsupported
  | unselected
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The wire tag of a status. -/
def RunStatus.tag : RunStatus → String
  | .written     => "written"
  | .skipped     => "skipped"
  | .outOfScope  => "outOfScope"
  | .unsat       => "unsat"
  | .unsupported => "unsupported"
  | .unselected  => "unselected"

instance : ToJson RunStatus where
  toJson s := .str s.tag

instance : FromJson RunStatus where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "written"     => return .written
    | "skipped"     => return .skipped
    | "outOfScope"  => return .outOfScope
    | "unsat"       => return .unsat
    | "unsupported" => return .unsupported
    | "unselected"  => return .unselected
    | _ => throw s!"unknown run status '{s}'"

/-! ## The outcome -/

/-- One per-preset run's result line inside an outcome (§16.1). The
optional fields fill as the pipeline grows: `records` and `seconds` when a
run writes records, `source` and `hint` when a witness search picks a
source, `reason` when a run explains itself. A survey run carries no
preset (§16.1), so the field is optional. -/
structure RunOutcome where
  /-- The preset the run fixed, when the run ran per preset. -/
  preset  : Option PresetId := none
  /-- The run's status. -/
  status  : RunStatus
  /-- How many records the run wrote. -/
  records : Nat := 0
  /-- The witness source that won, in its wire form. -/
  source  : Option String := none
  /-- What the hint source did, in its wire form (§16.1). -/
  hint    : Option String := none
  /-- The run's wall-clock seconds. -/
  seconds : Option Float := none
  /-- The reason a run reports, when it has one. -/
  reason  : Option String := none
  deriving ToJson, FromJson, Repr, BEq, Inhabited

/-- The per-theorem outcome the command writes and the report folds
(§16.1). -/
structure Outcome where
  /-- The theorem's full constant name. -/
  «theorem»     : Name
  /-- The spec function under test, when the reader found one (§7.2). -/
  target      : Option Name
  /-- The shape's wire tag (`Statement.Shape.wire`). -/
  shape       : String
  /-- How the theorem came to the generator's attention. -/
  origin      : OutcomeOrigin
  /-- The inputs the block-input rule puts out of scope (§1.2). -/
  blockInputs : Array Name
  /-- How many disjuncts the prepare pass produced; stage 1 prepares
  none. -/
  disjuncts   : Nat
  /-- One entry per preset the theorem's line runs. -/
  runs        : Array RunOutcome
  deriving ToJson, FromJson, Repr

/-! ## The file -/

/-- The path of a fork's outcome directory, `<outDir>/outcomes/<fork>`. -/
def Outcome.dir (outDir : System.FilePath) (forkTag : String) :
    System.FilePath :=
  outDir / "outcomes" / forkTag

/-- The outcome file's path for a theorem whose proof-namespace prefix is
already stripped. -/
def Outcome.file (outDir : System.FilePath) (forkTag : String)
    (thmLocal : String) : System.FilePath :=
  Outcome.dir outDir forkTag / (thmLocal ++ ".json")

/-- Write one outcome file, creating the fork's outcome directory when it
does not exist. -/
def Outcome.write (outDir : System.FilePath) (forkTag : String) (o : Outcome)
    (thmLocal : String) : IO Unit := do
  IO.FS.createDirAll (Outcome.dir outDir forkTag)
  -- `Json.render` is a `Format`; `Format.pretty` lays it out as one
  -- document the file can hold
  IO.FS.writeFile (Outcome.file outDir forkTag thmLocal)
    ((toJson o).render.pretty (width := 100) ++ "\n")

/-- Read one outcome file back. A file that does not parse, or does not
match the structure, is an error: the generator wrote it, so a mismatch is
a defect. -/
def Outcome.read (path : System.FilePath) : IO Outcome := do
  match Json.parse (← IO.FS.readFile path) with
  | .error e => throw (IO.userError e)
  | .ok j =>
    match fromJson? (α := Outcome) j with
    | .ok o => return o
    | .error e => throw (IO.userError s!"cannot read the outcome file \
        {path}: {e}")

/-- Every outcome of one fork, in name order. -/
def Outcome.readFork (outDir : System.FilePath) (forkTag : String) :
    IO (Array Outcome) := do
  let dir := Outcome.dir outDir forkTag
  if ← dir.isDir then
    let mut os : Array Outcome := #[]
    for entry in ← dir.readDir do
      if entry.path.toString.endsWith ".json" then
        os := os.push (← Outcome.read entry.path)
    return os.qsort fun a b => a.theorem.toString < b.theorem.toString
  else
    return #[]

/-- The fork tags that have outcome directories, in name order. -/
def Outcome.forks (outDir : System.FilePath) : IO (Array String) := do
  let root := outDir / "outcomes"
  if ← root.isDir then
    let mut fs : Array String := #[]
    for entry in ← root.readDir do
      if ← entry.path.isDir then
        fs := fs.push entry.fileName
    return fs.qsort (· < ·)
  else
    return #[]

end EthCLLib.TheoremVectors
