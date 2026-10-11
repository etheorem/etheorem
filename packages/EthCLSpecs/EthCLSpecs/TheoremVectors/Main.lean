import EthCLSpecs.TheoremVectors
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Formats.Function
import EthCLLib.TheoremVectors.Record

/-!
# `EthCLSpecs.TheoremVectors.Main`: the command-line harness

The `theorem_vectors` executable (`THEOREM_VECTORS_ARCHITECTURE.md` §15). It never
elaborates a theorem; the records on disk are its input. Four subcommands:

- `render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]`
  turns every record into every format that accepts it (phase C1, §13.2);
- `check [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]`
  replays the rendered vectors through each format's consumer (C2); the
  function format answers `noConsumer`, so `check` passes until the pyspec
  format's `runCase` consumer lands in stage 7;
- `report [--out <dir>]` folds the outcome files into `report.md` (C3);
- `list [--out <dir>]` prints one line per record.
-/

set_option autoImplicit false

open Lean
open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Main

/-- One exe subcommand (`THEOREM_VECTORS_ARCHITECTURE.md` §15). -/
inductive Subcommand where
  | render
  | check
  | report
  | list
  deriving DecidableEq, Repr, Inhabited

/-- Parse a subcommand name. -/
def Subcommand.ofString? : String → Option Subcommand
  | "render" => some .render
  | "check"  => some .check
  | "report" => some .report
  | "list"   => some .list
  | _        => none

/-- The flag names the subcommand takes: `render` and `check` take all
four, `report` and `list` take only `--out`. -/
def Subcommand.flags : Subcommand → List String
  | .render | .check => ["--fork", "--preset", "--format", "--out"]
  | .report | .list  => ["--out"]

/-- The flags the subcommands share. An `out` of `none` means
`EthCLSpecs.TheoremVectors.outDir`, the path the lakefile pins
(`THEOREM_VECTORS_ARCHITECTURE.md` §2.3, §15). -/
structure Options where
  fork   : Option String := none
  preset : Option PresetId := none
  format : Option String := none
  out    : Option String := none
  deriving Repr

/-- The usage text, printed on a malformed invocation. -/
def usage : String :=
  "usage: theorem_vectors <subcommand> [flags]\n" ++
  "  render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]\n" ++
  "  check  [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]\n" ++
  "  report [--out <dir>]\n" ++
  "  list   [--out <dir>]\n" ++
  "  presets: minimal | mainnet; --out defaults to " ++
    EthCLSpecs.TheoremVectors.outDir ++ "\n"

mutual
/-- Parse the flag list: every flag takes exactly one value, and a
repeated flag keeps its last occurrence. An unknown flag, a missing value,
a value that starts with `--`, or a preset name outside `minimal` /
`mainnet` fails. -/
def parseOptions (allowed : List String) : List String → Option Options
  | [] => some {}
  | [_] => none
  | flag :: value :: rest =>
    if value.startsWith "--" then none
    else parseFlag allowed flag value rest

/-- One flag with its value, and the tail still to parse. -/
def parseFlag (allowed : List String) (flag value : String)
    (rest : List String) : Option Options :=
  if flag == "--fork" && allowed.contains "--fork" then
    (parseOptions allowed rest).map fun o =>
      { o with fork := o.fork.orElse fun _ => some value }
  else if flag == "--preset" && allowed.contains "--preset" then
    match PresetId.ofTag? value with
    | none => none
    | some p => (parseOptions allowed rest).map fun o =>
      { o with preset := o.preset.orElse fun _ => some p }
  else if flag == "--format" && allowed.contains "--format" then
    (parseOptions allowed rest).map fun o =>
      { o with format := o.format.orElse fun _ => some value }
  else if flag == "--out" && allowed.contains "--out" then
    (parseOptions allowed rest).map fun o =>
      { o with out := o.out.orElse fun _ => some value }
  else none
end

/-- The output root for a subcommand: `--out`, or the spec-half root's
`outDir` constant (§15). -/
def outRoot (opts : Options) : System.FilePath :=
  (opts.out.getD EthCLSpecs.TheoremVectors.outDir)

/-- The render environment the exe builds: the bindings table from
`Bindings.lean` (§15). -/
def renderEnv (out : System.FilePath) : RenderEnv where
  outDir := out
  bindings := EthCLSpecs.TheoremVectors.Bindings.ofTag

/-- Does the record pass the exe's selection flags? -/
def selects (opts : Options) (r : VectorRecord) : Bool :=
  (opts.fork.all fun f => r.fork == f)
    && (opts.preset.all fun p => r.preset == p)

/-- One rendered vector, as the manifest between the render and check
passes holds (§13.2: check receives what render returned). -/
structure Rendered where
  /-- The record directory the vector came from. -/
  recordPath : String
  /-- The format's registry name. -/
  format : String
  /-- The files the format wrote. -/
  paths : Array String
  deriving ToJson, FromJson

/-- Walk the records tree and render every selected record through every
accepting format (§13.2). Writes `<out>/formats/manifest.json`, the list
of rendered vectors the `check` subcommand replays, and returns the count
of rendered files. -/
def renderRecords (opts : Options) (out : System.FilePath) : IO Nat := do
  let env := renderEnv out
  let forkTags ← match opts.fork with
    | some f => pure #[f]
    | none => do
      let root := Record.dir out
      if ← root.isDir then (← root.readDir).mapM (fun e => pure e.fileName)
      else pure #[]
  let ps : Array PresetId :=
    match opts.preset with
    | some p => #[p]
    | none => #[.minimal, .mainnet]
  let mut n := 0
  let mut rendered : Array Rendered := #[]
  for forkTag in forkTags do
    for p in ps do
      for (path, rb) in ← Record.readAll out forkTag p do
        unless selects opts rb.record do continue
        for f in Formats.all do
          if (opts.format.all fun name => f.name == name)
              && f.accepts rb.record then
            let paths ← f.render env rb.record rb.inputBytes rb.outputBytes
            n := n + paths.size
            rendered := rendered.push
              { recordPath := path.toString, format := f.name,
                paths := paths.map (·.toString) }
            for q in paths do
              IO.println s!"theorem_vectors render: {f.name} {q}"
  IO.FS.createDirAll (out / "formats")
  IO.FS.writeFile (out / "formats" / "manifest.json")
    ((toJson rendered).render.pretty (width := 100) ++ "\n")
  return n

/-- Walk the records tree and print one line per record, for scripts
(§15's `list`). -/
private partial def listRecords (dir : System.FilePath) : IO Unit := do
  unless ← dir.isDir do
    return
  for entry in ← dir.readDir do
    let path := entry.path
    if ← path.isDir then
      listRecords path
    else if path.fileName == "record.json" then
      IO.println path.toString

/-- Read the manifest the render pass wrote (§13.2). A missing manifest
means nothing was rendered. -/
def readManifest (out : System.FilePath) : IO (Array Rendered) := do
  let path := out / "formats" / "manifest.json"
  unless ← path.pathExists do
    return #[]
  match Json.parse (← IO.FS.readFile path) with
  | .error e => throw (IO.userError s!"cannot read {path}: {e}")
  | .ok j =>
    match fromJson? (α := Array Rendered) j with
    | .ok rs => return rs
    | .error e => throw (IO.userError s!"cannot read {path}: {e}")

/-- Run a parsed subcommand. -/
def runSub (sc : Subcommand) (opts : Options) : IO UInt32 := do
  let out := outRoot opts
  match sc with
  | .report =>
    let nForks ← EthCLLib.TheoremVectors.Report.write out
    IO.println s!"theorem_vectors report: wrote {out}/report.md \
      ({nForks} forks)"
    return 0
  | .list =>
    listRecords (out / "records")
    return 0
  | .render =>
    let n ← renderRecords opts out
    IO.println s!"theorem_vectors render: rendered {n} files"
    return 0
  | .check =>
    -- phase C2 (§13.2, §13.5): every registered format's consumer replays
    -- what the render pass returned, through the manifest. The function
    -- format answers `noConsumer`, so the check passes over it; the
    -- pyspec format's `runCase` consumer lands in stage 7.
    let env := renderEnv out
    let rendered ← readManifest out
    let mut nChecked := 0
    let mut failures : Array String := #[]
    for r in rendered do
      unless opts.format.all (fun name => name == r.format) do
        continue
      let some f := Formats.all.find? (·.name == r.format)
        | throw (IO.userError s!"theorem_vectors check: unknown format \
          {r.format} in the manifest")
      let rb ← Record.read r.recordPath
      unless selects opts rb.record do continue
      let checkResult ← f.check env rb.record
        (r.paths.map System.FilePath.mk)
      match checkResult with
      | .passed => nChecked := nChecked + 1
      | .noConsumer => pure ()
      | .failed detail =>
        failures := failures.push s!"{f.name} {r.recordPath}: {detail}"
    IO.println s!"theorem_vectors check: {nChecked} passed, \
      {failures.size} failed"
    unless failures.isEmpty do
      for f in failures do
        IO.eprintln s!"theorem_vectors check: {f}"
      return 1
    return 0

/-- Parse the invocation, then run the subcommand. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln usage
    return 2
  | sub :: rest =>
    match Subcommand.ofString? sub with
    | none =>
      IO.eprintln s!"theorem_vectors: unknown subcommand '{sub}'\n{usage}"
      return 2
    | some sc =>
      match parseOptions sc.flags rest with
      | none =>
        IO.eprintln s!"theorem_vectors {sub}: bad flags\n{usage}"
        return 2
      | some opts => runSub sc opts

end EthCLSpecs.TheoremVectors.Main

/-- The executable entry point. -/
def main (args : List String) : IO UInt32 :=
  EthCLSpecs.TheoremVectors.Main.run args
