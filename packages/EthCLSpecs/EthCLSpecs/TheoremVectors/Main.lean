import EthCLSpecs.TheoremVectors

/-!
# `EthCLSpecs.TheoremVectors.Main`: the command-line harness

The `theorem_vectors` executable (`THEOREM_VECTORS_ARCHITECTURE.md` §15). It never
elaborates a theorem; the records on disk are its input. Four subcommands:

- `render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]`
  turns every record into every format that accepts it;
- `check` replays the rendered vectors through each format's consumer;
- `report [--out <dir>]` folds the outcome files into `report.md`;
- `list [--out <dir>]` prints one line per record.

Stage 1 wires `report` (§16.2) and answers `render`, `check`, and `list`
over the records tree, which stage 1 leaves empty: they walk the tree,
report what they find, and exit 0, so the `theorem-vectors` recipe runs
green. §15's real bodies for those three land with the records (stage 2)
and the pyspec check (stage 7); `IMPLEMENTATION_NOTES.md` records the
staging deviation.
-/

set_option autoImplicit false

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

/-- Count the records on disk, `<fork>/<preset>/<thm>/<case>/record.json`.
Returns `none` when the records root does not exist. -/
private partial def countRecords (dir : System.FilePath) : IO (Option Nat) := do
  unless ← dir.isDir do
    return none
  let mut n := 0
  for entry in ← dir.readDir do
    let path := entry.path
    if ← path.isDir then
      match ← countRecords path with
      | some k => n := n + k
      | none => pure ()
    else if entry.fileName == "record.json" then
      n := n + 1
  return some n

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
    match ← countRecords (out / "records") with
    | none => IO.println s!"theorem_vectors render: no records under \
        {out}/records"
    | some n => IO.eprintln s!"theorem_vectors render: {n} records found, \
        but no format is registered yet (stage 2); the records stay in \
        place (§18)"
    return 0
  | .check =>
    match ← countRecords (out / "records") with
    | none => IO.println s!"theorem_vectors check: no records under \
        {out}/records"
    | some n => IO.println s!"theorem_vectors check: {n} records, no \
        consumer check registered yet (stage 7)"
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
