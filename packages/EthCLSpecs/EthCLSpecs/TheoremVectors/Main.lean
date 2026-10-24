import EthCLSpecs.TheoremVectors
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Formats.Function
import EthCLLib.TheoremVectors.Record

/-!
# `EthCLSpecs.TheoremVectors.Main`: the command-line harness

The `theorem_vectors` executable (`THEOREM_VECTORS_ARCHITECTURE.md` §15). It never
elaborates a theorem; the records on disk are its input. Five subcommands:

- `render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]`
  turns every record into every format that accepts it (phase C1, §13.2);
- `check [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]`
  replays the rendered vectors through each format's consumer (C2); the
  function format joins the client harness's results file (§13.3), and
  the epoch_processing format replays its cases through `runCase` (§13.5);
- `report [--out <dir>]` folds the outcome files into `report.md` (C3),
  with the client harness's answers in the Formats cells (§16.2);
- `list [--out <dir>]` prints one line per record;
- `prysm-corpus [--out <dir>]` mirrors every rendered upstream case layout
  under `<out>/tests`, each `.ssz` part snappy-encoded (§13.6, §13.7), the
  corpus tree a Prysm checkout runs its spectests from.
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
  | prysmCorpus
  deriving DecidableEq, Repr, Inhabited

/-- Parse a subcommand name. -/
def Subcommand.ofString? : String → Option Subcommand
  | "render" => some .render
  | "check"  => some .check
  | "report" => some .report
  | "list"   => some .list
  | "prysm-corpus" => some .prysmCorpus
  | _        => none

/-- The flags the subcommands share. -/
inductive Flag where
  | fork
  | preset
  | format
  | out
  deriving DecidableEq, Repr, Inhabited

/-- Read a flag from its command-line spelling. -/
def Flag.ofString? : String → Option Flag
  | "--fork"   => some .fork
  | "--preset" => some .preset
  | "--format" => some .format
  | "--out"    => some .out
  | _          => none

/-- The flags each subcommand takes: `render` and `check` take all four,
`report`, `list`, and `prysm-corpus` take only `--out`. -/
def Subcommand.flags : Subcommand → List Flag
  | .render | .check => [.fork, .preset, .format, .out]
  | .report | .list | .prysmCorpus => [.out]

/-- The flags a subcommand parsed (`THEOREM_VECTORS_ARCHITECTURE.md` §15).
`out` defaults to `EthCLSpecs.TheoremVectors.outDir`, the path the lakefile
pins (§2.3, §15). -/
structure Options where
  fork   : Option String := none
  preset : Option PresetId := none
  format : Option String := none
  out    : String := EthCLSpecs.TheoremVectors.outDir
  deriving Repr

/-- The usage text, printed on a malformed invocation. -/
def usage : String :=
  "usage: theorem_vectors <subcommand> [flags]\n" ++
  "  render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]\n" ++
  "  check  [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]\n" ++
  "  report [--out <dir>]\n" ++
  "  list   [--out <dir>]\n" ++
  "  prysm-corpus [--out <dir>]\n" ++
  "  presets: minimal | mainnet; --out defaults to " ++
    EthCLSpecs.TheoremVectors.outDir ++ "\n"

mutual
/-- Parse the flag list: every flag takes exactly one value, and a
repeated flag keeps its first occurrence. An unknown flag, a missing value,
a value that starts with `--`, or a preset name outside `minimal` /
`mainnet` fails. -/
def parseOptions (allowed : List Flag) : List String → Option Options
  | [] => some {}
  | [_] => none
  | flag :: value :: rest =>
    if value.startsWith "--" then none
    else parseFlag allowed flag value rest

/-- One flag with its value, and the tail still to parse. -/
def parseFlag (allowed : List Flag) (flag value : String)
    (rest : List String) : Option Options :=
  match Flag.ofString? flag with
  | none => none
  | some f =>
    if !allowed.contains f then none
    else
      match f with
      | .fork =>
        (parseOptions allowed rest).map fun o => { o with fork := some value }
      | .preset =>
        match PresetId.ofTag? value with
        | none => none
        | some p =>
          (parseOptions allowed rest).map fun o => { o with preset := some p }
      | .format =>
        (parseOptions allowed rest).map fun o => { o with format := some value }
      | .out =>
        (parseOptions allowed rest).map fun o => { o with out := value }
end

/-- The output root for a subcommand: the parsed `--out`, or the spec-half
root's `outDir` constant when the flag is absent (§15). -/
def outRoot (opts : Options) : System.FilePath := opts.out

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
              && f.accepts env rb.record then
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

/-! ## The `prysm-corpus` emitter

The mirror writes the corpus tree a Prysm checkout runs its spectests from
(§15). It reads the manifest the render pass wrote and touches nothing else
in the output tree; it never renders. -/

/-- The two formats whose entries describe an upstream case layout
(§13.6, §13.7). Every other format's entries the mirror skips. -/
private def prysmCorpusFormats : List String := ["epoch_processing", "operations"]

/-- The six segments a case directory keeps after the `formats/pyspec`
pair: the fork, the preset, the runner, the handler, the suite directory
(`pyspec_tests` today), and the case. Named fields keep the mirror's swap
of the first two readable. -/
private structure CaseSegs where
  fork : String
  preset : String
  runner : String
  handler : String
  suite : String
  caseName : String

/-- Parse the six segments out of a case directory path, the parent of a
case entry's first path. Any shape other than
`<...>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/<suite>/<case>`
fails, and the error names the offending path. -/
private def caseSegsOfDir (dir : System.FilePath) : IO CaseSegs := do
  let bad := s!"prysm-corpus: {dir} is not a case directory \
    (expected <...>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/\
    <suite>/<case>)"
  let segs := dir.toString.splitOn "/"
  -- the real `formats` root is the last `formats` segment: a stray earlier
  -- one can only come from the `--out` prefix the render pass recorded
  let some j := segs.reverse.findIdx? (· == "formats")
    | throw (IO.userError bad)
  let i := segs.length - 1 - j
  unless segs[i + 1]? == some "pyspec" do
    throw (IO.userError bad)
  match segs.drop (i + 2) with
  | [f, p, r, h, s, c] =>
    pure { fork := f, preset := p, runner := r, handler := h, suite := s, caseName := c }
  | _ => throw (IO.userError bad)

/-- The mirror directory of one case under `<out>/tests`: the preset and
the fork swap places, and the rest keeps the case layout's order. A Prysm
checkout expects the suite at `tests/<preset>/<fork>/...`, the layout
upstream's consolidation publishes. -/
private def CaseSegs.mirrorDir (segs : CaseSegs) (out : System.FilePath) :
    System.FilePath :=
  out / "tests" / segs.preset / segs.fork / segs.runner / segs.handler /
    segs.suite / segs.caseName

/-- Mirror every rendered upstream case layout under `<out>/tests` (§15).
Reads the manifest the render pass wrote, so a stale case of a removed
record cannot survive: the mirror root is wiped first. Each case directory
mirrors to `<out>/tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>`.
Every `.ssz` part is written snappy-encoded as `<stem>.ssz_snappy`, and
`manifest.yaml` is copied raw. `meta.yaml` is never copied: ours carries
`bls_setting: 2`, and the suite's real BLS backend drops every case that
declares it. Upstream's consolidation cases carry no `meta.yaml`, and the
mirror follows them. A case with no `post.ssz` part (an expected-failure
case) keeps the mark: no post part is written. Returns the case count and
the written-file count. -/
private def writePrysmCorpus (out : System.FilePath) : IO (Nat × Nat) := do
  let manifest := out / "formats" / "manifest.json"
  unless ← manifest.pathExists do
    throw (IO.userError s!"prysm-corpus: no manifest at {manifest}; \
      run render first")
  let rendered ← readManifest out
  if rendered.isEmpty then
    throw (IO.userError s!"prysm-corpus: {manifest} holds no entries (0); \
      run render first")
  let cases := rendered.filter (fun r => prysmCorpusFormats.contains r.format)
  if cases.isEmpty then
    throw (IO.userError s!"prysm-corpus: {manifest} holds no \
      epoch_processing or operations entries \
      (0 of {rendered.size}); run render first")
  let testsDir := out / "tests"
  if ← testsDir.pathExists then
    IO.FS.removeDirAll testsDir
  let mut nFiles := 0
  for r in cases do
    let some first := r.paths[0]?
      | throw (IO.userError s!"prysm-corpus: the entry for {r.recordPath} \
          holds no paths")
    let some dir := (System.FilePath.mk first).parent
      | throw (IO.userError s!"prysm-corpus: {first} has no parent directory")
    let segs ← caseSegsOfDir dir
    let mirror := segs.mirrorDir out
    IO.FS.createDirAll mirror
    for entry in ← dir.readDir do
      let p := entry.path
      if ← p.isDir then continue
      let name := entry.fileName
      -- `meta.yaml` and anything else the layouts do not write: skipped
      if name == "meta.yaml" then continue
      if name.endsWith ".ssz" then
        let target := mirror / ((name.dropEnd 4).toString ++ ".ssz_snappy")
        IO.FS.writeBinFile target (Snappy.encode (← IO.FS.readBinFile p))
        nFiles := nFiles + 1
        IO.println s!"theorem_vectors prysm-corpus: {target}"
      else if name == "manifest.yaml" then
        let target := mirror / name
        IO.FS.writeBinFile target (← IO.FS.readBinFile p)
        nFiles := nFiles + 1
        IO.println s!"theorem_vectors prysm-corpus: {target}"
  return (cases.size, nFiles)

/-- The record directories no registered format accepted (§16.2's list).
The report subcommand walks the records tree and asks every format's
`accepts`. -/
def unacceptedRecords (out : System.FilePath) : IO (Array String) := do
  let env := renderEnv out
  let root := Record.dir out
  unless ← root.isDir do
    return #[]
  let mut acc : Array String := #[]
  for forkEntry in ← root.readDir do
    unless ← forkEntry.path.isDir do continue
    for presetEntry in ← forkEntry.path.readDir do
      let some p := PresetId.ofTag? presetEntry.fileName | continue
      unless ← presetEntry.path.isDir do continue
      for (path, rb) in ← Record.readAll out forkEntry.fileName p do
        unless Formats.all.any (fun f => f.accepts env rb.record) do
          acc := acc.push path.toString
  return acc

/-- Run a parsed subcommand. -/
def runSub (sc : Subcommand) (opts : Options) : IO UInt32 := do
  let out := outRoot opts
  match sc with
  | .report =>
    let nForks ← EthCLLib.TheoremVectors.Report.write out
      (← unacceptedRecords out)
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
    -- format joins the client harness's results file (§13.3), answering
    -- `noConsumer` for records no client ran; the epoch_processing and
    -- operations formats replay their cases through the pyspec driver.
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
  | .prysmCorpus =>
    -- the snappy mirror of the rendered upstream case layouts (§15): the
    -- corpus tree a Prysm checkout runs its spectests from. Reads the
    -- manifest; never renders.
    let (nCases, nFiles) ← writePrysmCorpus out
    IO.println s!"theorem_vectors prysm-corpus: mirrored {nCases} cases, \
      {nFiles} files"
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

/-- The executable entry point. The catch is the harness's error contract:
an error escaping `run` prints on stderr under the `theorem_vectors: `
prefix and exits 1. No error may reach the runtime's default
uncaught-exception handler instead: on this toolchain that handler dies
with SIGSEGV for this exe, so an escaping error would end the process with
no message (exit 139). The catch covers every throw site `run` can reach,
the reads in the precompiled libraries included. -/
def main (args : List String) : IO UInt32 := do
  try
    EthCLSpecs.TheoremVectors.Main.run args
  catch e =>
    IO.eprintln s!"theorem_vectors: {toString e}"
    return (1 : UInt32)
