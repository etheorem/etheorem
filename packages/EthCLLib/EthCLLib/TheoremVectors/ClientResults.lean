import Lean
import EthCLLib.TheoremVectors.Types

/-!
# `EthCLLib.TheoremVectors.ClientResults`: the client harness's answers

The results file the client harness writes (`clients/prysm`),
`<outDir>/client-results.json` (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). One JSON array,
one entry per function-format file the harness walked:

```json
{ "path": "formats/function/<fork>/<preset>/<Target>/<Thm>_<index>[_t|_f].yaml",
  "fork": "gloas", "preset": "minimal", "specName": "increase_balance",
  "status": "passed", "detail": "post state matched (bytes and root)" }
```

An entry's `path` is relative to the outDir. The file is a cross-pass
file, and §13.2's manifest between the render and check passes is the
precedent: the harness writes it, the function format's `check` (§13.3)
and the report's Formats cell (§16.2) read it, and neither writes it.

`read` answers the empty array when the file is absent, which is the
harness-never-ran state. Both readers then answer as they did before the
client landed: `check` answers `noConsumer`, and the report's Formats
cell prints empty.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## The entry -/

/-- One harness status (`clients/prysm`'s summary): the replay passed,
it failed, or the coverage table recorded a skip. -/
inductive ClientStatus where
  | passed
  | failed
  | skipped
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The wire tag of a status, as the results file writes it. -/
def ClientStatus.tag : ClientStatus → String
  | .passed  => "passed"
  | .failed  => "failed"
  | .skipped => "skipped"

instance : ToJson ClientStatus where
  toJson s := .str s.tag

instance : FromJson ClientStatus where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "passed"  => return .passed
    | "failed"  => return .failed
    | "skipped" => return .skipped
    | _ => throw s!"unknown client status '{s}'"

/-- One entry of the results file (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3): the function-format
file the harness walked, the fork and preset it ran at, the function it
mapped the record to, its answer, and the answer's detail line. The wire
field names are the harness's JSON keys. -/
structure ClientResult where
  /-- The walked file, relative to the outDir. -/
  path     : String
  /-- The fork tag, such as `"gloas"`. -/
  fork     : String
  /-- The preset tag, such as `"minimal"`. -/
  preset   : String
  /-- The pyspec function the harness mapped the record to. -/
  specName : String
  /-- The harness's answer. -/
  status   : ClientStatus
  /-- The answer's detail line: what matched, what disagreed, or the
  skip's reason. -/
  detail   : String
  deriving ToJson, FromJson, Repr, BEq, Inhabited

/-! ## The file -/

/-- The results file's path, `<outDir>/client-results.json` (§13.3). -/
def ClientResults.file (outDir : System.FilePath) : System.FilePath :=
  outDir / "client-results.json"

/-- Read the results file (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). A missing file answers the
empty array: the harness never ran. A file that does not parse, or does
not match the entry structure, is an error: the harness wrote it, so a
mismatch is a defect. -/
def ClientResults.read (outDir : System.FilePath) : IO (Array ClientResult) := do
  let path := ClientResults.file outDir
  unless ← path.pathExists do
    return #[]
  match Json.parse (← IO.FS.readFile path) with
  | .error e => throw (IO.userError s!"cannot read {path}: {e}")
  | .ok j =>
    match fromJson? (α := Array ClientResult) j with
    | .ok rs => return rs
    | .error e => throw (IO.userError s!"cannot read {path}: {e}")

/-! ## The joins -/

/-- A rendered file's path as the results file spells it: the path
relative to the outDir. Render builds every format path by joining under
`env.outDir`, so stripping that prefix, then the one separator that
follows it, answers the entry's `path` byte for byte. The separator
check keeps a sibling directory whose name shares the outDir's prefix
(`theorem` beside `theorem-vectors`) unstripped, and the prefix loses
its trailing separators first, so a `--out tv/` invocation still joins.
The unmatched branch answers the input with its leading slashes
dropped. -/
def ClientResults.relPath (outDir rendered : System.FilePath) : String :=
  let cs := rendered.toString.toList
  let pre := ((outDir.toString.toList).reverse.dropWhile (· == '/')).reverse
  let cs :=
    if pre.length < cs.length && pre == cs.take pre.length
        && (cs.drop pre.length).head? == some '/' then
      cs.drop (pre.length + 1)
    else cs
  String.ofList (cs.dropWhile (· == '/'))

#guard ClientResults.relPath ("tv" : System.FilePath)
    ("tv/formats/function/f.yaml" : System.FilePath)
  == "formats/function/f.yaml"
#guard ClientResults.relPath ("tv" : System.FilePath)
    ("tvx/formats/function/f.yaml" : System.FilePath)
  == "tvx/formats/function/f.yaml"
#guard ClientResults.relPath ("tv/" : System.FilePath)
    ("tv/formats/function/f.yaml" : System.FilePath)
  == "formats/function/f.yaml"

/-- One path suffix dropped, the caller having checked the shape. Over
lists, because this toolchain's `String.take` and `String.drop` return
slices, and the suffixes here are a few characters. -/
private def dropSuffix (suffix s : String) : String :=
  let cs := s.toList
  let sf := suffix.toList
  if sf.length ≤ cs.length && sf == cs.drop (cs.length - sf.length) then
    String.ofList (cs.take (cs.length - sf.length))
  else s

/-- One trailing `_<digits>` disjunct index dropped (§13.3's file-name
shape). The theorem's own name may carry underscores, so the split reads
the last segment alone. The digit test runs first as a `Bool`, outside
the `if`: a `(·.isDigit)` section in an `if` inside a `match` arm
leaves this elaborator with a stuck universe constraint. -/
private def dropDisjunctIndex (stem : String) : String :=
  let parts := stem.splitOn "_"
  let lastIsIndex := match parts.getLast? with
    | some last => 2 ≤ parts.length && !last.isEmpty && last.all Char.isDigit
    | none => false
  if lastIsIndex then String.intercalate "_" parts.dropLast else stem

/-- The theorem name an entry's path spells: the file's base name
without the `.yaml` suffix, the `_t` / `_f` side marker, and the trailing
`_<digits>` disjunct index. The three suffixes are the shapes
`Formats.functionFileName` and `Record.disjunctName` write, read back in
reverse order. -/
def ClientResults.thmOfPath (path : String) : String :=
  let base := (path.splitOn "/").getLast?.getD path
  dropDisjunctIndex (dropSuffix "_f" (dropSuffix "_t" (dropSuffix ".yaml" base)))

#guard ClientResults.thmOfPath
    "formats/function/gloas/minimal/EthCLSpecs.Gloas.canBuilderCoverBid/EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff_0_t.yaml"
  == "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff"
#guard ClientResults.thmOfPath
    "formats/function/fulu/minimal/EthCLSpecs.Fulu.decreaseBalance/EthCLSpecs.Proofs.Fulu.decreaseBalance_run_no_underflow_0.yaml"
  == "EthCLSpecs.Proofs.Fulu.decreaseBalance_run_no_underflow"
#guard ClientResults.thmOfPath
    "formats/function/gloas/minimal/EthCLSpecs.Gloas.canBuilderCoverBid/EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff_10_f.yaml"
  == "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff"
#guard ClientResults.thmOfPath
    "formats/function/fulu/minimal/EthCLSpecs.Fulu.sha256/EthCLSpecs.Proofs.Fulu.sha256_2_0.yaml"
  == "EthCLSpecs.Proofs.Fulu.sha256_2"

/-- The entry one rendered file's answer lives in: the entry whose
`path` equals the file's path relative to the outDir (§13.3's `check`
join). -/
def ClientResults.ofPath? (rs : Array ClientResult)
    (outDir rendered : System.FilePath) : Option ClientResult :=
  rs.find? fun e => e.path == relPath outDir rendered

/-- The entries one (fork, preset, theorem) ran under: every entry whose
`path` names the theorem, at the fork and preset (§16.2's Formats-cell
join). A theorem runs once per disjunct and per side, so the answer
usually holds more than one entry. -/
def ClientResults.ofThm (rs : Array ClientResult)
    (fork preset thm : String) : Array ClientResult :=
  rs.filter fun e => e.fork == fork && e.preset == preset
    && thmOfPath e.path == thm

/-- The client tag the report's Formats cell names (§16.2). The harness
is Prysm's; a second client grows the cell beside it. -/
def ClientResults.clientTag : String := "prysm"

/-- The Formats cell for one theorem's entries (§16.2): the worst answer
wins, `failed` over `passed` over `skipped`, so the review surface never
shows a pass over a failed disjunct. No entry answers the empty cell. A
passed disjunct outranks a skipped one; today one theorem's entries
share one coverage row, so a skip and a pass cannot mix, and a
per-disjunct coverage table would revisit this order. -/
def ClientResults.cell (es : Array ClientResult) : String :=
  if es.any fun e => e.status == .failed then
    s!"{clientTag} failed"
  else if es.any fun e => e.status == .passed then
    s!"{clientTag} passed"
  else if es.any fun e => e.status == .skipped then
    s!"{clientTag} skipped"
  else ""

end EthCLLib.TheoremVectors
