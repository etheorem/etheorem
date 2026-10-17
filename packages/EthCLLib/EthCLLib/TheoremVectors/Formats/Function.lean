import Lean
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Yaml
import EthCLLib.TheoremVectors.ClientResults
import EthCLLib.TheoremVectors.Formats.Pyspec

/-!
# `EthCLLib.TheoremVectors.Formats.Function`: the function format

The self-contained client-facing layout (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). It
accepts the records whose target the reader found: the file's `function`
field names the function a client exposes, and a record without one has
no function to name, so the format rejects it. §13.3 says the format
accepts every record; the notes record the deviation. The `function`
field spells the record's `specName`, the target's pyspec name the reader
read off the docstring (the stage-10 promotion). When `specName` is
`none`, the field falls back to the Lean target name. The directory
keeps the Lean target name either way. One YAML file per accepted
vector:

```
<outDir>/formats/function/<fork>/<preset>/<target>/<thm>_<index>[_t|_f].yaml
```

SSZ values go in as single-quoted hex with their root, scalars as literals,
and the theorem name is the point: the file names the proved property a
client that exposes the function would replay. Its `check` joins the
rendered file against the client harness's results file
(`ClientResults.lean`): a record the client passed passes, a record the
client failed fails with the harness's detail line, and `noConsumer` now
means no client ran the record, either because the coverage table maps
its target to nothing, the client build table-skipped it, or the harness
has not run.

## Lean idioms annotated

- A scalar's literal decides its YAML leaf: `true` / `false` are booleans,
  a digit string an integer, everything else a string. The record layer
  guarantees the literal's shape, so the mapping stays total on records.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- A record literal as one YAML leaf (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). -/
def literalYaml (lit : String) : Yaml :=
  if lit == "true" then .bool true
  else if lit == "false" then .bool false
  else if !lit.isEmpty && lit.all (·.isDigit) then
    .int (lit.toNat?.getD 0)
  else .str lit

/-- One recorded value as the function format writes it: a scalar as its
literal, an SSZ value as the value-and-root pair inline (§13.3). `bytes`
supplies the hex of the value's own side file; the record supplies the
root. -/
def valueYaml (v : VectorValue) (bytes : ByteArray) : Yaml :=
  match v.value with
  | .scalar lit => literalYaml lit
  | .ssz root => .map #[("ssz", .hex bytes), ("root", .hex root)]

/-- The file's name for one record, `<thm>_<index>[_t|_f].yaml`:
the theorem's local name, the zero-padded disjunct index, and the side
marker (§13.3). -/
def Formats.functionFileName (r : VectorRecord) : String :=
  r.«theorem».toString ++ "_" ++ toString r.disjunctIndex ++
    (match r.side with
     | some true => "_t"
     | some false => "_f"
     | none => "") ++ ".yaml"

/-- §13.3's check: the consumer answers back. The rendered file joins
against the client harness's results file by its path relative to
`outDir`, the way the harness spells the entry's `path`. `passed`
passes; `failed` fails with the harness's detail line; `skipped` and no
entry answer `noConsumer`, which now means no client ran this record:
the coverage table maps its target to nothing, the client build
table-skipped it, or the harness has not run. The function format writes
exactly one file per record, so the first path is the whole join key. -/
def Formats.functionCheck (env : RenderEnv) (_r : VectorRecord)
    (paths : Array System.FilePath) : IO CheckResult := do
  let rs ← ClientResults.read env.outDir
  let some file := paths[0]? | return .noConsumer
  match ClientResults.ofPath? rs env.outDir file with
  | none => return .noConsumer
  | some e =>
    match e.status with
    | .passed  => return .passed
    | .failed  => return .failed e.detail
    | .skipped => return .noConsumer

/-- The function format (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). It accepts
the records whose target the reader found: the file's `function` field
names the function a client exposes, and a record without one has no
function to name. The field carries the record's `specName`, the pyspec
name. When `specName` is `none`, it falls back to the Lean target name.
The directory spells the Lean target name either way. -/
def Formats.function : VectorFormat where
  name := "function"
  -- The env is unused here: §13.3's predicate reads the record alone.
  accepts _ r := r.target.isSome
  render env r inputBytes outputBytes := do
    let targetName := (r.target.getD r.«theorem»).toString
    let dir := env.outDir / "formats" / "function" / r.fork / r.preset.tag /
      targetName
    IO.FS.createDirAll dir
    let file := dir / Formats.functionFileName r
    let inputs : Array (String × Yaml) :=
      (r.inputs.zip inputBytes).map fun (v, bytes) =>
        (v.name.toString, valueYaml v bytes)
    let output : Yaml :=
      match r.output, outputBytes with
      | none, _ => .str ""
      | some v, some out => valueYaml v out
      | some v, none => valueYaml v (ByteArray.mk #[])
    let doc : Yaml :=
      .map #[
        ("theorem", .str r.«theorem».toString),
        ("function", .str (r.specName.getD targetName)),
        ("fork", .str r.fork),
        ("preset", .str r.preset.tag),
        ("shape", .str r.shape.tag),
        ("inputs", .map inputs),
        ("output", output),
        ("witnessSearcher", .str r.witnessSearcher.tag)
      ]
    IO.FS.writeFile file (Yaml.render doc)
    return #[file]
  check := Formats.functionCheck

/-- The format registry (`THEOREM_VECTORS_ARCHITECTURE.md` §13.1): the
function format (§13.3) and the pyspec format (§13.4, §13.5). A new
format is one more value here. -/
def Formats.all : Array VectorFormat := #[Formats.function, Formats.pyspec]

end EthCLLib.TheoremVectors
