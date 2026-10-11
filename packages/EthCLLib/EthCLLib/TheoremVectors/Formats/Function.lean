import Lean
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Yaml

/-!
# `EthCLLib.TheoremVectors.Formats.Function`: the function format

The self-contained client-facing layout (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). It
accepts the records whose target the reader found: the file's `function`
field names the function a client exposes, and a record without one has
no function to name, so the format rejects it. §13.3 says the format
accepts every record; the notes record the deviation. One YAML file per
accepted vector:

```
<outDir>/formats/function/<fork>/<preset>/<target>/<thm>_<case>[_t|_f].yaml
```

SSZ values go in as single-quoted hex with their root, scalars as literals,
and the theorem name is the point: the file names the proved property a
client that exposes the function would replay. Its `check` answers
`noConsumer`, because no Lean-side consumer drives it yet.

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
  | .ssz root =>
    .map #[("ssz", .hex bytes), ("root", .str (hexOf root))]

/-- The file's name for a case, `<thm>_<case>[_t|_f].yaml` (§13.3). -/
def Formats.functionFileName (r : VectorRecord) : String :=
  r.thm.toString ++ "_" ++ toString r.caseIndex ++
    (match r.side with
     | some true => "_t"
     | some false => "_f"
     | none => "") ++ ".yaml"

/-- The function format (`THEOREM_VECTORS_ARCHITECTURE.md` §13.3). It accepts
the records whose target the reader found: the file's `function` field
names the function a client exposes, and a record without one has no
function to name. -/
def Formats.function : VectorFormat where
  name := "function"
  accepts r := r.target.isSome
  render env r inputBytes outputBytes := do
    let targetDir := (r.target.getD r.thm).toString
    let dir := env.outDir / "formats" / "function" / r.fork / r.preset.tag /
      targetDir
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
        ("theorem", .str r.thm.toString),
        ("function", .str (r.target.getD r.thm).toString),
        ("fork", .str r.fork),
        ("preset", .str r.preset.tag),
        ("shape", .str r.shape.tag),
        ("inputs", .map inputs),
        ("output", output),
        ("source", .str r.source.tag)
      ]
    IO.FS.writeFile file (Yaml.render doc)
    return #[file]
  check _ _ _ := pure .noConsumer

/-- The format registry (`THEOREM_VECTORS_ARCHITECTURE.md` §13.1). Stage 2 holds the
function format alone; the pyspec format appends one value in stage 7. A
new format is one more value here. -/
def Formats.all : Array VectorFormat := #[Formats.function]

end EthCLLib.TheoremVectors
