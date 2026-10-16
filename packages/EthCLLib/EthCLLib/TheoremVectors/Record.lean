import Lean
import EthCLLib.TheoremVectors.Types

/-!
# `EthCLLib.TheoremVectors.Record`: the general vector on disk

One record directory per case (`THEOREM_VECTORS_ARCHITECTURE.md` §12.1):

```
<outDir>/records/<fork>/<preset>/<thm>/<case>[_t|_f]/
  record.json
  <input>.ssz          one per input, scalars included, named by the binder
  output.ssz           absent for .runError
```

The wire record is §12.2's JSON. Every value has an `ssz` file; a scalar
adds its literal, a container its Merkle root, so a `UInt64` never meets a
JSON reader's integer range. The writer and the reader move bytes and names
and hold no fork knowledge (§12.4). The read-back check (§12.5) runs in the
command, which owns the probe the check needs.

The on-disk JSON differs from §12.2's sketch in the field names, the
reasons recorded in `IMPLEMENTATION_NOTES.md`: the sketch spells the case
index `case`, and the derived JSON writes the Lean field name
`caseIndex`; the payload nests under `value`, because the scalar's
literal and the container's root share one field slot. The `theorem`
field spells with French quotes in Lean, `«theorem»`, and the derived
JSON writes the wire spelling §12.2 fixes. The sketch names no spec-name
field either; the record adds `specName`, the target's pyspec name
(the stage-10 promotion, recorded in the notes).

## Lean idioms annotated

- The case directory zero-pads the index to three digits, so a directory
  listing reads in case order.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## JSON instances for the wire vocabulary -/

instance : ToJson ShapeTag where
  toJson s := .str s.tag

instance : FromJson ShapeTag where
  fromJson? j := do
    let s ← j.getStr?
    match ShapeTag.ofTag? s with
    | some t => return t
    | none => throw s!"unknown shape tag '{s}'"

instance : ToJson WitnessSourceTag where
  toJson s := .str s.tag

instance : FromJson WitnessSourceTag where
  fromJson? j := do
    let s ← j.getStr?
    match WitnessSourceTag.ofTag? s with
    | some t => return t
    | none => throw s!"unknown witness source tag '{s}'"

/-! ## The record -/

/-- One recorded value (`THEOREM_VECTORS_ARCHITECTURE.md` §5.6): the binder name, the
spec type as the probe rendered it (§12.2), and the payload form §5.6's
`ValueData` picks. -/
structure VectorValue where
  /-- The binder name, or `output`. -/
  name  : Name
  /-- The spec type, rendered: `EthCLSpecs.Gloas.BeaconState`,
  `Fin (3 * slotsPerEpoch)`. -/
  type  : String
  value : ValueData
  deriving ToJson, FromJson

/-- One record directory's content (`THEOREM_VECTORS_ARCHITECTURE.md` §5.6). -/
structure VectorRecord where
  /-- The theorem's full constant name. `theorem` is a keyword, so the
  field carries French quotes and the derived JSON writes the wire spelling
  §12.2 fixes. -/
  «theorem»   : Name
  /-- The binding's tag, such as `"gloas"`. -/
  fork      : String
  /-- The preset the run fixed. -/
  preset    : PresetId
  /-- The spec function under test, when the reader found one (§7.2). -/
  target    : Option Name
  /-- The target's pyspec name, when the reader read one off the target's
  docstring (the stage-10 promotion). The derived JSON writes the wire key
  `specName`, the way `caseIndex` spells. -/
  specName  : Option String
  /-- The conclusion's shape. -/
  shape     : ShapeTag
  /-- The zero-based case index. -/
  caseIndex : Nat
  /-- The `.iffTrue` side, when the shape is `.iffTrue`. -/
  side      : Option Bool
  /-- One entry per input, in binder order. -/
  inputs    : Array VectorValue
  /-- The recorded output, `none` for `.runError`. -/
  output    : Option VectorValue
  /-- The error's `repr`, `.runError` only. -/
  error     : Option String
  /-- The witness source that won. -/
  source    : WitnessSourceTag
  deriving ToJson, FromJson

/-- Build one recorded value from a run's outputs (`THEOREM_VECTORS_ARCHITECTURE.md`
§12.2): a literal records as a scalar, everything else as an SSZ value with
its root. §11.4: an SSZ value with no root is a build error, never an empty
root. -/
def VectorValue.ofRun (name : Name) (typeName : String)
    (literal? : Option String) (root? : Option ByteArray) : MetaM VectorValue := do
  match literal? with
  | some lit => pure { name, type := typeName, value := .scalar lit }
  | none =>
    let some root := root?
      | throwError "theorem_vectors: `{name}` of `{typeName}` has no SSZ \
          form and no Merkle root, so there is nothing to record (§11.4)"
    pure { name, type := typeName, value := .ssz root }

/-! ## The paths (§12.1) -/

/-- The records root, `<outDir>/records`. -/
def Record.dir (outDir : System.FilePath) : System.FilePath :=
  outDir / "records"

/-- One theorem's record directory,
`<outDir>/records/<fork>/<preset>/<thm>`. -/
def Record.thmDir (outDir : System.FilePath) (forkTag : String)
    (preset : PresetId) (thmLocal : String) : System.FilePath :=
  Record.dir outDir / forkTag / preset.tag / thmLocal

/-- The case directory's name: the zero-padded case index, `_t` or `_f`
marking the `.iffTrue` side (§12.1). -/
def Record.caseName (caseIndex : Nat) (side : Option Bool) : String :=
  let digits := toString caseIndex
  String.ofList (List.replicate (3 - min 3 digits.length) '0') ++ digits ++
    (match side with
     | some true => "_t"
     | some false => "_f"
     | none => "")

/-- One case's record directory. -/
def Record.caseDir (outDir : System.FilePath) (forkTag : String)
    (preset : PresetId) (thmLocal : String) (caseIndex : Nat)
    (side : Option Bool) : System.FilePath :=
  Record.thmDir outDir forkTag preset thmLocal /
    Record.caseName caseIndex side

/-! ## The writer and the reader (§12.4) -/

/-- Write one record directory (§12.4): `record.json`, one `<input>.ssz` per
input, and `output.ssz` when the record carries an output. A `.bound`
record's output file holds the literal's UTF-8 bytes, because a `Nat` has no
SSZ form; the record marks it as a scalar either way. -/
def Record.write (outDir : System.FilePath) (forkTag : String)
    (r : VectorRecord) (thmLocal : String) (inputBytes : Array ByteArray)
    (outputBytes : Option ByteArray) : IO Unit := do
  let dir := Record.caseDir outDir forkTag r.preset thmLocal r.caseIndex r.side
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "record.json")
    ((toJson r).render.pretty (width := 100) ++ "\n")
  for (v, bytes) in r.inputs.zip inputBytes do
    IO.FS.writeBinFile (dir / (v.name.toString ++ ".ssz")) bytes
  if let some out := outputBytes then
    IO.FS.writeBinFile (dir / "output.ssz") out

/-- The outcome of reading a record directory back. -/
structure ReadBack where
  record      : VectorRecord
  inputBytes  : Array ByteArray
  outputBytes : Option ByteArray

/-- Read one record directory back (§12.4). A missing `record.json`, a
missing side file, or a JSON mismatch is an error: the generator wrote the
directory, so a mismatch is a defect. -/
def Record.read (dir : System.FilePath) : IO ReadBack := do
  let j ← match Json.parse (← IO.FS.readFile (dir / "record.json")) with
    | .error e => throw (IO.userError s!"cannot read {dir}/record.json: {e}")
    | .ok j => pure j
  let r ← match fromJson? (α := VectorRecord) j with
    | .error e =>
      throw (IO.userError s!"cannot read {dir}/record.json: {e}")
    | .ok r => pure r
  let mut inputBytes : Array ByteArray := #[]
  for v in r.inputs do
    inputBytes := inputBytes.push
      (← IO.FS.readBinFile (dir / (v.name.toString ++ ".ssz")))
  let outputBytes ←
    if r.output.isSome then
      some <$> IO.FS.readBinFile (dir / "output.ssz")
    else
      pure none
  return { record := r, inputBytes, outputBytes }

/-- Every record of one fork and preset, in theorem-then-case order
(the exe's render and list walks). -/
partial def Record.readAll (outDir : System.FilePath) (forkTag : String)
    (preset : PresetId) : IO (Array (System.FilePath × ReadBack)) := do
  let mut out : Array (System.FilePath × ReadBack) := #[]
  let root := Record.dir outDir / forkTag / preset.tag
  unless ← root.isDir do
    return #[]
  for thmEntry in ← root.readDir do
    unless ← thmEntry.path.isDir do continue
    for caseEntry in ← thmEntry.path.readDir do
      unless ← caseEntry.path.isDir do continue
      let path := caseEntry.path
      unless (← path.readDir).any (·.fileName == "record.json") do continue
      out := out.push (path, ← Record.read path)
  return out.qsort fun a b => a.1.toString < b.1.toString

end EthCLLib.TheoremVectors
