import Lean
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Yaml
import EthCLLib.TheoremVectors.Record
import EthCLLib.Internal.ProofLedger
import EthCLLib.PySpecTests.Driver

/-!
# `EthCLLib.TheoremVectors.Formats.Pyspec`: the epoch_processing format and the shared pyspec case-layout helpers

The `epoch_processing` format value, and the pyspec case-layout helpers
both upstream-runner formats share. The format renders the upstream
`epoch_processing` case layout from `.runOk` and `.runError` records
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.4):

```
<outDir>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<thm>_<case>/
  pre.ssz
  post.ssz          absent for .runError, which marks an invalid case
  meta.yaml         {bls_setting: 2, theorem: <name>}
  manifest.yaml     {preset, fork, runner, handler, suite, case}
```

The layout is the upstream one with raw `.ssz` in place of
`.ssz_snappy`; the Python harness hands the paths to the pyspec server,
which decodes the pre-state, runs the handler, and compares the post
root. `meta.yaml` goes out as one flow line, the form the cached
upstream corpus writes (§12.3).

The check (§13.5) is the point of the format: it rebuilds a
`EthCLLib.PySpecTests.CaseRequest` from the rendered files and replays
it through `runCase` with the fork's `ForkInterface`, so a handler
theorem's vector takes the same path the upstream vectors take. A
`CaseResult` with `passed = false` comes back as `CheckResult.failed`
with the result's bucket and detail line. A flagged pass fails the same
way, with the flag named: the driver scored an invalid vector's replay
reject as a bug-smell, and a bug-smell reject never ships green.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The theorem's local name for a pyspec case directory (§13.4): the
record's theorem with the fork's proof-namespace prefix removed. A
theorem outside the namespace keeps its full name. -/
def Formats.pyspecThmLocal (binding : ForkBinding) (thm : Name) : Name :=
  thm.replacePrefix (EthCLLib.Internal.proofNamespaceOf binding.fork) Name.anonymous

/-- §13.4's acceptance predicate: a `.runOk` or `.runError` record whose
fork resolves to a binding, whose target maps to a `("epoch_processing", _)`
pair in the binding's `handlerOf` map, and whose single input is the state
(input type string equals the binding's state type spelling). The runner
pin gives the value its name's meaning: a single-state record of another
runner's handler belongs to that runner's format, once that format
exists. -/
def Formats.epochProcessingAccepts (env : RenderEnv) (r : VectorRecord) : Bool :=
  (r.shape == .runOk || r.shape == .runError)
    && (match env.bindings r.fork, r.target, r.inputs with
        | some b, some target, #[v] =>
          match b.handlerOf target with
          | some (runner, _) =>
            runner == "epoch_processing"
              && v.type == b.stateType.toString
          | none => false
        | _, _, _ => false)

/-- The §13.4 case directory's own name: the theorem's local name and the
disjunct name, joined with an underscore. The path builder and both
renders read this one composition, so the directory name and the
manifest's `case` key can never disagree. -/
def Formats.pyspecCaseName (binding : ForkBinding) (r : VectorRecord) : String :=
  (Formats.pyspecThmLocal binding r.«theorem»).toString ++ "_" ++
    Record.disjunctName r.disjunctIndex r.side

/-- The §13.4 case directory under `env.outDir`: the `formats/pyspec`
prefix, the fork, the preset tag, the runner, the handler, the
`pyspec_tests` segment, and the case name. The operations format will
render the same layout, so the path stays one shared decision. -/
def Formats.pyspecCaseDir (env : RenderEnv) (b : ForkBinding)
    (r : VectorRecord) (runner handler : String) : System.FilePath :=
  env.outDir / "formats" / "pyspec" / r.fork / r.preset.tag /
    runner / handler / "pyspec_tests" / Formats.pyspecCaseName b r

/-- The §13.4 `post.ssz` write: when the record carries an output, the
helper writes the bytes and answers the path. A record with an output
but no output bytes is a render error. The decision reads the record,
the same field `check` reads, so the two passes can never disagree about
the file's presence. The operations format will share the write. -/
def Formats.pyspecWritePost (dir : System.FilePath) (r : VectorRecord)
    (outputBytes : Option ByteArray) : IO (Option System.FilePath) := do
  if r.output.isSome then
    match outputBytes with
    | some out =>
      let postFile := dir / "post.ssz"
      IO.FS.writeBinFile postFile out
      return some postFile
    | none =>
      throw (IO.userError s!"pyspec render: {r.«theorem»} has an output \
        but no output bytes")
  else
    return none

/-- The §13.4 `meta.yaml` write: the `{bls_setting: 2, theorem: <name>}`
map as one upstream flow line (§12.3). The operations format will share
the write. -/
def Formats.pyspecWriteMeta (dir : System.FilePath) (r : VectorRecord) :
    IO System.FilePath := do
  let metaFile := dir / "meta.yaml"
  let doc : Yaml :=
    .map #[("bls_setting", .int 2), ("theorem", .str r.«theorem».toString)]
  IO.FS.writeFile metaFile (Yaml.renderFlowDoc doc)
  return metaFile

/-- The §13.4 `manifest.yaml` write: the six-key block map upstream puts
in every case directory, rendered through `Yaml.render`'s block form with
one `key: value` line per key in upstream's order (`preset, fork,
runner, handler, suite, case`). The helper derives `preset` and `fork`
from the record and fixes `suite` to `pyspec_tests`. The `case` key
comes from `Formats.pyspecCaseName`, the one composition the directory
name uses, so the key cannot drift from the directory. The operations
format shares the write, and the check never parses the file. -/
def Formats.pyspecWriteManifest (dir : System.FilePath) (b : ForkBinding)
    (r : VectorRecord) (runner handler : String) : IO System.FilePath := do
  let preset := r.preset.tag
  let fork := r.fork
  let suite := "pyspec_tests"
  let case := Formats.pyspecCaseName b r
  let manifestFile := dir / "manifest.yaml"
  let doc : Yaml :=
    .map #[("preset", .str preset), ("fork", .str fork),
      ("runner", .str runner), ("handler", .str handler),
      ("suite", .str suite), ("case", .str case)]
  IO.FS.writeFile manifestFile (Yaml.render doc)
  return manifestFile

/-- §13.4's render: one case directory under `env.outDir` with
`pre.ssz`, `post.ssz` when the record carries an output, `meta.yaml`, and
`manifest.yaml`. Returns the written paths in that order, the list the
check receives (§13.2). -/
def Formats.epochProcessingRender (env : RenderEnv) (r : VectorRecord)
    (inputBytes : Array ByteArray) (outputBytes : Option ByteArray) :
    IO (Array System.FilePath) := do
  let some b := env.bindings r.fork
    | throw (IO.userError
        s!"epoch_processing render: no binding for fork '{r.fork}'")
  let some target := r.target
    | throw (IO.userError
        s!"epoch_processing render: record of {r.«theorem»} has no target")
  let some (runner, handler) := b.handlerOf target
    | throw (IO.userError
        s!"epoch_processing render: {target} has no (runner, handler) pair")
  let some preBytes := inputBytes[0]?
    | throw (IO.userError
        s!"epoch_processing render: no input bytes for the state")
  let dir := Formats.pyspecCaseDir env b r runner handler
  IO.FS.createDirAll dir
  let preFile := dir / "pre.ssz"
  IO.FS.writeBinFile preFile preBytes
  let mut files := #[preFile]
  let postFile ← Formats.pyspecWritePost dir r outputBytes
  if let some postFile := postFile then
    files := files.push postFile
  let metaFile ← Formats.pyspecWriteMeta dir r
  let manifestFile ← Formats.pyspecWriteManifest dir b r runner handler
  return (files.push metaFile).push manifestFile

/-- The §13.5 post read: the post bytes when the record carries an
output, `none` when it does not. A record with an output but no
`post.ssz` in the paths answers the error string, and a check turns that
into `.failed`. The error line carries the caller's format prefix, the
one detail convention the two checks share. The caller's format also
fixes the position: the epoch_processing layout carries the post at
position 1, the operations layout at position 2, where the operand part
sits between pre and post. -/
def Formats.pyspecReadPost (fmt : String) (postIdx : Nat) (r : VectorRecord)
    (paths : Array System.FilePath) : IO (Except String (Option ByteArray)) := do
  if r.output.isSome then
    match paths[postIdx]? with
    | none => return .error s!"{fmt} check: no post.ssz in the rendered paths"
    | some p => return .ok (some (← IO.FS.readBinFile p))
  else
    return .ok none

/-- §13.5's check: rebuild the case from the files `render` returned and
replay it through `EthCLLib.PySpecTests.runCase` with the binding's
`ForkInterface` at the record's preset. The paths arrive in the order
render returned them: `pre.ssz`, then `post.ssz` when the record has an
output, then `meta.yaml`, then `manifest.yaml` (§13.2). A failed replay
names the result's bucket and its detail line, so a human sees why it
failed. A flagged pass fails too: the replay rejected an invalid vector
with a bug-smell the case's caught set admits, and a bug-smell reject
never ships green.

Only the pre and post bytes come from the files. `meta.yaml` is written
but never parsed: the check rebuilds `caseMeta` from the constant
`{ blsSetting := 2 }`, and the `epoch_processing` dispatch reads no meta,
so a tampered meta cannot change the outcome. `manifest.yaml` is written
but never parsed: the check reads no path after `meta.yaml`, so a
tampered manifest cannot change the outcome. -/
def Formats.epochProcessingCheck (env : RenderEnv) (r : VectorRecord)
    (paths : Array System.FilePath) : IO CheckResult := do
  let some b := env.bindings r.fork
    | return .failed s!"epoch_processing check: no binding for fork '{r.fork}'"
  let some target := r.target
    | return .failed
        s!"epoch_processing check: record of {r.«theorem»} has no target"
  let some (_runner, handler) := b.handlerOf target
    | return .failed
        s!"epoch_processing check: {target} has no (runner, handler) pair"
  let some iface := b.interface r.preset
    | return .failed s!"epoch_processing check: binding '{b.tag}' has no interface \
        at preset {r.preset.tag}"
  let some prePath := paths[0]?
    | return .failed "epoch_processing check: no pre.ssz in the rendered paths"
  let pre ← IO.FS.readBinFile prePath
  let post ←
    match ← Formats.pyspecReadPost "epoch_processing" 1 r paths with
    | .error msg => return .failed msg
    | .ok post => pure post
  let req : EthCLLib.PySpecTests.CaseRequest :=
    { runner := "epoch_processing", handler, pre, post, inputs := #[],
      caseMeta := { blsSetting := 2 } }
  -- The interface value passes as the explicit instance argument: the
  -- check holds one runtime value, so there is no instance to synthesize.
  let res := @EthCLLib.PySpecTests.runCase iface req
  -- A flagged pass is a bug-smell the check refuses to bless: the driver
  -- scored an invalid vector as rejected by an `.outOfBounds`-class
  -- reject the case's caught set admits. The check fails and names the
  -- flag, whether or not the record's pure column recorded the same class.
  if res.passed && res.flagged then
    return .failed s!"epoch_processing replay: flagged pass, bucket {res.bucket.tag} \
      ({EthCLLib.PySpecTests.CaseResult.flattenDetail res.detail})"
  if res.passed then
    return .passed
  let flagPart :=
    match res.flagged with
    | true => ", flagged"
    | false => ""
  return .failed s!"epoch_processing replay: bucket {res.bucket.tag} \
    ({EthCLLib.PySpecTests.CaseResult.flattenDetail res.detail}){flagPart}"

/-- The epoch_processing format (`THEOREM_VECTORS_ARCHITECTURE.md` §13.4,
§13.5). It accepts the run-shape records whose target maps to the
`epoch_processing` runner and whose single input is the state, renders the
upstream case layout, and replays the rendered case through the pyspec
driver. The value takes its runner's name, and `accepts` pins the runner,
so the name stays honest. -/
def Formats.epochProcessing : VectorFormat where
  name    := "epoch_processing"
  accepts := Formats.epochProcessingAccepts
  render  := Formats.epochProcessingRender
  check   := Formats.epochProcessingCheck

end EthCLLib.TheoremVectors
