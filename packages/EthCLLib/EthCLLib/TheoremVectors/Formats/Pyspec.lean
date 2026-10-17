import Lean
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Yaml
import EthCLLib.TheoremVectors.Record
import EthCLLib.Internal.ProofLedger
import EthCLLib.PySpecTests.Driver

/-!
# `EthCLLib.TheoremVectors.Formats.Pyspec`: the pyspec format

The upstream pyspec case layout, rendered from `.runOk` and `.runError`
records (`THEOREM_VECTORS_ARCHITECTURE.md` §13.4):

```
<outDir>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<thm>_<case>/
  pre.ssz
  post.ssz          absent for .runError, which marks an invalid case
  meta.yaml         {bls_setting: 2, theorem: <name>}
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
fork resolves to a binding, whose target has a `(runner, handler)` pair
in the binding's `handlerOf` map, and whose single input is the state
(input type string equals the binding's state type spelling). -/
def Formats.pyspecAccepts (env : RenderEnv) (r : VectorRecord) : Bool :=
  (r.shape == .runOk || r.shape == .runError)
    && (match env.bindings r.fork, r.target, r.inputs with
        | some b, some target, #[v] =>
          (b.handlerOf target).isSome
            && v.type == b.stateType.toString
        | _, _, _ => false)

/-- §13.4's render: one case directory under `env.outDir` with
`pre.ssz`, `post.ssz` when the record carries an output, and
`meta.yaml`. Returns the written paths in that order, the list the
manifest carries to `check` (§13.2). -/
def Formats.pyspecRender (env : RenderEnv) (r : VectorRecord)
    (inputBytes : Array ByteArray) (outputBytes : Option ByteArray) :
    IO (Array System.FilePath) := do
  let some b := env.bindings r.fork
    | throw (IO.userError s!"pyspec render: no binding for fork '{r.fork}'")
  let some target := r.target
    | throw (IO.userError s!"pyspec render: record of {r.«theorem»} has no target")
  let some (runner, handler) := b.handlerOf target
    | throw (IO.userError s!"pyspec render: {target} has no (runner, handler) pair")
  let some preBytes := inputBytes[0]?
    | throw (IO.userError s!"pyspec render: no input bytes for the state")
  let dir := env.outDir / "formats" / "pyspec" / r.fork / r.preset.tag /
    runner / handler / "pyspec_tests" /
    ((Formats.pyspecThmLocal b r.«theorem»).toString ++ "_" ++
      Record.disjunctName r.disjunctIndex r.side)
  IO.FS.createDirAll dir
  let preFile := dir / "pre.ssz"
  IO.FS.writeBinFile preFile preBytes
  let mut files := #[preFile]
  -- The post decision reads the record, the same field `check` reads, so
  -- the two passes can never disagree about the file's presence.
  if r.output.isSome then
    match outputBytes with
    | some out =>
      let postFile := dir / "post.ssz"
      IO.FS.writeBinFile postFile out
      files := files.push postFile
    | none =>
      throw (IO.userError s!"pyspec render: {r.«theorem»} has an output \
        but no output bytes")
  let metaFile := dir / "meta.yaml"
  let doc : Yaml :=
    .map #[("bls_setting", .int 2), ("theorem", .str r.«theorem».toString)]
  IO.FS.writeFile metaFile (Yaml.renderFlowDoc doc)
  return files.push metaFile

/-- §13.5's check: rebuild the case from the files `render` returned and
replay it through `EthCLLib.PySpecTests.runCase` with the binding's
`ForkInterface` at the record's preset. The paths arrive in the order
render returned them: `pre.ssz`, then `post.ssz` when the record has an
output, then `meta.yaml` (§13.2). A failed replay names the result's
bucket and its detail line, so a human sees why it failed. A flagged
pass fails too: the replay rejected an invalid vector with a bug-smell
the case's caught set admits, and a bug-smell reject never ships green.

Only the pre and post bytes come from the files. `meta.yaml` is written
but never parsed: the check rebuilds `caseMeta` from the constant
`{ blsSetting := 2 }`, and the `epoch_processing` dispatch reads no meta,
so a tampered meta cannot change the outcome. -/
def Formats.pyspecCheck (env : RenderEnv) (r : VectorRecord)
    (paths : Array System.FilePath) : IO CheckResult := do
  let some b := env.bindings r.fork
    | return .failed s!"pyspec check: no binding for fork '{r.fork}'"
  let some target := r.target
    | return .failed s!"pyspec check: record of {r.«theorem»} has no target"
  let some (runner, handler) := b.handlerOf target
    | return .failed s!"pyspec check: {target} has no (runner, handler) pair"
  let some iface := b.interface r.preset
    | return .failed s!"pyspec check: binding '{b.tag}' has no interface \
        at preset {r.preset.tag}"
  let some prePath := paths[0]?
    | return .failed "pyspec check: no pre.ssz in the rendered paths"
  let pre ← IO.FS.readBinFile prePath
  let post ←
    if r.output.isSome then
      match paths[1]? with
      | none => return .failed "pyspec check: no post.ssz in the rendered paths"
      | some p => some <$> IO.FS.readBinFile p
    else
      pure none
  let req : EthCLLib.PySpecTests.CaseRequest :=
    { runner, handler, pre, post, inputs := #[],
      caseMeta := { blsSetting := 2 } }
  -- The interface value passes as the explicit instance argument: the
  -- check holds one runtime value, so there is no instance to synthesize.
  let res := @EthCLLib.PySpecTests.runCase iface req
  -- A flagged pass is a bug-smell the check refuses to bless: the driver
  -- scored an invalid vector as rejected by an `.outOfBounds`-class
  -- reject the case's caught set admits. The check fails and names the
  -- flag, whether or not the record's pure column recorded the same class.
  if res.passed && res.flagged then
    return .failed s!"pyspec replay: flagged pass, bucket {res.bucket.tag} \
      ({EthCLLib.PySpecTests.CaseResult.flattenDetail res.detail})"
  if res.passed then
    return .passed
  let flagPart :=
    match res.flagged with
    | true => ", flagged"
    | false => ""
  return .failed s!"pyspec replay: bucket {res.bucket.tag} \
    ({EthCLLib.PySpecTests.CaseResult.flattenDetail res.detail}){flagPart}"

/-- The pyspec format (`THEOREM_VECTORS_ARCHITECTURE.md` §13.4, §13.5).
It accepts the run-shape records whose target has a handler and whose
single input is the state, renders the upstream case layout, and replays
the rendered case through the pyspec driver. -/
def Formats.pyspec : VectorFormat where
  name    := "pyspec"
  accepts := Formats.pyspecAccepts
  render  := Formats.pyspecRender
  check   := Formats.pyspecCheck

end EthCLLib.TheoremVectors
