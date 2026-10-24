import Lean
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.Formats.Pyspec
import EthCLLib.PySpecTests.Interface
import EthCLLib.PySpecTests.Driver

/-!
# `EthCLLib.TheoremVectors.Formats.Operations`: the operations format

The upstream `operations` case layout, rendered from `.runOk` and
`.runError` records that carry one operand beside the state
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.6):

```
<outDir>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<thm>_<case>/
  pre.ssz
  <operand>.ssz      the operand part, named by `OpKind.inputName`
  post.ssz           absent for .runError, which marks an invalid case
  meta.yaml          {bls_setting: 2, theorem: <name>}
  manifest.yaml      {preset, fork, runner, handler, suite, case}
```

The path layout is the pyspec format's (§13.4). The case parts differ:
the operand part sits between `pre.ssz` and `post.ssz`, and its file
name comes from the `OpKind.inputName` table. The table decides, never
the handler string echoed: `block_header` writes `block.ssz`, and
`voluntary_exit_churn` writes `voluntary_exit.ssz`. A record with two
inputs has no part in the pyspec layout, and a single-state record has
no part here, so the two formats never accept the same record.

The check (§13.5) rebuilds a `EthCLLib.PySpecTests.CaseRequest` from the
rendered files and replays it through `runCase` with the fork's
`ForkInterface`. The driver's `dispatch` parses the handler string to
its typed `OpKind` and calls `runOperation` with the operand bytes, so a
handler theorem's vector takes the same path the upstream vectors take.
A `CaseResult` with `passed = false` comes back as `CheckResult.failed`
with the result's bucket and detail line. A flagged pass fails the same
way, with the flag named: the driver scored an invalid vector's replay
reject as a bug-smell, and a bug-smell reject never ships green.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- §13.6's acceptance predicate: a `.runOk` or `.runError` record whose
fork resolves to a binding, whose target has a `(runner, handler)` pair
with runner `"operations"`, whose handler `OpKind.ofString?` parses, and
whose two inputs are the state and one operand in either position. The
type string identifies the state, so position does not matter; render
finds the state by type. -/
def Formats.operationsAccepts (env : RenderEnv) (r : VectorRecord) : Bool :=
  (r.shape == .runOk || r.shape == .runError)
    && (match env.bindings r.fork, r.target, r.inputs with
        | some b, some target, #[v, w] =>
          match b.handlerOf target with
          | some (runner, handler) =>
            runner == "operations"
              && (EthCLLib.PySpecTests.OpKind.ofString? handler).isSome
              && ((v.type == b.stateType.toString
                    && w.type != b.stateType.toString)
                  || (v.type != b.stateType.toString
                    && w.type == b.stateType.toString))
          | none => false
        | _, _, _ => false)

/-- §13.6's render: one case directory under `env.outDir` with
`pre.ssz`, the operand part at `<k.inputName>.ssz`, `post.ssz` when the
record carries an output, `meta.yaml`, and `manifest.yaml`. The state
input is found by type, never by position, and the operand takes the
other slot. Returns the written paths in that order, the list the check
receives (§13.2). -/
def Formats.operationsRender (env : RenderEnv) (r : VectorRecord)
    (inputBytes : Array ByteArray) (outputBytes : Option ByteArray) :
    IO (Array System.FilePath) := do
  let some b := env.bindings r.fork
    | throw (IO.userError s!"operations render: no binding for fork '{r.fork}'")
  let some target := r.target
    | throw (IO.userError s!"operations render: record of {r.«theorem»} has no target")
  let some (_runner, handler) := b.handlerOf target
    | throw (IO.userError s!"operations render: {target} has no (runner, handler) pair")
  -- The ascription fixes `k`'s type: `ofString?`'s `Option` element type
  -- is a metavariable until the projection below forces it.
  let some k := (EthCLLib.PySpecTests.OpKind.ofString? handler :
      Option EthCLLib.PySpecTests.OpKind)
    | throw (IO.userError s!"operations render: no OpKind for handler '{handler}'")
  let some stateIdx := r.inputs.findIdx? (·.type == b.stateType.toString)
    | throw (IO.userError s!"operations render: no state input for {r.«theorem»}")
  let some operandIdx := r.inputs.findIdx? (·.type != b.stateType.toString)
    | throw (IO.userError s!"operations render: no operand input for {r.«theorem»}")
  let some preBytes := inputBytes[stateIdx]?
    | throw (IO.userError s!"operations render: no input bytes for the state")
  let some operandBytes := inputBytes[operandIdx]?
    | throw (IO.userError s!"operations render: no input bytes for the operand")
  let dir := Formats.pyspecCaseDir env b r "operations" handler
  IO.FS.createDirAll dir
  let preFile := dir / "pre.ssz"
  IO.FS.writeBinFile preFile preBytes
  let operandFile := dir / (k.inputName ++ ".ssz")
  IO.FS.writeBinFile operandFile operandBytes
  let mut files := #[preFile, operandFile]
  let postFile ← Formats.pyspecWritePost dir r outputBytes
  if let some postFile := postFile then
    files := files.push postFile
  let metaFile ← Formats.pyspecWriteMeta dir r
  let manifestFile ← Formats.pyspecWriteManifest dir b r "operations" handler
  return (files.push metaFile).push manifestFile

/-- §13.5's check over the §13.6 layout: rebuild the case from the files
`render` returned and replay it through `EthCLLib.PySpecTests.runCase`
with the binding's `ForkInterface` at the record's preset. The paths
arrive in the order render returned them: `pre.ssz`, the operand part,
`post.ssz` when the record has an output, then `meta.yaml`, then
`manifest.yaml` (§13.2). The post read goes through the shared
`pyspecReadPost`, which this format calls at position 2, where the
operand part sits. A failed replay names the result's bucket and its
detail line, so a human sees why it failed. A flagged pass fails too:
the replay rejected an invalid vector with a bug-smell the case's caught
set admits, and a bug-smell reject never ships green.

Only the pre, operand, and post bytes come from the files. `meta.yaml`
is written but never parsed: the check rebuilds `caseMeta` from the
constant `{ blsSetting := 2 }`. `manifest.yaml` is written but never
parsed: the check reads no path after `meta.yaml`, so a tampered
manifest cannot change the outcome. -/
def Formats.operationsCheck (env : RenderEnv) (r : VectorRecord)
    (paths : Array System.FilePath) : IO CheckResult := do
  let some b := env.bindings r.fork
    | return .failed s!"operations check: no binding for fork '{r.fork}'"
  let some target := r.target
    | return .failed s!"operations check: record of {r.«theorem»} has no target"
  let some (_runner, handler) := b.handlerOf target
    | return .failed s!"operations check: {target} has no (runner, handler) pair"
  let some iface := b.interface r.preset
    | return .failed s!"operations check: binding '{b.tag}' has no interface \
        at preset {r.preset.tag}"
  let some prePath := paths[0]?
    | return .failed "operations check: no pre.ssz in the rendered paths"
  let pre ← IO.FS.readBinFile prePath
  let some operandPath := paths[1]?
    | return .failed "operations check: no operand file in the rendered paths"
  let operandBytes ← IO.FS.readBinFile operandPath
  let post ←
    match ← Formats.pyspecReadPost "operations" 2 r paths with
    | .error msg => return .failed msg
    | .ok post => pure post
  let req : EthCLLib.PySpecTests.CaseRequest :=
    { runner := "operations", handler, pre, post, inputs := #[operandBytes],
      caseMeta := { blsSetting := 2 } }
  -- The interface value passes as the explicit instance argument: the
  -- check holds one runtime value, so there is no instance to synthesize.
  let res := @EthCLLib.PySpecTests.runCase iface req
  -- A flagged pass is a bug-smell the check refuses to bless: the driver
  -- scored an invalid vector as rejected by an `.outOfBounds`-class
  -- reject the case's caught set admits. The check fails and names the
  -- flag, whether or not the record's pure column recorded the same class.
  if res.passed && res.flagged then
    return .failed s!"operations replay: flagged pass, bucket {res.bucket.tag} \
      ({EthCLLib.PySpecTests.CaseResult.flattenDetail res.detail})"
  if res.passed then
    return .passed
  let flagPart :=
    match res.flagged with
    | true => ", flagged"
    | false => ""
  return .failed s!"operations replay: bucket {res.bucket.tag} \
    ({EthCLLib.PySpecTests.CaseResult.flattenDetail res.detail}){flagPart}"

/-- The operations format (`THEOREM_VECTORS_ARCHITECTURE.md` §13.6). It
accepts the run-shape records whose target names an operations handler
and whose two inputs are the state and one operand, renders the upstream
case layout with the operand part between pre and post, and replays the
rendered case through the pyspec driver. -/
def Formats.operations : VectorFormat where
  name    := "operations"
  accepts := Formats.operationsAccepts
  render  := Formats.operationsRender
  check   := Formats.operationsCheck

end EthCLLib.TheoremVectors
