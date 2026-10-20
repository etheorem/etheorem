import Lean
import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Formats.Pyspec
import EthCLLib.TheoremVectors.Formats.Operations
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.ToyRun

/-!
# `EthCLLib.TheoremVectors.Tests.Operations`: the operations format over the toy fork

Build-gate checks for the operations format (`THEOREM_VECTORS_ARCHITECTURE.md`
§13.6), over the toy run binding: what `accepts` takes and refuses, the
rendered case layout with its byte-exact `meta.yaml`, and the check that
rebuilds a `CaseRequest` from the rendered files and replays it through
`runCase`. The records are hand-built, no search involved.

Two pins carry the format's point:

- the rendered `.runOk` case round-trips: the bytes travel through the
  written files, and `check` answers `passed` from them alone; a tampered
  `post.ssz` answers `failed` with the root mismatch named;
- the `.runError` case writes no `post.ssz`, and `check` builds a
  `post := none` request that the toy interface genuinely rejects (the
  `block_header` operation runs `toyOpApply` on a zero amount, and the
  interface reports its `throw "zero"` as the spec assert `toy: zero`,
  which the `operations` caught set admits).

The binding's `handlerOf` row maps `toyOpApply` to `block_header`, and
`OpKind.inputName .blockHeader` is `"block"`. The choice is deliberate: the
pinned operand file name `block.ssz` proves the writer reads the
`inputName` table and never echoes the handler string.

The two formats partition the run-shape records: a two-input record has no
part in the pyspec layout, and a one-input record has no part here, so the
drive pins `Formats.pyspec` refusing the record this format accepts. Two
further pins cover the edges: a preset the binding's interface does not
answer fails the check defensively, and an unparseable handler fails the
`OpKind.ofString?` leg of `accepts`.

The scratch output tree lives under this package's `.lake/build`, so the
gitignore carries it and the final `run_cmd` removes it.
-/

set_option autoImplicit false

open Lean
open EthCLLib.Spec (HasherTag)

namespace EthCLLib.TheoremVectors.Tests.Operations

/-- The scratch output root this module's drive writes and removes. -/
def scratchOutDir : System.FilePath := ".lake/build/test-theorem-vectors-operations"

/-- The render environment the drive builds: one binding, by tag. -/
def toyEnv : RenderEnv :=
  { outDir := scratchOutDir,
    bindings := fun tag =>
      if tag == "toyrun" then some EthCLLib.TheoremVectors.Tests.ToyFork.toyRunBinding
      else none }

/-- The toy state's rendered type: the state constant's full name, the
spelling the probe puts in a record (§12.2). -/
def toyStateType : String :=
  (`EthCLLib.TheoremVectors.Tests.ToyRun.ToyState).toString

/-- The toy operand's rendered type: the operand constant's full name. -/
def toyReqType : String :=
  (`EthCLLib.TheoremVectors.Tests.ToyRun.ToyReq).toString

/-- The pre-state, the balance the `.runOk` action overwrites. -/
def toyPre : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState := { bal := 5 }

/-- The post-state the action writes. -/
def toyPost : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState := { bal := 42 }

/-- The tampered post-state the drive writes over `post.ssz`. -/
def toyTampered : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState := { bal := 6 }

/-- The operand the `.runOk` action applies: the amount it writes. -/
def toyReq : EthCLLib.TheoremVectors.Tests.ToyRun.ToyReq := { amt := 42 }

/-- The zero operand the `.runError` action rejects on. -/
def toyReqZero : EthCLLib.TheoremVectors.Tests.ToyRun.ToyReq := { amt := 0 }

/-- The Merkle root of one toy state, under the fast hasher. -/
def toyRoot (s : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState) : ByteArray :=
  letI : HasherTag := EthCLLib.Spec.fastHasherTag
  SizzLean.SSZ.hashTreeRoot HasherTag.H s

/-- The Merkle root of one toy operand, under the fast hasher. -/
def toyReqRoot (r : EthCLLib.TheoremVectors.Tests.ToyRun.ToyReq) : ByteArray :=
  letI : HasherTag := EthCLLib.Spec.fastHasherTag
  SizzLean.SSZ.hashTreeRoot HasherTag.H r

/-- The hand-built `.runOk` record (§13.6): the state and the operand as
the inputs, the post-state as the output, the toy operation as the target. -/
def toyOpRunOkRecord : VectorRecord :=
  { «theorem» := `EthCLLib.TheoremVectors.Tests.ToyRun.toyOpRunOk,
    fork := "toyrun", preset := .minimal,
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toyOpApply,
    pyspecName := none,
    shape := .runOk, disjunctIndex := 0, side := none,
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) },
                { name := `req, type := toyReqType,
                  value := .ssz (toyReqRoot toyReq) }],
    output := some { name := `output, type := toyStateType,
                     value := .ssz (toyRoot toyPost) },
    error := none, witnessSearcher := .base }

/-- The same record with the operand first: `accepts` and `render` read the
state out by type, so the binder order never decides. -/
def toyOpOperandFirstRecord : VectorRecord :=
  { toyOpRunOkRecord with
    inputs := #[{ name := `req, type := toyReqType,
                  value := .ssz (toyReqRoot toyReq) },
                { name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) }] }

/-- The same record with an `.eq` shape: the shape leg refuses it. -/
def toyOpEqRecord : VectorRecord := { toyOpRunOkRecord with shape := .eq }

/-- The same record with no target: no `(runner, handler)` pair to map,
so the target leg refuses it. -/
def toyOpNoTargetRecord : VectorRecord := { toyOpRunOkRecord with target := none }

/-- The same record with the state alone: `accepts` matches exactly two
inputs, so the inputs leg refuses it. -/
def toyOpOneInputRecord : VectorRecord :=
  { toyOpRunOkRecord with
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) }] }

/-- The same record with two state-typed inputs: no input differs from the
state type, so the type-split leg refuses it. -/
def toyOpTwoStatesRecord : VectorRecord :=
  { toyOpRunOkRecord with
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) },
                { name := `other, type := toyStateType,
                  value := .ssz (toyRoot toyPre) }] }

/-- The same record with the epoch action as the target: `toySetBal` maps
to `epoch_processing`, so the runner leg refuses it. -/
def toyOpWrongRunnerRecord : VectorRecord :=
  { toyOpRunOkRecord with
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toySetBal }

/-- The hand-built `.runError` record (§13.6): the zero operand, no
output, the error's repr. -/
def toyOpRunErrorRecord : VectorRecord :=
  { «theorem» := `EthCLLib.TheoremVectors.Tests.ToyRun.toyOpRunError,
    fork := "toyrun", preset := .minimal,
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toyOpApply,
    pyspecName := none,
    shape := .runError, disjunctIndex := 0, side := none,
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) },
                { name := `req, type := toyReqType,
                  value := .ssz (toyReqRoot toyReqZero) }],
    output := none, error := some (reprStr "zero"), witnessSearcher := .base }

/-- A binding whose `operations` row names a handler no `OpKind` parses:
the `OpKind.ofString?` leg refuses the record under it. -/
private def toyBogusBinding : ForkBinding :=
  { EthCLLib.TheoremVectors.Tests.ToyFork.toyRunBinding with
    handlerOf := fun
      | `EthCLLib.TheoremVectors.Tests.ToyRun.toyOpApply =>
          some ("operations", "not_a_handler")
      | _ => none }

/-- The render environment over the bogus binding. -/
private def toyBogusEnv : RenderEnv :=
  { outDir := scratchOutDir,
    bindings := fun tag =>
      if tag == "toyrun" then some toyBogusBinding else none }

/-- One check outcome that must answer `passed`. -/
private def checkOutcome (label : String) (r : CheckResult) : IO Unit :=
  match r with
  | .passed => pure ()
  | .failed d =>
    throw (IO.userError s!"{label}: the check failed: {d}")
  | .noConsumer =>
    throw (IO.userError s!"{label}: the check answered noConsumer")

/-- One check outcome that must answer `failed`, with `needle` in the
detail line. -/
private def checkFailsWith (label : String) (needle : String)
    (r : CheckResult) : IO Unit :=
  match r with
  | .failed d =>
    unless d.contains needle do
      throw (IO.userError s!"{label}: unexpected detail {d}")
  | .passed =>
    throw (IO.userError s!"{label}: the check passed")
  | .noConsumer =>
    throw (IO.userError s!"{label}: the check answered noConsumer")

end EthCLLib.TheoremVectors.Tests.Operations

open Lean.Elab.Command in
open EthCLLib.TheoremVectors in
open EthCLLib.TheoremVectors.Tests.Operations in
run_cmd do
  Lean.Elab.Command.liftIO do
    IO.FS.createDirAll scratchOutDir
    -- what accepts takes and refuses (§13.6)
    unless Formats.operations.accepts toyEnv toyOpRunOkRecord do
      throw (IO.userError "operations accepts: the runOk record was refused")
    unless Formats.operations.accepts toyEnv toyOpOperandFirstRecord do
      throw (IO.userError "operations accepts: the operand-first record was refused")
    unless Formats.operations.accepts toyEnv toyOpRunErrorRecord do
      throw (IO.userError "operations accepts: the runError record was refused")
    if Formats.operations.accepts toyEnv toyOpEqRecord then
      throw (IO.userError "operations accepts: the eq-shaped record was accepted")
    if Formats.operations.accepts toyEnv toyOpNoTargetRecord then
      throw (IO.userError "operations accepts: the targetless record was accepted")
    if Formats.operations.accepts toyEnv toyOpOneInputRecord then
      throw (IO.userError "operations accepts: the one-input record was accepted")
    if Formats.operations.accepts toyEnv toyOpTwoStatesRecord then
      throw (IO.userError "operations accepts: the two-state-inputs record was accepted")
    if Formats.operations.accepts toyEnv toyOpWrongRunnerRecord then
      throw (IO.userError "operations accepts: the epoch-runner record was accepted")
    -- the partition pin: the two-input record belongs to this format alone
    if Formats.pyspec.accepts toyEnv toyOpRunOkRecord then
      throw (IO.userError "operations accepts: the pyspec format accepted the runOk record")
    -- the unparseable handler: the `OpKind.ofString?` leg refuses it
    if Formats.operations.accepts toyBogusEnv toyOpRunOkRecord then
      throw (IO.userError "operations accepts: the bogus-handler record was accepted")
    -- the rendered layout (§13.6): pre, operand, post, meta, in one case
    -- directory, the operand file named by `OpKind.inputName`
    let preBytes := SizzLean.SSZ.serialize toyPre
    let reqBytes := SizzLean.SSZ.serialize toyReq
    let postBytes := SizzLean.SSZ.serialize toyPost
    let paths ← Formats.operations.render toyEnv toyOpRunOkRecord
      #[preBytes, reqBytes] (some postBytes)
    unless paths.size == 4 do
      throw (IO.userError s!"operations render: {paths.size} paths, expected 4")
    let caseDir := scratchOutDir / "formats" / "pyspec" / "toyrun" /
      "minimal" / "operations" / "block_header" /
      "pyspec_tests" / "EthCLLib.TheoremVectors.Tests.ToyRun.toyOpRunOk_000"
    unless paths[0]!.toString == (caseDir / "pre.ssz").toString do
      throw (IO.userError s!"operations render: pre path is {paths[0]!}")
    unless paths[1]!.toString == (caseDir / "block.ssz").toString do
      throw (IO.userError s!"operations render: operand path is {paths[1]!}")
    unless paths[2]!.toString == (caseDir / "post.ssz").toString do
      throw (IO.userError s!"operations render: post path is {paths[2]!}")
    unless paths[3]!.toString == (caseDir / "meta.yaml").toString do
      throw (IO.userError s!"operations render: meta path is {paths[3]!}")
    unless (← IO.FS.readBinFile paths[0]!) == preBytes do
      throw (IO.userError "operations render: pre.ssz is not the pre-state's bytes")
    unless (← IO.FS.readBinFile paths[1]!) == reqBytes do
      throw (IO.userError "operations render: block.ssz is not the operand's bytes")
    unless (← IO.FS.readBinFile paths[2]!) == postBytes do
      throw (IO.userError "operations render: post.ssz is not the post-state's bytes")
    -- meta.yaml, byte for byte in the upstream flow form (§12.3)
    unless (← IO.FS.readFile paths[3]!) ==
        "{bls_setting: 2, theorem: EthCLLib.TheoremVectors.Tests.ToyRun.toyOpRunOk}\n" do
      throw (IO.userError "operations render: meta.yaml is not the pinned flow line")
    -- the operand-first render lands the same paths in the same order: the
    -- state input is found by type, the operand takes the other slot
    let firstPaths ← Formats.operations.render toyEnv toyOpOperandFirstRecord
      #[reqBytes, preBytes] (some postBytes)
    unless firstPaths.size == 4 do
      throw (IO.userError s!"operations render: {firstPaths.size} paths \
        for the operand-first record, expected 4")
    unless firstPaths[0]!.toString == (caseDir / "pre.ssz").toString do
      throw (IO.userError s!"operations render: the operand-first pre path is {firstPaths[0]!}")
    unless firstPaths[1]!.toString == (caseDir / "block.ssz").toString do
      throw (IO.userError s!"operations render: the operand-first operand path \
        is {firstPaths[1]!}")
    unless (← IO.FS.readBinFile firstPaths[1]!) == reqBytes do
      throw (IO.userError "operations render: the operand-first operand file \
        is not the operand's bytes")
    unless (← IO.FS.readBinFile firstPaths[0]!) == preBytes do
      throw (IO.userError "operations render: the operand-first pre file \
        is not the pre-state's bytes")
    -- the check replays the rendered files through runCase (§13.5)
    checkOutcome "operations check runOk"
      (← Formats.operations.check toyEnv toyOpRunOkRecord paths)
    -- a preset the binding's interface does not answer fails defensively,
    -- before any file is read
    checkFailsWith "operations check no-interface" "no interface"
      (← Formats.operations.check toyEnv
        { toyOpRunOkRecord with preset := .mainnet } paths)
    -- This pin guards the post read's position. On the success fixture the
    -- operand bytes and the post bytes serialize identically, both one-`UInt64`
    -- containers holding 42, so the `check` pass alone cannot catch a post
    -- read at position 1.
    IO.FS.writeBinFile paths[2]! (SizzLean.SSZ.serialize toyTampered)
    checkFailsWith "operations check tampered" "post-state root mismatch"
      (← Formats.operations.check toyEnv toyOpRunOkRecord paths)
    -- the runError case: no post.ssz, and the returned paths reflect that
    let zeroReqBytes := SizzLean.SSZ.serialize toyReqZero
    let errPaths ← Formats.operations.render toyEnv toyOpRunErrorRecord
      #[preBytes, zeroReqBytes] none
    unless errPaths.size == 3 do
      throw (IO.userError s!"operations render: {errPaths.size} paths for runError, \
        expected 3")
    unless errPaths.all fun p => p.fileName == "pre.ssz" || p.fileName == "block.ssz"
        || p.fileName == "meta.yaml" do
      throw (IO.userError s!"operations render: the runError case wrote \
        {errPaths.map (·.fileName)}")
    -- the invalid case genuinely rejects: the toy interface answers the
    -- assert `toy: zero`, and the `operations` caught set admits it
    checkOutcome "operations check runError"
      (← Formats.operations.check toyEnv toyOpRunErrorRecord errPaths)
    IO.FS.removeDirAll scratchOutDir
