import Lean
import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Formats.Pyspec
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.ToyRun

/-!
# `EthCLLib.TheoremVectors.Tests.Pyspec`: the epoch_processing format over the toy fork

Build-gate checks for the epoch_processing format
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.4, §13.5), over the toy run
binding: what `accepts` takes and refuses, the rendered case layout with
its byte-exact `meta.yaml` and `manifest.yaml`, and the check that
rebuilds a `CaseRequest` from the rendered files and replays it through
`runCase`. The records are hand-built, no search involved.

Two pins carry the format's point:

- the rendered `.runOk` case round-trips: the bytes travel through the
  written files, and `check` answers `passed` from them alone; a
  tampered `post.ssz` answers `failed`;
- the `.runError` case writes no `post.ssz`, and `check` builds a
  `post := none` request that the toy interface genuinely rejects (the
  `slashings` step runs `toyFail`, and the interface reports its
  `throw "boom"` as the spec assert `toy: boom`).

Three further pins cover the check's other answers: a preset the binding's
interface does not answer, a valid marking whose dispatch rejects (the
driver's `.error e, some _` row), and the index-miss case whose reject
the driver scores as a flagged pass, where `check` fails on the flag.

The scratch output tree lives under this package's `.lake/build`, so the
gitignore carries it and the final `run_cmd` removes it.
-/

set_option autoImplicit false

open Lean
open EthCLLib.Spec (HasherTag)

namespace EthCLLib.TheoremVectors.Tests.Pyspec

/-- A minimal binding standing in for Gloas, so the guard below pins
`Formats.pyspecThmLocal` itself and not a restatement of its body. -/
private def gloasLikeBinding : ForkBinding where
  fork := `EthCLSpecs.Gloas
  tag := "gloas"
  presets := #[]
  hasherTag := `EthCLLib.Spec.fastHasherTag
  crypto := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType := `EthCLSpecs.Gloas.BeaconState
  blockTypes := #[]
  opens := #[]
  builders := #[]
  handlerOf := fun _ => none
  -- §6: the guard pins the local-name fold alone, so the table stays empty.
  pyspecNames := #[]
  interface := fun _ => none

-- the theorem's local name (§13.4): the fork's proof namespace, then the
-- prefix removed
#guard EthCLLib.Internal.proofNamespaceOf `EthCLSpecs.Gloas == `EthCLSpecs.Proofs.Gloas
#guard Formats.pyspecThmLocal gloasLikeBinding
    `EthCLSpecs.Proofs.Gloas.processSlashings == `processSlashings

/-- The scratch output root this module's drive writes and removes. -/
def scratchOutDir : System.FilePath := ".lake/build/test-theorem-vectors-pyspec"

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

/-- The pre-state, the balance the `.runOk` action overwrites. -/
def toyPre : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState := { bal := 5 }

/-- The post-state the action writes. -/
def toyPost : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState := { bal := 42 }

/-- The tampered post-state the drive writes over `post.ssz`. -/
def toyTampered : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState := { bal := 6 }

/-- The Merkle root of one toy state, under the fast hasher. -/
def toyRoot (s : EthCLLib.TheoremVectors.Tests.ToyRun.ToyState) : ByteArray :=
  letI : HasherTag := EthCLLib.Spec.fastHasherTag
  SizzLean.SSZ.hashTreeRoot HasherTag.H s

/-- The hand-built `.runOk` record (§13.4): the state input, the
post-state output, the toy action as the target. -/
def toyRunOkRecord : VectorRecord :=
  { «theorem» := `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk,
    fork := "toyrun", preset := .minimal,
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toySetBal,
    pyspecName := none,
    shape := .runOk, disjunctIndex := 0, side := none,
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) }],
    output := some { name := `output, type := toyStateType,
                     value := .ssz (toyRoot toyPost) },
    error := none, witnessSearcher := .base }

/-- The same record with an `.eq` shape: the epoch_processing format
refuses it. -/
def toyEqRecord : VectorRecord := { toyRunOkRecord with shape := .eq }

/-- The same record with no target: nothing to map through `handlerOf`. -/
def toyNoTargetRecord : VectorRecord := { toyRunOkRecord with target := none }

/-- The same record whose input's type string differs from the binding's
state type: the input is not the state. -/
def toyWrongTypeRecord : VectorRecord :=
  { toyRunOkRecord with
    inputs := #[{ name := `state, type := "Nat", value := .ssz (toyRoot toyPre) }] }

/-- The same record with the operation action as the target: `toyOpApply`
maps to the `operations` runner, so the runner pin refuses it. The pin
keeps the value honest to its name. -/
def toyWrongRunnerRecord : VectorRecord :=
  { toyRunOkRecord with
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toyOpApply }

/-- The hand-built `.runError` record (§13.4): no output, the error's
repr, the toy fail action as the target. -/
def toyRunErrorRecord : VectorRecord :=
  { «theorem» := `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunError,
    fork := "toyrun", preset := .minimal,
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toyFail,
    pyspecName := none,
    shape := .runError, disjunctIndex := 0, side := none,
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) }],
    output := none, error := some (reprStr "boom"), witnessSearcher := .base }

/-- The same `.runOk` record with the toy fail action as the target: a
valid marking (`post.ssz` present) whose dispatch rejects. The driver's
`.error e, some _` row scores it failed, and `check` follows (§13.5). -/
def toyValidRejectedRecord : VectorRecord :=
  { toyRunOkRecord with target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toyFail }

/-- The `.runError` record whose replay rejects out-of-bounds: the toy
index-miss action as the target. The caught set for
`epoch_processing`/`inactivity_updates` is `expect_assertion_error`, which
admits an `.outOfBounds`, so the driver answers a flagged pass and
`check` fails on the flag (§13.5). -/
def toyFlaggedRecord : VectorRecord :=
  { «theorem» := `EthCLLib.TheoremVectors.Tests.ToyRun.toyIndexMissRun,
    fork := "toyrun", preset := .minimal,
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toyIndexMiss,
    pyspecName := none,
    shape := .runError, disjunctIndex := 0, side := none,
    inputs := #[{ name := `state, type := toyStateType,
                  value := .ssz (toyRoot toyPre) }],
    output := none, error := some (reprStr (SizzLean.Cache.IndexError.indexError 5 1)),
    witnessSearcher := .base }

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

end EthCLLib.TheoremVectors.Tests.Pyspec

open Lean.Elab.Command in
open EthCLLib.TheoremVectors in
open EthCLLib.TheoremVectors.Tests.Pyspec in
run_cmd do
  Lean.Elab.Command.liftIO do
    IO.FS.createDirAll scratchOutDir
    -- what accepts takes and refuses (§13.4)
    unless Formats.epochProcessing.accepts toyEnv toyRunOkRecord do
      throw (IO.userError "epoch_processing accepts: the runOk record was refused")
    if Formats.epochProcessing.accepts toyEnv toyEqRecord then
      throw (IO.userError "epoch_processing accepts: the eq-shaped record was accepted")
    if Formats.epochProcessing.accepts toyEnv toyNoTargetRecord then
      throw (IO.userError "epoch_processing accepts: the targetless record was accepted")
    if Formats.epochProcessing.accepts toyEnv toyWrongTypeRecord then
      throw (IO.userError "epoch_processing accepts: the non-state input record was accepted")
    if Formats.epochProcessing.accepts toyEnv toyWrongRunnerRecord then
      throw (IO.userError "epoch_processing accepts: the operations-runner record was accepted")
    unless Formats.epochProcessing.accepts toyEnv toyRunErrorRecord do
      throw (IO.userError "epoch_processing accepts: the runError record was refused")
    -- the rendered layout (§13.4): pre, post, meta, manifest, in one
    -- case directory
    let preBytes := SizzLean.SSZ.serialize toyPre
    let postBytes := SizzLean.SSZ.serialize toyPost
    let paths ← Formats.epochProcessing.render toyEnv toyRunOkRecord
      #[preBytes] (some postBytes)
    unless paths.size == 4 do
      throw (IO.userError s!"epoch_processing render: {paths.size} paths, expected 4")
    let caseDir := scratchOutDir / "formats" / "pyspec" / "toyrun" /
      "minimal" / "epoch_processing" / "effective_balance_updates" /
      "pyspec_tests" / "EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk_000"
    unless paths[0]!.toString == (caseDir / "pre.ssz").toString do
      throw (IO.userError s!"epoch_processing render: pre path is {paths[0]!}")
    unless paths[1]!.toString == (caseDir / "post.ssz").toString do
      throw (IO.userError s!"epoch_processing render: post path is {paths[1]!}")
    unless paths[2]!.toString == (caseDir / "meta.yaml").toString do
      throw (IO.userError s!"epoch_processing render: meta path is {paths[2]!}")
    unless paths[3]!.toString == (caseDir / "manifest.yaml").toString do
      throw (IO.userError s!"epoch_processing render: manifest path is {paths[3]!}")
    unless (← IO.FS.readBinFile paths[0]!) == preBytes do
      throw (IO.userError "epoch_processing render: pre.ssz is not the pre-state's bytes")
    unless (← IO.FS.readBinFile paths[1]!) == postBytes do
      throw (IO.userError "epoch_processing render: post.ssz is not the post-state's bytes")
    -- meta.yaml, byte for byte in the upstream flow form (§12.3)
    unless (← IO.FS.readFile paths[2]!) ==
        "{bls_setting: 2, theorem: EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk}\n" do
      throw (IO.userError "epoch_processing render: meta.yaml is not the pinned flow line")
    -- manifest.yaml, byte for byte in the upstream block form (§12.3):
    -- six keys in upstream order, the case path's segments as the values
    unless (← IO.FS.readFile paths[3]!) ==
        "preset: minimal\n" ++
        "fork: toyrun\n" ++
        "runner: epoch_processing\n" ++
        "handler: effective_balance_updates\n" ++
        "suite: pyspec_tests\n" ++
        "case: EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk_000\n" do
      throw (IO.userError "epoch_processing render: manifest.yaml is not the pinned block map")
    -- the check replays the rendered files through runCase (§13.5)
    checkOutcome "epoch_processing check runOk"
      (← Formats.epochProcessing.check toyEnv toyRunOkRecord paths)
    -- the manifest is written and never parsed: garbage in the file, and
    -- the check still passes on the same paths
    IO.FS.writeFile paths[3]! "garbage\n"
    checkOutcome "epoch_processing check runOk with a garbage manifest"
      (← Formats.epochProcessing.check toyEnv toyRunOkRecord paths)
    -- a preset the binding's interface does not answer fails defensively,
    -- before any file is read
    checkFailsWith "epoch_processing check no-interface" "no interface"
      (← Formats.epochProcessing.check toyEnv
        { toyRunOkRecord with preset := .mainnet } paths)
    -- a tampered post.ssz fails the replay with the root-mismatch detail
    IO.FS.writeBinFile paths[1]! (SizzLean.SSZ.serialize toyTampered)
    checkFailsWith "epoch_processing check tampered" "post-state root mismatch"
      (← Formats.epochProcessing.check toyEnv toyRunOkRecord paths)
    -- the runError case: no post.ssz, and the returned paths reflect that
    let errPaths ← Formats.epochProcessing.render toyEnv toyRunErrorRecord
      #[preBytes] none
    unless errPaths.size == 3 do
      throw (IO.userError s!"epoch_processing render: {errPaths.size} paths for runError, \
        expected 3")
    unless errPaths.all fun p => p.fileName == "pre.ssz" || p.fileName == "meta.yaml"
        || p.fileName == "manifest.yaml" do
      throw (IO.userError s!"epoch_processing render: the runError case wrote \
        {errPaths.map (·.fileName)}")
    -- the invalid case genuinely rejects: the toy interface answers the
    -- assert `toy: boom`, and runCase scores it as the expected rejection
    checkOutcome "epoch_processing check runError"
      (← Formats.epochProcessing.check toyEnv toyRunErrorRecord errPaths)
    -- a valid marking whose dispatch rejects fails the replay: the
    -- driver's `.error e, some _` row carries the reject itself in the
    -- detail, so the needle pins the toy's assert text (§13.5)
    let rejPaths ← Formats.epochProcessing.render toyEnv toyValidRejectedRecord
      #[preBytes] (some postBytes)
    checkFailsWith "epoch_processing check valid-rejected" "toy: boom"
      (← Formats.epochProcessing.check toyEnv toyValidRejectedRecord rejPaths)
    -- the index-miss case: the replay rejects out-of-bounds, an admitted
    -- reject the driver scores as a flagged pass, and `check` fails on
    -- the flag (§13.5)
    let flagPaths ← Formats.epochProcessing.render toyEnv toyFlaggedRecord
      #[preBytes] none
    checkFailsWith "epoch_processing check flagged" "flagged pass"
      (← Formats.epochProcessing.check toyEnv toyFlaggedRecord flagPaths)
    IO.FS.removeDirAll scratchOutDir
