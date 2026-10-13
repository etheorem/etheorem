import Lean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.ToyRun

/-!
# `EthCLLib.TheoremVectors.Tests.Probe`: the probe and the record round trip

Build-gate checks for the stage-2 pipeline (`THEOREM_VECTORS_ARCHITECTURE.md` §11, §12),
over the toy fork: two theorems, one `.eq` over `UInt64` and one
`.bound`, each run through the probe (build, `check` on the base
candidate, `run`) and a record write / read / re-run round trip; and a
pin that a deliberately wrong expected value fails the agreement check
(§11.3). The wrong theorem's subject is a `def` with an
`implemented_by` implementation one below the kernel's body: the kernel
proves `x + 4 = x + 4` with `rfl`, and the compiled code the probe runs
answers `x + 3`, which is exactly the compiler, FFI, or serialization
defect the check exists to catch, with no axiom in the environment. The
`.eq` construction lives in this test module; the run shapes'
disagreement constructions live beside the clean fixtures in
`ToyRun.lean`, and this module pins that their miss paths
(`runOkMiss` / `runErrorMiss`, §18) trip the executor's build error:
a rejecting `.runOk` run, with the run's repr named in the message, and
a clean `.runError` run.

The scratch output tree lives under this package's `.lake/build`, so the
gitignore carries it and the final `run_cmd` removes it.

## Lean idioms annotated

- The drives run inside `run_cmd` with `liftTermElabM`, because the probe
  and the statement reader are `MetaM` and the statement cannot leave the
  reader's telescope scope.
- `try … catch` distinguishes the expected agreement failure from a probe
  that stopped running: a wrong-value theorem whose run *succeeds* fails
  the test, not the build.
-/

set_option autoImplicit false

open Lean
open EthCLLib.Spec (HasherTag)

namespace EthCLLib.TheoremVectors.Tests.Probe

/-- The toy function under test. -/
def toyFun (x : UInt64) : UInt64 := x + 3

/-- The `.eq` toy theorem. -/
theorem toyEq [HasherTag] (x : UInt64) : toyFun x = x + 3 := rfl

/-- The `.bound` toy theorem. The hypothesis names `UInt64.toNat`, the
same Nat-level form the corpus's scalar bounds use. -/
theorem toyBound [HasherTag] (x : UInt64) (h : x.toNat < 100) :
    toyFun x < 103 := by
  show x + 3 < 103
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  simp only [UInt64.toNat_ofNat]
  omega

/-- The compiled body of `toyWrongFun`: one below the kernel's. -/
private def toyWrongFunImpl (x : UInt64) : UInt64 := x + 3

/-- The kernel's body: `x + 4`. The compiled implementation above computes
one less, so the kernel and the compiled code disagree. -/
@[implemented_by toyWrongFunImpl]
def toyWrongFun (x : UInt64) : UInt64 := x + 4

/-- The wrong-expected theorem. The kernel proves it with `rfl`; the
compiled code refutes it. -/
theorem toyWrongEq [HasherTag] (x : UInt64) : toyWrongFun x = x + 4 := rfl

/-- The evaluated probe for one theorem, with a skip reason turned into
the test failure it is. -/
private def builtProbe (thm : Name) (binding : ForkBinding)
    (ctx : StatementCtx) (cases : Array Case) : MetaM (ProbeInfo × Probe) := do
  match ← Probe.ofStatement binding .minimal ctx cases #[] with
  | .ok r => pure r
  | .error e => throwError s!"{thm}: the probe refused to build: {e}"

/-- The round trip for one theorem: read, prepare, build the probe, check
the base candidate, run, execute the shape's row (§11.3), write the
record, read it back, and re-run the probe on the stored bytes
(`THEOREM_VECTORS_ARCHITECTURE.md` §12.5). Returns the record the round
trip verified. -/
private def roundTrip (thm : Name) (dir : System.FilePath) :
    MetaM VectorRecord := do
  let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (cases, dropped) ← Prepare.pass stmt
    unless cases.size == 1 && dropped.isEmpty do
      throwError s!"{thm}: expected one prepared case, got {cases.size} \
        (dropped {dropped.size})"
    let (info, probe) := (← builtProbe thm binding ctx cases)
    let c := cases[0]!
    let sources : Array WitnessSource := #[baseSource]
    let searchCtx : SearchCtx :=
      { probe, info, binding, preset := .minimal,
        inputFvars := ctx.inputFvars, instFvars := ctx.instFvars,
        instConsts := #[], seedTerms := #[],
        drawMemo := ← IO.mkRef #[], outDir := Tests.ToyFork.scratchOutDir,
        builtStamp := "" }
    let won ← match ← searchCase sources searchCtx stmt c with
      | .ok (a, tag) =>
        unless tag == WitnessSourceTag.base do
          throwError s!"{thm}: expected the base source to win"
        match probe.run a with
        | .ok r => pure (a, r)
        | .error e => throwError s!"{thm}: the probe failed to run: {e}"
      | .error failure =>
        throwError s!"{thm}: the base source found no candidate: {repr failure}"
    let (a, r) := won
    let (outVal, errVal) ← Execute.output thm stmt.shape info r
    let some shapeTag := Shape.tag? stmt.shape
      | throwError s!"{thm}: an unsupported shape reached the record"
    let inputVals : Array VectorValue ←
      (Array.range info.inputNames.size).mapM fun i =>
        VectorValue.ofRun info.inputNames[i]! info.inputTypes[i]!
          (r.inputLiterals.getD i none) (r.inputRoots.getD i none)
    let record : VectorRecord :=
      { «theorem» := stmt.thm, fork := binding.tag, preset := .minimal,
        target := stmt.target, shape := shapeTag,
        caseIndex := c.index, side := c.side,
        inputs := inputVals,
        output := outVal, error := errVal,
        source := WitnessSourceTag.base }
    -- a record with no output (`.runError`) writes no `output.ssz` (§12.1)
    Record.write dir binding.tag record thm.toString a
      (record.output.map fun _ => r.output)
    let rb ← Record.read (Record.caseDir dir binding.tag .minimal
      thm.toString c.index c.side)
    let r2 ← match probe.run rb.inputBytes with
      | .ok r2 => pure r2
      | .error e => throwError s!"{thm}: the read-back failed to decode: {e}"
    unless compareBytes r2.output (rb.outputBytes.getD emptyBytes) do
      throwError s!"{thm}: the read-back disagreed with the recorded output"
    return rb.record

/-- The agreement check must reject the wrong theorem's run
(`THEOREM_VECTORS_ARCHITECTURE.md` §11.3). -/
private def expectAgreementFailure (thm : Name) : MetaM Unit := do
  let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (cases, _) ← Prepare.pass stmt
    let (_, probe) ← builtProbe thm binding ctx cases
    match probe.run probe.defaults with
    | .ok r =>
      unless !r.agree do
        throwError "toyWrongEq: the run agreed, but the theorem is false"
      let failed ← try
        let _ ← Execute.output stmt.thm stmt.shape default r
        pure false
      catch
        -- `Exception.error` carries the ref first, the message second
        | .error _ _ => pure true
        | e => throw e
      unless failed do
        throwError "toyWrongEq: the executor accepted a disagreement"
    | .error e =>
      throwError s!"toyWrongEq: the probe failed to run: {e}"

/-- The `.runOk` disagreement pin (`THEOREM_VECTORS_ARCHITECTURE.md` §18): the
compiled run rejects where the kernel proved `.ok`, so the executor must
throw, and the message must carry the run's rejection repr beside the two
byte values (`Execute.lean`'s disagreement print, fed by `runOkMiss`'s
`errorRepr`). -/
private def expectRunOkMiss (thm : Name) : MetaM Unit := do
  let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (cases, _) ← Prepare.pass stmt
    let (_, probe) ← builtProbe thm binding ctx cases
    match probe.run probe.defaults with
    | .ok r =>
      unless !r.agree do
        throwError s!"{thm}: the run agreed, but the compiled body rejects"
      unless r.errorRepr.isSome do
        throwError s!"{thm}: the miss result carries no rejection repr"
      let msg? ← try
        let _ ← Execute.output stmt.thm stmt.shape default r
        pure none
      catch
        -- `Exception.error` carries the ref first, the message second
        | .error _ m => pure (some (← MessageData.toString m))
        | e => throw e
      let some msg := msg?
        | throwError s!"{thm}: the executor accepted a run disagreement"
      unless msg.contains "; the run answered " do
        throwError s!"{thm}: the disagreement message names no run repr: \
          {msg}"
      unless msg.contains (reprStr "toy: the wrong run rejected") do
        throwError s!"{thm}: the disagreement message carries the wrong \
          repr: {msg}"
    | .error e =>
      throwError s!"{thm}: the probe failed to run: {e}"

/-- The `.runError` ran-clean pin (§18): the compiled run returns cleanly
where the kernel proved `.error`, so the executor must throw for it too.
The miss assembler `runErrorMiss` keeps `agree := false` and carries no
repr, so the message names none. -/
private def expectRunErrorMiss (thm : Name) : MetaM Unit := do
  let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (cases, _) ← Prepare.pass stmt
    let (_, probe) ← builtProbe thm binding ctx cases
    match probe.run probe.defaults with
    | .ok r =>
      unless !r.agree do
        throwError s!"{thm}: the run agreed, but the compiled body runs \
          clean"
      let failed ← try
        let _ ← Execute.output stmt.thm stmt.shape default r
        pure false
      catch
        -- `Exception.error` carries the ref first, the message second
        | .error _ _ => pure true
        | e => throw e
      unless failed do
        throwError s!"{thm}: the executor accepted a ran-clean runError"
    | .error e =>
      throwError s!"{thm}: the probe failed to run: {e}"

end EthCLLib.TheoremVectors.Tests.Probe

open Lean.Elab.Command in
open EthCLLib.TheoremVectors in
open EthCLLib.TheoremVectors.Tests.Probe in
run_cmd do
  liftTermElabM do
    let dir : System.FilePath := ".lake/build/test-theorem-vectors-probe"
    let eqRecord ← roundTrip `EthCLLib.TheoremVectors.Tests.Probe.toyEq dir
    unless eqRecord.output.any fun v => v.value == .scalar "3" do
      throwError "toyEq: expected the scalar output 3"
    unless eqRecord.inputs.any fun v => v.value == .scalar "0" do
      throwError "toyEq: expected the scalar input 0"
    let boundRecord ← roundTrip `EthCLLib.TheoremVectors.Tests.Probe.toyBound dir
    unless boundRecord.shape == .bound do
      throwError s!"toyBound: expected the bound shape, got {boundRecord.shape.tag}"
    unless boundRecord.output.any fun v => v.value == .scalar "3" do
      throwError "toyBound: expected the literal output 3"
    -- the run shapes (§11.3): `.runOk` records the post-state as an SSZ
    -- value with its root, `.runError` the error's repr with no output
    let okRecord ← roundTrip `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk dir
    unless okRecord.shape == .runOk do
      throwError s!"toyRunOk: expected the runOk shape, got {okRecord.shape.tag}"
    unless okRecord.error.isNone do
      throwError "toyRunOk: expected no error value"
    let okOutSsz := okRecord.output.any fun v =>
      match v.value with
      | .ssz root => !root.isEmpty
      | _ => false
    unless okOutSsz do
      throwError "toyRunOk: expected the output value to be an SSZ value \
        with a root"
    -- the recorded post-state is `{ bal := 42 }`: the toy state's SSZ form
    -- is its one `UInt64` field, little-endian. The path derives from the
    -- record, so a toy-binding rename cannot break one field silently
    let okFile := Record.caseDir dir okRecord.fork okRecord.preset
      okRecord.«theorem».toString okRecord.caseIndex okRecord.side
    unless compareBytes (← IO.FS.readBinFile (okFile / "output.ssz"))
        (uint64BytesLE 42) do
      throwError "toyRunOk: output.ssz is not the post-state with balance 42"
    let errThm := `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunError
    let errRecord ← roundTrip errThm dir
    unless errRecord.shape == .runError do
      throwError s!"toyRunError: expected the runError shape, got \
        {errRecord.shape.tag}"
    unless errRecord.output.isNone do
      throwError "toyRunError: expected no output value"
    -- the expected repr computes the same way the run body's term does
    unless errRecord.error == some (reprStr "boom") do
      throwError s!"toyRunError: expected the error repr \
        {reprStr "boom"}, got {errRecord.error}"
    -- §12.1: a `.runError` record writes no `output.ssz`
    let errDir := Record.caseDir dir errRecord.fork errRecord.preset
      errRecord.«theorem».toString errRecord.caseIndex errRecord.side
    let entries ← errDir.readDir
    unless entries.all fun e => e.fileName != "output.ssz" do
      throwError "toyRunError: the record directory wrote an `output.ssz`"
    -- the strict decodes (§9.3): a corrupt record answers `none`, and the
    -- read-back check reads that as a failed decode
    unless (decodeInput (T := Fin 3) #[uint64BytesLE 5] 0).isNone do
      throwError "the `Fin 3` decode accepted the out-of-range value 5"
    unless (decodeInput (T := Fin 3)
        #[ByteArray.mk (Array.replicate 9 0)] 0).isNone do
      throwError "the `Fin 3` decode accepted a nine-byte string"
    unless (decodeInput (T := Fin 3) #[uint64BytesLE 2] 0)
        == some ⟨2, by decide⟩ do
      throwError "the `Fin 3` decode refused the in-range value 2"
    unless (decodeInput (T := UInt64)
        #[ByteArray.mk (Array.replicate 9 0)] 0).isNone do
      throwError "the `SSZRepr` decode accepted a nine-byte string"
    unless (decodeInput (T := UInt64) #[uint64BytesLE 7] 0) == some 7 do
      throwError "the `SSZRepr` decode refused an exact eight-byte string"
    expectAgreementFailure `EthCLLib.TheoremVectors.Tests.Probe.toyWrongEq
    -- the run shapes' disagreement paths (§18): a compiled run that
    -- rejects where the kernel proved `.ok` throws, with the run's repr
    -- named in the message; a compiled run that returns cleanly where
    -- the kernel proved `.error` throws as well
    expectRunOkMiss `EthCLLib.TheoremVectors.Tests.ToyRun.toyWrongRunOk
    expectRunErrorMiss `EthCLLib.TheoremVectors.Tests.ToyRun.toyCleanRunError
    IO.FS.removeDirAll dir
