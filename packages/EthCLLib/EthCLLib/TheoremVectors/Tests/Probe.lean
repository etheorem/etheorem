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

/-!
# `EthCLLib.TheoremVectors.Tests.Probe`: the probe and the record round trip

Build-gate checks for the stage-2 pipeline (`THEOREM_VECTORS_ARCHITECTURE.md` §11, §12),
over the toy fork: two theorems, one `.eq` over `UInt64` and one
`.bound`, each run through the probe (build, `check` on the base
candidate, `run`) and a record write / read / re-run round trip; and a
pin that a deliberately wrong expected value fails the agreement check
(§11.3). The wrong theorem's proof rests on a false axiom, so the kernel
accepts an equality whose two compiled sides evaluate differently, which
is exactly the compiler, FFI, or serialization defect the check exists to
catch. The plan sketches the constant as `opaque`; an opaque cannot serve,
because the kernel never unfolds it and so can prove no wrong equality
about it, while a `native_decide` proof of one runs the same compiled
code the probe runs and the two sides would agree. The axiom lives in
this test module alone.

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

/-- The `.bound` toy theorem. The hypothesis rides `UInt64.toNat`, the
same Nat-level form the corpus's scalar bounds use. -/
theorem toyBound [HasherTag] (x : UInt64) (h : x.toNat < 100) :
    toyFun x < 103 := by
  show x + 3 < 103
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  simp only [UInt64.toNat_ofNat]
  omega

/-- A deliberately false axiom: it asserts what the compiled code
refutes, so the kernel accepts and the executor must disagree. -/
axiom toyKernelLies (x : UInt64) : toyFun x = x + 4

/-- The wrong-expected theorem. -/
theorem toyWrongEq [HasherTag] (x : UInt64) : toyFun x = x + 4 := toyKernelLies x

/-- The evaluated probe for one theorem, with a skip reason turned into
the test failure it is. -/
private def builtProbe (thm : Name) (binding : ForkBinding)
    (ctx : StatementCtx) (cases : Array Case) : MetaM (ProbeInfo × Probe) := do
  match ← Probe.ofStatement binding .minimal ctx cases #[] with
  | .ok r => pure r
  | .error e => throwError s!"{thm}: the probe refused to build: {e}"

/-- The round trip for one theorem: read, prepare, build the probe, check
the base candidate, run, write the record, read it back, and re-run the
probe on the stored bytes (`THEOREM_VECTORS_ARCHITECTURE.md` §12.5). Returns the record
the round trip verified. -/
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
    let searchCtx : SearchCtx := { probe, info, binding, preset := .minimal }
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
    unless r.agree do
      throwError s!"{thm}: the run disagreed"
    let inputVals : Array VectorValue :=
      (Array.range info.inputNames.size).map fun i =>
        VectorValue.ofRun info.inputNames[i]! info.inputTypes[i]!
          (r.inputLiterals.getD i none) (r.inputRoots.getD i none)
    let record : VectorRecord :=
      { thm := stmt.thm, fork := binding.tag, preset := .minimal,
        target := stmt.target, shape := match stmt.shape with
          | .eq .. => .eq
          | .bound .. => .bound
          | _ => .eq,
        caseIndex := c.index, side := c.side,
        inputs := inputVals,
        output := some (VectorValue.ofRun `output info.outputType
          r.literal r.outputRoot),
        error := none, source := WitnessSourceTag.base }
    Record.write dir binding.tag record thm.toString a (some r.output)
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
      catch _ => pure true
      unless failed do
        throwError "toyWrongEq: the executor accepted a disagreement"
    | .error e =>
      throwError s!"toyWrongEq: the probe failed to run: {e}"

end EthCLLib.TheoremVectors.Tests.Probe

open Lean.Elab.Command
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
    expectAgreementFailure `EthCLLib.TheoremVectors.Tests.Probe.toyWrongEq
    IO.FS.removeDirAll dir
