import Lean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.ToyRun
import EthCLLib.Tests.InheritanceReplay

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
a clean `.runError` run. The same drive pins the reader's store rule at
the toy level (§7.3): the two state binders of `toyRunPureOkSecond` read
`.runOk` with the second as the store, `toyRunPureError` reads the
`runPure`-form `.runError`, and a run whose store is a plain value binder
falls to `.eq`.

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

/-- A theorem over the toy fork's `callee`, the forkdef whose docstring
opens with the backticked spec name. The theorem lives outside the fork's
proof namespace, so the command tests' survey clause never discovers it. -/
theorem toyCallee : EthCLLib.Tests.InheritanceReplay.Base.callee = 1 := rfl

/-- A theorem over the toy fork's `caller`, the forkdef whose docstring
names no pyspec step in the opening span's position: the spec-name rule's
negative. -/
theorem toyCaller : EthCLLib.Tests.InheritanceReplay.Base.caller = 11 := rfl

/-- The evaluated probe for one theorem, with a skip reason turned into
the test failure it is. -/
private def builtProbe (thm : Name) (binding : ForkBinding)
    (ctx : StatementCtx) (disjuncts : Array Disjunct) :
    MetaM (ProbeInfo × Probe) := do
  match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
  | .ok r => pure r
  | .error e => throwError s!"{thm}: the probe refused to build: {e}"

/-- The round trip for one theorem: read, prepare, build the probe, check
the base candidate, run, execute the shape's row (§11.3), write the
record, read it back, and re-run the probe on the stored bytes
(`THEOREM_VECTORS_ARCHITECTURE.md` §12.5). Returns the record the round
trip verified. The binding is a parameter: the run-shape drives pass the
toy run binding, whose state type matches the toy state, so the reader's
run shapes fire (§7.3). -/
private def roundTrip (thm : Name) (binding : ForkBinding)
    (dir : System.FilePath) : MetaM VectorRecord := do
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (disjuncts, dropped) ← Prepare.pass stmt
    unless disjuncts.size == 1 && dropped.isEmpty do
      throwError s!"{thm}: expected one prepared disjunct, got {disjuncts.size} \
        (dropped {dropped.size})"
    let (info, probe) := (← builtProbe thm binding ctx disjuncts)
    let d := disjuncts[0]!
    let searchers : Array WitnessSearcher := #[baseSearcher]
    -- `Support.searchCtxOf` does not fit: the context pins
    -- `instConsts := #[]` on purpose, the base-searcher-only round trip
    -- never substitutes an instance, and the helper computes the
    -- constants through `Preset.constOf`
    let searchCtx : SearchCtx :=
      { probe, info, binding, preset := .minimal,
        inputFvars := ctx.inputFvars, instFvars := ctx.instFvars,
        instConsts := #[], manualTerms := #[],
        drawMemo := ← IO.mkRef #[], outDir := Tests.ToyFork.scratchOutDir,
        builtStamp := "", earlierWins := #[] }
    -- §9.4: the base searcher never proposes the binding's state. A
    -- statement over the state takes the probe's defaults here, the same
    -- candidate the base searcher would hand out for a scalar theorem; the
    -- search's own answers are the other test drives' subject
    let won ←
      if baseSearcher.applies searchCtx stmt d then
        match ← searchDisjunct searchers searchCtx stmt d with
        | .ok (a, tag) =>
          unless tag == WitnessSearcherTag.base do
            throwError s!"{thm}: expected the base searcher to win"
          match probe.run a with
          | .ok r => pure (a, r)
          | .error e => throwError s!"{thm}: the probe failed to run: {e}"
        | .error failure =>
          throwError s!"{thm}: the base searcher found no candidate: {repr failure}"
      else
        match probe.run probe.defaults with
        | .ok r => pure (probe.defaults, r)
        | .error e => throwError s!"{thm}: the probe failed to run: {e}"
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
        target := stmt.target, specName := stmt.specName,
        shape := shapeTag,
        disjunctIndex := d.index, side := d.side,
        inputs := inputVals,
        output := outVal, error := errVal,
        -- the searcher field is a record-round-trip label here: on the
        -- defaults branch no searcher ran, and nothing below reads it
        witnessSearcher := WitnessSearcherTag.base }
    -- a record with no output (`.runError`) writes no `output.ssz` (§12.1)
    Record.write dir binding.tag record thm.toString a
      (record.output.map fun _ => r.output)
    let rb ← Record.read (Record.disjunctDir dir binding.tag .minimal
      thm.toString d.index d.side)
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
    let (disjuncts, _) ← Prepare.pass stmt
    let (_, probe) ← builtProbe thm binding ctx disjuncts
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
`errorRepr`). The binding is the toy run binding, whose state type matches
the toy state, so the reader's run shapes fire (§7.3). -/
private def expectRunOkMiss (thm : Name) : MetaM Unit := do
  let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyRunBinding
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (disjuncts, _) ← Prepare.pass stmt
    let (_, probe) ← builtProbe thm binding ctx disjuncts
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
repr, so the message names none. The binding is the toy run binding, for
the reader's run shapes as above. -/
private def expectRunErrorMiss (thm : Name) : MetaM Unit := do
  let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyRunBinding
  Statement.readIn binding thm fun ctx => do
    let stmt ← Scope.classify binding ctx.stmt
    let (disjuncts, _) ← Prepare.pass stmt
    let (_, probe) ← builtProbe thm binding ctx disjuncts
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
    let toyBinding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
    let toyRunBinding := EthCLLib.TheoremVectors.Tests.ToyFork.toyRunBinding
    let eqRecord ← roundTrip `EthCLLib.TheoremVectors.Tests.Probe.toyEq toyBinding dir
    unless eqRecord.output.any fun v => v.value == .scalar "3" do
      throwError "toyEq: expected the scalar output 3"
    unless eqRecord.inputs.any fun v => v.value == .scalar "0" do
      throwError "toyEq: expected the scalar input 0"
    let boundRecord ← roundTrip `EthCLLib.TheoremVectors.Tests.Probe.toyBound toyBinding dir
    unless boundRecord.shape == .bound do
      throwError s!"toyBound: expected the bound shape, got {boundRecord.shape.tag}"
    unless boundRecord.output.any fun v => v.value == .scalar "3" do
      throwError "toyBound: expected the literal output 3"
    -- the run shapes (§11.3): `.runOk` records an SSZ value with its
    -- root, the run's return value when it is the state and the
    -- post-state otherwise, and `.runError` the error's repr with no
    -- output. The drives run under the toy run binding: its state type
    -- is the toy state, so the reader's run shapes fire (§7.3)
    let okRecord ← roundTrip `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk toyRunBinding dir
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
    let okFile := Record.disjunctDir dir okRecord.fork okRecord.preset
      okRecord.«theorem».toString okRecord.disjunctIndex okRecord.side
    unless compareBytes (← IO.FS.readBinFile (okFile / "output.ssz"))
        (uint64BytesLE 42) do
      throwError "toyRunOk: output.ssz is not the post-state with balance 42"
    let errThm := `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunError
    let errRecord ← roundTrip errThm toyRunBinding dir
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
    let errDir := Record.disjunctDir dir errRecord.fork errRecord.preset
      errRecord.«theorem».toString errRecord.disjunctIndex errRecord.side
    let entries ← errDir.readDir
    unless entries.all fun e => e.fileName != "output.ssz" do
      throwError "toyRunError: the record directory wrote an `output.ssz`"
    -- the two-state reading through the full pipeline (§11.3): the
    -- two-state binder theorem runs on the second state, the defaults
    -- branch fills both inputs, and the recorded post-state is the
    -- second input's bytes. The Fulu balance theorems state the same
    -- shape, so the path is the one their generator lines will take
    let twoRecord ← roundTrip
      `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunPureOkSecond toyRunBinding dir
    unless twoRecord.shape == .runOk do
      throwError s!"toyRunPureOkSecond: expected the runOk shape, got \
        {twoRecord.shape.tag}"
    unless twoRecord.inputs.size == 2 do
      throwError s!"toyRunPureOkSecond: expected two input values, got \
        {twoRecord.inputs.size}"
    let some outVal := twoRecord.output
      | throwError "toyRunPureOkSecond: expected an output value"
    let .ssz postRoot := outVal.value
      | throwError "toyRunPureOkSecond: expected an SSZ output value"
    unless !postRoot.isEmpty do
      throwError "toyRunPureOkSecond: the output value carries no root"
    -- the value-style `.runOk` (§11.3's output rule): the run returns
    -- the mutated state, so the record's output is the returned state's
    -- bytes. The defaults draw both states at balance 0. The action
    -- writes 1 and leaves the store at 0, so the store pick's bytes
    -- would read `uint64BytesLE 0`; the pin discriminates the two picks
    let valRecord ← roundTrip
      `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunValueOk toyRunBinding dir
    unless valRecord.shape == .runOk do
      throwError s!"toyRunValueOk: expected the runOk shape, got \
        {valRecord.shape.tag}"
    let some valOut := valRecord.output
      | throwError "toyRunValueOk: expected an output value"
    let some stateIn := valRecord.inputs[0]?
      | throwError "toyRunValueOk: expected a state input value"
    -- the pre-state's type renders to the same string, so the type pins
    -- guard the recorded type naming the container alone; the byte pin
    -- on `output.ssz` below is the one that discriminates the picks
    unless valOut.type == stateIn.type do
      throwError s!"toyRunValueOk: expected the output type to name the \
        container, got {valOut.type}"
    let valRootOk :=
      match valOut.value with
      | .ssz root => !root.isEmpty
      | _ => false
    unless valRootOk do
      throwError "toyRunValueOk: expected the output value to be an SSZ \
        value with a root"
    let valFile := Record.disjunctDir dir valRecord.fork valRecord.preset
      valRecord.«theorem».toString valRecord.disjunctIndex valRecord.side
    unless compareBytes (← IO.FS.readBinFile (valFile / "output.ssz"))
        (uint64BytesLE 1) do
      throwError "toyRunValueOk: output.ssz is not the returned state \
        with balance 1"
    -- the boxed-value spelling records the container's type and the same
    -- bytes: the box's `.view` read serializes the wrapped state, and
    -- the type string names the container the client holds
    let boxRecord ← roundTrip
      `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunBoxValueOk toyRunBinding dir
    unless boxRecord.shape == .runOk do
      throwError s!"toyRunBoxValueOk: expected the runOk shape, got \
        {boxRecord.shape.tag}"
    let some boxOut := boxRecord.output
      | throwError "toyRunBoxValueOk: expected an output value"
    unless boxOut.type == valOut.type do
      throwError s!"toyRunBoxValueOk: expected the output type to name \
        the container, got {boxOut.type}"
    let boxRootOk :=
      match boxOut.value with
      | .ssz root => !root.isEmpty
      | _ => false
    unless boxRootOk do
      throwError "toyRunBoxValueOk: expected the output value to be an \
        SSZ value with a root"
    let boxFile := Record.disjunctDir dir boxRecord.fork boxRecord.preset
      boxRecord.«theorem».toString boxRecord.disjunctIndex boxRecord.side
    unless compareBytes (← IO.FS.readBinFile (boxFile / "output.ssz"))
        (uint64BytesLE 1) do
      throwError "toyRunBoxValueOk: output.ssz is not the returned state \
        with balance 1"
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
    -- the reader's store rule at the toy level (§7.3): the run's state is
    -- one of the state-typed value binders, and the type identifies it
    -- whatever the binder's position
    Statement.readIn toyRunBinding
        `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunPureOkSecond fun ctx => do
      let stmt ← Scope.classify toyRunBinding ctx.stmt
      match stmt.shape with
      | .runOk _ pre _ _ =>
        let some second := ctx.inputFvars[1]?
          | throwError "toyRunPureOkSecond: the statement has no second \
            input binder"
        -- the store is the second of the two state binders
        unless pre == second do
          throwError "toyRunPureOkSecond: the run's store is not the \
            second state binder"
      | _ =>
        throwError s!"toyRunPureOkSecond: expected the runOk shape, got \
          {stmt.shape.wire}"
    Statement.readIn toyRunBinding
        `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunPureError fun ctx => do
      let stmt ← Scope.classify toyRunBinding ctx.stmt
      unless stmt.shape matches .runError _ _ _ do
        throwError s!"toyRunPureError: expected the runError shape, got \
          {stmt.shape.wire}"
    -- the negative: under a binding whose state type is not the toy
    -- state, the run's store is a plain value binder, the run shapes
    -- reject, and matching falls to `.eq`
    Statement.readIn toyBinding
        `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk fun ctx => do
      let stmt ← Scope.classify toyBinding ctx.stmt
      unless stmt.shape matches .eq _ _ do
        throwError s!"toyRunOk at the toy binding: expected the eq \
          fallback, got {stmt.shape.wire}"
    -- the spec name's promotion (stage 10): the target's docstring names the
    -- pyspec spelling, and the reader lifts it at read time
    Statement.readIn toyBinding
        `EthCLLib.TheoremVectors.Tests.Probe.toyCallee fun ctx => do
      unless ctx.stmt.target == some `EthCLLib.Tests.InheritanceReplay.Base.callee do
        throwError "toyCallee: the reader found no target"
      unless ctx.stmt.specName == some "callee" do
        throwError s!"toyCallee: expected the spec name `callee`, got \
          {repr ctx.stmt.specName}"
    -- a target whose docstring names no identifier in the opening
    -- span's position answers `none`
    Statement.readIn toyBinding
        `EthCLLib.TheoremVectors.Tests.Probe.toyCaller fun ctx => do
      unless ctx.stmt.target == some `EthCLLib.Tests.InheritanceReplay.Base.caller do
        throwError "toyCaller: the reader found no target"
      unless ctx.stmt.specName == none do
        throwError s!"toyCaller: expected no spec name, got \
          {repr ctx.stmt.specName}"
    -- a targetless statement answers `none` whatever its docstrings say
    Statement.readIn toyBinding
        `EthCLLib.TheoremVectors.Tests.Probe.toyEq fun ctx => do
      unless ctx.stmt.target == none do
        throwError "toyEq: expected no target"
      unless ctx.stmt.specName == none do
        throwError s!"toyEq: expected no spec name, got \
          {repr ctx.stmt.specName}"
    IO.FS.removeDirAll dir
