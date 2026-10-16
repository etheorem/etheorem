import Lean
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Record

/-!
# `EthCLLib.TheoremVectors.Execute`: the per-shape outcome from a probe run

The executor (`THEOREM_VECTORS_ARCHITECTURE.md` §11.3) turns one `ProbeResult` into the
record's output values, and the agreement check into the build error §18
demands: the kernel proved `f x = e x` for every `x`, so a disagreement
between the compiled sides is a compiler, FFI, or serialization defect, and
both values print.

Every conclusion shape runs: `.eq`, `.bound`, and `.iffTrue` record the
sides' bytes, `.runOk` records one side of the run's result pair, and
`.runError` records the error's `repr` in place of an output (§11.3). The
`.runOk` recorded side is the run's return value when it is the state,
and the store `runPure` produced otherwise.
An `.unsupported` statement never reaches the executor: the reader's
reason reports it before phase B.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- Whether the executor runs the shape: `none` means it runs, `some`
reason names why it cannot. Every conclusion shape runs, so the answer
is `none` on every arm, and an `.unsupported` statement never reaches
the test, because the reader's reason reports it before phase B. -/
def Execute.handles? (shape : Shape) : Option String :=
  match shape with
  | .eq .. | .bound .. | .iffTrue .. | .runOk .. | .runError .. => none
  | .unsupported _ => none

/-- The recorded output of one run (§11.3), plus the error's `repr` for
the `.runError` row. A `false` agreement is a build error with both
values printed as hex, and the run's repr printed beside them when the
result carries one (§11.3, §18). -/
def Execute.output (thm : Name) (shape : Shape) (info : ProbeInfo)
    (r : ProbeResult) : MetaM (Option VectorValue × Option String) := do
  let hexOfBytes (b : ByteArray) := EthCLLib.TheoremVectors.hexOf b
  unless r.agree do
    let reprPart :=
      match r.errorRepr with
      | some s => s!"; the run answered {s}"
      | none => ""
    throwError "theorem_vectors: the compiled sides of `{thm}` disagree \
      (§11.3): actual {hexOfBytes r.output}, expected \
      {hexOfBytes r.expected}{reprPart}; the kernel proved them equal, \
      so this is a compiler, FFI, or serialization defect"
  match shape with
  -- `.eq`, `.bound`, and `.iffTrue` record the left side. `.runOk`
  -- records the recorded side as an SSZ value with its root: the row's
  -- rule sets `literal := none`, and the root carries the value
  -- (§11.3, §12.2; the rule lives in `runOkResult`, `Probe.lean`, and
  -- `info.outputType` already names the recorded side's type)
  | .eq .. | .bound .. | .iffTrue .. | .runOk .. =>
    let out ← VectorValue.ofRun `output info.outputType r.literal r.outputRoot
    pure (some out, none)
  | .runError .. =>
    -- no output (§12.1); the record's `error` value is the actual
    -- error's repr (§12.2)
    pure (none, r.errorRepr)
  | .unsupported _ =>
    -- unreachable: the reader reports the reason before phase B
    pure (none, none)

end EthCLLib.TheoremVectors
