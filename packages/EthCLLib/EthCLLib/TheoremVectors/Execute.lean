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

Stage 3 carries the `.eq`, `.bound`, and `.iffTrue` rows; `.runOk` and
`.runError` land in stage 7. `handles` names the stage each
not-yet-executable shape waits for, and the command reports a skipped run
with that reason instead of searching a witness it could not record.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The stage that executes the shape, when stage 3's executor does not.
`none` means the shape runs here. An `.unsupported` statement never
reaches this test: the reader's reason reports it before phase B. -/
def Execute.handles? (shape : Shape) : Option String :=
  match shape with
  | .eq .. | .bound .. | .iffTrue .. => none
  | .runOk .. => some "the `.runOk` executor lands in stage 7"
  | .runError .. => some "the `.runError` executor lands in stage 7"
  | .unsupported _ => none

/-- The recorded output of one run (§11.3), plus the error's `repr` for the
`.runError` row stage 7 fills. A `false` agreement is a build error with
both values printed as hex (§11.3, §18). -/
def Execute.output (thm : Name) (shape : Shape) (info : ProbeInfo)
    (r : ProbeResult) : MetaM (Option VectorValue × Option String) := do
  let hexOfBytes (b : ByteArray) := EthCLLib.TheoremVectors.hexOf b
  unless r.agree do
    throwError "theorem_vectors: the compiled sides of `{thm}` disagree \
      (§11.3): lhs {hexOfBytes r.output}, rhs {hexOfBytes r.expected}; \
      the kernel proved them equal, so this is a compiler, FFI, or \
      serialization defect"
  match shape with
  | .eq .. | .bound .. | .iffTrue .. =>
    let out ← VectorValue.ofRun `output info.outputType r.literal r.outputRoot
    pure (some out, none)
  | _ =>
    -- `Probe.ofStatement` refuses to build these shapes in stage 3; the
    -- arms keep the match exhaustive for the later stages
    pure (none, none)

end EthCLLib.TheoremVectors
