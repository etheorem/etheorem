import EthCLLib.TheoremVectors
import EthCLSpecs.TheoremVectors.Bindings
import EthCLSpecs.TheoremVectors.Builders.Fulu
import EthCLSpecs.TheoremVectors.Builders.Gloas
import EthCLSpecs.TheoremVectors.Builders.Heze
import EthCLSpecs.TheoremVectors.Generators.Fulu
import EthCLSpecs.TheoremVectors.Generators.Gloas
import EthCLSpecs.TheoremVectors.Generators.Heze

/-!
# `EthCLSpecs.TheoremVectors`: the theorem-vector generator's spec half

Library root (`THEOREM_VECTORS_ARCHITECTURE.md` §2.1, §4.2). The spec half supplies every
fork fact the framework half asks for: one `ForkBinding` value per fork,
the state-builder catalogs, the committed hints, and the generator files
whose elaboration writes the records. The manual terms live under their
theorems in the `Proofs/` files. §4.2 places each of those in its own
module under this root. The
generator commands run
at `lake build` time, so building this library is what writes the
outcome files the report folds.
-/

set_option autoImplicit false

namespace EthCLSpecs.TheoremVectors

/-- The output root every command writes into (`THEOREM_VECTORS_ARCHITECTURE.md` §2.3).
The path is relative to the repository root, which is where Lake and the
just recipes run it; the exe's `--out` default comes from this constant,
and the check below holds the lakefile to the same path. -/
def outDir : String := "packages/EthCLSpecs/theorem_vectors"

/-! ## The output-root pin

The lakefile fixes `theorem_vectors.outDir` for this library with a `weak.`
`-D` setting (`THEOREM_VECTORS_ARCHITECTURE.md` §2.3), which the reader adopts once the
module that registers the option is imported. The check fires at build
time, so a lakefile that drops the setting or a constant that drifts from
it fails here instead of letting the records land under a default
directory. -/

open Lean Elab Command in
run_cmd do
  let v := (← getOptions).get? `theorem_vectors.outDir |>.getD ""
  unless v == outDir do
    throwError s!"theorem_vectors.outDir is '{v}'; the lakefile must pin \
      {outDir} so the records land in one place."

end EthCLSpecs.TheoremVectors
