import EthCLSpecs.Proofs.BuilderIndex
import EthCLSpecs.Proofs.InitializePtcWindow
import EthCLSpecs.Proofs.UpdateCheckpoints

/-!
# `EthCLSpecs.Proofs`: consensus-spec theorems (index)

Mathlib-free proofs about `EthCLSpecs` declarations, colocated with the specs
the way `SizzLean.Proofs` is colocated with `SizzLean`: same package, same
build, `bv_decide` / `decide` / `native_decide` over the spec's own types, no
mathlib. A theorem that turns out to need mathlib moves to the standalone
`EthCLProofs` package instead (`docs/SPECS_ARCHITECTURE.md` §11), the
`LeanPoseidonProofs` containment pattern, so mathlib never reaches this
library, the framework, the runner, or the conformance path.

Re-exports:

* `EthCLSpecs.Proofs.BuilderIndex`: the builder-index flag round-trip
  (`isBuilderIndex`, `toBuilderIndex`, `convertBuilderIndexToValidatorIndex`).
* `EthCLSpecs.Proofs.InitializePtcWindow`: the seeded `ptcWindow`'s two
  regions (`initializePtcWindow`).
* `EthCLSpecs.Proofs.UpdateCheckpoints`: `Gloas.updateCheckpoints` checkpoint
  monotonicity, the justified/finalized epoch never decreases.
-/
