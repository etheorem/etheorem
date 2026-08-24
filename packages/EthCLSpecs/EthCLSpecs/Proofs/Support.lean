import EthCLSpecs.Proofs.Support.OfFnM

/-!
# `EthCLSpecs.Proofs.Support`: fork-independent proof helpers (index)

Lemmas about the Lean library, not about a spec declaration. They belong to no single fork. A
fork's proof directory imports this module when it needs one.

Re-exports:

* `EthCLSpecs.Proofs.Support.OfFnM`: `ofFnM_eq_ok_ofFn`, collapsing an all-succeeding
  `Vector.ofFnM` in `Except` to the pure `Vector.ofFn`.
-/
