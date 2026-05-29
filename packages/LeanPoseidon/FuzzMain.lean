import LeanPoseidonTests.Differential

/-!
# `FuzzMain` — entry point for the `poseidon_fuzz` differential executable

A thin `main` over `LeanPoseidonTests.Differential.runMain`. It lives here,
*outside* the `LeanPoseidonTests` library's module hierarchy, on purpose:
an executable whose root is also a library member would have Lake link the
library's symbol-export object (which carries no C `main`). As a
standalone exe root, Lake compiles a dedicated object that emits `main`.

The actual differential logic, the splitmix64 PRNG, and the `@[extern]`
oracle binding all live in `LeanPoseidonTests`; this file only dispatches.
Run via `just fuzz-poseidon` or `lake exe poseidon_fuzz <trials>`.
-/

set_option autoImplicit false

/-- Entry point: forward CLI args to the differential test runner. -/
def main (args : List String) : IO Unit :=
  LeanPoseidonTests.runMain args
