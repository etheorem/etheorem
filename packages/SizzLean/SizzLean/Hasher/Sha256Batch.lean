import SizzLean.Hasher.Class
import LeanHazmatSha256
import LeanSha256.Core

/-!
# `SizzLean.Hasher.Sha256Batch`: batched FFI ≡ spec equivalence

The spec-side half of the batched SHA-256 sibling combine: a
pure-Lean reference function and the named axiom asserting that the
FFI primitive `LeanHazmat.Sha256.sha256BatchCombine` (in the
`LeanHazmatSha256` package) agrees with it pointwise.

The FFI binding itself lives in `LeanHazmatSha256`; this file holds
only the reference def and the axiom, because the axiom needs *both*
the FFI binding and the `LeanSha256` spec in scope, and SizzLean is
the one layer entitled to import both (hazmat-docs/ARCHITECTURE.md §9).

## The batched primitive (recap)

`LeanHazmat.Sha256.sha256BatchCombine lefts rights` takes two *parallel*
arrays, `lefts[i]` / `rights[i]` are the i-th sibling pair, and
returns a same-length array with `output[i] = SHA-256(lefts[i] ++
rights[i])`. The runtime amortises one `EVP_MD_CTX` across the whole
pair array; the FFI surface is shaped for a later SHA-NI / AVX-512
inner loop.

## Trust footprint

One named axiom, `sha256BatchCombine_eq_spec`, asserting that the
FFI primitive agrees pointwise with the pure-Lean SHA-256 reference
(`LeanSha256.combine`). Empirically validated by
`SizzLeanTests/Sha256BatchEquivalence.lean`. Same trust shape as the
scalar `sha256Hash_eq_spec` / `sha256Combine_eq_spec` pair in
`Sha256Equiv.lean`, we trust OpenSSL plus the C shim's loop. A future
`@[csimp]`-proved theorem would clear all three axioms at once; proof
shapes stay identical.
-/

set_option autoImplicit false

namespace SizzLean.Hasher

/-- The pure-Lean reference shape that `LeanHazmat.Sha256.sha256BatchCombine`
matches pointwise. Stated as a `def` so the axiom below can name the
equality cleanly. -/
def sha256BatchCombineSpec
    (lefts rights : Array ByteArray) : Array ByteArray :=
  (lefts.zip rights).map fun (l, r) => LeanSha256.combine l r

/-- **Axiom**: the FFI batched primitive
(`LeanHazmat.Sha256.sha256BatchCombine`, which calls `csrc/sha256_batch.c`'s
`lean_hazmat_sha256_batch_combine` via `@[extern]`) computes the same
function on every input as the pure-Lean reference. Empirically
validated by `Sha256BatchEquivalence.lean`; promoted here to a
named Lean axiom so proofs that depend on the batched primitive
can be audited via `#axioms`. Same trust footprint as
`sha256Combine_eq_spec`, the trust commitment is OpenSSL plus
the C shim's loop. A `@[csimp]`-proved theorem with the same
statement could replace this axiom without disturbing dependent
proofs. -/
axiom sha256BatchCombine_eq_spec :
    @LeanHazmat.Sha256.sha256BatchCombine = sha256BatchCombineSpec

/-! ### Smoke test: rewrite closes a batched-FFI goal -/

example (ls rs : Array ByteArray) :
    LeanHazmat.Sha256.sha256BatchCombine ls rs = sha256BatchCombineSpec ls rs := by
  rw [sha256BatchCombine_eq_spec]

end SizzLean.Hasher
