import SizzLean.Proofs.Roundtrip

/-!
# `SizzLean.Proofs.Injective`: non-malleability

ARCHITECTURE.md §4 calls non-malleability "the highest-value
publishable artefact in the library: SSZ guarantees it implicitly
by construction (canonical little-endian, monotonic offsets,
minimal bitlist trailing-bit, no extra bytes), but no
implementation has ever proved it. Stating, proving, and shipping
it as a Lean 4 artefact is the standard the EF should hold itself
to."

The proof is a direct corollary of `decode_encode`: if
`serialize s x = serialize s y`, decoding both sides yields the
same `Except`, and `decode_encode` tells us the decode result is
`(x, _)` on the left and `(y, _)` on the right; injection on
`Except.ok` and `Prod.mk` extracts `x = y`.

## Scope

Mirrors `Proofs/Roundtrip.lean`'s narrowing. `decode_encode` is
proved over `BasicSupported`; this file's `serialize_injective`
inherits that scope and grows mechanically as `BasicSupported`
extends.

## Lean idioms used here

* `Except.ok.inj`: Lean core lemma stating `.ok a = .ok b → a = b`.
  Generated automatically for inductive constructors. Combined with
  `Prod.mk.inj` to project out the first component.
* The three-line proof template: substitute the assumed equality
  with `rw [hxy] at hx_eq`, replace the LHS of `hx_eq` with `hy`'s
  closed-form decoding, then inject the `Except.ok` and project
  the first pair component.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- *Non-malleability* (ARCHITECTURE.md §4): two values of the
same `BasicSupported` shape never serialize to the same bytes
unless they are equal. Direct corollary of `decode_encode`.

The proof script:

1. Apply `decode_encode` twice, once to get
   `deserialize s (serialize s x) = .ok (x, _)` (call it `hx`),
   once for `y`.
2. Rewrite `hx` using the assumed `serialize s x = serialize s y`
   to replace its LHS with `deserialize s (serialize s y)`.
3. Combine with `hy` to get `.ok (x, _) = .ok (y, _)`.
4. Inject the `.ok` and project on the first pair component. -/
theorem serialize_injective : ∀ (s : SSZType), SSZType.BasicSupported s →
    ∀ (x y : s.interp),
      SSZType.serialize s x = SSZType.serialize s y → x = y := by
  intro s h_sup x y heq
  have hx := decode_encode h_sup x
  have hy := decode_encode h_sup y
  -- hx : deserialize s (serialize s x) = .ok (x, (serialize s x).size)
  -- hy : deserialize s (serialize s y) = .ok (y, (serialize s y).size)
  rw [heq] at hx
  -- hx : deserialize s (serialize s y) = .ok (x, (serialize s y).size)
  rw [hy] at hx
  -- hx : .ok (y, _) = .ok (x, _)
  -- `Except.ok.inj` gives `(y, _) = (x, _)`, then `Prod.mk.inj` projects.
  have hpair := Except.ok.inj hx
  exact (Prod.mk.inj hpair).1.symm

end SizzLean.Proofs
