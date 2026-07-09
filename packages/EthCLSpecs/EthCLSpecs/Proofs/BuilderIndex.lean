import EthCLSpecs.Gloas.Operations
import Std.Tactic.BVDecide

/-!
# `EthCLSpecs.Proofs.BuilderIndex`: the builder-index flag round-trip

`EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex` sets the
`BUILDER_INDEX_FLAG` bit and `EthCLSpecs.Gloas.toBuilderIndex` clears it, both
single bitwise operations on `UInt64` against the same single-bit mask
`EthCLSpecs.Fulu.Const.builderIndexFlag`. The round-trip properties are
conditional: each needs the relevant flag state before clearing or setting
the bit; see the individual theorems for the exact statement, via
`isBuilderIndex`, the spec's own named predicate for the bit test, rather
than the raw `&&&` expression it unfolds to.

All three proofs unfold to the raw `UInt64` bitwise expression and close with
`bv_decide`, no mathlib needed.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "New Gloas functionality".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLSpecs.Fulu
open EthCLSpecs.Gloas

/-- `convertBuilderIndexToValidatorIndex` and `toBuilderIndex` round-trip on
every `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit.
`convertBuilderIndexToValidatorIndex` sets that bit; `toBuilderIndex`
unconditionally clears it, so the hypothesis is what makes clearing it a
no-op.

`isBuilderIndex` tests via `!=` (`bne`), opaque to `bv_decide` until
`bne_eq_false_iff_eq` rewrites it into a plain `UInt64` equation. -/
theorem toBuilderIndex_convertBuilderIndexToValidatorIndex :
    ∀ (bi : BuilderIndex), isBuilderIndex bi = false →
      toBuilderIndex (convertBuilderIndexToValidatorIndex bi) = bi := by
  intro bi h
  unfold isBuilderIndex at h
  unfold toBuilderIndex convertBuilderIndexToValidatorIndex
  simp only [bne_eq_false_iff_eq] at h
  bv_decide

/-- The mirror direction: `toBuilderIndex` and `convertBuilderIndexToValidatorIndex`
round-trip on every `vi` that already carries the `BUILDER_INDEX_FLAG` bit.
`toBuilderIndex` clears that bit; `convertBuilderIndexToValidatorIndex`
unconditionally sets it, so the hypothesis is what makes setting it a no-op. -/
theorem convertBuilderIndexToValidatorIndex_toBuilderIndex :
    ∀ (vi : ValidatorIndex), isBuilderIndex vi = true →
      convertBuilderIndexToValidatorIndex (toBuilderIndex vi) = vi := by
  intro vi h
  unfold isBuilderIndex at h
  unfold toBuilderIndex convertBuilderIndexToValidatorIndex
  simp only [bne_iff_ne, ne_eq] at h
  bv_decide

/-- The tagging fact for `convertBuilderIndexToValidatorIndex`. Setting the
flag with `|||` makes the result satisfy `isBuilderIndex`, regardless of the
input.

`bne_iff_ne` performs the same `!=`-to-`UInt64`-equation rewrite as the round
trip's proof, here for `... = true` instead of `... = false`. -/
theorem isBuilderIndex_convertBuilderIndexToValidatorIndex :
    ∀ (bi : BuilderIndex), isBuilderIndex (convertBuilderIndexToValidatorIndex bi) = true := by
  intro bi
  unfold isBuilderIndex convertBuilderIndexToValidatorIndex
  simp only [bne_iff_ne, ne_eq]
  bv_decide

end EthCLSpecs.Proofs
