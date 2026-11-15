import EthCLSpecs.Gloas.Operations
import Std.Tactic.BVDecide

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderIndex`: the builder-index flag round-trip

`EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex` sets the
`BUILDER_INDEX_FLAG` bit and `EthCLSpecs.Gloas.toBuilderIndex` clears it, both
single bitwise operations on the raw `UInt64` value against the same single-bit
mask `EthCLSpecs.Gloas.Const.builderIndexFlag`. The checked `ValidatorIndex`
wrapper around `convertBuilderIndexToValidatorIndex`'s output is the trusted
route, so the round trip runs on the raw bits. The round-trip properties are
conditional: each needs the relevant flag state before clearing or setting
the bit; see the individual theorems for the exact statement. The mirror
theorem states its hypothesis through `isBuilderIndex`, the spec's own named
predicate for the bit test, which takes the checked `ValidatorIndex`; the
forward theorem's hypothesis is about a raw `BuilderIndex`, so it spells the
raw mask equation.

All three proofs unfold to the raw `UInt64` bitwise expression and close with
`bv_decide`, no mathlib needed. The wrapper equation in the second theorem
reduces through `CLUint64.val_inj`, the public injectivity of the checked
kind's native value (`EthCLLib/Spec/CLUint.lean`), and the `trustedOfUInt64`
equations fold away in every `simp only` that precedes the prover.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Round-trip and conversion
properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (CLUint64)
open EthCLSpecs.Gloas (BuilderIndex ValidatorIndex)
open EthCLSpecs.Gloas (isBuilderIndex toBuilderIndex convertBuilderIndexToValidatorIndex)

/-- `convertBuilderIndexToValidatorIndex` and `toBuilderIndex` round-trip on
every `bi` whose raw `BuilderIndex` value carries a clear `BUILDER_INDEX_FLAG`
bit. `convertBuilderIndexToValidatorIndex` sets that bit; `toBuilderIndex`
unconditionally clears it, so the hypothesis is what makes clearing it a
no-op. The hypothesis spells the raw mask equation: `BuilderIndex` is a raw
`UInt64`, and the spec's `is_builder_index` predicate takes the checked
`ValidatorIndex` the conversion produces, whose flag bit the conversion just
set. -/
@[characterizes EthCLSpecs.Gloas.toBuilderIndex]
theorem toBuilderIndex_convertBuilderIndexToValidatorIndex :
    ∀ (bi : BuilderIndex), (bi &&& EthCLSpecs.Gloas.Const.builderIndexFlag) = 0 →
      toBuilderIndex (convertBuilderIndexToValidatorIndex bi) = bi := by
  intro bi h
  unfold toBuilderIndex convertBuilderIndexToValidatorIndex
  simp only [CLUint64.trustedOfUInt64]
  bv_decide

/-- The mirror direction: `toBuilderIndex` and `convertBuilderIndexToValidatorIndex`
round-trip on every `vi` that already carries the `BUILDER_INDEX_FLAG` bit.
`toBuilderIndex` clears that bit; `convertBuilderIndexToValidatorIndex`
unconditionally sets it, so the hypothesis is what makes setting it a no-op. -/
@[characterizes EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex]
theorem convertBuilderIndexToValidatorIndex_toBuilderIndex :
    ∀ (vi : ValidatorIndex), isBuilderIndex vi = true →
      convertBuilderIndexToValidatorIndex (toBuilderIndex vi) = vi := by
  intro vi h
  unfold isBuilderIndex at h
  unfold toBuilderIndex convertBuilderIndexToValidatorIndex
  simp only [bne_iff_ne, ne_eq] at h
  apply CLUint64.val_inj
  simp only [CLUint64.trustedOfUInt64]
  bv_decide

/-- The tagging fact for `convertBuilderIndexToValidatorIndex`. Setting the
flag with `|||` makes the result satisfy `isBuilderIndex`, regardless of the
input.

`bne_iff_ne` performs the same `!=`-to-`UInt64`-equation rewrite as the round
trip's proof, here for `... = true` instead of `... = false`. -/
@[characterizes EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex]
theorem isBuilderIndex_convertBuilderIndexToValidatorIndex :
    ∀ (bi : BuilderIndex), isBuilderIndex (convertBuilderIndexToValidatorIndex bi) = true := by
  intro bi
  unfold isBuilderIndex convertBuilderIndexToValidatorIndex
  simp only [CLUint64.trustedOfUInt64, bne_iff_ne, ne_eq]
  bv_decide

end EthCLSpecs.Proofs.Gloas
