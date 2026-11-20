import EthCLSpecs.Gloas.Operations
import EthCLLib.Proofs.CLUint
import Std.Tactic.BVDecide

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderIndex`: the builder-index flag round-trip

`EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex` sets the
`BUILDER_INDEX_FLAG` bit and `EthCLSpecs.Gloas.toBuilderIndex` clears it, both
single bitwise operations against the same single-bit mask
`EthCLSpecs.Gloas.Const.builderIndexFlag`. The pinned forms follow the pyspec's
integer kinds: `builder_index | BUILDER_INDEX_FLAG` is the total same-width `|`
of two checked values, and `validator_index & ~BUILDER_INDEX_FLAG` is the mixed
`&` with the plain `int` `~BUILDER_INDEX_FLAG`, so `toBuilderIndex` returns a
`Checked` value. `toBuilderIndex_ok` proves that it never faults, through the
framework law `hand_invert_eq`. The round-trip properties are conditional: each
needs the relevant flag state before clearing or setting the bit, stated through
`isBuilderIndex`, the spec's own named predicate for the bit test.

Each proof reduces the checked values to their native words (`CLUint64.val_inj`)
and closes with `bv_decide`, no mathlib needed.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Round-trip and conversion
properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (CLUint64 Checked)
open EthCLSpecs.Gloas (BuilderIndex ValidatorIndex)
open EthCLSpecs.Gloas (isBuilderIndex toBuilderIndex convertBuilderIndexToValidatorIndex)

/-- The flag's native word, the literal `2^40`. -/
private theorem builderIndexFlag_val :
    EthCLSpecs.Gloas.Const.builderIndexFlag.val = 0x10000000000 := rfl

/-- `isBuilderIndex` read on the native word: the flag bit is set. The `!=` is a
`bne` on the checked value, and the same-width `&` projects to the native `&`. -/
private theorem isBuilderIndex_iff (vi : ValidatorIndex) :
    isBuilderIndex vi = true ↔ vi.val &&& 0x10000000000 ≠ 0 := by
  unfold isBuilderIndex
  rw [bne_iff_ne, ne_eq, ne_eq, ← builderIndexFlag_val]
  constructor
  · intro h hv
    exact h (CLUint64.val_inj hv)
  · intro h hv
    exact h (congrArg CLUint64.val hv)

/-- `convert_validator_index_to_builder_index` never faults: the mixed `&` with the
complement stays inside `[0, validator_index]`, so the result is the same-width
`&` with the 64-bit complement of the flag (`hand_invert_eq`). -/
theorem toBuilderIndex_ok (vi : ValidatorIndex) :
    toBuilderIndex vi =
      .ok (vi &&& CLUint64.trustedOfUInt64 (~~~ EthCLSpecs.Gloas.Const.builderIndexFlag.val)) :=
  EthCLLib.Proofs.hand_invert_eq _ _

/-- `convertBuilderIndexToValidatorIndex` and `toBuilderIndex` round-trip on
every `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit.
`convertBuilderIndexToValidatorIndex` sets that bit; `toBuilderIndex`
unconditionally clears it, so the hypothesis is what makes clearing it a
no-op. The clearing succeeds (`toBuilderIndex_ok`), with the original index. -/
@[characterizes EthCLSpecs.Gloas.toBuilderIndex]
theorem toBuilderIndex_convertBuilderIndexToValidatorIndex :
    ∀ (bi : BuilderIndex), isBuilderIndex bi = false →
      toBuilderIndex (convertBuilderIndexToValidatorIndex bi) = .ok bi := by
  intro bi h
  have hw : bi.val &&& 0x10000000000 = 0 := by
    have hn : ¬ (isBuilderIndex bi = true) := by rw [h]; decide
    rw [isBuilderIndex_iff] at hn
    exact Classical.byContradiction hn
  rw [toBuilderIndex_ok]
  refine congrArg Except.ok (CLUint64.val_inj ?_)
  show (bi.val ||| EthCLSpecs.Gloas.Const.builderIndexFlag.val) &&&
      ~~~ EthCLSpecs.Gloas.Const.builderIndexFlag.val = bi.val
  rw [builderIndexFlag_val]
  bv_decide

/-- The mirror direction: `toBuilderIndex` and `convertBuilderIndexToValidatorIndex`
round-trip on every `vi` that already carries the `BUILDER_INDEX_FLAG` bit.
`toBuilderIndex` clears that bit and succeeds; `convertBuilderIndexToValidatorIndex`
unconditionally sets it, so the hypothesis is what makes setting it a no-op. -/
@[characterizes EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex]
theorem convertBuilderIndexToValidatorIndex_toBuilderIndex :
    ∀ (vi : ValidatorIndex), isBuilderIndex vi = true →
      (convertBuilderIndexToValidatorIndex <$> toBuilderIndex vi : Checked ValidatorIndex)
        = .ok vi := by
  intro vi h
  rw [isBuilderIndex_iff] at h
  rw [toBuilderIndex_ok]
  refine congrArg Except.ok (CLUint64.val_inj ?_)
  show (vi.val &&& ~~~ EthCLSpecs.Gloas.Const.builderIndexFlag.val) |||
      EthCLSpecs.Gloas.Const.builderIndexFlag.val = vi.val
  rw [builderIndexFlag_val]
  bv_decide

/-- The tagging fact for `convertBuilderIndexToValidatorIndex`. Setting the
flag with `|||` makes the result satisfy `isBuilderIndex`, regardless of the
input. -/
@[characterizes EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex]
theorem isBuilderIndex_convertBuilderIndexToValidatorIndex :
    ∀ (bi : BuilderIndex), isBuilderIndex (convertBuilderIndexToValidatorIndex bi) = true := by
  intro bi
  rw [isBuilderIndex_iff]
  show (bi.val ||| EthCLSpecs.Gloas.Const.builderIndexFlag.val) &&& 0x10000000000 ≠ 0
  rw [builderIndexFlag_val]
  bv_decide

end EthCLSpecs.Proofs.Gloas
