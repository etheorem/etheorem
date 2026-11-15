import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Tests.AddOkIff`: when `+` on `CLUint64` succeeds

The success lemma the proof port needs (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §7, open work item 2):
`+` on the checked type succeeds exactly when the plain-`int` sum fits in `[0, 2^64)`.
The statement runs over plain values, and `toPlainInt` unfolds to `val.toNat`, so the
proof is `omega` over the native widths.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.AddOkIff

/-- `a + b` goes through the named `add`: the bridge the proof unfolds. -/
theorem add_eq (a b : CLUint64) : (a + b : Checked CLUint64) = CLUint64.add a b := rfl

/-- `+` succeeds exactly when the plain-`int` sum fits in `[0, 2^64)`. -/
theorem add_ok_iff (a b : CLUint64) :
    (∃ c, (a + b : Checked CLUint64) = .ok c) ↔ a.toPlainInt + b.toPlainInt < 2 ^ 64 := by
  rw [add_eq]; unfold CLUint64.add CLUint64.toPlainInt
  have ha := a.val.toNat_lt; have hb := b.val.toNat_lt
  constructor
  · intro ⟨c, h⟩
    split at h
    · cases h
    · rename_i hlt
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hlt
      omega
  · intro h
    refine ⟨⟨a.val + b.val⟩, ?_⟩
    split
    · rename_i hlt
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hlt
      omega
    · rfl

end EthCLLib.Tests.AddOkIff
