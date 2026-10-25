import EthCLLib.Spec.Errors
import EthCLLib.Proofs.Lemmas

/-!
# `EthCLLib.Proofs.CheckedOps`: checked `uint64` operations that do not overflow

`checkedMul` and `checkedAdd` (`EthCLLib/Spec/Errors.lean`) mirror the checked `uint64`
arithmetic of the pyspec. They raise `.arithmetic` when the result does not fit. The two
lemmas here state the other outcome in `Except`: when the operands and the result fit in
`uint64`, the operation returns the `Nat` result.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (StateTransitionError checkedMul checkedAdd)

/-- `checkedMul` of two `uint64` values whose product fits returns the product. -/
theorem checkedMul_ok {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a * b < 2 ^ 64)
    (descr : String) :
    (checkedMul (m := Except StateTransitionError) (UInt64.ofNat a) (UInt64.ofNat b) descr)
      = .ok (UInt64.ofNat (a * b)) := by
  have hprod : UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul, toNat_ofNat_lt64 ha, toNat_ofNat_lt64 hb, toNat_ofNat_lt64 hab,
      Nat.mod_eq_of_lt hab]
  -- The overflow test `a != 0 && a * b / a != b` is false: either `a = 0`, or the
  -- product divides back to `b`.
  have htest : (UInt64.ofNat a != 0 && UInt64.ofNat a * UInt64.ofNat b / UInt64.ofNat a
      != UInt64.ofNat b) = false := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    · have hdiv : UInt64.ofNat a * UInt64.ofNat b / UInt64.ofNat a = UInt64.ofNat b := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_div, hprod, toNat_ofNat_lt64 hab, toNat_ofNat_lt64 ha,
          toNat_ofNat_lt64 hb, Nat.mul_div_cancel_left _ hpos]
      simp [hdiv]
  unfold checkedMul
  rw [htest, hprod]
  rfl

/-- `checkedAdd` of two `uint64` values whose sum fits returns the sum. -/
theorem checkedAdd_ok {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a + b < 2 ^ 64)
    (descr : String) :
    (checkedAdd (m := Except StateTransitionError) (UInt64.ofNat a) (UInt64.ofNat b) descr)
      = .ok (UInt64.ofNat (a + b)) := by
  have hsum : UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, toNat_ofNat_lt64 ha, toNat_ofNat_lt64 hb, toNat_ofNat_lt64 hab,
      Nat.mod_eq_of_lt hab]
  -- The carry test `a + b < a` is false: the sum fits, so it is at least `a`.
  have htest : ¬ (UInt64.ofNat a + UInt64.ofNat b < UInt64.ofNat a) := by
    rw [hsum, UInt64.lt_iff_toNat_lt, toNat_ofNat_lt64 hab, toNat_ofNat_lt64 ha]
    omega
  unfold checkedAdd
  rw [if_neg htest, hsum]
  rfl

end EthCLLib.Proofs
