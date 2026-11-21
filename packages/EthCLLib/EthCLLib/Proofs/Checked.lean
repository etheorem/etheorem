import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Proofs.Checked`: when `checkedMul` raises

`checkedMul` (`EthCLLib/Spec/Errors.lean`) raises `.arithmetic` when the `uint64` product
overflows. Its guard compares a truncating `UInt64` division against the second operand.
`mulGuard_iff` reads that guard on `Nat`: it fires exactly when the `Nat` product reaches
`2 ^ 64`. `checkedMul_of_lt` and `checkedMul_of_ge` give the two outcomes in any monad the
checked operators run in, so a fork proof can rewrite a checked product to `pure` or to
`throwArithmetic` from a `Nat` bound.

The `_eq_ok` lemmas read a successful checked operation in `Except` back on `Nat`: the result
is the exact `Nat` sum, difference, or product.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (StateTransitionError ErrorConv checkedAdd checkedSub checkedMul
  throwArithmetic)

/-- `checkedMul`'s guard, read on `Nat`. With `a ≠ 0`, the guard fires exactly when the `Nat`
product reaches `2 ^ 64`. -/
theorem mulGuard_iff (a p : UInt64) (ha : a.toNat ≠ 0) :
    (a != 0 && a * p / a != p) = true ↔ 2 ^ 64 ≤ a.toNat * p.toNat := by
  have hapos : 0 < a.toNat := Nat.pos_of_ne_zero ha
  have hne : (a != 0) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro hz
    exact ha (by simp [hz])
  rw [hne, Bool.true_and]
  constructor
  · intro hg
    -- Below the bound the product is exact, so the division recovers `p`.
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have hrec : a * p / a = p := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
      exact Nat.mul_div_cancel_left _ hapos
    simp [hrec] at hg
  · intro hge
    -- At or above the bound the product wraps, and the wrapped value is below `a * p`, so the
    -- quotient falls below `p`.
    have hmod : (a.toNat * p.toNat) % 2 ^ 64 < a.toNat * p.toNat :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) hge
    have hq : (a * p / a).toNat < p.toNat := by
      rw [UInt64.toNat_div, UInt64.toNat_mul]
      exact (Nat.div_lt_iff_lt_mul hapos).mpr (Nat.lt_of_lt_of_eq hmod (Nat.mul_comm _ _))
    have : a * p / a ≠ p := fun heq => by rw [heq] at hq; exact Nat.lt_irrefl _ hq
    simpa using this

/-- A `checkedMul` whose `Nat` product stays below `2 ^ 64` returns the product, in any monad
the checked operators run in. -/
theorem checkedMul_of_lt {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a p : UInt64) (d : String)
    (h : a.toNat * p.toNat < 2 ^ 64) : (checkedMul a p d : m UInt64) = pure (a * p) := by
  unfold checkedMul
  by_cases ha : a.toNat = 0
  · have ha0 : a = 0 := UInt64.toNat_inj.mp (by simpa using ha)
    simp [ha0]
  · rw [ite_eq_right (fun hg => absurd ((mulGuard_iff a p ha).mp hg) (Nat.not_le.mpr h))]

/-- A `checkedMul` whose `Nat` product reaches `2 ^ 64` raises `.arithmetic` with its
description, in any monad the checked operators run in. -/
theorem checkedMul_of_ge {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a p : UInt64) (d : String)
    (h : 2 ^ 64 ≤ a.toNat * p.toNat) :
    (checkedMul a p d : m UInt64) = throwArithmetic d := by
  unfold checkedMul
  have ha : a.toNat ≠ 0 := fun hz => by rw [hz, Nat.zero_mul] at h; exact absurd h (by decide)
  rw [ite_eq_left ((mulGuard_iff a p ha).mpr h)]

/-- A `checkedAdd` whose `Nat` sum stays below `2 ^ 64` returns the sum, in any monad the
checked operators run in. -/
theorem checkedAdd_of_lt {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a b : UInt64) (d : String)
    (h : a.toNat + b.toNat < 2 ^ 64) : (checkedAdd a b d : m UInt64) = pure (a + b) := by
  unfold checkedAdd
  refine ite_eq_right (fun hlt => ?_)
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt h] at hlt
  omega

/-- A `checkedSub` with `b ≤ a` returns the difference, in any monad the checked operators
run in. -/
theorem checkedSub_of_le {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a b : UInt64) (d : String)
    (h : b ≤ a) : (checkedSub a b d : m UInt64) = pure (a - b) := by
  unfold checkedSub
  exact ite_eq_right (UInt64.not_lt.mpr h)

/-- A successful `checkedAdd` returns the exact `Nat` sum. -/
theorem checkedAdd_eq_ok (a b r : UInt64) (d : String)
    (h : (checkedAdd a b d : Except StateTransitionError UInt64) = .ok r) :
    r.toNat = a.toNat + b.toNat := by
  unfold checkedAdd at h
  split at h
  · cases h
  · rename_i hno
    injection h with h
    subst h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hno
    rw [UInt64.toNat_add]
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    omega

/-- A successful `checkedSub` had `b ≤ a`, and returns the exact `Nat` difference. -/
theorem checkedSub_eq_ok (a b r : UInt64) (d : String)
    (h : (checkedSub a b d : Except StateTransitionError UInt64) = .ok r) :
    b ≤ a ∧ r.toNat = a.toNat - b.toNat := by
  unfold checkedSub at h
  split at h
  · cases h
  · rename_i hno
    injection h with h
    subst h
    have hle : b ≤ a := UInt64.not_lt.mp hno
    exact ⟨hle, UInt64.toNat_sub_of_le _ _ hle⟩

/-- A successful `checkedMul` returns the exact `Nat` product. -/
theorem checkedMul_eq_ok (a b r : UInt64) (d : String)
    (h : (checkedMul a b d : Except StateTransitionError UInt64) = .ok r) :
    r.toNat = a.toNat * b.toNat := by
  by_cases hlt : a.toNat * b.toNat < 2 ^ 64
  · rw [checkedMul_of_lt a b d hlt] at h
    injection h with h
    subst h
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
  · rw [checkedMul_of_ge a b d (Nat.le_of_not_lt hlt)] at h
    cases h

end EthCLLib.Proofs
