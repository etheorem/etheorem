import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.PendingBalanceForBuilder`: the pending-balance sums

`get_pending_balance_to_withdraw_for_builder` (`gloas/beacon-chain.md:1168-1178`) accumulates
one `balance` with `+=` over `uint64` amounts, first over the pending withdrawals and then over
the pending payments. The SSZ backend raises a `ValueError` when the running balance passes
`2 ^ 64 - 1`, so the pyspec faults exactly when the natural-number total reaches `2 ^ 64`.
`getPendingBalanceToWithdrawForBuilder` folds one accumulator through `checkedAdd`, over the
withdrawals and then over the payments.

The two theorems here state the result against the natural-number total: the exact sum below
`2 ^ 64`, and the `.arithmetic` reject at or above it. A pair of private lemmas carries the
induction over a checked, filtered fold from any start value, once for either list.

The theorems bind plain `BeaconState` values and call the function on `pureState state`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError checkedAdd throwArithmetic liftErr)
open EthCLSpecs.Gloas (BuilderIndex Gwei Preset getPendingBalanceToWithdrawForBuilder)
open EthCLLib.Proofs (pureState except_bind_ok)
open SizzLean.Proofs (view_uncachedBox)

/-- The natural-number sum of `g` over the elements of `l` that `p` selects. -/
abbrev filteredSum {α : Type} (p : α → Bool) (g : α → UInt64) (l : List α) : Nat :=
  ((l.filter p).map (fun x => (g x).toNat)).sum

/-- **The checked fold, below the bound.** A fold that adds `g x` through `checkedAdd` for each
selected `x` succeeds, with the exact sum, while that sum stays below `2 ^ 64`. -/
private theorem foldlM_checked_ok {α : Type} (p : α → Bool) (g : α → UInt64) (d : String) :
    ∀ (l : List α) (acc : UInt64), acc.toNat + filteredSum p g l < 2 ^ 64 →
      ∃ r : UInt64,
        (l.foldlM (fun acc x => if p x then checkedAdd acc (g x) d else pure acc) acc
            : Except StateTransitionError UInt64) = .ok r ∧
          r.toNat = acc.toNat + filteredSum p g l := by
  intro l
  induction l with
  | nil =>
    intro acc _
    exact ⟨acc, rfl, by simp [filteredSum]⟩
  | cons x xs ih =>
    intro acc h
    by_cases hp : p x = true
    · have hsum : filteredSum p g (x :: xs) = (g x).toNat + filteredSum p g xs := by
        simp [filteredSum, hp]
      rw [hsum] at h ⊢
      have hstep : (acc + g x).toNat = acc.toNat + (g x).toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hc : ¬ acc + g x < acc := by
        rw [UInt64.lt_iff_toNat_lt, hstep]
        omega
      obtain ⟨r, hr, hrn⟩ := ih (acc + g x) (by rw [hstep]; omega)
      refine ⟨r, ?_, by rw [hrn, hstep]; omega⟩
      simp only [List.foldlM_cons, hp, ite_true, checkedAdd, hc, ite_false, pure_bind]
      exact hr
    · have hsum : filteredSum p g (x :: xs) = filteredSum p g xs := by
        simp [filteredSum, hp]
      rw [hsum] at h ⊢
      simp only [List.foldlM_cons, hp, Bool.false_eq_true, ite_false, pure_bind]
      exact ih acc h

/-- **The checked fold, at the bound.** Once the sum reaches `2 ^ 64`, the fold rejects with the
`.arithmetic` fault the step's descriptor names. -/
private theorem foldlM_checked_error {α : Type} (p : α → Bool) (g : α → UInt64) (d : String) :
    ∀ (l : List α) (acc : UInt64), 2 ^ 64 ≤ acc.toNat + filteredSum p g l →
      (l.foldlM (fun acc x => if p x then checkedAdd acc (g x) d else pure acc) acc
          : Except StateTransitionError UInt64)
        = .error (.arithmetic d) := by
  intro l
  induction l with
  | nil =>
    intro acc h
    have := UInt64.toNat_lt acc
    simp [filteredSum] at h
    omega
  | cons x xs ih =>
    intro acc h
    by_cases hp : p x = true
    · have hsum : filteredSum p g (x :: xs) = (g x).toNat + filteredSum p g xs := by
        simp [filteredSum, hp]
      rw [hsum] at h
      have hg := UInt64.toNat_lt (g x)
      by_cases hwrap : 2 ^ 64 ≤ acc.toNat + (g x).toNat
      · have hc : acc + g x < acc := by
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
          omega
        simp only [List.foldlM_cons, hp, ite_true, checkedAdd, hc]
        rfl
      · have hstep : (acc + g x).toNat = acc.toNat + (g x).toNat := by
          rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
        have hc : ¬ acc + g x < acc := by
          rw [UInt64.lt_iff_toNat_lt, hstep]
          omega
        simp only [List.foldlM_cons, hp, ite_true, checkedAdd, hc, ite_false, pure_bind]
        exact ih (acc + g x) (by rw [hstep]; omega)
    · have hsum : filteredSum p g (x :: xs) = filteredSum p g xs := by
        simp [filteredSum, hp]
      rw [hsum] at h
      simp only [List.foldlM_cons, hp, Bool.false_eq_true, ite_false, pure_bind]
      exact ih acc h

variable [Preset]

/-- The natural-number sum of the pending withdrawals for `builderIndex`. -/
abbrev pendingWithdrawalsSum (state : Gloas.BeaconState) (builderIndex : BuilderIndex) : Nat :=
  filteredSum (fun w => w.builderIndex == builderIndex) (fun w => w.amount)
    state.builderPendingWithdrawals.val.toList

/-- The natural-number sum of the queued payments for `builderIndex`. -/
abbrev pendingPaymentsSum (state : Gloas.BeaconState) (builderIndex : BuilderIndex) : Nat :=
  filteredSum (fun p => p.withdrawal.builderIndex == builderIndex) (fun p => p.withdrawal.amount)
    state.builderPendingPayments.toArray.toList

/-- The descriptor of the withdrawals step. -/
private abbrev withdrawalStep : String :=
  "get_pending_balance_to_withdraw_for_builder: balance += withdrawal.amount"

/-- The descriptor of the payments step. -/
private abbrev paymentStep : String :=
  "get_pending_balance_to_withdraw_for_builder: balance += payment.withdrawal.amount"

/-- The withdrawals fold from `0`, read against its `Nat` sum. -/
private theorem withdrawalsFold_ok (state : Gloas.BeaconState) (builderIndex : BuilderIndex)
    (h : pendingWithdrawalsSum state builderIndex < 2 ^ 64) :
    ∃ r : UInt64,
      (state.builderPendingWithdrawals.val.foldlM
          (fun acc w => if w.builderIndex == builderIndex then
              checkedAdd acc w.amount withdrawalStep
            else pure acc) 0 : Except StateTransitionError UInt64) = .ok r ∧
        r.toNat = pendingWithdrawalsSum state builderIndex := by
  obtain ⟨r, hr, hrn⟩ := foldlM_checked_ok (fun w => w.builderIndex == builderIndex)
    (fun w => w.amount) withdrawalStep state.builderPendingWithdrawals.val.toList 0
    (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact h)
  refine ⟨r, ?_, by rw [hrn, UInt64.toNat_zero, Nat.zero_add]⟩
  rw [← Array.foldlM_toList]
  exact hr

/-- **Below the bound.** When the two natural-number sums add to less than `2 ^ 64`, the function
succeeds, and its result is their exact total. -/
@[characterizes EthCLSpecs.Gloas.getPendingBalanceToWithdrawForBuilder]
theorem getPendingBalanceToWithdrawForBuilder_ok [HasherTag] :
    ∀ (state : Gloas.BeaconState) (builderIndex : BuilderIndex),
      pendingWithdrawalsSum state builderIndex + pendingPaymentsSum state builderIndex < 2 ^ 64 →
      ∃ r : Gwei,
        (getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex
            : Except StateTransitionError Gwei) = .ok r ∧
          r.toNat = pendingWithdrawalsSum state builderIndex
            + pendingPaymentsSum state builderIndex := by
  intro state builderIndex h
  obtain ⟨w, hw, hwn⟩ := withdrawalsFold_ok state builderIndex (by omega)
  -- The payments fold continues from the withdrawals result.
  obtain ⟨r, hr, hrn⟩ := foldlM_checked_ok (fun p => p.withdrawal.builderIndex == builderIndex)
    (fun p => p.withdrawal.amount) paymentStep state.builderPendingPayments.toArray.toList w
    (by rw [hwn]; exact h)
  refine ⟨r, ?_, by rw [hrn, hwn]⟩
  unfold getPendingBalanceToWithdrawForBuilder
  simp only [view_uncachedBox]
  rw [hw, except_bind_ok, ← Array.foldlM_toList]
  exact hr

/-- **At or above the bound.** When the two natural-number sums add to `2 ^ 64` or more, the
function rejects with `.arithmetic`. The pyspec raises `ValueError` at the first `+=` that passes
the bound, in the withdrawals loop or in the payments loop. -/
theorem getPendingBalanceToWithdrawForBuilder_overflow [HasherTag] :
    ∀ (state : Gloas.BeaconState) (builderIndex : BuilderIndex),
      2 ^ 64 ≤ pendingWithdrawalsSum state builderIndex + pendingPaymentsSum state builderIndex →
      ∃ d : String,
        (getPendingBalanceToWithdrawForBuilder (pureState state) builderIndex
            : Except StateTransitionError Gwei) = .error (.arithmetic d) := by
  intro state builderIndex h
  by_cases hW : 2 ^ 64 ≤ pendingWithdrawalsSum state builderIndex
  · have hw := foldlM_checked_error (fun w => w.builderIndex == builderIndex)
      (fun w => w.amount) withdrawalStep state.builderPendingWithdrawals.val.toList 0
      (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hW)
    -- `simp only` beta-reduces the instantiated fold function, so it matches the body's.
    simp only [Array.foldlM_toList] at hw
    refine ⟨withdrawalStep, ?_⟩
    unfold getPendingBalanceToWithdrawForBuilder
    simp only [view_uncachedBox]
    rw [hw]
    rfl
  · -- The withdrawals fit, so the running balance passes the bound in the payments loop.
    obtain ⟨w, hw, hwn⟩ := withdrawalsFold_ok state builderIndex (by omega)
    have hp := foldlM_checked_error (fun p => p.withdrawal.builderIndex == builderIndex)
      (fun p => p.withdrawal.amount) paymentStep state.builderPendingPayments.toArray.toList w
      (by rw [hwn]; exact h)
    simp only [Array.foldlM_toList] at hp
    refine ⟨paymentStep, ?_⟩
    unfold getPendingBalanceToWithdrawForBuilder
    simp only [view_uncachedBox]
    rw [hw, except_bind_ok, hp]

end EthCLSpecs.Proofs.Gloas
