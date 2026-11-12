import SizzLean.Proofs.ProgressiveListSet
import EthCLLib.Spec.State

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Lists`: reads and writes on a progressive list

Gloas keeps its registry and queues in `ProgressiveList`s. The Fulu success proofs read and write
`SSZList`s through a handful of lemmas (`Proofs/Fulu/EpochSuccess/Balances.lean`,
`.FieldSteps`, `.Rewards`); these are the same lemmas for a progressive list, under a `plist_`
prefix.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open SizzLean.Repr (ProgressiveList)

/-- A `set!` writes the underlying array in place, within bounds. -/
theorem plist_set!_val {α : Type} (xs : ProgressiveList α) (i : Nat) (v : α) :
    (xs.set! i v).val = xs.val.setIfInBounds i v := by
  unfold ProgressiveList.set!
  simp

/-- An in-range total read is the checked read. -/
theorem plist_getElem!_eq {α : Type} [Inhabited α] (xs : ProgressiveList α) {i : Nat}
    (h : i < xs.val.size) : xs[i]! = xs.val[i] := by
  rw [getElem!_pos (dom := fun (xs : ProgressiveList α) i => i < xs.size) (h := h)]
  rfl

/-- In range, the spec's checked read returns the total read's element. -/
theorem plist_get?_eq {α : Type} [Inhabited α] (xs : ProgressiveList α) (i : Nat)
    (h : i < xs.size) : EthCLLib.Spec.IdxRead.get? xs i = some xs[i]! := by
  rw [plist_getElem!_eq xs h]
  exact Array.getElem?_eq_getElem h

/-- An in-range element is a member. -/
theorem plist_getElem!_mem {α : Type} [Inhabited α] (xs : ProgressiveList α) {i : Nat}
    (h : i < xs.size) : xs[i]! ∈ xs.val := by
  rw [plist_getElem!_eq xs h]
  exact Array.getElem_mem _

/-- A bound on every element survives a `set!` of a value under the bound. -/
theorem plist_set!_bound {xs : ProgressiveList UInt64} {j : Nat} {y : UInt64} {c : Nat}
    (hxs : ∀ x ∈ xs.val, x.toNat ≤ c) (hy : y.toNat ≤ c) :
    ∀ x ∈ (xs.set! j y).val, x.toNat ≤ c := by
  intro x hx
  rw [plist_set!_val] at hx
  rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
  · exact hxs x hx
  · exact hy

/-- A `set!` at `i` leaves every other in-range entry alone. -/
theorem plist_set!_getElem!_of_ne {α : Type} [Inhabited α] (xs : ProgressiveList α) {i j : Nat}
    (y : α) (hj : j < xs.val.size) (hne : i ≠ j) : (xs.set! i y)[j]! = xs[j]! := by
  rw [plist_getElem!_eq _ (by rw [plist_set!_val]; simpa using hj), plist_getElem!_eq _ hj]
  simp only [plist_set!_val]
  rw [Array.getElem_setIfInBounds hj, ite_eq_right hne]

/-- A `set!` keeps the length. -/
theorem plist_set!_size {α : Type} (xs : ProgressiveList α) (i : Nat) (v : α) :
    (xs.set! i v).val.size = xs.val.size := by
  rw [plist_set!_val, Array.size_setIfInBounds]

end EthCLSpecs.Proofs.Gloas
