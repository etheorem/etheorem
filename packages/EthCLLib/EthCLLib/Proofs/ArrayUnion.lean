import EthCLLib.Spec.Arith

/-!
# `EthCLLib.Proofs.ArrayUnion`: membership in `arrayUnion`

`arrayUnion xs ys` (`EthCLLib/Spec/Arith.lean`) appends each element of `ys` that the
running result does not contain. With a lawful `==`, an element is in the result exactly
when it is in `xs` or in `ys`. `collectInclusionListTransactions` removes duplicate
transactions with `arrayUnion #[]`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (arrayUnion)

/-- The `arrayUnion` loop over a list: an element is in the result exactly when it is in
the start array or in the list. -/
private theorem mem_foldl_union {α : Type} [BEq α] [LawfulBEq α] (x : α) :
    ∀ (l : List α) (xs : Array α),
      x ∈ l.foldl (fun acc i => if acc.contains i then acc else acc.push i) xs ↔
        x ∈ xs ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro xs; simp
  | cons y l ih =>
    intro xs
    rw [List.foldl_cons, ih]
    by_cases hy : xs.contains y
    · have hmem : y ∈ xs := by simpa using hy
      simp only [hy, if_true, List.mem_cons]
      constructor
      · rintro (h | h) <;> simp [*]
      · rintro (h | rfl | h) <;> simp [*]
    · simp only [hy, Bool.false_eq_true, if_false, Array.mem_push, List.mem_cons]
      constructor
      · rintro ((h | rfl) | h) <;> simp [*]
      · rintro (h | rfl | h) <;> simp [*]

/-- An element is in `arrayUnion xs ys` exactly when it is in `xs` or in `ys`. -/
theorem mem_arrayUnion {α : Type} [BEq α] [LawfulBEq α] (xs ys : Array α) (x : α) :
    x ∈ arrayUnion xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  unfold arrayUnion
  rw [← Array.foldl_toList, mem_foldl_union, Array.mem_toList_iff]

end EthCLLib.Proofs
