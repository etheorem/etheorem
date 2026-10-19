import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.ProgressiveListSet`: `ProgressiveList.set!`'s read-back behavior

`ProgressiveList.set!` lowers to `Array.setIfInBounds` (`Repr/Instances.lean`):
in range it replaces one element, past the end it is a silent no-op. This file
says what the total reads `xs[i]!` and `xs.size` observe afterwards, which is
the pair the `sszUpdate` / `sszModify` macros emit for an `[i]!` path on a
progressive list.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- `ProgressiveList.set!` preserves the runtime length, in range or past the end. -/
theorem progressiveListSet!_size {α : Type}
    (xs : ProgressiveList α) (i : Nat) (v : α) :
    (xs.set! i v).size = xs.size := by
  simp [ProgressiveList.set!, ProgressiveList.size, Array.size_setIfInBounds]

/-- In range, the written index reads back exactly the written value. -/
theorem progressiveListSet!_getElem!_self {α : Type} [Inhabited α]
    (xs : ProgressiveList α) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set! i v)[i]! = v := by
  rw [getElem!_pos (dom := fun (xs : ProgressiveList α) i => i < xs.size)
    (h := by simpa [progressiveListSet!_size] using h)]
  show (xs.set! i v).val[i]'_ = v
  simp [ProgressiveList.set!]

/-- Every index other than the written one is untouched, whether or not that other
index `j` is itself in range. -/
theorem progressiveListSet!_getElem!_ne {α : Type} [Inhabited α]
    (xs : ProgressiveList α) (i j : Nat) (v : α) (hij : i ≠ j) :
    (xs.set! i v)[j]! = xs[j]! := by
  by_cases hj : j < xs.size
  · rw [getElem!_pos (dom := fun (xs : ProgressiveList α) i => i < xs.size)
          (h := by simpa [progressiveListSet!_size] using hj),
        getElem!_pos (dom := fun (xs : ProgressiveList α) i => i < xs.size) (h := hj)]
    show (xs.set! i v).val[j]'_ = xs.val[j]'_
    exact Array.getElem_setIfInBounds_ne hj hij
  · rw [getElem!_neg (dom := fun (xs : ProgressiveList α) i => i < xs.size)
          (h := by simpa [progressiveListSet!_size] using hj),
        getElem!_neg (dom := fun (xs : ProgressiveList α) i => i < xs.size) (h := hj)]

/-- Past the end, the write is a no-op on the whole list. -/
theorem progressiveListSet!_eq_of_size_le {α : Type}
    (xs : ProgressiveList α) (i : Nat) (v : α) (h : xs.size ≤ i) :
    xs.set! i v = xs := by
  cases xs
  simp [ProgressiveList.set!, Array.setIfInBounds_eq_of_size_le (by simpa [ProgressiveList.size] using h)]

end SizzLean.Proofs
