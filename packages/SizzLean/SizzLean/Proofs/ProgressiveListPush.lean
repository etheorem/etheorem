import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.ProgressiveListPush`: `ProgressiveList.push`'s fold behavior

`ProgressiveList.push` always appends (`Repr/Instances.lean`). Folding a list
of values through it lands on the original array plus every value, in order.
There is no capacity clamp: the per-payload caps moved to processing asserts
when the lists became progressive.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- `ProgressiveList.push` appends the value to the array. -/
theorem progressiveListPush_val {α : Type} (xs : ProgressiveList α) (v : α) :
    (xs.push v).val = xs.val.push v := rfl

/-- Folding `ProgressiveList.push` over a list of values appends every value,
in order. -/
theorem progressiveListFoldlPush_val {α : Type} (xs : ProgressiveList α) (vs : List α) :
    (vs.foldl (fun l w => l.push w) xs).val = xs.val ++ vs.toArray := by
  induction vs generalizing xs with
  | nil => simp
  | cons v rest ih =>
    rw [List.foldl_cons, ih]
    unfold ProgressiveList.push
    rw [Array.push_eq_append, Array.append_assoc, ← List.toArray_cons]

end SizzLean.Proofs
