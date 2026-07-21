import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.SSZListPush`: `SSZList.push`'s fold-clamp behavior

`SizzLean.Repr.SSZList.push` appends a single element, silently clamping (a
no-op) once the list is at capacity (`Repr/Instances.lean`). This file
characterizes what folding a list of values through it, one push at a time,
produces: the original array plus however much of the values list fits under
the capacity, in order, unconditionally. Under an explicit capacity
hypothesis, the clamp never engages and every value is appended.

Generic over the element type and capacity; not tied to any particular SSZ
container or consensus spec.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- Folding `SSZList.push` over a list of values lands on the original array
plus however much of the values list fits under `cap`: once the list is at
capacity, `SSZList.push`'s own `if` makes every further push a no-op, so only
the first `cap - xs.val.size` values appear in the result, in order. No
additional capacity hypothesis is required. -/
theorem sszListFoldlPush_val {α : Type} {cap : Nat} (xs : SSZList α cap) (vs : List α) :
    (vs.foldl (fun l w => l.push w) xs).val =
      xs.val ++ (vs.take (cap - xs.val.size)).toArray := by
  induction vs generalizing xs with
  | nil => simp
  | cons v rest ih =>
    rw [List.foldl_cons, ih]
    by_cases h : xs.val.size < cap
    · have hpush : (xs.push v).val = xs.val.push v := by
        unfold SSZList.push
        rw [dif_pos h]
      rw [hpush, Array.size_push]
      have htake : cap - xs.val.size = cap - (xs.val.size + 1) + 1 := by omega
      rw [htake, List.take_succ_cons, List.toArray_cons, Array.push_eq_append,
        Array.append_assoc]
    · have hpush : (xs.push v).val = xs.val := by
        unfold SSZList.push
        rw [dif_neg h]
      have hcap : cap - xs.val.size = 0 := by omega
      rw [hpush, hcap]
      simp

/-- Under an explicit capacity hypothesis, `sszListFoldlPush_val`'s clamp never
engages: every value in `vs` is appended, in order. -/
theorem sszListFoldlPush_val_of_fits {α : Type} {cap : Nat} (xs : SSZList α cap)
    (vs : List α) (hfits : xs.val.size + vs.length ≤ cap) :
    (vs.foldl (fun l w => l.push w) xs).val = xs.val ++ vs.toArray := by
  rw [sszListFoldlPush_val, List.take_of_length_le (by omega)]

end SizzLean.Proofs
