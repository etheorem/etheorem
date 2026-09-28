import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.SSZListPush`: the checked append

`SizzLean.Repr.SSZList.push` appends to a list that has room, and it takes the room proof
as an argument. `SSZList.push?` is the checked form: `some` of the longer list below the
capacity, `none` at it (`Repr/Instances.lean`). The `none` branch stands for the spec's
`List.append` raise.

This file states the two branches of `push?`, and what a fold of `push?` over a list of
values gives: the original array followed by every value when they all fit, and `none`
otherwise. `sszListFoldlMPush?_val` states the fold in the `Option` monad, with no state
machine around it.

The results hold for every element type and capacity. No SSZ container or consensus spec
appears.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- `push` appends `x` to the underlying array. -/
@[simp] theorem sszListPush_val {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α)
    (h : xs.val.size < cap) : (xs.push x h).val = xs.val.push x := rfl

/-- Below the capacity, `push?` is `some` of `push`. -/
theorem sszListPush?_of_lt {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α)
    (h : xs.val.size < cap) : xs.push? x = some (xs.push x h) := dif_pos h

/-- At the capacity, `push?` is `none`. -/
theorem sszListPush?_of_le {α : Type} {cap : Nat} (xs : SSZList α cap) (x : α)
    (h : cap ≤ xs.val.size) : xs.push? x = none := dif_neg (by omega)

/-- A fold of `push?` over `vs`, in the `Option` monad. When all of `vs` fits under `cap`,
the result is the original array followed by `vs`, in order. Otherwise the fold stops at
the first `none`, and the result is `none`. The statement compares arrays through
`Option.map (·.val)`, because the list carries its size proof. -/
theorem sszListFoldlMPush?_val {α : Type} {cap : Nat} (xs : SSZList α cap) (vs : List α) :
    (vs.foldlM (fun (l : SSZList α cap) w => l.push? w) xs).map (·.val) =
      if xs.val.size + vs.length ≤ cap then some (xs.val ++ vs.toArray) else none := by
  induction vs generalizing xs with
  | nil =>
    have := xs.property
    simp [this]
  | cons v rest ih =>
    rw [List.foldlM_cons]
    by_cases h : xs.val.size < cap
    · rw [sszListPush?_of_lt xs v h]
      -- `some a >>= f` reduces to `f a` in the `Option` monad.
      show (rest.foldlM (fun (l : SSZList α cap) w => l.push? w) (xs.push v h)).map (·.val) = _
      rw [ih, sszListPush_val, Array.size_push]
      have harr : xs.val.push v ++ rest.toArray = xs.val ++ (v :: rest).toArray := by simp
      rw [harr, List.length_cons]
      split <;> split <;> first | rfl | (exfalso; omega)
    · rw [sszListPush?_of_le xs v (by omega)]
      have hover : ¬ (xs.val.size + (v :: rest).length ≤ cap) := by
        rw [List.length_cons]; omega
      rw [if_neg hover]
      rfl

end SizzLean.Proofs
