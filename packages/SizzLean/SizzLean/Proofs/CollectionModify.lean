import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.CollectionModify`: `modify` as a `set!`

`SSZList.modify`, `ProgressiveList.modify` and `Vector.modify` (`Repr/Instances.lean`) each
wrap core `Array.modify`. `Array.modify` moves the element out before it calls `f`, so `f`
can update the element in place. That is the reason to call `modify` in place of
`set! i (f xs[i]!)`, which reads the element and keeps a second reference to it.

`Array.modify` goes through `Id.run` and `modifyM`, so it does not unfold to
`set! i (f xs[i]!)` by `rfl`. This file proves the two equal for each type, and proves that
`modify` keeps the size. A caller states its contract in the `set!` form and rewrites
through `*Modify_eq_set!`. The read-back lemmas of `SSZListSet.lean` and
`ProgressiveListSet.lean` then apply unchanged.

Generic over the element type and capacity; not tied to any SSZ container or consensus
spec.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- The `Array` fact under the three collection lemmas below: `modify` equals a write of
`f` applied to the total read. Out of range both sides return `xs` unchanged. The
`[Inhabited α]` binder exists only for the `xs[i]!` on the right; the left side needs
no default. -/
theorem arrayModify_eq_setIfInBounds {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) :
    xs.modify i f = xs.setIfInBounds i (f xs[i]!) := by
  apply Array.ext
  · simp
  · intro j h₁ _
    rw [Array.getElem_modify h₁, Array.getElem_setIfInBounds (by simpa using h₁)]
    by_cases hij : i = j
    · subst hij
      simp [getElem!_pos xs i (by simpa using h₁)]
    · simp [hij]

/-! ## `SSZList` -/

/-- `SSZList.modify` keeps the runtime length, in range or past the end. -/
theorem sszListModify_size {α : Type} {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (f : α → α) :
    (xs.modify i f).size = xs.size := by
  simp [SSZList.modify, SSZList.size]

/-- `SSZList.modify` is `set!` of `f` applied to the total read. -/
theorem sszListModify_eq_set! {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (f : α → α) :
    xs.modify i f = xs.set! i (f xs[i]!) := by
  apply Subtype.ext
  show xs.val.modify i f = xs.val.set! i (f xs[i]!)
  rw [Array.set!_eq_setIfInBounds, arrayModify_eq_setIfInBounds]
  by_cases h : i < xs.size
  · rw [getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size) (h := h),
      getElem!_pos xs.val i h]
    rfl
  · have h' : xs.val.size ≤ i := by simpa [SSZList.size] using h
    simp [Array.setIfInBounds_eq_of_size_le h']

/-! ## `ProgressiveList` -/

/-- `ProgressiveList.modify` keeps the runtime length, in range or past the end. -/
theorem progressiveListModify_size {α : Type}
    (xs : ProgressiveList α) (i : Nat) (f : α → α) :
    (xs.modify i f).size = xs.size := by
  simp [ProgressiveList.modify, ProgressiveList.size]

/-- `ProgressiveList.modify` is `set!` of `f` applied to the total read. -/
theorem progressiveListModify_eq_set! {α : Type} [Inhabited α]
    (xs : ProgressiveList α) (i : Nat) (f : α → α) :
    xs.modify i f = xs.set! i (f xs[i]!) := by
  show (⟨xs.val.modify i f⟩ : ProgressiveList α) = ⟨xs.val.setIfInBounds i (f xs[i]!)⟩
  rw [arrayModify_eq_setIfInBounds]
  by_cases h : i < xs.size
  · rw [getElem!_pos (dom := fun (xs : ProgressiveList α) i => i < xs.size) (h := h),
      getElem!_pos xs.val i h]
    rfl
  · have h' : xs.val.size ≤ i := by simpa [ProgressiveList.size] using h
    simp [Array.setIfInBounds_eq_of_size_le h']

/-! ## `Vector` -/

/-- `Vector.modify` keeps the length. The type already says so; this lemma states it for
the underlying array, which is what a caller that projects through `toArray` reads. -/
theorem vectorModify_size {α : Type} {n : Nat}
    (xs : Vector α n) (i : Nat) (f : α → α) :
    (xs.modify i f).toArray.size = xs.toArray.size := by
  simp

/-- `Vector.modify` is core `Vector.set!` of `f` applied to the total read. -/
theorem vectorModify_eq_set! {α : Type} [Inhabited α] {n : Nat}
    (xs : Vector α n) (i : Nat) (f : α → α) :
    xs.modify i f = xs.set! i (f xs[i]!) := by
  apply Vector.toArray_inj.mp
  show xs.toArray.modify i f = xs.toArray.set! i (f xs[i]!)
  rw [Array.set!_eq_setIfInBounds, arrayModify_eq_setIfInBounds]
  by_cases h : i < n
  · rw [getElem!_pos xs i h, getElem!_pos xs.toArray i (by simpa using h)]
    simp
  · have h' : xs.toArray.size ≤ i := by simpa using h
    simp [Array.setIfInBounds_eq_of_size_le h']

end SizzLean.Proofs
