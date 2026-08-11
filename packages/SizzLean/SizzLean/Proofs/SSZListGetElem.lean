import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.SSZListGetElem`: total reads as checked reads

`SizzLean.Repr.SSZList`'s `GetElem` instance carries the faithful validity
predicate `fun xs i => i < xs.size` (`Repr/Instances.lean`), so the same list
supports three reads: `xs[i]!` yields the element type's `default` past the end,
`xs[i]?` yields `none`, and `xs[i]'h` demands an in-bounds proof. Spec code reaches
for `xs[i]!`, which keeps it total and free of proof obligations.

That choice follows the value into every theorem about such code. A statement
mentioning `xs[i]!` is silent about whether the read landed inside the list, even
when a neighbouring hypothesis already settles it, so a reader has to connect the
two by hand.

`sszListMap_getElem!_eq_attachMap` closes that gap for the common shape: mapping a
total read across an array of indices. Given that every index is in range, the
result equals the same map written with `Array.attach`, where each read carries its
own in-bounds proof. Callers state their theorems in the checked form and rewrite to
reach the implementation's literal one.

Generic over the element type, the capacity, the index type, and the projection
applied after the read; not tied to any particular SSZ container or consensus spec.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- Mapping a total `xs[·]!` read across `is` equals mapping the checked read across
`is.attach`, provided every index `is` points at is in range.

`idx` extracts the `Nat` position from an index element (consensus indices are
`UInt64`, so this is typically `UInt64.toNat`), and `f` is whatever projection the
caller applies to the element it read. Both are arbitrary, the argument only needs
`getElem!_pos` to fire pointwise. -/
theorem sszListMap_getElem!_eq_attachMap {α β ι : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (is : Array ι) (idx : ι → Nat) (f : α → β)
    (hRange : ∀ i ∈ is, idx i < xs.size) :
    is.map (fun i => f xs[idx i]!)
      = is.attach.map (fun i => f (xs[idx i.1]'(hRange i.1 i.2))) := by
  apply Array.ext
  · simp
  · intro i _ _
    -- Both sides read position `i`; `Array.getElem_attach` strips the subtype on the
    -- right, leaving the two element reads to be reconciled.
    simp only [Array.getElem_map, Array.getElem_attach]
    -- In bounds, so the total read agrees with the checked one.
    rw [getElem!_pos]

end SizzLean.Proofs
