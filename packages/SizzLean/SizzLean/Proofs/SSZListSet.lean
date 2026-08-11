import SizzLean.Repr.Instances

/-!
# `SizzLean.Proofs.SSZListSet`: `SSZList.set!`'s read-back behavior

`SizzLean.Repr.SSZList.set!` lowers to `Array.setIfInBounds` (`Repr/Instances.lean`):
in range it replaces one element, past the end it is a silent no-op. This file says
what the total reads `xs[i]!` and `xs.size` observe afterwards, which is the pair the
`sszUpdate` / `sszModify` macros emit for an `[i]!` path.

Generic over the element type and capacity; not tied to any particular SSZ container
or consensus spec.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Repr

/-- `SSZList.set!` preserves the runtime length, in range or past the end. -/
theorem sszListSet!_size {α : Type} {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (v : α) :
    (xs.set! i v).size = xs.size := by
  simp [SSZList.size]

/-- In range, the written index reads back exactly the written value. -/
theorem sszListSet!_getElem!_self {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set! i v)[i]! = v := by
  -- `getElem!_pos` swaps the total read for the proof-carrying one; its `dom` is
  -- `SSZList`'s faithful validity predicate, which `set!`'s size preservation
  -- discharges at the written index.
  rw [getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size)
    (h := by simpa [sszListSet!_size] using h)]
  show (xs.set! i v).val[i]'_ = v
  simp

/-- Every index other than the written one is untouched, whether or not that other
index `j` is itself in range. -/
theorem sszListSet!_getElem!_ne {α : Type} [Inhabited α] {cap : Nat}
    (xs : SSZList α cap) (i j : Nat) (v : α) (hij : i ≠ j) :
    (xs.set! i v)[j]! = xs[j]! := by
  by_cases hj : j < xs.size
  · rw [getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size)
          (h := by simpa [sszListSet!_size] using hj),
        getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size) (h := hj)]
    show (xs.set! i v).val[j]'_ = xs.val[j]'_
    exact Array.getElem_setIfInBounds_ne hj hij
  · rw [getElem!_neg (dom := fun (xs : SSZList α cap) i => i < xs.size)
          (h := by simpa [sszListSet!_size] using hj),
        getElem!_neg (dom := fun (xs : SSZList α cap) i => i < xs.size) (h := hj)]

/-- Past the end, the write is a no-op on the *whole* list, so no read at any index
can tell the pre- and post-write lists apart. Stronger than the per-index facts
above, and what a caller needs to frame an out-of-range `[i]!` write. -/
theorem sszListSet!_eq_of_size_le {α : Type} {cap : Nat}
    (xs : SSZList α cap) (i : Nat) (v : α) (h : xs.size ≤ i) :
    xs.set! i v = xs := by
  apply Subtype.ext
  exact Array.setIfInBounds_eq_of_size_le (by simpa [SSZList.size] using h)

end SizzLean.Proofs
