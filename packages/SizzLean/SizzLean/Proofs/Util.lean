/-!
# `SizzLean.Proofs.Util`: elementary container bridges

Generic, dependency-free lemmas shared across the proof layers: the `getElem!` /
`get!` bridges for `Array` and `ByteArray` push/reads. A leaf module (no
SizzLean imports), so both the `Spec` proof files and the `Cache/MerkleTree`
shape modules can import it without layering concerns.

The `Array` pair lives here and not in the Merkle-tree shapes module. The
completeness proof then reaches a generic array fact without importing tree
vocabulary. `Proofs/BitPack.lean` and `Proofs/UIntWide.lean` import
`get!_eq_getElem` from here. All three declared it once each before, in this one
namespace, so any change to the statement broke whichever module loaded second.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

/-- `get!` agrees with the bounds-checked `b[i]` when in range.
`get!` unfolds to `b.data[i]!`, and `getElem!_pos` discharges its panic branch
against the supplied bound. -/
theorem get!_eq_getElem (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.get! i = b[i] := by
  show b.data[i]! = b[i]
  rw [ByteArray.getElem_eq_getElem_data]
  exact getElem!_pos b.data i h

/-- `(a.push x)[i]!` for `i < a.size` reads `a[i]!`: the push is invisible below
the old length. Collapses the recurring three-rewrite elimination block. -/
theorem getElem!_push_lt {α} [Inhabited α] (a : Array α) (x : α) (i : Nat)
    (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by rw [Array.size_push]; omega),
      Array.getElem_push_lt h, getElem!_pos a i h]

/-- `(a.push x)[a.size]!` reads the pushed element. The companion top-index case. -/
theorem getElem!_push_size {α} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega),
      Array.getElem_push]
  simp

end SizzLean.Proofs
