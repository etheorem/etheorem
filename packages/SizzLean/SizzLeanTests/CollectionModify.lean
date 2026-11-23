import SizzLean.Repr.Instances

/-!
# `SizzLeanTests.CollectionModify`: `modify` on the three collection types

Gates for `SSZList.modify`, `ProgressiveList.modify` and `Vector.modify`
(`Repr/Instances.lean`). Each type gets two checks: an index in range, where the element
becomes `f` applied to it, and an index past the end, where the collection comes back
unchanged. The proofs of the general contract live in
`SizzLean.Proofs.CollectionModify`; these checks run the compiled code.

`modify` never reads past the end, so the out-of-range cases print no
`index out of bounds` line.
-/

set_option autoImplicit false

namespace SizzLeanTests.CollectionModify

open SizzLean.Repr

/-- A three-element list under a cap of four. -/
def sampleList : SSZList Nat 4 := ⟨#[1, 2, 3], by decide⟩

/-- The same elements as a progressive list. -/
def sampleProgressive : ProgressiveList Nat := ⟨#[1, 2, 3]⟩

/-- The same elements as a fixed-length vector. -/
def sampleVector : Vector Nat 3 := #v[1, 2, 3]

-- `SSZList`: in range, then past the end.
#guard (sampleList.modify 1 (· + 10)).val == #[1, 12, 3]
#guard (sampleList.modify 3 (· + 10)).val == #[1, 2, 3]
#guard (sampleList.modify 1 (· + 10)).size == 3

-- `ProgressiveList`: in range, then past the end.
#guard (sampleProgressive.modify 0 (· * 5)).val == #[5, 2, 3]
#guard (sampleProgressive.modify 7 (· * 5)).val == #[1, 2, 3]

-- `Vector`: in range, then past the end.
#guard (sampleVector.modify 2 (· + 1)).toArray == #[1, 2, 4]
#guard (sampleVector.modify 3 (· + 1)).toArray == #[1, 2, 3]

end SizzLeanTests.CollectionModify
