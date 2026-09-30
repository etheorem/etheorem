import LeanRlp.Schema.Interp
import LeanRlp.Schema.Type
import LeanRlp.Spec.Item

/-!
# `LeanRlp.Schema.ToItem`: values to `Item` trees

`toItem s v` maps a value `v : s.interp` to its `Item` tree, by
recursion on the schema `s`. Scalars use the minimal big-endian form
of `Spec.Scalar`, `fixed n` writes all `n` bytes, `struct` builds the
positional list, and `option t` writes the empty string for `none`.

The isomorphism law `fromItem_toItem` (`Proofs/Schema.lean`,
theorem 5 of ARCHITECTURE.md §5) says the round trip through
`fromItem` recovers `v` on a `WellFormed` shape.

Filled in PLAN.md Stage 4.
-/

set_option autoImplicit false

namespace LeanRlp.Schema

end LeanRlp.Schema
