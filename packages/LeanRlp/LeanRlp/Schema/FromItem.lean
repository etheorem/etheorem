import LeanRlp.Schema.Error
import LeanRlp.Schema.Interp
import LeanRlp.Schema.Type
import LeanRlp.Spec.Item

/-!
# `LeanRlp.Schema.FromItem`: `Item` trees to values

`fromItem s i` maps an `Item` tree to a value `v : s.interp`, or
fails with a `SchemaError` under the path of the failing field.
Fixed width, scalar bounds, leading zeros, and boolean form are all
checked here, each with its own constructor.

The isomorphism law `toItem_fromItem` (`Proofs/Schema.lean`,
theorem 6 of ARCHITECTURE.md §5) says anything that decodes
re-encodes to the same tree. It holds unconditionally; only
theorem 5 carries `WellFormed`.

Filled in PLAN.md Stage 4.
-/

set_option autoImplicit false

namespace LeanRlp.Schema

end LeanRlp.Schema
