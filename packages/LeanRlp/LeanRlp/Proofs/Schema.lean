import LeanRlp.Schema.FromItem
import LeanRlp.Schema.ToItem
import LeanRlp.Schema.Type

/-!
# `LeanRlp.Proofs.Schema`: the schema isomorphism laws

Theorems 5 and 6 (ARCHITECTURE.md §5), by induction over `RlpType`,
one case per arm:

* `fromItem_toItem : s.WellFormed → fromItem s (toItem s v) = .ok v`
* `toItem_fromItem : fromItem s i = .ok v → toItem s v = i`

Theorem 5 carries the `WellFormed` hypothesis; theorem 6 holds
unconditionally, which makes `Rlp.canonical` unconditional. The
proof cases live here, so a new arm is one new case (OCP).

Filled in PLAN.md Stage 4.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
