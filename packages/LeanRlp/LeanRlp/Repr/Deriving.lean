import LeanRlp.Repr.Class
import LeanRlp.Repr.Instances

/-!
# `LeanRlp.Repr.Deriving`: the `deriving RlpRepr` handler

Emits an `RlpRepr` instance for a structure from the field
instances in declaration order: `shape := .struct [...]`, `toRepr`
and `fromRepr` as the positional pair, `wellFormed` by `decide`,
and the two laws from the field laws. A flat structure closes each
law by `rfl`; a structure with `RlpRepr` fields closes them by
rewriting with their `to_from` laws, in the pattern of SizzLean's
deriving handler (ARCHITECTURE.md §2.3). A derived instance carries
a verified round trip with no proof written by hand.

One field list, written once at the structure; encode and decode
derive from it (DRY).

Filled in PLAN.md Stage 5.
-/

set_option autoImplicit false

namespace LeanRlp

end LeanRlp
