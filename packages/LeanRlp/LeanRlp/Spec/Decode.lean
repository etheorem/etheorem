import LeanRlp.Spec.Error
import LeanRlp.Spec.Item
import LeanRlp.Spec.Scalar

/-!
# `LeanRlp.Spec.Decode`: the RLP decoder

One total, strict decoder (ARCHITECTURE.md §2.1). `decodeHeader`
reads a header, makes every canonical check, and reports the kind
and the payload span as a `Header`. `decode` parses a whole input,
`decodePrefix` parses one item and reports where it ended.

Termination sits on a fuel argument: each item node and each list
element uses one unit, and a sufficiency lemma certifies the fuel
the public entry points pass, so `outOfFuel` is a dead branch for
them. The decoder also carries a depth bound: a nest deeper than
the bound fails with `tooDeep`, before it can exhaust the native
stack. The default bound is 1024, recorded as a discrepancy against
the reference oracle, which carries no limit (ARCHITECTURE.md
§2.1).

Strictness is a theorem: `decode b = .ok t → encode t = b`
(ARCHITECTURE.md §5). Every decoded item carries the canonical
form, at every entry point, at no run-time cost.

ARCHITECTURE.md §7 lists the non-canonical inputs. The five
item-layer rows are Stage 1 gates, each expected to fail with its
`DecodeError` constructor.

Filled in PLAN.md Stage 1.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

end LeanRlp.Spec
