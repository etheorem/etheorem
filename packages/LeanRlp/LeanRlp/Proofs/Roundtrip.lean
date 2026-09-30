import LeanRlp.Spec.Decode
import LeanRlp.Spec.Encode

/-!
# `LeanRlp.Proofs.Roundtrip`: decode of encode

Theorem 1 (ARCHITECTURE.md §5): `decode (encode t) = .ok t` for an
`Encodable` item whose encoding sits within the depth bound. The
proof is a mutual induction over `Item` and `List Item`, standing
on `Proofs.Scalar` and `Proofs.Header`. A lemma alongside it says
every decoded item is `Encodable` and within the bound, because the
decoder reads at most eight length bytes and enforces the bound
itself.

Filled in PLAN.md Stage 3.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
