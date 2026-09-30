import LeanRlp.Spec.Decode
import LeanRlp.Spec.Encode

/-!
# `LeanRlp.Proofs.Canonical`: encode of decode

Theorem 2 (ARCHITECTURE.md §5): `decode b = .ok t → encode t = b`.
Every decoded value is canonical, at every entry point, at no
run-time cost. Theorem 3, `encode_injective` on `Encodable` items
within the depth bound, follows from the round trip.

Filled in PLAN.md Stage 3.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
