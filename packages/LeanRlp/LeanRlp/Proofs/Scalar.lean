import LeanRlp.Spec.Scalar

/-!
# `LeanRlp.Proofs.Scalar`: scalar minimality and round trip

The lemmas every other proof stands on: the big-endian encoding of a
`Nat` is minimal (no leading zero unless the value is zero), and
decoding it gives the value back. Stage 3 builds the header and item
proofs from these.

Filled in PLAN.md Stage 3.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
