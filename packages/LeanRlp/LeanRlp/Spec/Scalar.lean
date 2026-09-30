/-!
# `LeanRlp.Spec.Scalar`: `Nat` and minimal big-endian bytes

The scalar layer under the RLP wire format. RLP writes an integer as
the shortest big-endian byte string that holds it, and zero as the
empty string. This module holds the pair of functions that do that
conversion, plus the lemmas the decoder and the proofs need: the
encoding is minimal (no leading zero unless the value is zero), and
the decode of an encode gives the value back.

Filled in PLAN.md Stage 1.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

end LeanRlp.Spec
