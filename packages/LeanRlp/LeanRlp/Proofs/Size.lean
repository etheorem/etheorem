import LeanRlp.Spec.Encode
import LeanRlp.Spec.Item

/-!
# `LeanRlp.Proofs.Size`: the encoder's byte count

Theorem 4 (ARCHITECTURE.md §5): `(encode t).size = t.encodedSize`,
where `encodedSize` is the structural size function over the `Item`
tree. EIP-7934's block size limit reads this, and the size pre-pass
of the Stage 7 one-buffer encoder is proved against it.

Filled in PLAN.md Stage 3.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
