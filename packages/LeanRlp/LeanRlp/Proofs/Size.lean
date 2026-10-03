import LeanRlp.Spec.Encode
import LeanRlp.Spec.Item

/-!
# `LeanRlp.Proofs.Size`: the encoder's byte count

Theorem 4 (ARCHITECTURE.md §5): `(encode t).size = t.encodedSize`,
where `encodedSize` is the structural size function over the `Item`
tree. The EIP-7934 block size limit applies to this count, and
Stage 7 proves the size pre-pass of the one-buffer encoder
against it.

Filled in PLAN.md Stage 3.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
