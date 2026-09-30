import LeanRlp.Spec.Decode
import LeanRlp.Spec.Encode

/-!
# `LeanRlp.Proofs.Header`: headers invert

The lemma the item proofs recurse through: `decodeHeader` inverts
`encodeHeader`. A header written by `encodeHeader` decodes to the
kind and payload span it was written from, with every canonical check
passing. `Proofs/Canonical.lean` lifts this to whole items.

Filled in PLAN.md Stage 3.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
