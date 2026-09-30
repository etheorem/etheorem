import LeanRlp.Spec.Item
import LeanRlp.Spec.Scalar

/-!
# `LeanRlp.Spec.Encode`: the RLP encoder

The encoder is total and returns a plain `ByteArray` (ARCHITECTURE.md
§2.1). It recurses over an `Item` tree: a byte string below 0x80
encodes as itself, a longer one gets a string header, and a list
gets a list header over the concatenation of its items.

`encodeHeader` writes the header for a payload of `len` bytes. The
short form is one byte in `[base, base + 55]`; the long form is
`base + 55` followed by the minimal big-endian length, which is
what `Spec.Scalar` supplies. One definition serves strings and
lists.

Filled in PLAN.md Stage 1.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

end LeanRlp.Spec
