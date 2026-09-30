/-!
# `LeanRlp.Spec.Item`: the RLP item tree

The untyped value layer of the codec: an `Item` is either a byte
string or a list of items. Every execution-layer structure encodes
to an `Item` tree first and to bytes second, and the codec names no
execution-layer type; a consumer derives or writes instances for
its own types in its own package (ARCHITECTURE.md §3).

The module also defines `Item.Encodable`: every byte-string payload
in the tree, and every list payload, is shorter than 2^64 bytes.
The bound covers list payloads because a list payload of 2^64 bytes
overflows the long-form header byte. The round-trip theorems take
`Encodable` as a hypothesis, and the encoder performs no runtime
check (ARCHITECTURE.md §2.1).

Filled in PLAN.md Stage 1.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

/-- An RLP item: a byte string, or a list of items. -/
inductive Item where
  | bytes (b : ByteArray)
  | list (items : List Item)

end LeanRlp.Spec
