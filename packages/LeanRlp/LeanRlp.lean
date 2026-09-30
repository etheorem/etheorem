import LeanRlp.Spec.Scalar
import LeanRlp.Spec.Item
import LeanRlp.Spec.Encode
import LeanRlp.Spec.Error
import LeanRlp.Spec.Decode
import LeanRlp.Schema.Type
import LeanRlp.Schema.Interp
import LeanRlp.Schema.Error
import LeanRlp.Schema.ToItem
import LeanRlp.Schema.FromItem
import LeanRlp.Repr.Class
import LeanRlp.Repr.Instances
import LeanRlp.Repr.Deriving

/-!
# `LeanRlp`: the RLP codec for the execution layer (library root)

Recursive-Length Prefix (RLP) as `ethereum-rlp` defines it: `encode`,
`decode`, and the typed `decode_to`. This package takes the role
`SizzLean` has for the consensus layer, one standalone package with a
verified core, for the execution layer's wire format.

Three layers, each its own module subtree:

* `LeanRlp.Spec`: the byte-level codec. `Item`, the two-arm tree of
  byte strings and lists; `encode`; and a total, strict decoder on
  a fuel argument with a depth bound. The decoder rejects every
  non-canonical input form at the item layer, and each rejection is
  a typed `DecodeError`.
* `LeanRlp.Schema`: the schema universe `RlpType`, its `interp`, and
  the typed codec `toItem` / `fromItem` written once over the
  universe. `SchemaError` names the reason and the field path.
* `LeanRlp.Repr`: the user surface. `RlpRepr` (shape, isomorphism,
  and the decidable `wellFormed` field, six fields in all), the
  `deriving RlpRepr` handler, and `Rlp.encode` / `Rlp.decode`.

The theorems live under `LeanRlp.Proofs` (not re-exported here):
round trip, canonical form, injectivity, size, and the schema
isomorphism laws. The axiom gate `Proofs/Axioms.lean` holds each of
them to `propext`, `Classical.choice`, and `Quot.sound` at most.

Out of scope, by design: Keccak (its own Hazmat package,
`LeanHazmatKeccak`), the `Hasher` class (planned for `EthCommon`),
the hash entry point (a consumer calls `Hasher.hash` on the
`Rlp.encode` output), the EIP-2718 typed envelope, the MPT,
and the hash memo. See `docs/ARCHITECTURE.md` for the boundary.
-/
