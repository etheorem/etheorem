# LeanRlp: architecture

The RLP codec for an execution layer in Etheorem. This file is the
binding design. [PLAN.md](PLAN.md) stages the work; module
docstrings cite these sections.

## 1. What this package is

One standalone package, the role `SizzLean` has for the consensus
layer: a total encoder, a total and strict decoder, a deriving
handler for record codecs, and theorems that say the two directions
agree. In scope: RLP as `ethereum-rlp` defines it (`encode`,
`decode`, the typed `decode_to`), the schema universe, and the codec
theorems.

Out of scope: Keccak, the `Hasher` class, the hash entry point, the
EIP-2718 typed envelope, the MPT, the hash memo, `forkrlp`, trailing
optional fields, and the devp2p uses of RLP. The `Hasher` class
lives in `EthCommon`; the Keccak implementation is its own Hazmat
package, `LeanHazmatKeccak`; §3 places the instances. A consumer
hashes an encoding by calling `Hasher.hash` on the `Rlp.encode`
output. `forkrlp` is an `EthELLib` form that wraps this package's
deriving handler. Trailing optional fields (a record that admits
20, 21 or 23 fields) constrain consumers: each fork declares its
full field list through that form, and LeanRlp decodes exactly the
declared shape.

## 2. The three layers

### 2.1 `Spec`: bytes to `Item` and back

`Item` is the two-arm tree: `.bytes b` and `.list items`. The
encoder recurses over it and returns a plain `ByteArray`. It is
total. `Item.Encodable` bounds every byte-string payload and every
list payload below 2^64 bytes; the round-trip theorems take it as a
hypothesis. List payloads need the bound as much as strings do: a
list payload of 2^64 bytes overflows the long-form header byte.

The decoder is one function family, `decodeHeader` over `decode`
and `decodePrefix`. Termination sits on a fuel argument: each item
node and each list element uses one unit, and a sufficiency lemma
certifies the fuel the public entry points pass, so `outOfFuel` is
a dead branch for them. `input.size` needs a proof before it can
serve as the fuel: under that measure, a two-byte input can use
three units. The decoder also carries a depth bound from Stage 1
on, and a nest deeper than the bound fails with `tooDeep`, before
it can exhaust the native stack. The default bound is 1024.
Consensus structures nest a handful of levels, and the fixtures sit
far below it. The reference oracle carries no limit, so this bound
is a recorded discrepancy, and Stage 2 keeps its random generator
under the bound.

The decoder is strict at the item layer, and each canonical rule is
one `DecodeError` constructor:

* single-byte form only for bytes below `0x80` (`nonCanonicalByte`);
* long form only for payloads above 55 bytes (`nonCanonicalLength`);
* minimally encoded length, no leading zero (`nonCanonicalLength`);
* the payload fully inside its parent (`truncated`, `listOverrun`);
* all of the input consumed (`trailingBytes`).

Structural recursion reduces in the kernel, so gate goals over the
byte operations reduce under `decide`. A probe on the pinned
toolchain confirms reduction for `extract`, `++`, and indexing;
`native_decide` is the fallback if a full gate stalls. Equality on
`Item` does not derive, because the type nests through `List`;
Stage 1 adds a hand-written `DecidableEq Item`, and the known-answer
gates use it.

### 2.2 `Schema`: wire shapes

`RlpType` describes a wire shape, nine arms. `RlpType.interp` gives
the Lean type of each shape. `toItem` and `fromItem` are written
once over the universe. `WellFormed` carries the one soundness
condition (`option t` never encodes to the empty string). Theorem 5
takes it as a hypothesis, and the `RlpRepr` class carries it as a
field (§2.3), so callers read it from the instance.

Fixed bytes and scalars are different arms (`fixed n`, `nat`,
`uint bits`). A block root can begin with a zero byte. A scalar
cannot. The scalar rules: zero is the empty string, a leading zero
byte is `leadingZero`, and a `uint bits` value of `2^bits` or more
is `overflow`. A `fixed n` field of another length is `wrongWidth`.
Each rule is its own `SchemaError` constructor.

### 2.3 `Repr`: the user surface

`RlpRepr` is the record class, six fields: `shape`, `toRepr`,
`fromRepr`, the two isomorphism laws, and
`wellFormed : shape.WellFormed`. `WellFormed` is decidable, the
derived field closes by `decide`, and the schema theorems read it
from the class. The `struct` arm nests through `List`, so
`Decidable WellFormed` needs a hand-written instance (Stage 4).
The polymorphic instances take `wellFormed` from the field
instance's proof, and a derived structure with a type parameter
does the same. `deriving RlpRepr` emits the instance from the
field instances in declaration order. A flat structure closes both
laws by `rfl`; a structure with `RlpRepr` fields closes them by
rewriting with the field laws, in the pattern of SizzLean's
deriving handler. A structure spells its field list once, and
encode and decode derive from that one list.

`Rlp.encode` and `Rlp.decode` are the two entry points the
execution layer calls. The hash of an encoding is a one-liner on
the consumer side, `Hasher.hash (Rlp.encode x)`, and lives one
layer up (§3).

## 3. The package stands alone

`packages/LeanRlp`, declarative `lakefile.toml`, namespace
`LeanRlp`. It holds no hash class, no hash entry point, and no
require on another Etheorem package, so it can mirror to its own
repository like `LeanSha256`.

The hash seam sits one layer up. The `Hasher` class lives in
`EthCommon`. Each instance lives with its consumer, in the `Sha256`
pattern: SizzLean hosts `Hasher Sha256` beside its FFI bridges, and
the execution-layer package hosts `Hasher Keccak256` beside the
axiom that equates the FFI Keccak with the pure-Lean reference.
`LeanHazmatKeccak` is a crypto-only package and requires no
`EthCommon`. `EthCommon` is planned consensus-side work; until it
lands, the class is `SizzLean.Hasher`, and no Keccak instance
exists. The codec names no execution-layer type: a consumer
derives or writes instances for its own types in its own package.

## 4. One representation

Everything, proofs included, runs on `ByteArray` with a cursor. The
proofs target the same functions the runner executes, and a second
`List UInt8` view would be a hand-synced copy.

## 5. The theorems

Nine, in `Proofs/`:

1. `decode_encode`: `t.Encodable → t within the depth bound →
   decode (encode t) = .ok t`
2. `encode_decode`: `decode b = .ok t → encode t = b`
3. `encode_injective` on `Encodable` items within the depth bound,
   from 1
4. `size_encode`: `(encode t).size = t.encodedSize`
5. `fromItem_toItem`, on a `WellFormed` shape
6. `toItem_fromItem`, unconditional
7. `Rlp.roundtrip`: `(toItem x).Encodable`, `x` within the depth
   bound, and the class's `wellFormed` field give
   `Rlp.decode (Rlp.encode x) = .ok x`
8. `Rlp.canonical`: `Rlp.decode b = .ok x → Rlp.encode x = b`,
   unconditional, by 2 through the class laws
9. `Rlp.encode_injective`, under 7's hypotheses

Theorem 2 is the strictness theorem: every accepted input
re-encodes to itself, at every entry point, at no run-time cost.
Theorem 9 is what lets a consumer treat a hash of an encoding as
identifying a value, up to the hash function's collisions, within
theorem 7's hypothesis class. A lemma beside theorem 1 says every
decoded item is `Encodable` and within the depth bound, because the
decoder reads at most eight length bytes and enforces the bound.

`Proofs/Axioms.lean` holds each theorem to `propext`,
`Classical.choice`, and `Quot.sound` at most. The package declares
no opaque constant and no axiom of its own.

## 6. Errors, two layers

`DecodeError` speaks about bytes; `SchemaError` speaks about
shapes, with the path to the failing field. `DecodeError` carries
the canonical rejections of §2.1 plus `tooDeep` and `outOfFuel`;
the sufficiency lemma keeps `outOfFuel` out of public results. Each
canonical constructor maps to one EEST exception tag, and
`EthELLib` owns that mapping. `tooDeep` and `outOfFuel` carry no
EEST tag; `EthELLib` maps them to its own rejection class. LeanRlp
knows no EEST name.

## 7. Evidence the codec matches Ethereum

* Known answers: the RLP specification's examples, plus the
  non-canonical inputs below. The consensus fixtures exercise none
  of them, so codec strictness has no upstream vector, and this
  package gates it itself. The five item-layer inputs are Stage 1
  gates, each to its `DecodeError` constructor; the scalar row is a
  schema-layer error, gated in Stage 4.

  | input | meaning | layer |
  |---|---|---|
  | `81 05` | one byte below `0x80` behind a string header | item |
  | `b8 01 05` | long form for a 1-byte string | item |
  | `f8 01 05` | long form for a 1-byte list payload | item |
  | `b8 00` | long form, zero length | item |
  | `b9 00 38 …` | leading zero in a long-form length | item |
  | `00` read as a scalar | leading zero | schema |

* RLPTests: the `rlp_vectors` runner reads the three
  `ethereum/tests` files at a pinned tag.
* Differential oracle: a Python script drives `ethereum-rlp`
  against the Lean codec on random trees, random typed values, and
  mutated encodings. This covers the typed layer, which RLPTests
  does not.

## 8. No cache box

SSZ merkleization is a tree, so one field write changes one path
and a cache reuses the rest. RLP has no such tree: the hash of a
record is one Keccak over its whole encoding. LeanRlp has no box.
Trie caching belongs to `LeanMpt`. Records hashed more than once
get the `Encoded` wrapper and `Rlp.decodeKeep` in Stage 7, on a
profile.

## 9. Layout

```
packages/LeanRlp/
├── lakefile.toml
├── LeanRlp.lean                 # root, imports only
├── LeanRlp/
│   ├── Spec/                    # Scalar, Item, Encode, Error, Decode
│   ├── Schema/                  # Type, Interp, Error, ToItem, FromItem
│   ├── Repr/                    # Class, Instances, Deriving
│   └── Proofs/                  # Scalar, Header, Roundtrip, Canonical,
│                                #   Size, Schema, Axioms
├── LeanRlpTests.lean            # gates, separate lean_lib
├── LeanRlpTests/                # gate modules
├── Runner/                      # rlp_vectors executable (Stage 2)
├── docs/
└── README.md, LICENSE
```

## 10. Risks

* **`ByteArray` proofs.** Core has fewer lemmas for
  `ByteArray.extract` and `++` than for `List`. Stage 3 may need a
  small lemma file that moves facts through `ByteArray.data`.
* **Kernel reduction.** The known-answer gates run under `decide`,
  and core `ByteArray` lemmas are thin. Stage 1 probes the cost on
  the first gate; `native_decide` is the stated fallback.
* **Nested inductive.** `Item` nests through `List`, so the encoder
  and the proofs run as a mutual pair over `Item` and `List Item`.
* **`interp` cost.** A value goes to `interp`, then to `Item`, then
  to bytes. Execution-layer hashes are dominated by Keccak, so this
  waits for a profile that shows it (Stage 7).
* **Universe fit.** A field kind outside the nine arms needs a new
  arm and its proof case. `item` is the fallback until then.
