# Non-malleability of the SSZ codec

A codec is malleable in two ways. Two different values can share one
encoding. Or one value can have two encodings that the decoder accepts.
Consensus code compares, caches, and hashes encoded bytes, so either case
lets a peer alter the bytes of a block without changing what it means.

Two properties rule out the two cases:

| Property | Statement | Rules out | Status |
| --- | --- | --- | --- |
| Encoder injectivity | `serialize s x = serialize s y → x = y` | two values, one encoding | proved |
| Decoder canonicity | `deserialize s b = .ok (x, b.size) → serialize s x = b` | one value, two encodings | open, false today |

This file states what SizzLean proves, what each hypothesis is for, and
what stays open. The proof ledger rows are in
[`PROOF_LEDGER.md`](PROOF_LEDGER.md); the design is in
[`ARCHITECTURE.md`](ARCHITECTURE.md) §4 and §5.1.

## What is proved

The spec-level theorem sits in `Proofs/Injective.lean`:

```lean
theorem serialize_injective : ∀ (s : SSZType), SSZType.BasicSupported s →
    ∀ (x y : s.interp), EncodedFits s x →
      SSZType.serialize s x = SSZType.serialize s y → x = y
```

It is a corollary of `decode_encode`. Decode both sides of the equal
encodings. The roundtrip theorem says the left side decodes to `x` and the
right side to `y`, and the decoder is a function, so `x = y`.

`SSZ.serialize_injective` in `Repr/Class.lean` lifts the theorem to any
type with an `SSZRepr` instance. The spec theorem gives
`toRepr x = toRepr y`, and the `to_from` law carries it back to `x = y`.

`EthCLSpecs/Proofs/<Fork>/Codec.lean` applies it to the real consensus
containers. For Fulu, Gloas, and Heze, the `BeaconState`,
`BeaconBlockBody`, `BeaconBlock`, and `SignedBeaconBlock` theorems hold at
the mainnet and minimal presets. Heze's `SignedInclusionList` theorem
holds at every preset. The size bound is the only hypothesis left.

Every one of these theorems rests on `propext`, `Classical.choice`, and
`Quot.sound` alone. No `native_decide`, `bv_decide` certificate, or
SHA-256 axiom enters, because serialization never hashes.

## The two hypotheses

**`BasicSupported s`** excludes the shapes where the claim is false. Take
`.list (.container []) 4`, a list of empty containers. Each element
encodes to zero bytes, so a list of one element and a list of two both
encode to the empty buffer. Encoder injectivity fails, and no proof can
exist. The predicate asks for `0 < t.fixedByteSize` on a list of
fixed-size elements, and for a positive length on every vector and
bitvector. The decoder rejects a zero-length vector, so roundtrip fails
there too.

The gate costs the caller nothing on a concrete schema.
`Spec/BasicSupportedDecide.lean` makes the predicate decidable, and
`by decide` proves it in the kernel for any closed shape. The fork
theorems close it this way on the 38-field `BeaconState`.

The fork theorems name the two shipped presets for one reason. The
`Preset` class carries no positivity proof for `epochsPerSlashingsVector`
or `ptcSize`. A preset that sets either to zero puts a zero-length vector
in the state, and then the gate fails.

**`EncodedFits s x`** says the encoding of `x` is shorter than `2 ^ 32`
bytes. SSZ stores every offset in a `uint32`, so a longer encoding has
no valid offsets. The bound is a fact about one value, so the theorem
takes it as a hypothesis. A bound on `x` is enough, because
`serialize s x = serialize s y` gives `y` the same size.

## What is open

### Decoder canonicity

The decoder accepts some byte strings that are not the canonical encoding
of the value they decode to. Issue
[#81](https://github.com/etheorem/etheorem/issues/81) records the cause.
The vector and list arms never check that the first offset equals the size
of the offset table. The container arm does check it.

A concrete pair, at the shape `.vector (.list (.uintN 8) 4) 1`:

| Bytes | Decodes to | Bytes consumed |
| --- | --- | --- |
| `04 00 00 00 00 00 00 00` | `[[0, 0, 0, 0]]` | 8 of 8 |
| `00 00 00 00` | `[[0, 0, 0, 0]]` | 4 of 4 |

The second buffer has offset `0`, so the one element's body starts inside
the offset table and reads the offset bytes as its data. Both buffers
decode fully to the same value. The SSZ spec lists "offsets: out of order,
out of range, mismatching minimum element size" among the checks a decoder
must make. Conformance stays green, so the `ssz_generic` invalid vectors
do not exercise this case.

The plan has two steps. First, fix #81 with the check the container arm
already makes. Second, prove `encode_decode` over `BasicSupported`,
by the same induction as `decode_encode`:

```lean
theorem encode_decode : ∀ (s : SSZType), SSZType.BasicSupported s →
    ∀ (b : ByteArray) (x : s.interp),
      SSZType.deserialize s b = .ok (x, b.size) → SSZType.serialize s x = b
```

With it, two byte strings that both decode fully to one value are the same
bytes. That is the statement
[`research/pre-research.md`](research/pre-research.md) aims at.

### Trailing bytes at the user surface

`SSZ.deserialize` drops the consumed-byte count that
`SSZType.deserialize` returns. So the user surface accepts a buffer with
extra bytes after a fixed-size value. The 9-byte buffer
`01 00 00 00 00 00 00 00 07` decodes as the `UInt64` value `1`. The SSZ
spec names "extra unused bytes" as a case a decoder must reject.

For a type with a variable-size tail, the last field runs to the end of
the buffer, so the extra bytes land inside it. The gap is for fixed-size
values: `Checkpoint`, `AttestationData`, a bare `uint64`. The
`ssz_generic` runner compares the count with the buffer size itself, so it
catches these cases. The fork-choice driver in
`packages/EthCLLib/EthCLLib/PySpecTests/Interface.lean` calls
`SSZ.deserialize` directly.

The fix is one comparison in `SSZ.deserialize`: return
`.error .trailingBytes` when the count differs from the buffer size.
`SSZ.roundtrip` keeps its proof, because `decode_encode` already gives a
count equal to the size.

### Merkle roots

Two values with one `hash_tree_root` would be a third kind of ambiguity,
since signatures cover the root. For every arm that hashes, ruling it out
needs the collision resistance of SHA-256. The library records that as a
trust boundary (the `trust × sha256-ffi` ledger row) and does not prove
it. The basic arms apply no hash, and `hashTreeRoot_basic_injective`
proves them injective outright.

## Files

| File | Holds |
| --- | --- |
| `SizzLean/Proofs/Injective.lean` | `serialize_injective` over the `SSZType` universe |
| `SizzLean/Proofs/Roundtrip.lean` | `decode_encode`, the theorem it rests on |
| `SizzLean/Repr/Class.lean` | `SSZ.serialize_injective` and `SSZ.roundtrip` for user types |
| `SizzLean/Spec/BasicSupportedDecide.lean` | the decision procedure for the gate |
| `EthCLSpecs/Proofs/{Fulu,Gloas,Heze}/Codec.lean` | the theorems on the fork containers |
