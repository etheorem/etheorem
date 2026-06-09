/-!
# `LeanHazmatBls.Ffi`: Ethereum consensus BLS behind `@[extern]`

`@[extern] opaque` bindings to the C shim in `csrc/bls_shim.c`, which
wraps supranational/blst for the **minimal-pubkey-size** BLS signature
scheme used by the Ethereum consensus layer:

* public keys in **G1**, 48-byte compressed;
* signatures in **G2**, 96-byte compressed;
* secret keys are 32-byte big-endian scalars;
* ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`, the
  *proof-of-possession* (POP) suite. (A *ciphersuite* fixes the
  hash-to-curve domain-separation tag and signing variant; "G1/G2" are
  the two source groups of the BLS12-381 pairing; "compressed" stores a
  curve point as its x-coordinate plus a sign bit.)

This is the **raw primitive** surface, `Sign` / `Verify` / aggregation
/ pairing verification. Composition into protocol objects (collecting a
committee's pubkeys, choosing the message to sign) is the caller's job
(hazmat-docs/ARCHITECTURE.md §4).

## Conventions

* Byte arguments are `@&`-borrowed (`b_lean_obj_arg` in C); the shim
  never mutates or retains them.
* Point-returning operations (`sign`, `aggregate`, `ethAggregatePubkeys`)
  return a fresh `ByteArray`; an **empty** `ByteArray` is the error
  sentinel (invalid input, bad encoding, or an empty aggregation list).
  Check `.isEmpty` / `.size` at the call site.
* Verification operations return `Bool`. A `false` is a *legitimate*
  "does not verify" (or invalid input), never a panic.

## Trust boundary (ARCHITECTURE.md §10)

Unlike SHA-256, BLS has **no** kernel-reducible pure-Lean reference:
each binding is an opaque `@[extern]` boundary whose only validation is
the official consensus-spec BLS test vectors (`LeanHazmatBlsTests`).
`opaque` keeps the kernel from trying to reduce a pairing; `@[extern]`
emits a direct call to the named blst-backed C symbol. The empirical
trust assumption, *that blst implements BLS12-381 and this ciphersuite
correctly*, is what the KAT pins.
-/

set_option autoImplicit false

namespace LeanHazmat.Bls

/-- BLS `Sign(sk, message)` → 96-byte G2 signature. `sk` is a 32-byte
big-endian scalar; `message` is arbitrary bytes. Returns the **empty**
`ByteArray` if `sk` is not 32 bytes.

Runtime: `csrc/bls_shim.c`'s `lean_hazmat_bls_sign` (blst
`blst_hash_to_g2` + `blst_sign_pk_in_g1`).

**Trust assumption:** blst implements the
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_` ciphersuite. Validated by
the consensus-spec `sign` vectors in `LeanHazmatBlsTests`. -/
@[extern "lean_hazmat_bls_sign"]
opaque sign (sk : @& ByteArray) (message : @& ByteArray) : ByteArray

/-- `SkToPk(sk)` → the 48-byte G1 public key for a 32-byte secret key
(validator key → pubkey). Returns the **empty** `ByteArray` if `sk` is
not 32 bytes.

Runtime: `csrc/bls_shim.c`'s `lean_hazmat_bls_sk_to_pk` (blst
`blst_sk_to_pk_in_g1`). -/
@[extern "lean_hazmat_bls_sk_to_pk"]
opaque skToPk (sk : @& ByteArray) : ByteArray

/-- BLS `Verify(pubkey, message, signature)` → `Bool`. `pubkey` is a
48-byte G1 point, `signature` a 96-byte G2 point. Performs the
consensus `KeyValidate` reject of the identity pubkey and the subgroup
checks on both points. Any malformed input yields `false`.

Runtime: `lean_hazmat_bls_verify` (blst `blst_core_verify_pk_in_g1`). -/
@[extern "lean_hazmat_bls_verify"]
opaque verify
    (pubkey : @& ByteArray) (message : @& ByteArray)
    (signature : @& ByteArray) : Bool

/-- `KeyValidate(pubkey)` → `Bool`: the 48-byte input decodes to a
non-identity G1 point in the prime-order subgroup. The pubkey-validity
predicate the consensus spec requires before `Verify`.

Runtime: `lean_hazmat_bls_key_validate`. -/
@[extern "lean_hazmat_bls_key_validate"]
opaque keyValidate (pubkey : @& ByteArray) : Bool

/-- `Aggregate(signatures)` → one 96-byte G2 signature (point sum).
Returns the **empty** `ByteArray` for an empty list or any
bad/wrong-length signature. Subgroup membership is not re-checked here
(the spec `Aggregate` assumes valid inputs); validity is established by
the matching `*Verify`.

Runtime: `lean_hazmat_bls_aggregate` (blst `blst_p2_add_or_double_affine`). -/
@[extern "lean_hazmat_bls_aggregate"]
opaque aggregate (signatures : @& Array ByteArray) : ByteArray

/-- `eth_aggregate_pubkeys(pubkeys)` → one 48-byte G1 public key (point
sum). Returns the **empty** `ByteArray` for an empty list or any bad
pubkey.

Runtime: `lean_hazmat_bls_eth_aggregate_pubkeys` (blst
`blst_p1_add_or_double_affine`). -/
@[extern "lean_hazmat_bls_eth_aggregate_pubkeys"]
opaque ethAggregatePubkeys (pubkeys : @& Array ByteArray) : ByteArray

/-- `g1Add(a, b)` → the 48-byte compressed sum of two G1 public keys
(the spec's `G1_to_bytes48(add(bytes48_to_G1 a, bytes48_to_G1 b))`).
Returns the **empty** `ByteArray` on a wrong length / bad encoding. The
result may be the point at infinity (`0xc0‖0×47`). Raw point op: no
subgroup / identity check (validity is established via `verify`).

Runtime: `lean_hazmat_bls_g1_add` (blst `blst_p1_add_or_double_affine`). -/
@[extern "lean_hazmat_bls_g1_add"]
opaque g1Add (a : @& ByteArray) (b : @& ByteArray) : ByteArray

/-- `g1Neg(a)` → the 48-byte compressed negation of a G1 public key
(the spec's `G1_to_bytes48(neg(bytes48_to_G1 a))`). Empty `ByteArray` on
a wrong length / bad encoding.

Runtime: `lean_hazmat_bls_g1_neg` (blst `blst_p1_cneg`). -/
@[extern "lean_hazmat_bls_g1_neg"]
opaque g1Neg (a : @& ByteArray) : ByteArray

/-- `AggregateVerify(pubkeys, messages, signature)` → `Bool`, the
distinct-message pairing check. `pubkeys` and `messages` must be the
same non-zero length; `signature` is 96 bytes. Each pubkey is
`KeyValidate`d. Malformed input or a length mismatch yields `false`.

Runtime: `lean_hazmat_bls_aggregate_verify` (blst pairing API:
`blst_pairing_init` / `blst_pairing_aggregate_pk_in_g1` /
`blst_pairing_commit` / `blst_pairing_finalverify`). -/
@[extern "lean_hazmat_bls_aggregate_verify"]
opaque aggregateVerify
    (pubkeys : @& Array ByteArray) (messages : @& Array ByteArray)
    (signature : @& ByteArray) : Bool

/-- `FastAggregateVerify(pubkeys, message, signature)` → `Bool`: verify
one `signature` of one shared `message` under the aggregate of
`pubkeys`. The pubkey list must be non-empty (the IETF function is
undefined for an empty list → `false` here).

Runtime: `lean_hazmat_bls_fast_aggregate_verify` (G1 aggregate +
`blst_core_verify_pk_in_g1`). -/
@[extern "lean_hazmat_bls_fast_aggregate_verify"]
opaque fastAggregateVerify
    (pubkeys : @& Array ByteArray) (message : @& ByteArray)
    (signature : @& ByteArray) : Bool

/-- `eth_fast_aggregate_verify(pubkeys, message, signature)` → `Bool`,
the consensus variant of `FastAggregateVerify`: an **empty** pubkey
list verifies iff `signature` is the G2 point at infinity
(`0xc0‖0×95`); otherwise it is `FastAggregateVerify`.

Runtime: `lean_hazmat_bls_eth_fast_aggregate_verify`. -/
@[extern "lean_hazmat_bls_eth_fast_aggregate_verify"]
opaque ethFastAggregateVerify
    (pubkeys : @& Array ByteArray) (message : @& ByteArray)
    (signature : @& ByteArray) : Bool

end LeanHazmat.Bls
