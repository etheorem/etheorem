/-!
# `LeanHazmatXmss.Ffi`: xmss-reference behind `@[extern]`

Four `@[extern] opaque` declarations bridge Lean's `ByteArray` to the C shim
in `csrc/xmss_shim.c`, which wraps xmss-reference for RFC 8391 XMSS-SHA2
one-time signatures.

## Parameter sets and OID encoding

The OID argument is 4 bytes, big-endian (the same layout xmss-reference stores
in the first 4 bytes of pk and sk). All three SHA-2/256 sets share n = 32,
w = 16, so pk is `4 + 2·32 = 68` bytes and the signature is `2180 + 32·h`
bytes (`params.c`: `index_bytes + n + wots_sig_bytes + h·n`):

| Name             | OID bytes                 | n  | h  | pk   | sig    |
|------------------|---------------------------|----|----|------|--------|
| XMSS-SHA2_10_256 | `#[0x00, 0x00, 0x00, 0x01]` | 32 | 10 | 68 B | 2500 B |
| XMSS-SHA2_16_256 | `#[0x00, 0x00, 0x00, 0x02]` | 32 | 16 | 68 B | 2692 B |
| XMSS-SHA2_20_256 | `#[0x00, 0x00, 0x00, 0x03]` | 32 | 20 | 68 B | 2820 B |

`paramSizes` returns these numbers straight from `params.c`, so callers never
hard-code them.

## Return layouts

* `paramSizes oid → some (pk_bytes, sig_bytes, sk_bytes)`, or `none` for an
  unrecognized OID.
* `keygenFromSeed oid seed → pk ++ sk`: pk occupies the first `pk_bytes` bytes.
* `sign sk msg → sig ++ new_sk`: sig occupies the first `sig_bytes` bytes.
  The `new_sk` tail replaces `sk` for the next sign call (XMSS is stateful).
* `verify pk sig msg → Bool`.

Empty `ByteArray` / `false` is the error sentinel for invalid OID or bad sizes.

## Trust boundary

`opaque` prevents the kernel from reducing these calls in proofs. `@[extern]`
instructs the compiler to emit a direct call to the named C symbol at link
time. The empirical trust assumption, that xmss-reference correctly implements
RFC 8391 XMSS-SHA2, is validated by the KAT in `LeanHazmatXmssTests/Vectors.lean`.

Each result is a pure function of its byte-array arguments: the shim holds no
process state, so `opaque` is sound (two calls with equal arguments return
equal bytes).

## Lean idioms used here

* `@[extern "symbol"] opaque foo : T` — FFI primitive: runtime dispatches to
  the C symbol; kernel treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else).
* `@&` — borrowed argument: Lean does not bump the refcount; C receives a
  `b_lean_obj_arg` pointer it may read but must not retain.
-/

set_option autoImplicit false

namespace LeanHazmat.Xmss

/-- Buffer sizes for an XMSS parameter set, read from `params.c`. Returns
`some (pk_bytes, sig_bytes, sk_bytes)` (the OID-prefixed pk/sk sizes and the
exact signature size) for a recognized 4-byte big-endian `oid`, or `none`
otherwise. This is the single source of truth for slicing `keygenFromSeed`
and `sign` output; callers should not retype the constants from the table
above.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_param_sizes`. -/
@[extern "lean_hazmat_xmss_param_sizes"]
opaque paramSizes (oid : @& ByteArray) : Option (Nat × Nat × Nat)

/-- XMSS key generation from an explicit seed. `oid` is a 4-byte big-endian OID
(see the module docstring). `seed` must be exactly `3·n` bytes
(`sk_seed ‖ sk_prf ‖ pub_seed`, so 96 bytes for the SHA-2/256 sets). Returns
`pk ++ sk` where pk occupies the first `pk_bytes` bytes, or the empty
`ByteArray` on an unrecognized OID or a wrong-length seed.

**Danger: the key material is exactly `seed`.** The output private key is a
deterministic, publicly derivable function of `oid` and `seed`. That is what
makes it usable for reproducible KATs, and what makes it catastrophic outside
tests: signing under a key whose seed is known or reused destroys the one-time
security XMSS depends on. Any real deployment must pass a seed drawn from a
CSPRNG, and must never sign twice under the same leaf index.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_keygen_from_seed`.

**Trust assumption:** xmss-reference correctly implements RFC 8391 XMSS-SHA2.
Validated by `LeanHazmatXmssTests/Vectors.lean`. -/
@[extern "lean_hazmat_xmss_keygen_from_seed"]
opaque keygenFromSeed (oid : @& ByteArray) (seed : @& ByteArray) : ByteArray

/-- XMSS sign. `sk` is the current secret key (from `keygenFromSeed` or a
previous `sign` call). `msg` is the message to sign (arbitrary length).
Returns `sig ++ new_sk` where sig occupies the first `sig_bytes` bytes.
The `new_sk` tail must replace `sk` for the next sign (XMSS is stateful;
re-using the same leaf index breaks one-time security).
Returns the empty `ByteArray` on invalid SK or unrecognized OID.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_sign`.

**Trust assumption:** xmss-reference correctly implements RFC 8391 XMSS-SHA2.
Validated by `LeanHazmatXmssTests/Vectors.lean`. -/
@[extern "lean_hazmat_xmss_sign"]
opaque sign (sk : @& ByteArray) (msg : @& ByteArray) : ByteArray

/-- XMSS signature verification. `pk` is the public key; `sig` is the
signature (`sig_bytes` bytes for the given OID); `msg` is the message.
Returns `true` if the signature is valid, `false` on invalid signature,
mismatched sizes, or unrecognized OID.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_verify`.

**Trust assumption:** xmss-reference correctly implements RFC 8391 XMSS-SHA2.
Validated by `LeanHazmatXmssTests/Vectors.lean`. -/
@[extern "lean_hazmat_xmss_verify"]
opaque verify (pk : @& ByteArray) (sig : @& ByteArray) (msg : @& ByteArray) : Bool

end LeanHazmat.Xmss
