/-!
# `LeanHazmatXMSS.Ffi`: xmss-reference behind `@[extern]`

Three `@[extern] opaque` declarations bridge Lean's `ByteArray` to the C shim
in `csrc/xmss_shim.c`, which wraps xmss-reference for RFC 8391 XMSS-SHA2
one-time signatures.

## Parameter sets and OID encoding

The OID argument is 4 bytes, big-endian (same layout xmss-reference stores in
the first 4 bytes of pk and sk):

| Name               | OID bytes              | n  | h  | pk   | sig   |
|--------------------|------------------------|----|----|------|-------|
| XMSS-SHA2_10_256   | #[0x00, 0x00, 0x00, 0x01] | 32 | 10 | 68 B | 2500 B |
| XMSS-SHA2_16_256   | #[0x00, 0x00, 0x00, 0x02] | 32 | 16 | 68 B | 4708 B |
| XMSS-SHA2_20_256   | #[0x00, 0x00, 0x00, 0x03] | 32 | 20 | 68 B | 9124 B |

## Return layouts

* `keygenSeeded oid → pk ++ sk`: pk occupies the first `pk_bytes` bytes
  (68 for SHA2_10/16/20_256).
* `sign sk msg → sig ++ new_sk`: sig occupies the first `sig_bytes` bytes.
  The `new_sk` tail replaces `sk` for the next sign call (XMSS is stateful).
* `verify pk sig msg → Bool`.

Empty `ByteArray` / `false` is the error sentinel for invalid OID or bad sizes.

## Trust boundary

`opaque` prevents the kernel from reducing these calls in proofs. `@[extern]`
instructs the compiler to emit a direct call to the named C symbol at link
time. The empirical trust assumption, that xmss-reference correctly implements
RFC 8391 XMSS-SHA2, is validated by the KAT in `LeanHazmatXMSSTests/Vectors.lean`.

## Lean idioms used here

* `@[extern "symbol"] opaque foo : T` — FFI primitive: runtime dispatches to
  the C symbol; kernel treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else).
* `@&` — borrowed argument: Lean does not bump the refcount; C receives a
  `b_lean_obj_arg` pointer it may read but must not retain.
-/

set_option autoImplicit false

namespace LeanHazmat.Xmss

/-- Deterministic XMSS key generation. `oid` is a 4-byte big-endian OID
(see module docstring). Returns `pk ++ sk` where pk occupies the first
`pk_bytes` bytes. Successive calls with the same OID produce identical output
(counter seed reset to 0 per call), making this suitable for reproducible KATs.
Returns the empty `ByteArray` if the OID is unrecognized.

For security-sensitive use outside tests, randomness must come from a CSPRNG;
see the `randombytes` comment in `csrc/xmss_shim.c`.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_keygen_seeded`.

**Trust assumption:** xmss-reference correctly implements RFC 8391 XMSS-SHA2.
Validated by `LeanHazmatXMSSTests/Vectors.lean`. -/
@[extern "lean_hazmat_xmss_keygen_seeded"]
opaque keygenSeeded (oid : @& ByteArray) : ByteArray

/-- XMSS sign. `sk` is the current secret key (from `keygenSeeded` or a
previous `sign` call). `msg` is the message to sign (arbitrary length).
Returns `sig ++ new_sk` where sig occupies the first `sig_bytes` bytes.
The `new_sk` tail must replace `sk` for the next sign (XMSS is stateful;
re-using the same leaf index breaks one-time security).
Returns the empty `ByteArray` on invalid SK or unrecognized OID.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_sign`.

**Trust assumption:** xmss-reference correctly implements RFC 8391 XMSS-SHA2.
Validated by `LeanHazmatXMSSTests/Vectors.lean`. -/
@[extern "lean_hazmat_xmss_sign"]
opaque sign (sk : @& ByteArray) (msg : @& ByteArray) : ByteArray

/-- XMSS signature verification. `pk` is the public key; `sig` is the
signature (`sig_bytes` bytes for the given OID); `msg` is the message.
Returns `true` if the signature is valid, `false` on invalid signature,
mismatched sizes, or unrecognized OID.

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_verify`.

**Trust assumption:** xmss-reference correctly implements RFC 8391 XMSS-SHA2.
Validated by `LeanHazmatXMSSTests/Vectors.lean`. -/
@[extern "lean_hazmat_xmss_verify"]
opaque verify (pk : @& ByteArray) (sig : @& ByteArray) (msg : @& ByteArray) : Bool

end LeanHazmat.Xmss
