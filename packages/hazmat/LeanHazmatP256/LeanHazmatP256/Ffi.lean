/-!
# `LeanHazmatP256.Ffi`: NIST P-256 verification behind `@[extern]`

One `@[extern] opaque` declaration bridges Lean to the C shim in
`csrc/p256_shim.c`: ECDSA verification on NIST P-256 (secp256r1), the
primitive behind the execution-layer `P256VERIFY` precompile (EIP-7951,
Fusaka; RIP-7212 compatible).

This module deliberately holds **only** the FFI binding. The
precompile is *not* assembled here: the 160-byte input layout
(`msgHash ‖ r ‖ s ‖ qx ‖ qy`), the gas schedule, and the `0x…01`
success encoding are the consumer's job (packages/hazmat/docs/ARCHITECTURE.md
§4). The primitive answers `Bool`.

## Encodings

* All five arguments are 32-byte big-endian fields (hash, `r`, `s`,
  public-key `x`, public-key `y`).
* High-`s` signatures are accepted: EIP-7951 verifies exactly the
  ECDSA equation, no anti-malleability policy (its published suite
  marks a malleability case valid).
* `false` covers every malformed input (wrong lengths, coordinates ≥
  p, a point off the curve, `r` or `s` zero) as well as a failed
  verification, never an error.

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatP256`); the
declaration lives under the *brand* namespace `LeanHazmat.P256`. The
two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for P-256 ECDSA; the binding is an
opaque `@[extern]` boundary. The empirical trust assumption, *that the
linked OpenSSL libcrypto implements NIST P-256 ECDSA verification
correctly*, is validated only against the official EIP-7951 vectors
(Project Wycheproof, via the EIP's `test-vectors.json`) in
`LeanHazmatP256Tests/`.

## Lean idioms used here

* `@[extern "C-symbol"] opaque foo : T`: declare `foo : T` such that
  the *runtime* implementation is the named C symbol, while the
  *kernel* treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else). Exactly what an FFI
  primitive we don't want to reduce inside proofs needs.
* `@&` on a function argument marks it as *borrowed*. Lean's runtime
  does not bump the refcount when passing it in. The C side receives
  a `b_lean_obj_arg` for these.
-/

set_option autoImplicit false

namespace LeanHazmat.P256

/-- Verify a P-256 (secp256r1) ECDSA signature: `(r, s)` over
`msgHash`, against the public key at affine coordinates
`(qx, qy)`. Runtime implementation is `csrc/p256_shim.c`'s
`lean_hazmat_p256_verify`, which fetches against a private OpenSSL
library context (`default` provider loaded, process default context
untouched), imports the key through `EVP_PKEY_fromdata`, DER-encodes
the raw pair, and calls `EVP_PKEY_verify` (the OpenSSL 3.x provider
API; no deprecated `EC_KEY` / `ECDSA_*` calls).

High-`s` signatures verify (EIP-7951 has no malleability policy).
`false` covers "does not verify" and every malformed input.

**Trust assumption:** the linked OpenSSL `libcrypto` computes NIST
P-256 ECDSA verification correctly. Validated by the official EIP-7951
vectors in `LeanHazmatP256Tests/Vectors.lean`. -/
@[extern "lean_hazmat_p256_verify"]
opaque p256Verify (msgHash : @& ByteArray) (r : @& ByteArray)
    (s : @& ByteArray) (qx : @& ByteArray) (qy : @& ByteArray) : Bool

end LeanHazmat.P256
