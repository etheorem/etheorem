/-!
# `LeanHazmatSecp256k1.Ffi`: secp256k1 ECDSA behind `@[extern]`

Two `@[extern] opaque` declarations bridge Lean to the C shim in
`csrc/secp256k1_shim.c`, which wraps the vendored bitcoin-core
libsecp256k1: public-key recovery and plain verification for compact
`(r, s)` ECDSA signatures on secp256k1.

This module deliberately holds **only** the FFI bindings. The
ecRecover precompile is *not* assembled here: it composes
`ecdsaRecover` with `keccak256` and a 12-byte truncation, and that
composition is the consumer's job (packages/hazmat/docs/ARCHITECTURE.md §4). So
this package exposes the raw recovered public key, depends on nothing,
and stays independent of `LeanHazmatKeccak`.

## Encodings

* The message hash and both signature scalars are 32-byte big-endian.
* The public key is 64 bytes, uncompressed `x ‖ y`, big-endian, the
  EL's point encoding. The shim converts from the 33/65-byte
  serialized forms libsecp256k1's own API surfaces.
* `recId` is libsecp256k1's recovery id, 0-3: bit 0 is the
  y-coordinate parity of `R`, bit 1 an r-overflow flag. The EL
  transaction `v` maps in the caller: legacy `v ∈ {27, 28}` →
  `recId = v - 27`; EIP-155 `v = chain_id * 2 + 35 + parity` →
  `recId = (v - 35) mod 2`.

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatSecp256k1`); the
declarations live under the *brand* namespace `LeanHazmat.Secp256k1`.
The two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for secp256k1 ECDSA; each binding is an
opaque `@[extern]` boundary. The empirical trust assumption, *that the
vendored bitcoin-core libsecp256k1 (v0.8.0) implements ECDSA recovery
and verification correctly*, is validated only against the published
vectors in `LeanHazmatSecp256k1Tests/`, the EIP-155 example
transaction (recovery) plus a deterministic second signature and
negative cases.

## Lean idioms used here

* `@[extern "C-symbol"] opaque foo : T`: declare `foo : T` such that
  the *runtime* implementation is the named C symbol, while the
  *kernel* treats `foo` as fully opaque (no reduction, no
  definitional equality with anything else). Exactly what an FFI
  primitive we don't want to reduce inside proofs needs.
* `@&` on a function argument marks it as *borrowed*. Lean's runtime
  does not bump the refcount when passing it in. The C side receives
  a `b_lean_obj_arg` for these. The `UInt32` recovery id lowers to a
  plain `uint32_t` parameter, no boxing.
-/

set_option autoImplicit false

namespace LeanHazmat.Secp256k1

/-- Recover the 64-byte secp256k1 public key (`x ‖ y`, big-endian)
from a compact `(r, s)` ECDSA signature over a 32-byte message hash.

This is the primitive behind transaction sender recovery and the
ecRecover precompile (0x01); the address itself
(`keccak256(pk)[12:32]`) is the caller's composition.

Empty `ByteArray` on any failure: wrong lengths, `recId > 3`, an
out-of-range or zero `r` / `s`, or a signature that does not recover.

**Trust assumption:** the vendored bitcoin-core libsecp256k1 (v0.8.0)
implements ECDSA recovery correctly. Validated by
`LeanHazmatSecp256k1Tests/Vectors.lean`. -/
@[extern "lean_hazmat_secp256k1_ecdsa_recover"]
opaque ecdsaRecover (msgHash : @& ByteArray) (r : @& ByteArray)
    (s : @& ByteArray) (recId : UInt32) : ByteArray

/-- Verify a compact `(r, s)` ECDSA signature over a 32-byte message
hash against a 64-byte uncompressed public key. `false` covers "does
not verify" and every malformed input (wrong lengths, out-of-range
scalars, unparseable key). The shim normalizes a high `s` to its low
form before the library's verify, so `(r, s)` and `(r, n - s)` verify
identically: the execution layer has no Bitcoin-style anti-malleability
policy.

**Trust assumption:** same library as `ecdsaRecover`. Validated by the
round-trip and negative cases in
`LeanHazmatSecp256k1Tests/Vectors.lean`. -/
@[extern "lean_hazmat_secp256k1_ecdsa_verify"]
opaque ecdsaVerify (msgHash : @& ByteArray) (r : @& ByteArray)
    (s : @& ByteArray) (pubkey : @& ByteArray) : Bool

end LeanHazmat.Secp256k1
