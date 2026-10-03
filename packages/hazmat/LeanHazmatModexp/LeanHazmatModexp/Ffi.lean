/-!
# `LeanHazmatModexp.Ffi`: modular exponentiation behind `@[extern]`

One `@[extern] opaque` declaration bridges Lean to the C shim in
`csrc/modexp_shim.c`: raw modular exponentiation over big-endian byte
strings, via OpenSSL's `BN_mod_exp`.

This module deliberately holds **only** the FFI binding. The modexp
precompile (0x05) is *not* assembled here: the EIP-198
length-prefixed input parse, the excess-data and right-padding rules,
the EIP-2565 / 7883 gas schedule, and the output left-padding to the
modulus's length are all the consumer's job
(packages/hazmat/docs/ARCHITECTURE.md §4). The primitive answers
`(base ** exponent) mod modulus` in `BN_bn2bin`'s minimal big-endian
form.

## Encodings

* All three inputs are big-endian byte strings of any length (leading
  zeros allowed, `BN_bin2bn` ignores them).
* The result is minimal big-endian: no leading zero bytes. A zero
  result is the single byte `00`. Left-padding to the modulus length
  is the caller's step.
* A zero modulus is a failure (the empty `ByteArray`): reduction mod 0
  is undefined.
* Exponent 0 answers `1 mod modulus` (so modulus 1 answers `00`).

## Naming: package vs. brand

The import unit is the *package* (`import LeanHazmatModexp`); the
declaration lives under the *brand* namespace `LeanHazmat.Modexp`. The
two are decoupled exactly as SizzLean decouples the file path
`SizzLean/Hasher/Sha256.lean` from its `SizzLean.Hasher` namespace
(ARCHITECTURE.md §3.3).

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for big-integer modular exponentiation
at this size; the binding is an opaque `@[extern]` boundary. The
empirical trust assumption, *that the linked OpenSSL libcrypto
implements `BN_mod_exp` correctly*, is validated only against the
EIP-198 worked examples and fixed modular-arithmetic cases in
`LeanHazmatModexpTests/` (cross-checked against Python's `pow` at
authoring time).

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

namespace LeanHazmat.Modexp

/-- `(base ** exponent) mod modulus` over big-endian byte strings.
Runtime implementation is `csrc/modexp_shim.c`'s
`lean_hazmat_modexp`, which wraps OpenSSL's `BN_mod_exp`.

The result is minimal big-endian (no leading zero bytes); the modexp
precompile's left-padding to the modulus length is the caller's step.
Empty `ByteArray` on failure: an input above `INT_MAX` bytes (the shim
rejects it rather than truncating into `BN_bin2bn`'s `int` length), a
zero modulus, or a BIGNUM error.

**Trust assumption:** the linked OpenSSL `libcrypto` computes modular
exponentiation correctly. Validated by
`LeanHazmatModexpTests/Vectors.lean`. -/
@[extern "lean_hazmat_modexp"]
opaque modExp (base : @& ByteArray) (exponent : @& ByteArray)
    (modulus : @& ByteArray) : ByteArray

end LeanHazmat.Modexp
