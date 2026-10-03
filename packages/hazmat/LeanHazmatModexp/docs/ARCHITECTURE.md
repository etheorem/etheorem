# LeanHazmatModexp: Architecture

The single-family trust-boundary record for `LeanHazmatModexp`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md).

## What this package is

Raw modular exponentiation in namespace `LeanHazmat.Modexp`:

| Primitive | C symbol |
| --- | --- |
| `modExp` | `lean_hazmat_modexp` |

`(base ** exponent) mod modulus` over big-endian byte strings. The
result is minimal big-endian (`BN_bn2bin`: no leading zeros; a zero
result is the single byte `00`, the empty output stays reserved for
the error sentinel). Inputs are *exact* byte strings, `BN_bin2bn`
converts every byte it is given, so the EIP-198 "excess data is
ignored" and right-padding rules are the caller's parse, not this
primitive's. Special cases follow the arithmetic: modulus 0 is a
failure (reduction mod 0 is undefined), exponent 0 answers
`1 mod modulus`.

## Backend

The system OpenSSL `libcrypto`, `BN_mod_exp` over `BIGNUM`s converted
at the boundary (`BN_bin2bn` in, `BN_bn2bin` out). Discovery via
`pkg-config` exactly as in `LeanHazmatSha256` (helpers duplicated per
§3.3). `BN_CTX` per call; no global state.

## Trust boundary

No pure-Lean reference exists at this size; the binding is an opaque
`@[extern]` boundary. The empirical trust assumption is *that the
linked OpenSSL libcrypto implements modular exponentiation correctly*,
validated by `LeanHazmatModexpTests`:

* **EIP-198 worked examples**, verbatim from the EIP text: the Fermat
  case (`3^(2^256 - 2^32 - 978) mod (2^256 - 2^32 - 977) = 1`, pinned
  in minimal form as `01`), the zero-base case (`0`), and the
  `3^65535 mod 2^255` parse (cross-checked against Python's `pow`).
* **Fixed modular-arithmetic cases**: zero exponent, modulus 1,
  a multi-byte result (`256^2 mod 65519 = 17`), leading-zero operands.
* **Negatives**: a zero modulus is a failure.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT.
