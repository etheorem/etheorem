import LeanHazmatModexp.Ffi

/-!
# `LeanHazmatModexp`: library root

FFI binding for **modular exponentiation**, the primitive behind the
execution-layer modexp precompile (0x05, EIP-198; gas via EIP-2565 /
7883), wrapping the system OpenSSL `libcrypto` BIGNUM API behind
`@[extern]` under the `LeanHazmat.Modexp` brand namespace. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) crypto family.

`import LeanHazmatModexp` brings the public surface into scope:

* `modExp`: `(base ** exponent) mod modulus` over big-endian byte
  strings, minimal big-endian result.

See [`LeanHazmatModexp/Ffi.lean`](LeanHazmatModexp/Ffi.lean) for the
binding and its trust assumption, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's trust
boundary (library, encodings, validation vectors).

## What stays with the caller

Per the LeanHazmat "raw primitives, not assembled precompiles" rule
(packages/hazmat/docs/ARCHITECTURE.md §4): the EIP-198 length-prefixed input
parse, the excess-data and right-padding rules, the gas schedule, and
the output left-padding to the modulus length. The primitive is the
bare exponentiation.

No vendoring and no C build beyond the shim: libcrypto is a system
library discovered with `pkg-config`, exactly as in
`LeanHazmatSha256`.

## Trust boundary

No pure-Lean reference exists; the binding is an opaque `@[extern]`
boundary validated only against the EIP-198 examples and fixed
modular-arithmetic cases (`LeanHazmatModexpTests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatModexpTests`); the default `lake build` skips them and they
fire via `lake build LeanHazmatModexpTests`.
-/
