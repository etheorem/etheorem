# LeanHazmatModexp

Lean 4 FFI binding for **modular exponentiation**, the primitive
behind the execution-layer modexp precompile (0x05, EIP-198; gas via
EIP-2565 / 7883). Wraps the system OpenSSL `libcrypto` BIGNUM API
(`BN_mod_exp`). Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto family.

## What stays with the caller

Per the LeanHazmat "raw primitives, not assembled precompiles" rule:
the EIP-198 length-prefixed input parse, the excess-data and
right-padding rules, the gas schedule, and the output left-padding to
the modulus length. The primitive is the bare exponentiation over
exact big-endian byte strings.

## Usage

```lean
import LeanHazmatModexp
open LeanHazmat.Modexp

def r : ByteArray := modExp base exponent modulus
-- minimal big-endian result (no leading zeros; zero is the single `00`).
-- Left-pad to the modulus length yourself for the precompile output.
```

## API (namespace `LeanHazmat.Modexp`)

```lean
modExp : ByteArray → ByteArray → ByteArray → ByteArray
--        base(BE)     exponent(BE)   modulus(BE)   → minimal BE result
```

Empty `ByteArray` on failure: an input above `INT_MAX` bytes (the shim
rejects it rather than truncating into `BN_bin2bn`'s `int` length), a
zero modulus, or a BIGNUM error.
Exponent 0 answers `1 mod modulus` (so modulus 1 answers `00`).

## Trust boundary

No pure-Lean reference at this size: the binding is an opaque
`@[extern]` boundary over OpenSSL, validated only against the EIP-198
examples and fixed modular-arithmetic cases. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatModexpTests    # EIP-198 worked examples + fixed cases + negatives
```

## Linking (for consumers)

libcrypto is a *system* library, and link arguments do not propagate
across `require` (packages/hazmat/docs/PLAN.md Stage 0). Any executable that
transitively links this family must supply the libcrypto flags itself
(`pkg-config --libs libcrypto`, or the hardcoded `-lcrypto` plus the
platform `-L` paths, as `EthCLSpecs` does). This package's own test
lib carries its own discovery.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
