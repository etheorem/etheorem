# LeanHazmatP256

Lean 4 FFI binding for **NIST P-256 (secp256r1) ECDSA verification**,
the primitive behind the execution-layer `P256VERIFY` precompile
(EIP-7951, Fusaka; RIP-7212 compatible). Wraps the system OpenSSL
`libcrypto`. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto family.

## Usage

```lean
import LeanHazmatP256
open LeanHazmat.P256

def ok : Bool := p256Verify msgHash r s qx qy
-- all five arguments 32-byte big-endian; the precompile's 160-byte
-- input layout (hash ‖ r ‖ s ‖ x ‖ y) and its `0x…01` output are the
-- caller's composition.
```

High-`s` signatures verify: EIP-7951 checks exactly the ECDSA
equation, no anti-malleability policy (its published suite marks a
malleability case valid).

## API (namespace `LeanHazmat.P256`)

```lean
p256Verify : ByteArray → ByteArray → ByteArray → ByteArray → ByteArray → Bool
--            msgHash(32)   r(32)       s(32)       qx(32)      qy(32)
```

`false` covers "does not verify" and every malformed input (wrong
lengths, coordinates ≥ p, a point off the curve, `r` or `s` zero),
never an error.

## Trust boundary

No pure-Lean reference: the binding is an opaque `@[extern]` boundary
over OpenSSL, validated only against the official EIP-7951 vectors.
See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatP256Tests    # EIP-7951 / Wycheproof anchors + negatives
```

## Linking (for consumers)

libcrypto is a *system* library, and link arguments do not propagate
across `require` (packages/hazmat/docs/PLAN.md Stage 0). Any executable that
transitively links this family must supply the libcrypto flags itself
(`pkg-config --libs libcrypto`, or the hardcoded `-lcrypto` plus the
platform `-L` paths, as `EthCLSpecs` does). This package's own test
lib carries its own discovery. On a glibc older than 2.34 the shim's
`pthread_once` also needs `-lpthread` at link time (libc carries it on
2.34+, musl, and macOS); this package's own link adds the flag.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
