# LeanHazmatSecp256k1

Lean 4 FFI bindings for **secp256k1 ECDSA**, transaction sender
recovery and the ecRecover precompile's primitive (0x01). Wraps the
vendored [bitcoin-core/libsecp256k1](https://github.com/bitcoin-core/secp256k1).
Part of the [LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto
family.

## No address derivation here

The ecRecover precompile composes recovery with `keccak256` and a
truncation. Per the LeanHazmat "raw primitives, not assembled
precompiles" rule, this package exposes the raw recovered public key
and does **not** depend on `LeanHazmatKeccak`; the composition lives
with the caller.

## Setup

```bash
just hazmat-secp256k1-vendor    # libsecp256k1 v0.8.0
lake build LeanHazmatSecp256k1
```

## Usage

```lean
import LeanHazmatSecp256k1
open LeanHazmat.Secp256k1

-- v → recId in the caller: legacy v ∈ {27, 28} → v - 27;
-- EIP-155 v = chain_id*2 + 35 + parity → (v - 35) % 2
def pk : ByteArray := ecdsaRecover msgHash r s recId   -- 64-byte x ‖ y
def ok : Bool     := ecdsaVerify msgHash r s pk
```

## API (namespace `LeanHazmat.Secp256k1`)

```lean
ecdsaRecover : ByteArray → ByteArray → ByteArray → UInt32 → ByteArray
--              msgHash(32)   r(32)       s(32)       recId     → pk(64, x ‖ y, BE)
ecdsaVerify  : ByteArray → ByteArray → ByteArray → ByteArray → Bool
```

Empty `ByteArray` on any recovery failure. `false` on any verification
failure or malformed input. High-`s` signatures verify (the raw
primitive carries no anti-malleability policy).

## Trust boundary

No pure-Lean reference: the bindings are opaque `@[extern]` boundaries
over libsecp256k1, validated only against the published vectors. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatSecp256k1Tests    # EIP-155 example + second signature + negatives
```

## Linking (for consumers)

The family is self-contained: the vendored libsecp256k1 lands in the
`extern_lib` archive, and link arguments do not propagate across
`require` (packages/hazmat/docs/PLAN.md Stage 0). On a glibc older
than 2.34 the shim's `pthread_once` needs `-lpthread` at link time
(libc carries it on 2.34+, musl, and macOS); this package's own link
adds the flag, and a consumer's standalone executable does the same.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE). The
vendored libsecp256k1 is MIT.
