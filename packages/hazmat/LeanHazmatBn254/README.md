# LeanHazmatBn254

Lean 4 FFI bindings for the **alt_bn128 (BN254) curve**, the
EIP-196 add/mul precompiles, the EIP-197 / 1108 G2 operations and
pairing check. Wraps the vendored [herumi/mcl](https://github.com/herumi/mcl).
Part of the [LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto
family. The one LeanHazmat family with a **C++** build.

## Setup

```bash
just hazmat-bn254-vendor    # mcl v4.10
lake build LeanHazmatBn254
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatBn254"
path = "…/packages/hazmat/LeanHazmatBn254"     # or a git source
```

No `-lstdc++` needed anywhere: mcl compiles with the C++ runtime
switched off (exceptions, RTTI, threadsafe statics, string, CSPRNG,
Xbyak), so the archive references only libc and libgcc (see
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)).

## Usage

The EIP-197 pairing check composes the three pairing primitives in the
caller:

```lean
import LeanHazmatBn254
open LeanHazmat.Bn254

def pairingCheck (pairs : Array (ByteArray × ByteArray)) : Bool :=
  gtIsOne (finalExp (millerLoopVec (pairs.map (·.1)) (pairs.map (·.2))))

def sum : ByteArray := g1Add p q           -- EIP-196 ECADD, 64-byte points
def mul : ByteArray := g1Mul p scalar      -- EIP-196 ECMUL, 32-byte scalar
def g2  : ByteArray := g2Add u v           -- EIP-197, 128-byte points
```

## API (namespace `LeanHazmat.Bn254`)

```lean
g1Add, g1Mul   : ByteArray → ByteArray → ByteArray   -- EIP-196
g2Add, g2Mul   : ByteArray → ByteArray → ByteArray   -- EIP-197 G2
millerLoopVec  : Array ByteArray → Array ByteArray → ByteArray  -- → GT(384)
finalExp       : ByteArray → ByteArray               -- GT → GT
gtIsOne        : ByteArray → Bool
```

Encodings are the EIPs' own: 32-byte big-endian fields, G1 = `x ‖ y`
(64), G2 = `(xₐ ‖ x_b) ‖ (yₐ ‖ y_b)` with the imaginary half first
(128), infinity = all zeros, scalars reduced mod the group order.
Empty `ByteArray` on any invalid input.

## Trust boundary

No pure-Lean reference: the bindings are opaque `@[extern]` boundaries
over mcl, validated only against the published EIP-196/197 vectors.
See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatBn254Tests    # py_ecc ground-truth anchors + pairing checks + negatives
```

## Linking (for consumers)

The family is self-contained: the compiled mcl lands in the
`extern_lib` archive with its C++ runtime compiled out, so no
`-lstdc++` is ever needed. Link arguments do not propagate across
`require` (packages/hazmat/docs/PLAN.md Stage 0). On a glibc older
than 2.34 the shim's `pthread_once` needs `-lpthread` at link time
(libc carries it on 2.34+, musl, and macOS); this package's own link
adds the flag, and a consumer's standalone executable does the same.

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE). The
vendored mcl is BSD-3-Clause (modified).
