# LeanHazmatSha256

Lean 4 FFI bindings for NIST FIPS 180-4 SHA-256, wrapping the system
OpenSSL `libcrypto`. Part of the
[LeanHazmat](../../hazmat-docs/ARCHITECTURE.md) FFI crypto family, the FFI
counterpart to the pure-Lean reference [`LeanSha256`](../LeanSha256).

## Setup

Only the system OpenSSL `libcrypto` (3.x), discovered via `pkg-config`. No
vendoring.

```bash
# Debian/Ubuntu:  sudo apt install libssl-dev pkg-config
# Fedora:         sudo dnf install openssl-devel pkgconf-pkg-config
# macOS:          brew install openssl@3 pkg-config
lake build LeanHazmatSha256
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatSha256"
path = "…/packages/LeanHazmatSha256"     # or a git source
```

## Usage

```lean
import LeanHazmatSha256
open LeanHazmat.Sha256

-- 32-byte digest of arbitrary input.
def digest : ByteArray := sha256Hash (String.toUTF8 "abc")

-- The SSZ inner-Merkle step: SHA-256(left ++ right) without concatenating.
def zero : ByteArray := ByteArray.mk (Array.replicate 32 0)
def node : ByteArray := sha256Combine zero zero               -- = SSZ ZERO_HASHES[1]

-- Level-batched: output[i] = SHA-256(lefts[i] ++ rights[i]).
def level : Array ByteArray := sha256BatchCombine #[zero, zero] #[zero, zero]

def main : IO Unit :=
  IO.println s!"SHA-256(\"abc\") = {digest.toList}"
```

### Running and checking

These are `@[extern]` native primitives, so they run as **compiled** code.
Call them from an executable (`lake exe …`) or a `def`/`IO` action your app
compiles. To assert results at build time, use `native_decide` (this is how
the test suite runs them):

```lean
-- SHA-256("") = e3b0c442… (FIPS 180-4 §B.0)
example :
    sha256Hash ByteArray.empty
      = ByteArray.mk #[0xe3,0xb0,0xc4,0x42,0x98,0xfc,0x1c,0x14,
                       0x9a,0xfb,0xf4,0xc8,0x99,0x6f,0xb9,0x24,
                       0x27,0xae,0x41,0xe4,0x64,0x9b,0x93,0x4c,
                       0xa4,0x95,0x99,0x1b,0x78,0x52,0xb8,0x55] := by native_decide
```

Plain `#eval` in the interpreter cannot execute opaque `@[extern]` functions.

## API (namespace `LeanHazmat.Sha256`)

```lean
sha256Hash         : ByteArray → ByteArray                              -- digest of one input
sha256Combine      : ByteArray → ByteArray → ByteArray                  -- SHA-256(left ++ right)
sha256BatchCombine : Array ByteArray → Array ByteArray → Array ByteArray -- pointwise combine
```

Every result is 32 bytes.

## Trust boundary

`@[extern] opaque` over OpenSSL. The kernel never reduces a hash; the
single assumption is that OpenSSL implements SHA-256, validated by the
byte-level NIST CAVP KAT in `LeanHazmatSha256Tests`. SHA-256 is special
among LeanHazmat families: it *also* has a kernel-reducible pure-Lean spec
(`LeanSha256`), and `SizzLean` ties the two together with named
equivalence axioms. See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatSha256Tests     # full NIST CAVP (129 vectors) + combine/batch anchors
```

## License

LGPL-3.0-only, see the umbrella [`LICENSE`](../../LICENSE).
