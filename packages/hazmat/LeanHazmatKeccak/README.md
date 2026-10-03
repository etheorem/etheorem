# LeanHazmatKeccak

Lean 4 FFI binding for **Keccak-256**, the execution layer's most-used
primitive: the `KECCAK256` opcode (0x20), address derivation, storage
slot hashing, the MPT trie, and RLP hashing. Wraps the vendored
[coruus/keccak-tiny](https://github.com/coruus/keccak-tiny) single-file
implementation. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto family.

## Keccak-256, not SHA3-256

Ethereum's digest uses the **original Keccak padding** (`0x01`), not
FIPS 202's `0x06`. The two differ on every input, so no SHA3
implementation substitutes, the reason OpenSSL SHA3 was rejected. The
shim calls keccak-tiny's delimiter-parametrized sponge with rate 136
and delimiter `0x01`.

## Setup

```bash
just hazmat-keccak-vendor    # keccak-tiny, pinned rev 64b66475…
lake build LeanHazmatKeccak
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatKeccak"
path = "…/packages/hazmat/LeanHazmatKeccak"     # or a git source
```

## Usage

```lean
import LeanHazmatKeccak
open LeanHazmat.Keccak

def digest : ByteArray := keccak256 (String.toUTF8 "abc")
-- 4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

-- Address derivation is the *caller's* composition (the raw-primitives
-- rule): `addr = (keccak256 pubkey)[12:32]`, where `pubkey` is the
-- 64-byte `x ‖ y` key, exactly what `LeanHazmatSecp256k1.ecdsaRecover`
-- returns.
def pubkey : ByteArray := ecdsaRecover msgHash r s recId   -- 64 bytes
def addr : ByteArray := (keccak256 pubkey).extract 12 32
```

## API (namespace `LeanHazmat.Keccak`)

```lean
keccak256 : ByteArray → ByteArray   -- 32-byte digest, any input length
```

## Trust boundary

No pure-Lean reference: the binding is an opaque `@[extern]` boundary
over keccak-tiny, validated only against the published vectors. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatKeccakTests    # EVM constants + published vectors + address derivation
```

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE). The
vendored keccak-tiny is CC0.
