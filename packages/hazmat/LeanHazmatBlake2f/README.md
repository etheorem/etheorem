# LeanHazmatBlake2f

Lean 4 FFI binding for the **BLAKE2b `F` compression function**
(RFC 7693 section 3.2), the primitive behind the execution-layer
BLAKE2f precompile (EIP-152). Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) FFI crypto family.

## No vendored library

EIP-152 needs the raw rounds-parametrized `F(h, m, t0, t1, last,
rounds)`, arbitrary `rounds`, final-block flag, which no standard
BLAKE2 library exposes (libb2 / OpenSSL surface a blake2b *hash API*,
never the raw compression). The function is ~60 lines of RFC 7693, so
it lives in this package's `csrc/blake2f_shim.c`, written in-repo,
and the EIP-152 vectors pin it completely.

## Setup

Nothing to vendor: the shim lives in this repo and links no library.

```bash
lake build LeanHazmatBlake2f
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatBlake2f"
path = "…/packages/hazmat/LeanHazmatBlake2f"    # or a git source
```

## Usage

```lean
import LeanHazmatBlake2f
open LeanHazmat.Blake2f

-- The EIP-152 precompile input is `rounds(4, BE) ‖ h ‖ m ‖ t0(8, LE) ‖ t1(8, LE) ‖ f(1)`;
-- splitting it is the caller's job.
def out : ByteArray := blake2fCompress 12 h m 3 0 true   -- 64-byte state
```

## API (namespace `LeanHazmat.Blake2f`)

```lean
blake2fCompress : UInt32 → ByteArray → ByteArray → UInt64 → UInt64 → Bool → ByteArray
--                 rounds     h(64)      m(128)      t0       t1       last  → new state(64)
```

Empty `ByteArray` on a wrong `h` / `m` length. `native_decide` runs the
primitive at build time; the compiled-code caveat in
[`LeanHazmatSha256`'s README](../LeanHazmatSha256/README.md) applies.

## Tests

```bash
lake build LeanHazmatBlake2fTests    # EIP-152 vectors 4–8 (rounds 0, 1, 12, 0xffffffff) + sentinels
```

The `0xffffffff`-rounds case runs ~4 · 10⁹ rounds and dominates the
suite (~50 s); the suite is explicit-only for that reason.

## Trust boundary

The single assumption, that the in-repo shim implements RFC 7693's
`F` correctly, is validated by the EIP-152 vectors. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../../LICENSE).
