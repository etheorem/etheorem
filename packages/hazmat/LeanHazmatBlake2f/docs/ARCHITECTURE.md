# LeanHazmatBlake2f: Architecture

The single-family trust-boundary record for `LeanHazmatBlake2f`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md);
this file records *this* family's backend, build shape, and validation
vectors.

## What this package is

The raw BLAKE2b `F` compression (RFC 7693 section 3.2) behind the
execution-layer BLAKE2f precompile (EIP-152), in namespace
`LeanHazmat.Blake2f`:

| Primitive | C symbol |
| --- | --- |
| `blake2fCompress` | `lean_hazmat_blake2f_compress` |

Arguments: `rounds : UInt32`, `h : ByteArray` (64), `m : ByteArray`
(128), `t0 t1 : UInt64`, `last : Bool`; result: the updated 64-byte
state. The ten-round sigma schedule cycles, so any `rounds` count is
valid. Precompile composition (the 213-byte input parse, gas, the
`0x…00` failure encoding) is the caller's concern.

## Backend: none, in-repo shim

EIP-152 needs raw `F` (arbitrary `rounds`, the final-block flag);
BLAKE2 libraries expose only a hash API. The function is ~60 lines of
RFC 7693, so `csrc/blake2f_shim.c` writes it directly: the `G` mixing
function, the sigma table (indexed `sigma[r % 10]`), and the XOR
feed-forward. There is no `vendor/` tree and no fetch recipe. The
whole native surface is this one file, built as a single `buildO`
target into the `libleanhazmat_blake2f` `extern_lib`. No
`-march=native`: the shim is portable scalar code and the precompile
is not on a hot path.

## Trust boundary

No pure-Lean reference and no third-party library: the single
empirical assumption is *that the in-repo shim implements RFC 7693's
`F` correctly*, validated only by `LeanHazmatBlake2fTests`:

* **EIP-152 test vectors 4–8**, byte-for-byte: rounds 0, 1, 12, and
  `0xffffffff`, both final-block flags. Together they pin the round
  schedule, the sigma indexing, the counter XOR, and the feed-forward.
* **Length sentinels**: wrong-length `h` / `m` return the empty
  `ByteArray`.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT. The `0xffffffff`-rounds
case dominates the suite (~50 s), which is why the test lib is
explicit-only.

## Validation vectors: pin

The EIP-152 specification's own test vectors (fetched from
`ethereum/EIPs` at authoring time and hard-coded into
`LeanHazmatBlake2fTests/Vectors.lean`, keeping the build hermetic).
