# LeanHazmatXmss

Lean 4 FFI bindings for RFC 8391 **XMSS-SHA2** one-time, hash-based signatures,
wrapping [XMSS/xmss-reference](https://github.com/XMSS/xmss-reference). Part of
the [LeanHazmat](../../hazmat-docs/ARCHITECTURE.md) FFI crypto family.

XMSS is **stateful**: a secret key signs `2^h` messages, and each signature
consumes a leaf index that must never be reused. Three parameter sets are
recognized (all n = 32, w = 16): XMSS-SHA2_10_256 / _16_256 / _20_256, selected
by a 4-byte big-endian OID. `sign` returns the updated secret key in its tail;
the caller threads it forward.

This is a reference-implementation wrapper for cross-validation and
experimenting, not a production signer. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the trust boundary.

## Setup

xmss-reference is vendored. Fetch it once, then build:

```bash
just hazmat-xmss-vendor    # commit 171ccbd
lake build LeanHazmatXmss
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatXmss"
path = "…/packages/LeanHazmatXmss"     # or a git source
```

## Usage

Generate a key from a seed, sign, verify:

```lean
import LeanHazmatXmss
open LeanHazmat.Xmss

def oid  : ByteArray := .mk #[0x00, 0x00, 0x00, 0x01]   -- XMSS-SHA2_10_256
-- Seed must be 3*n = 96 bytes. Draw it from a CSPRNG for any real key;
-- this fixed seed is for reproducible demos only.
def seed : ByteArray := .mk ((List.range 96).map (fun i => i.toUInt8)).toArray

def main : IO Unit := do
  let some (pk, sig, _) := paramSizes oid | IO.println "bad oid"
  let pkSk := keygenFromSeed oid seed
  let pubkey := pkSk.extract 0 pk
  let sk     := pkSk.extract pk pkSk.size
  let msg    := String.toUTF8 "message one"
  let other  := String.toUTF8 "message two"
  let sigNewSk := sign sk msg
  let signature := sigNewSk.extract 0 sig
  -- newSk MUST replace sk for the next sign; the index has advanced.
  let newSk := sigNewSk.extract sig sigNewSk.size
  IO.println s!"valid:    {verify pubkey signature msg}"     -- true
  IO.println s!"tampered: {verify pubkey signature other}"   -- false
```

### Running and checking

These are `@[extern]` native primitives, so they run as **compiled** code. Call
them from an executable (`lake exe …`) or a `def`/`IO` action your app compiles.
To assert results at build time, use `native_decide` (this is how the test
suite runs them):

```lean
example : verify pubkey signature msg = true := by native_decide
```

Plain `#eval` in the interpreter cannot execute opaque `@[extern]` functions.

### Statefulness and error handling

`sign` returns `sig ++ new_sk`. Re-using an old secret key (signing twice under
the same leaf index) breaks XMSS one-time security; always thread `new_sk`
forward. `keygenFromSeed` and `sign` return the **empty `ByteArray`** on invalid
input (unrecognized OID, wrong seed or key length), no exception. `verify`
returns `Bool`, with `false` covering both "does not verify" and invalid input.
`paramSizes` returns `none` for an unrecognized OID.

## API (namespace `LeanHazmat.Xmss`)

```lean
paramSizes     : ByteArray → Option (Nat × Nat × Nat)   -- oid → (pk, sig, sk) sizes
keygenFromSeed : ByteArray → ByteArray → ByteArray      -- oid, seed(3n) → pk ++ sk
sign           : ByteArray → ByteArray → ByteArray      -- sk, msg → sig ++ new_sk
verify         : ByteArray → ByteArray → ByteArray → Bool  -- pk, sig, msg
```

## Trust boundary

Each binding is an opaque `@[extern]` over xmss-reference, no pure-Lean
reference. RFC 8391 ships no official vectors, so the tests cross-check against
xmss-reference's own `test/vectors.c` reference digests (same fixed seed),
validating the shim against upstream's driver. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatXmssTests     # size / keygen / signing KATs + round-trip
```

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../LICENSE).
