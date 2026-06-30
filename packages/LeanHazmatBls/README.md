# LeanHazmatBls

Lean 4 FFI bindings for Ethereum consensus BLS12-381 signatures
(minimal-pubkey-size, ciphersuite
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`), wrapping
[supranational/blst](https://github.com/supranational/blst). Part of the
[LeanHazmat](../../hazmat-docs/ARCHITECTURE.md) FFI crypto family.

Public keys are 48-byte compressed G1 points, signatures 96-byte
compressed G2 points, secret keys 32-byte big-endian scalars.

## Setup

blst is vendored. Fetch it once, then build:

```bash
just hazmat-bls-vendor    # blst v0.3.16
lake build LeanHazmatBls
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatBls"
path = "…/packages/LeanHazmatBls"     # or a git source
```

## Usage

Derive a public key, sign, verify:

```lean
import LeanHazmatBls
open LeanHazmat.Bls

def sk  : ByteArray := ByteArray.mk ((Array.replicate 31 0).push 3)  -- 32-byte secret key
def pk  : ByteArray := skToPk sk                                     -- 48-byte public key
def msg : ByteArray := String.toUTF8 "attestation data"
def sig : ByteArray := sign sk msg                                   -- 96-byte signature

def main : IO Unit := do
  IO.println s!"valid:     {verify pk msg sig}"                       -- true
  IO.println s!"tampered:  {verify pk (String.toUTF8 "other") sig}"   -- false
  IO.println s!"key valid: {keyValidate pk}"                          -- true
```

Aggregate signatures over the **same** message (e.g. a sync committee),
then verify against the set of public keys:

```lean
def sk2 : ByteArray := ByteArray.mk ((Array.replicate 31 0).push 5)
def pk2 : ByteArray := skToPk sk2

def aggSig : ByteArray := aggregate #[sign sk msg, sign sk2 msg]

def committeeOk : Bool := fastAggregateVerify #[pk, pk2] msg aggSig
```

Aggregate over **distinct** messages → `aggregateVerify`:

```lean
def msg2 : ByteArray := String.toUTF8 "other data"

def aggOk : Bool :=
  aggregateVerify #[pk, pk2] #[msg, msg2] (aggregate #[sign sk msg, sign sk2 msg2])
```

### Running and checking

These are `@[extern]` native primitives, so they run as **compiled** code.
Call them from an executable (`lake exe …`) or a `def`/`IO` action your app
compiles. To assert results at build time, use `native_decide` (this is how
the test suite runs them):

```lean
example : verify pk msg sig = true := by native_decide
```

Plain `#eval` in the interpreter cannot execute opaque `@[extern]` functions.

### Error handling

Point-returning operations (`sign`, `skToPk`, `aggregate`,
`ethAggregatePubkeys`) return the **empty `ByteArray`** on invalid input
(wrong length, bad encoding, empty list), no exception. Verification
returns `Bool`; `false` covers "does not verify" and invalid input.

## API (namespace `LeanHazmat.Bls`)

```lean
sign        : ByteArray → ByteArray → ByteArray            -- sk, msg → sig(96)
skToPk      : ByteArray → ByteArray                        -- sk → pubkey(48)
verify      : ByteArray → ByteArray → ByteArray → Bool     -- pk, msg, sig
keyValidate : ByteArray → Bool                             -- pubkey valid?
aggregate            : Array ByteArray → ByteArray         -- sigs → sig
ethAggregatePubkeys  : Array ByteArray → ByteArray         -- pubkeys → pubkey
aggregateVerify        : Array ByteArray → Array ByteArray → ByteArray → Bool  -- pks, msgs, sig
fastAggregateVerify    : Array ByteArray → ByteArray → ByteArray → Bool        -- pks, msg, sig
ethFastAggregateVerify : Array ByteArray → ByteArray → ByteArray → Bool        -- + empty-list/∞ case
```

## Trust boundary

Each binding is an opaque `@[extern]` over blst, no pure-Lean reference,
validated only against the consensus-spec BLS vectors. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatBlsTests     # consensus-spec anchors + aggregate round-trips
```

## License

LGPL-3.0-only: see the umbrella [`LICENSE`](../../LICENSE).
