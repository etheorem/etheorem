# LeanHazmatSecp256k1: Architecture

The single-family trust-boundary record for `LeanHazmatSecp256k1`. The
cross-family view is
[`../../docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md);
this file records *this* family's library, pin, build shape, and
validation vectors.

## What this package is

Raw secp256k1 ECDSA recovery and verification in namespace
`LeanHazmat.Secp256k1`:

| Primitive | C symbol |
| --- | --- |
| `ecdsaRecover` | `lean_hazmat_secp256k1_ecdsa_recover` |
| `ecdsaVerify` | `lean_hazmat_secp256k1_ecdsa_verify` |

Encodings: message hash and scalars are 32-byte big-endian; the public
key is the 64-byte uncompressed `x ‖ y` (the EL's point encoding; the
shim does the conversion); `recId` is
libsecp256k1's recovery id (bit 0 = y parity, bit 1 = r-overflow), with
the `v` → `recId` mapping documented on the binding.

## Backend & pin

**bitcoin-core libsecp256k1**, tag **`v0.8.0`**, vendored (`just
hazmat-secp256k1-vendor`). The plan's "system lib if available" branch
is unrealized: one pinned source of truth today; a pkg-config branch is
a later refinement if a consumer wants it.

## Build shape

The library's own amalgamation (`src/secp256k1.c`, transitively
including the whole tree) plus its two committed ecmult table units
(`src/precomputed_ecmult.c`, `src/precomputed_ecmult_gen.c`, the
`secp256k1_pre_g` / `secp256k1_ecmult_gen_prec_table` symbols the core
references), and the Lean shim. One define matters:

* `-DENABLE_MODULE_RECOVERY`, the recovery module is still a
  compile-time module gate in v0.8.0; without it
  `secp256k1_ecdsa_recover` does not exist.

`SECP256K1_BUILD` is deliberately not passed: the amalgamation defines
it itself (`src/secp256k1.c`, before it includes the public header),
and a command-line copy only produces a
`"SECP256K1_BUILD" redefined` warning. The shim compiles as a plain
consumer of the header, also without the define.

Context: `secp256k1_context_static` (recovery and verification need no
precomputed signing tables and no randomization; thread-safe, free),
gated on one `secp256k1_selftest` call (the library recommends it for
the static context; it aborts on failure, so returning normally means
the run passed).

## High-s policy (recorded)

`secp256k1_ecdsa_verify` rejects `s > n/2` (Bitcoin's
anti-malleability rule). The execution layer has no such policy for the
raw primitive, `(r, s)` and `(r, n - s)` have identical validity, so
`ecdsaVerify` parses the compact pair and lets the library's own
`secp256k1_ecdsa_signature_normalize` fold a high `s` to its low form
before verification. Recovery needs no normalization.

## Trust boundary

No pure-Lean reference exists; each binding is an opaque `@[extern]`
boundary. The empirical trust assumption is *that the vendored
libsecp256k1 implements ECDSA recovery and verification correctly*,
validated only by `LeanHazmatSecp256k1Tests`:

* **EIP-155 ground truth**: the example transaction the EIP publishes
  (signing hash, `v = 37`, `(r, s)`, and the private key) recovers its
  published public key byte-for-byte; `ecdsaVerify` accepts the triple.
  The derived sender address is checked in `LeanHazmatKeccakTests`.
* **A second deterministic signature** over a different hash recovers
  and verifies against the same pinned key.
* **Negatives**: tampered `s` recovers a different key (recovery alone
  does not detect tampering, that is what verify is for), out-of-range
  `r` and `recId > 3` fail, wrong parity recovers the mirrored key.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per
case), the acceptable regime for an FFI KAT.

## Validation vectors: pin

EIP-155's own example (fetched from `ethereum/EIPs` at authoring time)
plus a deterministic self-generated signature; both hard-coded into
`LeanHazmatSecp256k1Tests/Vectors.lean`, keeping the build hermetic.
