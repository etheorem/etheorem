# LeanHazmatBls: Architecture

The single-family trust-boundary record for `LeanHazmatBls`. The
cross-family view is
[`../../../hazmat-docs/ARCHITECTURE.md`](../../../hazmat-docs/ARCHITECTURE.md);
this file records *this* family's library, version pin, validation
vectors, and build shape.

## What this package is

FFI bindings for **Ethereum consensus-layer BLS12-381 signatures**,
minimal-pubkey-size scheme, ciphersuite
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_` (the proof-of-possession
suite). Public keys are 48-byte compressed **G1** points, signatures
96-byte compressed **G2** points, secret keys 32-byte big-endian
scalars. The surface (all in namespace `LeanHazmat.Bls`):

| Primitive | C symbol |
| --- | --- |
| `sign` | `lean_hazmat_bls_sign` |
| `skToPk` | `lean_hazmat_bls_sk_to_pk` |
| `verify` | `lean_hazmat_bls_verify` |
| `keyValidate` | `lean_hazmat_bls_key_validate` |
| `aggregate` | `lean_hazmat_bls_aggregate` |
| `ethAggregatePubkeys` | `lean_hazmat_bls_eth_aggregate_pubkeys` |
| `aggregateVerify` | `lean_hazmat_bls_aggregate_verify` |
| `fastAggregateVerify` | `lean_hazmat_bls_fast_aggregate_verify` |
| `ethFastAggregateVerify` | `lean_hazmat_bls_eth_fast_aggregate_verify` |

These are the raw signature primitives behind attestations, block
signatures, sync committees, deposits, and exits. Protocol composition
(which message to sign, which committee's keys to aggregate) is the
caller's concern (cross-family ARCHITECTURE.md §4).

## Backend & pin

**supranational/blst**, the field reference implementation, **vendored**
at tag **`v0.3.16`** (commit `e7f90de551e8df682f3cc99067d204d8b90d27ad`).
This is exactly the blst rev that `c-kzg-4844` `v2.1.7` pins as its own
submodule, so `LeanHazmatBls` is the **single blst owner**: `LeanHazmatKzg`
builds c-kzg against *this* archive rather than vendoring a second copy
(cross-family ARCHITECTURE.md §4). Bumping this pin requires re-checking
the c-kzg rev in lockstep.

`just vendor-bls` shallow-clones the tag into a gitignored `vendor/blst/`;
the build is offline thereafter. Never a git submodule (cross-family
ARCHITECTURE.md §6).

## Build shape

blst's "build" is two compiler invocations over its own amalgamation
(`src/server.c` includes the whole C tree; `build/assembly.S` dispatches
the pre-generated per-platform assembly) plus an `ar`. The lakefile
compiles those two objects directly as Lake `buildO` targets (the plan's
sanctioned "server.c amalgamation" path), with flags mirroring blst's
default `CFLAGS` minus `-Werror`, plus **`-D__BLST_PORTABLE__`**, which
compiles both ADX and non-ADX paths behind a runtime CPUID dispatch, so
the archive runs on any x86-64 host. For that reason the package adds no
`-march=native`. The shim and the two blst objects archive into one
`extern_lib` (`libleanhazmat_bls`) that propagates to dependents.

## Trust boundary

Unlike SHA-256, BLS has **no** kernel-reducible pure-Lean reference: each
binding is an opaque `@[extern]` boundary. The single empirical trust
assumption is **that blst implements BLS12-381 and this ciphersuite
correctly**. It is validated only by `LeanHazmatBlsTests`, which runs:

* **Ground-truth anchors** from `ethereum/consensus-spec-tests` v1.5.0
  (`general/phase0/bls`): a `sign` vector matched byte-for-byte and a
  `verify` valid-case accepted.
* **Self-contained round-trips**: `skToPk` → `sign` → `aggregate` →
  `fastAggregateVerify` / `aggregateVerify`, plus the consensus
  `eth_fast_aggregate_verify` empty-list / infinity-signature case.

Each gate is a `native_decide` (one `Lean.ofReduceBool` axiom per case),
the acceptable regime for an FFI KAT.

## Validation vectors: pin

`ethereum/consensus-spec-tests` **v1.5.0**, `general` config, `bls` suite.
The anchor vectors are hard-coded into `LeanHazmatBlsTests/Vectors.lean`
(keeping the build hermetic); bump them in lockstep when raising spec
coverage (per the project's "pin vectors to the latest release" rule).
