# LeanHazmatSha256: Architecture

The single-family trust-boundary record for `LeanHazmatSha256`. The
cross-family view it hangs under is
[`../../../hazmat-docs/ARCHITECTURE.md`](../../../hazmat-docs/ARCHITECTURE.md);
this file records *this* family's library, validation vectors, and the
one way it is special among the LeanHazmat families.

## What this package is

The FFI binding for **NIST FIPS 180-4 SHA-256**, wrapping the system
OpenSSL `libcrypto` behind three `@[extern] opaque` primitives in the
`LeanHazmat.Sha256` namespace:

| Primitive | Meaning | C symbol |
| --- | --- | --- |
| `LeanHazmat.Sha256.sha256Hash` | digest of one input | `lean_hazmat_sha256_hash` |
| `LeanHazmat.Sha256.sha256Combine` | digest of `left ++ right` | `lean_hazmat_sha256_combine` |
| `LeanHazmat.Sha256.sha256BatchCombine` | level-batched sibling combine | `lean_hazmat_sha256_batch_combine` |

These are the SSZ-merkleization hot path: `hash_tree_root`,
`compute_shuffled_index`, RANDAO mixing, and deposit Merkle proofs all
bottom out in SHA-256.

## Backend & why

OpenSSL `libcrypto`, discovered via `pkg-config` (cross-family
ARCHITECTURE.md §5/§6). It carries SHA-NI assembly, the fastest
option on the merkleization hot path, and is a *system* library, so
there is nothing to vendor and no vendored-source audit burden. This
is the one consensus family that needs **no** vendoring, which is why
PLAN.md sequences it first as the cross-package de-risk.

## The double life (cross-family ARCHITECTURE.md §9)

SHA-256 is the only primitive in the whole LeanHazmat surface with
*both* an FFI binding (here) **and** a kernel-reducible pure-Lean
reference (`LeanSha256`, a sibling package). The two are tied together
by named equivalence axioms, `sha256Hash_eq_spec`,
`sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec`, that live in
`SizzLean`, the one layer entitled to import both the FFI binding and
the spec. This package deliberately holds **only** the bindings: no
`Hasher` typeclass, no `Sha256` tag, no axiom, no spec reference.
Keeping the bindings spec-free is what lets the package ship
standalone as a mirror.

## Trust boundary

`@[extern] opaque` means the kernel never reduces a hash; the compiler
emits a direct call to the C symbol at runtime. The single empirical
trust assumption is **that the linked OpenSSL implements NIST FIPS
180-4 SHA-256**. It is validated two ways, both under this package's
own test lib (no external dependency):

* `LeanHazmatSha256Tests/Cavp.lean`: the full NIST CAVP byte-oriented
  suite (129 vectors) run against `sha256Hash` via `native_decide`.
* `LeanHazmatSha256Tests/Vectors.lean`: FIPS 180-4 §B anchors plus
  the `combine` / `batchCombine` cases CAVP doesn't cover.

The FFI ≡ pure-Lean equivalence (the evidence backing the SizzLean
axioms) is cross-checked in `SizzLeanTests` because it needs both this
package and `LeanSha256`.

Each `native_decide` call adds one `Lean.ofReduceBool` axiom; that is
acceptable on the KAT path and forbidden on the proof path (cross-family
ARCHITECTURE.md §10, CLAUDE.md "Proofs involving SSZ hashes").

## Validation vectors: pin

NIST CAVP CAVS 11.0 byte-oriented SHA-256 vectors
(`SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`), committed under `cavp/`
and regenerated into `LeanHazmatSha256Tests/Cavp.lean` by
`scripts/gen_cavp.py` (umbrella `just gen-cavp-hazmat`). They are
checked in so the build is hermetic (no network fetch). The Monte
Carlo vector set is deliberately excluded, it adds no qualitatively
new coverage over the byte-oriented vectors.

## Build & linking

`lakefile.lean` (procedural, required for C compilation and
`pkg-config` discovery, which the declarative TOML form cannot
express). The two shim `.c` files compile to one static archive
`libleanhazmat_sha256`. Lake links that archive into any precompiled
library or executable that transitively `require`s this package
(`SizzLean`, and downstream exes). The OpenSSL `-lcrypto` *flag* does
**not** propagate across `require` (PLAN.md Stage 0), so every
exe-hosting dependent, `SizzLean`, `LeanEthCS`, keeps its own
minimal pkg-config discovery; this package keeps its own for its test
lib.
