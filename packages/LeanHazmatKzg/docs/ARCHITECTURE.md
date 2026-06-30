# LeanHazmatKzg: Architecture

The single-family trust-boundary record for `LeanHazmatKzg`. The
cross-family view is
[`../../../hazmat-docs/ARCHITECTURE.md`](../../../hazmat-docs/ARCHITECTURE.md);
this file records *this* family's library, version pins, validation
vectors, and the build wiring that makes it share blst with
`LeanHazmatBls`.

## What this package is

FFI bindings for **Ethereum consensus-layer KZG / polynomial
commitments**, EIP-4844 blobs (Deneb) and EIP-7594 / Fulu PeerDAS cells,
wrapping ethereum/c-kzg-4844. Surface (all in namespace `LeanHazmat.Kzg`):

| Primitive | Spec |
| --- | --- |
| `blobToKzgCommitment`, `computeKzgProof`, `computeBlobKzgProof` | EIP-4844 |
| `verifyKzgProof`, `verifyBlobKzgProof`, `verifyBlobKzgProofBatch` | EIP-4844 |
| `computeCellsAndKzgProofs`, `verifyCellKzgProofBatch`, `recoverCellsAndKzgProofs` | EIP-7594 (Fulu) |

Used for blob-sidecar verification, gossip validation, and data
availability sampling.

## Backend & pins

**ethereum/c-kzg-4844**, the consensus reference, **vendored** at tag
**`v2.1.7`** (commit `9f4bcc83…`). It is built on **blst**, which it pins
(as a submodule) at exactly **`v0.3.16`** (`e7f90de5…`), the
`LeanHazmatBls` pin. So this package does **not** vendor its own blst:
`just hazmat-kzg-vendor` clones c-kzg *without* `--recursive`, and the build
compiles c-kzg against `LeanHazmatBls`'s blst (cross-family
ARCHITECTURE.md §4). Bumping either pin requires re-checking the other in
lockstep (`git ls-tree <c-kzg tag> blst` gives the expected blst rev).

## Build wiring

The verified shape:

* Compile c-kzg's own single-TU amalgamation `src/ckzg.c` (it `#include`s
  every other `.c`) with `-I vendor/c-kzg-4844/src` and `-I` blst's
  `bindings/` (from the sibling Bls package). No `-D` flags.
* Compile the Lean shim `csrc/kzg_shim.c` the same way.
* Embed the trusted setup with `.incbin` (`csrc/trusted_setup_incbin.S`),
  the bytes copied from `data/trusted_setup.txt` at assemble time. No
  runtime file lookup happens. The C shim loads it once at library load via
  `fmemopen` + `load_trusted_setup_file` (`precompute = 0`, verify-only).

### Sharing one blst across the package boundary

blst is the single owner's (`LeanHazmatBls`). Two link facts make this
work without duplicating it:

* **Static archive (final executables).** This package's `extern_lib`
  (`libleanhazmat_kzg`) holds only `ckzg.o` + `kzg_shim.o` +
  `trusted_setup.o`, **no blst**. At the final exe link, `blst_*`
  resolves from `LeanHazmatBls`'s propagated archive, so there is exactly
  one blst copy and no duplicate symbols.
* **Shared lib (precompiled module / `native_decide`).** The precompiled
  module's `.so` would otherwise have undefined `blst_*` at load. The
  package's `moreLinkArgs` give it `-l:libleanhazmat_bls.so` +
  `-L`/`-rpath` into Bls's build lib, so the loader pulls Bls's shared lib
  and resolves `blst_*`, mirroring how `LeanHazmatSha256`'s `.so` gains
  `NEEDED libcrypto.so.3`. That link reference is invisible to Lake's
  scheduler, so the `extern_lib` folds Bls's shared-lib build into its own
  dependency trace (`Job.zipWith` over `findExternLib? `libleanhazmat_bls`)
  to keep clean parallel builds from racing ahead of Bls's `.so`.

## Trust boundary

KZG has **no** pure-Lean reference; each binding is an opaque `@[extern]`
boundary. The empirical trust assumption, *that c-kzg-4844 (+ blst)
implements EIP-4844 / EIP-7594 correctly*, is validated only by
`LeanHazmatKzgTests`, which runs self-contained round-trips via
`native_decide`:

* EIP-4844: commit → blob-proof → verify (+ corrupted-proof/commitment
  negatives), the point-evaluation proof, and the batch verifier.
* Fulu: `computeCellsAndKzgProofs` → `verifyCellKzgProofBatch` over all
  128 cells (+ a tampered-cell negative), and an erasure-recovery
  round-trip reconstructing all 128 cells from a 64-cell subset.

These also exercise loading the embedded trusted setup.

## Validation vectors: pin

c-kzg-4844 v2.1.7 ships the consensus-spec KZG test vectors under
`tests/`. The current gate uses self-contained round-trips (no vendored
vector files committed); raising coverage to the published case files is
a follow-up, pinned in lockstep with the c-kzg tag.
