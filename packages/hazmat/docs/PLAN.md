# LeanHazmat: Implementation Plan

This document sequences the work that
[`ARCHITECTURE.md`](ARCHITECTURE.md) describes, the plan for the
LeanHazmat package family. Each stage has a goal, the concrete
deliverables it ships, an acceptance criterion (one observable that
says the stage is done), and notes on dependencies, parallelism, and
risk.

The phases run **consensus first, execution second**: Phase 1 delivers
the three consensus families (SHA-256, BLS, KZG) and their aggregator;
Phase 2 delivers the execution-layer families and completes the
aggregator surface. SHA-256 goes first because it is the one family
that needs *no* vendoring, so it de-risks the whole per-family
machinery before any native library has to be vendored and compiled. That machinery covers a new package, `SizzLean`
consuming it across the package boundary, link-arg behaviour, and the
equivalence-axiom split. Both phases are complete (see the status snapshot
at the bottom and the per-stage records).

Every stage adds an independent Lake package under `packages/`. A package
is "done" when it builds green from the umbrella, its byte-level KAT
(Known-Answer-Test) gate passes, and it is registered in the umbrella
`lakefile.toml`. **Mirroring a family to its own repo stays an optional
later step** per [`ARCHITECTURE.md`](ARCHITECTURE.md) §11, outside the phase
gates.

No time estimates, these depend on developer capacity and how much of the
Lake `extern_lib` / vendored-C-build toolchain is already familiar.

---

## Stage 0: Cross-package linking spike

**Goal.** Settle the one blocking unknown before any code moves: does
Lake propagate a package's `extern_lib` / `moreLinkArgs` to a *dependent*
package's link step? The answer decides whether `LeanHazmatSha256` can be
the single OpenSSL pkg-config home (with `SizzLean` inheriting the link
args) or whether each downstream package must re-run its own discovery.

**Deliverables.**
- A throwaway two-package experiment: package `A` declaring an
  `extern_lib` + OpenSSL `moreLinkArgs`; package `B` that `require`s `A`,
  references one of `A`'s `@[extern]` symbols, and builds an executable
  that must link `libcrypto`. Observe whether `B` links cleanly *without*
  re-declaring the OpenSSL args.
- A one-line recorded outcome (yes / no) added to this stage, feeding
  Stage 1's final step.

**Acceptance.** The experiment builds (or fails to link) decisively, and
the propagation question is answered in writing.

**Risk.** Low, it is a probe, discarded after. The prior evidence points
to **no** propagation: `packages/EthCLSpecs/lakefile.toml` hand-mirrors
`-l:libcrypto.so.3` rather than inheriting it from `SizzLean`.

**Notes.** If propagation works, Stage 1 lets `SizzLean` (and the consensus
packages) drop their OpenSSL args entirely. If not, both keep a minimal pkg-config
discovery, accepted, per the no-shared-lakefile-code decision
([`ARCHITECTURE.md`](ARCHITECTURE.md) §3.3).

> **Outcome (settled, verified on real code during Stage 1).** Lake
> propagates `extern_lib` **archives** but **not** `moreLinkArgs`
> across `require`. Confirmed two ways against the migrated tree:
> (1) `LeanEthCS`'s `eth_ssz_vector_runner` and `SizzLean`'s `ssz_bench`
> both link cleanly. The `libleanhazmat_sha256.a` archive is pulled in
> transitively, carrying the `lean_hazmat_sha256_*` symbols and the
> `__libc_csu_*` stubs; (2) temporarily blanking `SizzLean`'s
> `moreLinkArgs` makes `ssz_bench` fail at link with
> `undefined symbol: EVP_DigestFinal_ex` (and friends) *referenced from
> that very archive*, i.e. the archive crossed the package boundary
> but the `-lcrypto` flag did not. **Decision:** each exe-hosting
> dependent keeps its own OpenSSL discovery. `SizzLean` keeps its
> `pkg-config` `lakefile.lean` (it also still needs procedural
> `globsUnder`), the consensus packages keep their hardcoded
> `-l:libcrypto.so.3`, and `LeanHazmatSha256` keeps its own for its
> test lib. No package reverts to a TOML lakefile. This matches the
> prior link-arg evidence and the no-shared-lakefile-code decision (§3.3).
>
> **Addendum (macOS portability).** `EthCLLib`/`EthCLSpecs`'s hardcoded
> flag later changed from the Linux-only `-l:libcrypto.so.3` to the
> portable `-lcrypto` plus Homebrew's `-L` paths, so the same
> independent, hardcoded re-supply this stage decided on now resolves
> on macOS too. The propagation finding and the decision to re-supply
> independently are unchanged, only the literal flag each package hardcodes.

---

## Phase 1: Consensus core

The three consensus families plus their aggregator. The exit gate is a
consumer being able to `require LeanHazmatConsensus` and get working
SHA-256, BLS, and KZG, with `SizzLean`'s hash path served from
`LeanHazmatSha256`.

### Stage 1: SHA-256 migration (`LeanHazmatSha256` + SizzLean rewire)

**Goal.** Move the FFI SHA-256 binding out of `SizzLean` into a new
self-contained `LeanHazmatSha256` package, leaving the pure-Lean spec in
`LeanSha256` and the equivalence axioms in `SizzLean`. Keep the whole
umbrella green.

**Deliverables.**
- `packages/hazmat/LeanHazmatSha256/` scaffold: `lakefile.lean` (procedural, owns
  the C targets + pkg-config discovery), `csrc/`, `LeanHazmatSha256.lean`
  root, `LeanHazmatSha256/` modules, `LeanHazmatSha256Tests/` +
  `LeanHazmatSha256Tests.lean`, `docs/ARCHITECTURE.md`, `README.md`.
- Move `csrc/sha256_shim.c` + `csrc/sha256_batch.c` from `SizzLean` into
  `LeanHazmatSha256/csrc/`, with the OpenSSL pkg-config / C build targets
  and the `extern_lib`.
- Move the three `@[extern] opaque` decls (`sha256Hash`, `sha256Combine`,
  `sha256BatchCombine`) into `LeanHazmatSha256`, in namespace `LeanHazmat`
  (names unchanged: `LeanHazmat.sha256Hash`, …).
- **`SizzLean` keeps and rewires**: the `Hasher` typeclass, the `Sha256`
  tag, `instance : Hasher Sha256` (now delegating to
  `LeanHazmat.sha256Hash` / `sha256Combine`), and **all three** equivalence
  axioms (`sha256Hash_eq_spec`, `sha256Combine_eq_spec`,
  `sha256BatchCombine_eq_spec`) plus the `sha256BatchCombineSpec` reference
  def. This **splits** `Hasher/Sha256.lean`, `Hasher/Sha256Batch.lean`, and
  `Hasher/Sha256Equiv.lean`: the externs cross to `LeanHazmatSha256`; the
  spec defs + axioms stay behind.
- `SizzLean` gains `require LeanHazmatSha256`; keeps `require LeanSha256`.
- **Tests split by what they prove**: CAVP byte-level KAT → new
  `LeanHazmatSha256Tests`; the FFI ↔ pure-Lean equivalence cross-checks
  (`Sha256Equivalence`, `Sha256BatchEquivalence`) **stay** in
  `SizzLeanTests` (they need both packages).
- The one real internal extern caller, `SizzLean/Cache/MerkleTree/Zero.lean`
  (the zero-hash tower), rewired from `sha256Combine` to
  `LeanHazmat.sha256Combine`. (`sha256BatchCombine` turned out to have **no**
  library callers, only tests and its own module, so the planned
  "`SizzLeanBench` batch path rewire" was a no-op; the bench reaches the
  hasher only through the cache layer / the `Hasher` typeclass.)
- Umbrella `lakefile.toml` gains `[[require]] LeanHazmatSha256`.
- Per Stage 0's outcome: keep a minimal OpenSSL discovery in each
  exe-hosting package (`SizzLean`, `EthCLSpecs`, and `LeanHazmatSha256` for
  its test lib). No package reverts to TOML. Link args do **not** propagate
  (Stage 0), and `SizzLean` still needs procedural `globsUnder` regardless.

**Acceptance.** `lake build` is green across the umbrella; `lake build
SizzLeanTests` and `lake build LeanHazmatSha256Tests` both pass; `#axioms`
on a `SizzLean` hash-root theorem still cites the three named equivalence
axioms; the pyspec suites (`just ethcl-pyspec` and
`just sizzlean-pyspec`) still pass unchanged.

**Risk.** Medium. The cross-package link integration (Stage 0 settles its
shape) and the three-file axiom/extern split are the fiddly parts; the
axioms must still name the *moved* externs.

**Notes.** No vendoring: `LeanHazmatSha256`'s only native dependency is the
system `libcrypto`, already pkg-config-discovered. This stage is the
cross-package de-risk for everything after it.

> **Status: done (verified).** `packages/hazmat/LeanHazmatSha256/` ships the three
> externs (namespace `LeanHazmat`, C symbols renamed `lean_ssz_*` →
> `lean_hazmat_*`, archive `libleanhazmat_sha256`). The `Hasher`
> typeclass, `Sha256` tag + instance, and all three equivalence axioms +
> `sha256BatchCombineSpec` stayed in `SizzLean`, rewired to the moved
> externs. `lake build` (all libs), `SizzLeanTests`, and
> `LeanHazmatSha256Tests` are green; `just lint` is clean; `#print axioms`
> on the bridge theorems cites exactly `sha256{Hash,Combine,BatchCombine}_eq_spec`.
> The hazmat test lib is **self-contained** (full NIST CAVP 129-vector FFI
> suite generated by `scripts/gen_cavp.py` + a hand-written combine/batch
> anchor KAT), so the package validates standalone for a future mirror.

---

### Stage 2: BLS (`LeanHazmatBls`) + vendoring harness

**Goal.** Wrap `blst` (BLS12-381) behind `@[extern]` bindings, and stand up
the vendored-library build harness that every later vendored family reuses.

**Deliverables.**
- `packages/hazmat/LeanHazmatBls/` scaffold (per-family shape).
- A `just hazmat-bls-vendor` recipe: shallow `git clone --depth 1 --branch <tag>` of
  `blst` at a **pinned tag** into a gitignored `vendor/`. Pin the rev to the
  one `c-kzg-4844` expects, so Stage 3 can share it
  ([`ARCHITECTURE.md`](ARCHITECTURE.md) §4).
- A Lake target compiling blst (delegating to blst's own `build.sh` /
  `server.c` amalgamation, not re-deriving its flags) → `extern_lib`.
- `csrc/bls_shim.c` + `@[extern] opaque` decls (namespace `LeanHazmat`) for
  the consensus BLS surface: `Sign`, `Verify`, `Aggregate`,
  `AggregateVerify`, `FastAggregateVerify`, `eth_aggregate_pubkeys`,
  `eth_fast_aggregate_verify`, `KeyValidate`, minimal-pubkey-size,
  ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.
- `LeanHazmatBlsTests`: byte-level KAT against the IETF BLS draft vectors
  and the consensus-spec `bls` test suite.
- CI: a vendoring step (`just hazmat-bls-vendor`) before `lake build`, plus a
  `doctor-native` entry for the C toolchain.
- Umbrella `[[require]] LeanHazmatBls`.

**Acceptance.** `lake build` green after `just hazmat-bls-vendor`; the KAT gate
passes, including at least one Sign/Verify roundtrip and one
`FastAggregateVerify` case; a fresh CI run vendors and builds clean.

**Risk.** Medium-high. This is the first vendored library. The blst build
wiring, the CI vendoring step, and ciphersuite correctness (POP scheme,
pubkey/sig group choice) are all new surface.

**Notes.** `LeanHazmatBls` is the **single blst owner** for the family; Stage
3's KZG links *this* blst rather than vendoring its own.

> **Status: done (verified).** `packages/hazmat/LeanHazmatBls/` wraps blst
> **v0.3.16** (commit `e7f90de5…`, exactly the rev c-kzg-4844 v2.1.7
> pins, so Stage 3 shares it). `just hazmat-bls-vendor` shallow-clones the tag
> into gitignored `vendor/blst/`. The lakefile compiles blst's own
> `src/server.c` amalgamation + `build/assembly.S` directly as `buildO`
> targets with `-D__BLST_PORTABLE__` (portable archive; the flags mirror
> blst's default `CFLAGS` minus `-Werror`), the plan's "server.c
> amalgamation" path; `--recursive` is unnecessary (blst has no
> submodules). The surface is `sign` / `skToPk` / `verify` / `keyValidate`
> / `aggregate` / `ethAggregatePubkeys` / `aggregateVerify` /
> `fastAggregateVerify` / `ethFastAggregateVerify` (`skToPk` added for
> deposits + self-contained round-trip tests). `LeanHazmatBlsTests` passes:
> consensus-spec v1.5.0 sign/verify **anchors matched byte-for-byte** plus
> self-contained aggregate / `FastAggregateVerify` / distinct-message
> `AggregateVerify` / `eth_fast_aggregate_verify` infinity-signature
> round-trips, all via `native_decide`. CI gains a `just hazmat-bls-vendor` step;
> `doctor-native` gains `cc` + `git` checks. `lake build` (all libs) and
> `just lint` are green. (One deviation logged: the plan said "delegate to
> build.sh"; compiling the amalgamation directly is the sibling convention and integrates with Lake's trace cache far more cleanly.)

---

### Stage 3: KZG (`LeanHazmatKzg` → `LeanHazmatBls`)

**Goal.** Wrap `c-kzg-4844` behind `@[extern]` bindings, building it against
`LeanHazmatBls`'s blst (not c-kzg's bundled copy), with the trusted setup
loaded at init.

**Deliverables.**
- `packages/hazmat/LeanHazmatKzg/` scaffold; `require LeanHazmatBls`.
- A `just hazmat-kzg-vendor` recipe: shallow clone of `c-kzg-4844` at a pinned tag.
  Do **not** pull its `--recursive` blst. Stage 2's blst is used instead.
- A Lake target compiling c-kzg's own `c_kzg_4844.c` against Bls's blst
  archive → `extern_lib`.
- `data/trusted_setup.txt` + an `initialize`-block / `IO.Ref` loader that
  ingests it once at module load.
- `csrc/kzg_shim.c` + `@[extern] opaque` decls (namespace `LeanHazmat`):
  `blob_to_kzg_commitment`, `compute_kzg_proof`, `compute_blob_kzg_proof`,
  `verify_kzg_proof`, `verify_blob_kzg_proof`, `verify_blob_kzg_proof_batch`;
  Fulu PeerDAS: `compute_cells_and_kzg_proofs`, `verify_cell_kzg_proof_batch`,
  `recover_cells_and_kzg_proofs`.
- `LeanHazmatKzgTests`: KAT against the consensus-spec `kzg` test vectors
  (Deneb proof/verify + Fulu cells).
- Umbrella `[[require]] LeanHazmatKzg`.

**Acceptance.** `lake build` green; c-kzg compiles and links against the
external blst; the KZG spec-vector KAT passes; the trusted setup loads once
and a `verify_blob_kzg_proof` round trips.

**Risk.** High. Building c-kzg against an *external* blst (rather than its
submodule) is the open wiring item from [`ARCHITECTURE.md`](ARCHITECTURE.md)
§4; trusted-setup init ordering and the Fulu cell functions add surface.

**Notes.** Confirm the blst rev `LeanHazmatBls` pins satisfies c-kzg; if it
does not, bump Bls's pin to c-kzg's expectation.

> **Status: done (verified).** `packages/hazmat/LeanHazmatKzg/` wraps c-kzg-4844
> **v2.1.7**, `require`s `LeanHazmatBls`, and shares its blst. Confirmed
> that c-kzg v2.1.7 pins blst at exactly `e7f90de5…` = the v0.3.16 Bls
> pin, so no second blst is vendored. `just hazmat-kzg-vendor` clones c-kzg
> *without* `--recursive`. The lakefile compiles c-kzg's `src/ckzg.c`
> amalgamation + the shim against Bls's `bindings/`. Surface complete:
> all six EIP-4844 functions + the three Fulu cell functions. KAT passes
> via self-contained `native_decide` round-trips (EIP-4844 commit/prove/
> verify + batch + negatives; Fulu `computeCellsAndKzgProofs` →
> `verifyCellKzgProofBatch` over 128 cells + erasure recovery from 64).
>
> Two design points settled during implementation, both noted in the
> lakefile:
> - **Trusted setup**: embedded into the archive via `.incbin` (from
>   `data/trusted_setup.txt`) and loaded once at library load with
>   `fmemopen` + a constructor (`precompute=0`, verify-only), rather than
>   an `initialize`-block file read, which would need a fragile runtime
>   path. Self-contained and hermetic.
> - **Sharing one blst across the package boundary**: the KZG *static*
>   archive is blst-free (so the final exe link sees one blst copy, via
>   Bls propagation, no duplicate symbols), while the *precompiled
>   module `.so`* gains `blst_*` through `moreLinkArgs`
>   (`-l:libleanhazmat_bls.so` + `-rpath`), exactly mirroring how the
>   SHA-256 family's `.so` reaches `libcrypto`. Because that link
>   reference is invisible to Lake's scheduler, a clean parallel build
>   would race (KZG's `.so` linking before Bls's `.so` exists); the KZG
>   `extern_lib` therefore folds Bls's shared-lib build into its own
>   dependency trace with `Job.zipWith` (`findExternLib? `libleanhazmat_bls`),
>   making the ordering explicit, verified by repeated from-clean builds.
>   This was the high-risk wiring item; resolving it is what makes
>   precompiled cross-package FFI work under one shared blst.

---

### Stage 4: Consensus aggregator (`LeanHazmatConsensus`), DEFERRED

**Goal.** A single meta-package re-exporting the three consensus families.

**Deliverables.**
- `packages/hazmat/LeanHazmatConsensus/`: declarative `lakefile.toml`, no C; a
  `LeanHazmatConsensus.lean` root that `import`s and re-exports the
  `LeanHazmatSha256` / `LeanHazmatBls` / `LeanHazmatKzg` roots; `[[require]]`
  blocks for all three.
- Umbrella `[[require]] LeanHazmatConsensus`.

**Acceptance.** `import LeanHazmatConsensus` brings every consensus family's
`LeanHazmat.*` names into scope; `lake build` green.

**Risk.** Low, re-export only, no compilation.

> **Status: done (verified).** The aggregator shipped together with the
> execution-layer work, when the top `LeanHazmat` umbrella gave it a real
> consumer (its own `require` in the top umbrella). It is exactly the planned
> shape: a declarative `lakefile.toml`, a re-export root importing the three
> family roots, and `[[require]]` blocks by local path.

**Phase 1 exit gate: MET.** Consensus crypto is complete and green: a
downstream project can `require` any of `LeanHazmatSha256` / `LeanHazmatBls`
/ `LeanHazmatKzg` on its own, or `LeanHazmatConsensus` for the layer;
`SizzLean`'s hash-tree-root path is served by `LeanHazmatSha256` with the three
equivalence axioms intact (`#print axioms` confirms). `lake build` across all
libraries is green and `just lint` is clean.

---

## Phase 2: Execution layer

The execution-layer families. Each is independent except where a primitive
reuses a consensus package (SHA-256 `0x02` → `…Sha256`, point-eval `0x0a` →
`…Kzg`, EIP-2537 → `…Bls`, no new packages). Per
[`ARCHITECTURE.md`](ARCHITECTURE.md) §4, each package exposes the **raw**
primitive; precompile composition (input parsing, gas, output hashing) is
the consumer's concern.

### Stage 5: Keccak-256 (`LeanHazmatKeccak`)

**Goal.** Wrap Keccak-256 (the EL's most-used primitive) behind `@[extern]`.

**Deliverables.**
- `packages/hazmat/LeanHazmatKeccak/` scaffold; `just hazmat-keccak-vendor`
  (coruus/keccak-tiny, pinned by commit rev, fetched and checked back).
- `csrc/keccak_shim.c` + `@[extern] opaque keccak256` (namespace
  `LeanHazmat`). **Keccak padding, not SHA3**, distinct domain separation.
- `LeanHazmatKeccakTests`: KAT including the empty-input and known-vector
  digests; an EVM-style address-derivation example documented as
  *consumer-side* composition, not part of the primitive.
- Umbrella `[[require]]`.

**Acceptance.** `lake build` green; KAT passes; `keccak256 ""` matches the
known constant.

**Risk.** Low. The single-file library keeps the audit surface small;
correctness is well-pinned by vectors.

> **Status: done (verified).** `packages/hazmat/LeanHazmatKeccak/` wraps
> **coruus/keccak-tiny** (CC0, single file; the "small single-file vetted
> keccak" branch of the open item, smallest trusted base, and its
> delimiter-parametrized sponge is exactly what raw Keccak needs). Upstream
> tags no releases, so the pin is the commit rev `64b66475…`, fetched by
> rev and checked back by `just hazmat-keccak-vendor`. Ethereum's Keccak-256
> is the 0x01-padding sponge at rate 136, **not** SHA3, so the shim
> translation unit `#include`s the vendored `.c` unmodified (its sponge is
> `static`) and calls it with the original Keccak delimiter; a `memset_s`
> macro maps glibc's missing Annex K function to `memset` before the
> include. The vendored file's content is folded into the shim target's
> trace explicitly (the `#include` is invisible to a single-input trace).
> Surface: `keccak256`. KAT passes: `keccak256 ""` = `c5d246…a470`, the
> empty trie root `keccak256 0x80` = `56e81f…b421`, block-boundary and
> multi-block vectors, and the EIP-155 address derivation
> (`keccak256(pk)[12:32]`) documented as consumer-side composition.

---

### Stage 6: secp256k1 / ecRecover (`LeanHazmatSecp256k1`)

**Goal.** Wrap `libsecp256k1` ECDSA public-key recovery.

**Deliverables.**
- `packages/hazmat/LeanHazmatSecp256k1/` scaffold; `just
  hazmat-secp256k1-vendor` (bitcoin-core `libsecp256k1` v0.8.0, vendored,
  pinned tag + rev, fetched and checked back).
- `csrc/secp256k1_shim.c` + `@[extern] opaque ecdsaRecover` (namespace
  `LeanHazmat`) returning the **raw** recovered public key, *not* the
  `0x01` precompile output (keccak + truncate stays with the caller).
- `LeanHazmatSecp256k1Tests`: KAT for recovery against known
  message/signature/pubkey triples.
- Umbrella `[[require]]`.

**Acceptance.** `lake build` green; recovery KAT passes.

**Risk.** Low-medium. Context handling for libsecp256k1 (settled on
`secp256k1_context_static`, which the library asks callers to
self-test once); no system-library branch remains.

> **Status: done (verified).** `packages/hazmat/LeanHazmatSecp256k1/` wraps
> bitcoin-core **libsecp256k1 v0.8.0**, vendored (`just
> hazmat-secp256k1-vendor`; the "system lib if available" branch is
> unrealized, one pinned source of truth today, a pkg-config branch is a
> later refinement). The lakefile compiles the library's amalgamation
> (`src/secp256k1.c`) plus its two committed ecmult table units with
> `-DENABLE_MODULE_RECOVERY` (still a compile-time module gate in v0.8.0).
> `SECP256K1_BUILD` is deliberately not passed: the amalgamation defines
> it itself, and a command-line copy only yields a redefinition warning.
> Context: `secp256k1_context_static` (recovery
> and verification need no signing tables), gated on one
> `secp256k1_selftest` call. Surface: `ecdsaRecover` (→ the raw 64-byte
> `x ‖ y` public key, *not* the precompile output) and `ecdsaVerify`.
> One policy choice recorded in the shim: `secp256k1_ecdsa_verify` rejects
> high-`s` (Bitcoin's anti-malleability rule), so `ecdsaVerify` normalizes
> `s` in place, `(r, s)` and `(r, n - s)` have identical validity, and the
> raw primitive carries no policy. KAT passes: the EIP-155 example
> transaction recovers its published key byte-for-byte (and
> `LeanHazmatKeccakTests` checks the derived sender address), a second
> deterministic signature recovers the same key, and negatives cover
> tampering, out-of-range `r`, `recId > 3`, and the wrong-parity mirrored
> key.

---

### Stage 7: BN254 / alt_bn128 (`LeanHazmatBn254`)

**Goal.** Wrap `herumi/mcl` for alt_bn128 add / mul / pairing, the C++
toolchain step.

**Deliverables.**
- `packages/hazmat/LeanHazmatBn254/` scaffold; `just hazmat-bn254-vendor` (pinned mcl).
- A Lake target building mcl with the **C++** toolchain; `csrc/bn254_shim.cpp`
  with `extern "C"` wrappers; the C++ runtime compiled out at the source
  level, so no `-lstdc++` / `-lc++` is needed anywhere.
- `@[extern] opaque` decls (namespace `LeanHazmat`) for G1/G2 add, scalar
  mul, and pairing covering EIP-196/197/1108.
- `LeanHazmatBn254Tests`: KAT against the EIP-197 pairing vectors.
- Umbrella `[[require]]`.

**Acceptance.** `lake build` green (C++ link included); pairing KAT passes.

**Risk.** Medium-high. This is the only C++ family. Compiler selection, name
mangling via `extern "C"`, and stdlib linking are new build shape.

> **Status: done (verified).** `packages/hazmat/LeanHazmatBn254/` wraps herumi
> **mcl v4.10**, vendored (`just hazmat-bn254-vendor`). Build shape
> (settled by experiment, recorded in the lakefile): mcl's whole `mclBn*`
> C API comes out of ONE translation unit, `src/fp.cpp`, compiled with
> `-DMCL_FP_BIT=256 -DMCL_FR_BIT=256` (the `src/bn_c256.cpp` in the tree
> is an empty placeholder) and `-DMCL_BINT_ASM=0` (upstream's default
> bignum primitives need x64 assembly or LLVM-IR objects; the generic C
> path keeps the archive portable and dependency-free), no GMP. The shim
> is `.cpp` with `extern "C"` entry points exposing the raw primitives:
> `g1Add` / `g1Mul` (EIP-196), `g2Add` / `g2Mul` (EIP-197), and the
> pairing pieces `millerLoopVec` / `finalExp` / `gtIsOne`, the EIP-197
> check is `gtIsOne (finalExp (millerLoopVec pairs))` in the caller.
> Encodings are the EIPs' own at the boundary (32-byte big-endian fields,
> all-zero infinity, G2 imaginary-half-first; mcl's (real, imag) order is
> swapped in the shim), so the vectors read verbatim.
>
> Two C++-build decisions recorded in the shim's header comment:
> - **No C++ runtime.** mcl's compiled code would reference the libstdc++
>   ABI (std::string, hash-map internals, iostream's static init), and
>   link args do not propagate across `require` (Stage 0), so a consumer
>   flag was never viable. The build instead compiles the runtime out:
>   `-fno-exceptions -fno-rtti -fno-threadsafe-statics` plus
>   `-DCYBOZU_DONT_USE_EXCEPTION -DCYBOZU_DONT_USE_STRING
>   -DMCL_DONT_USE_CSPRNG -DMCL_DONT_USE_XBYAK`, verified by `nm -u` to
>   leave only libc and libgcc references. The archive is as
>   self-contained as the C families, with no consumer flags.
> - **Portable bignum.** `-DMCL_BINT_ASM=0` avoids upstream's asm/LLVM
>   bignum objects.
>
> KAT passes against **ethereum/py_ecc** ground truth (the implementation
> EIP-197 itself links): G1/G2 arithmetic anchors, the two-pair pairing
> check whose discrete-log sum vanishes, the empty-pair rule, the
> infinity pair, the not-one probe, and off-curve / length-mismatch
> negatives. (Authoring note: py_ecc's FQ2 coefficient order is
> (real, imag) and EIP-197 encodes (imag, real); the generator swaps, the
> shim swaps, and the vectors pin the EIP order.)

---

### Stage 8: BLAKE2f (`LeanHazmatBlake2f`)

**Goal.** A hand-rolled RFC 7693 `F`-compression for EIP-152.

**Deliverables.**
- `packages/hazmat/LeanHazmatBlake2f/` scaffold; `csrc/blake2f_shim.c`, an
  in-repo, rounds-parametrised `F` compression (no vendored library).
- `@[extern] opaque blake2fCompress` (namespace `LeanHazmat`).
- `LeanHazmatBlake2fTests`: KAT against the EIP-152 test vectors (including
  the rounds=0 and large-rounds edge cases).
- Umbrella `[[require]]`.

**Acceptance.** `lake build` green; EIP-152 vectors pass.

**Risk.** Low-medium. Small, self-contained; correctness is fully pinned by
the EIP vectors. (Confirm hand-roll beats pulling `libb2`, the open item.)

> **Status: done (verified).** `packages/hazmat/LeanHazmatBlake2f/` ships the
> hand-rolled RFC 7693 `F` compression in `csrc/blake2f_shim.c` (the
> open item resolved: no library exposes raw `F`, and ~60 lines do not
> justify a vendored dependency; the hand-roll was confirmed). Surface:
> `blake2fCompress (rounds) (h) (m) (t0) (t1) (last)`, the raw
> rounds-parametrized primitive; the 213-byte EIP-152 input parse is
> decoded in the *test*, mirroring the raw-primitives rule. KAT passes:
> EIP-152 test vectors 4–8 byte-for-byte (rounds 0, 1, 12, and
> `0xffffffff`, both final-block flags) plus the wrong-length sentinels.
> The `0xffffffff`-rounds case runs ~4 · 10⁹ rounds in the FFI and
> dominates the suite (~50 s), acceptable for an explicit-only test lib.

---

### Stage 9: OpenSSL execution shims (`LeanHazmatRipemd160` / `…Modexp` / `…P256`)

**Goal.** The three OpenSSL-backed EL primitives, each a ~zero-compile shim
linking the system `libcrypto`.

**Deliverables.**
- `packages/hazmat/LeanHazmatRipemd160/`: `@[extern] opaque ripemd160`; the
  shim loads OpenSSL 3.x's **default provider** (required) and **legacy
  provider** (best-effort, for 3.0.0-3.0.6) into a **private
  `OSSL_LIB_CTX`** (leaving the process's default context untouched),
  once, with a load-failure path.
- `packages/hazmat/LeanHazmatModexp/`: `@[extern] opaque modExp` over
  `BN_mod_exp` (BIGNUM); raw modular exponentiation, with input parsing and
  the EIP-2565/7883 gas schedule left to the caller.
- `packages/hazmat/LeanHazmatP256/`: `@[extern] opaque p256Verify` (NIST P-256,
  EIP-7951).
- A KAT test lib per package; umbrella `[[require]]` for each.

**Acceptance.** `lake build` green; each package's KAT passes (RIPEMD-160
known digests; modexp known triples; P256VERIFY EIP-7951 vectors).

**Risk.** Low-medium. The legacy-provider loading is the one gotcha; the
rest reuses the established OpenSSL pkg-config path from Stage 1.

> **Status: done (verified).** All three packages follow the
> LeanHazmatSha256 pkg-config pattern (duplicated per §3.3):
> - `LeanHazmatRipemd160`: `EVP_Q_digest` over "RIPEMD-160" against a
>   **private `OSSL_LIB_CTX`** with `default` + `legacy` loaded (the
>   process's default context stays untouched; setup via `pthread_once`,
>   a failed setup is not retried) and surfaced as the empty
>   `ByteArray`, the load-failure path the plan called out. KAT passes:
>   the nine published vectors (verified against `openssl dgst -rmd160`
>   at authoring time), including the million-`a` case.
> - `LeanHazmatModexp`: `BN_mod_exp` over big-endian byte strings, the
>   result in minimal big-endian (`BN_bn2bin`; a zero result is the
>   single `00`, the empty output stays reserved for errors). The EIP-198
>   input parse, padding, and gas are the caller's, as is the excess-data
>   rule. The primitive's inputs are exact byte strings. KAT passes: the
>   EIP-198 worked examples (Fermat, zero base, `3^65535 mod 2^255`)
>   plus fixed cases cross-checked against Python's `pow`, and the zero
>   modulus failure.
> - `LeanHazmatP256`: the raw `(r, s)` pair is DER-encoded by hand as
>   an ECDSA-Sig-Value, the key is imported as the `0x04 ‖ x ‖ y`
>   octet string (`EVP_PKEY_fromdata`), then `EVP_PKEY_verify`; all on
>   the OpenSSL 3.x provider API, no deprecated `EC_KEY` / `ECDSA_*`
>   calls. High-`s` signatures verify
>   (EIP-7951 has no malleability policy; its own suite marks one valid).
>   KAT passes: official EIP-7951 vectors from the EIP's
>   `test-vectors.json` (Project Wycheproof), three valid (including the
>   malleability case) and two invalid, plus tamper and off-curve
>   negatives.

---

### Stage 10: Execution aggregator + top umbrella

**Goal.** Tie the EL families together and complete the brand surface.

**Deliverables.**
- `packages/hazmat/LeanHazmatExecution/`: declarative `lakefile.toml`; re-exports
  the EL family roots; `[[require]]` blocks for each.
- `packages/hazmat/LeanHazmat/`: the top umbrella; `require`s
  `LeanHazmatConsensus` + `LeanHazmatExecution` and re-exports both.
- Umbrella `lakefile.toml` registers both aggregators.

**Acceptance.** `import LeanHazmat` brings the whole `LeanHazmat.*` surface
(consensus + execution) into scope; `lake build` green.

**Risk.** Low, re-export only.

> **Status: done (verified).** All three aggregators landed as planned:
> declarative `lakefile.toml`s, re-export roots, `[[require]]` blocks by
> local path, registered in the umbrella. `import LeanHazmat` brings the
> whole `LeanHazmat.*` surface (consensus + execution) into scope; the
> build is green through the umbrella (`lake build LeanHazmat`, 137 jobs).

**Phase 2 exit gate: MET.** The full Ethereum-protocol crypto surface ships as
one package per family, with `LeanHazmatConsensus` / `LeanHazmatExecution`
/ `LeanHazmat` aggregators over them. Every family's KAT gate passes
(`just test` runs all ten family gates), `lake build` is green across the umbrella, and
`just lint` is clean.

---

## Cross-cutting concerns (apply to every stage)

- **Literate by default** (CLAUDE.md). Every new `*.lean` file opens with a
  `/-! … -/` module docstring framing it for both Lean-fluent and
  crypto-fluent readers; every public declaration carries a `/--`
  *why*-docstring. **Every `@[extern] opaque` docstring names the empirical
  trust assumption** it rests on (which library, which spec/EIP/KAT validates
  it), visible later under `#axioms`.
- **KAT vectors pinned to the latest official release.** Each family's test
  vectors track the latest consensus-specs / EIP / reference release; bumping
  spec coverage means bumping the pinned vector tag in lockstep.
- **Vendoring pinned to tags, fetched shallow, never submodules.** `just
  hazmat-<family>-vendor` records an exact tag + rev; `vendor/` is gitignored; the
  build itself stays offline.
- **No `sorry` in committed code.** A `TODO` + tracking note is acceptable for
  a single-commit WIP; CI rejects `sorry` on `main`.
- **`set_option autoImplicit false` per file.**
- **No committed `#eval` / `#check` / `#print`.** Use `example : … := by …`
  or `#guard` for build-time assertions; `native_decide` for KAT that must
  reduce concrete FFI bytes.
- **Configure, don't integrate.** C compilation is Lake `target` /
  `extern_lib` (delegating to a vendored library's own build where
  non-trivial), never a standalone Makefile.

## Status snapshot

| Phase | Stages | Status |
| --- | --- | --- |
| 0: Linking spike | Stage 0 | **done**: archives propagate, link flags don't (settled in writing above) |
| 1: Consensus core | Stages 1–3 (SHA-256 migration, BLS, KZG) | **done**: all three green; Phase 1 exit gate met |
| 1: Consensus aggregator | Stage 4 (`LeanHazmatConsensus`) | **done**: landed with the other aggregators |
| 2: Execution layer | Stages 5–10 (Keccak, secp256k1, BN254, BLAKE2f, OpenSSL shims, aggregators) | **done**: all seven families + the three aggregators green; Phase 2 exit gate met |

**Phase 1's families are complete.** The consensus crypto surface ships as
three separate packages: `LeanHazmatSha256` (OpenSSL, the SHA-256
migration out of SizzLean), `LeanHazmatBls` (blst, the vendoring harness),
and `LeanHazmatKzg` (c-kzg-4844 over Bls's shared blst). `SizzLean`'s
hash-tree-root path is served by `LeanHazmatSha256` with the equivalence
axioms intact; `lake build` across all libraries is green and `just lint`
is clean. Per-family KAT gates (`lake build LeanHazmat<Family>Tests`) pass.
The consensus aggregator ships as `LeanHazmatConsensus` (Stage 4).

Phase 2 is **complete**. The execution-layer families ship as seven
separate packages: `LeanHazmatKeccak` (keccak-tiny, vendored by rev),
`LeanHazmatSecp256k1` (libsecp256k1 v0.8.0, vendored), `LeanHazmatBn254`
(herumi/mcl v4.10, vendored, the family's one C++ build, with the
C++ runtime compiled out at the source level so consumers need no
C++ flags),
`LeanHazmatBlake2f` (the in-repo RFC 7693 shim, no library),
`LeanHazmatRipemd160` / `LeanHazmatModexp` / `LeanHazmatP256` (system
libcrypto). The aggregators `LeanHazmatConsensus`, `LeanHazmatExecution`,
and the top `LeanHazmat` umbrella complete the brand surface. Per-family
KAT gates pass against the published ground truth for each primitive:
the EIP-152 vectors (BLAKE2f), the EIP-155 example (secp256k1 recovery,
plus a deterministic second signature), py_ecc-generated EIP-196/197
point and pairing checks (BN254), the EIP-198 worked examples (modexp),
the EIP-7951 / Wycheproof set (P256VERIFY), the published RIPEMD-160
vector set, and the EVM Keccak constants. `lake build` is green across
the umbrella, and `just lint` is clean. Mirroring stays opt-in per
family, outside the phase gates.
