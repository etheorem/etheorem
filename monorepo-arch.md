# How the Etheorem monorepo is laid out

A reader's reference for the repo's physical structure: where
each piece of source lives, how Lake's umbrella + subpackage
arrangement is wired, and the conventions that keep the layout
stable. For *what* each subpackage does, see the per-package
READMEs and `packages/SizzLean/docs/ARCHITECTURE.md`.

## Four subpackages under one umbrella

```
LeanSha256  ←  SizzLean  ←  LeanEthCS          LeanPoseidon
   (pure)      (SSZ +        (consensus          (pure Poseidon2,
               cache +       containers,          BN254 t=3 —
               FFI hash)     Phase 0 → Gloas)     standalone island)
```

`LeanPoseidon` sits *outside* the `LeanSha256 → SizzLean → LeanEthCS`
chain: it is a second pure-crypto primitive, parallel to `LeanSha256`,
that nothing in the monorepo imports (and which imports nothing from it).
The umbrella `[[require]]`s it so `lake build` builds it, but there is no
edge into the SSZ side — see `packages/LeanPoseidon/docs/ARCHITECTURE.md`.

A fifth package, **`LeanPoseidonProofs`**, hangs off `LeanPoseidon` (it
`[[require]]`s the core + **mathlib**) and holds the machine-checked
fast-≡-reference equivalence proof. It is the monorepo's only mathlib
dependency and is **standalone** — deliberately *not* in the umbrella
`[[require]]`s — so mathlib (clone, olean cache, build) is contained to
that one package and its one CI job, leaving the root build and every
other package mathlib-free. Build it on its own:
`cd packages/LeanPoseidonProofs && lake build` (or `just
test-poseidon-proofs`).

```
<repo-root>/
├── lean-toolchain                    # single, repo-wide; subpackages don't override
├── lakefile.toml                     # umbrella; declares no Lean libraries of its own
├── lake-manifest.json                # committed (per the dep policy in CLAUDE.md)
├── .gitignore
├── README.md / CLAUDE.md / monorepo-arch.md
├── Justfile                          # task runner over the umbrella
├── scripts/                          # Python harnesses (run_conformance.py, …)
└── packages/
    ├── LeanSha256/
    │   ├── lakefile.toml             # pure Lean, no C, declarative
    │   ├── LeanSha256.lean           # library root
    │   ├── LeanSha256/               # Core.lean, Nist.lean
    │   ├── cavp/                     # NIST CAVP fixtures consumed by Nist.lean
    │   ├── LeanSha256Tests/          # in-Lean conformance gates
    │   └── README.md
    ├── SizzLean/
    │   ├── lakefile.lean             # procedural — needed for the FFI C-shim target
    │   ├── csrc/                     # sha256_shim.c, sha256_batch.c
    │   ├── docs/                     # ARCHITECTURE.md, PLAN.md, OPTIMISATION.md, research/
    │   ├── SizzLean.lean
    │   ├── SizzLean/                 # Spec/, Repr/, Hasher/, Cache/, Proofs/
    │   ├── SizzLeanTests/            # property tests + acceptance gates
    │   ├── SizzLeanBench/            # microbench scenarios + Fulu reference fixture
    │   ├── bench/                    # session-output TSVs (gitignored)
    │   └── README.md
    ├── LeanEthCS/
    │   ├── lakefile.toml             # declarative
    │   ├── LeanEthCS.lean
    │   ├── LeanEthCS/                # Forks/{Phase0..Gloas}/, Cli/, Primitives.lean, Preset*.lean
    │   └── README.md
    ├── LeanPoseidon/                 # standalone island (parallel to LeanSha256)
    │   ├── lakefile.lean             # procedural — C ABI shim + cargo (zkhash) extern_libs
    │   ├── csrc/                     # poseidon_shim.c (Lean ByteArray ↔ raw-pointer Rust ABI)
    │   ├── rust-oracle/              # vendored zkhash crate (test-only differential oracle)
    │   ├── docs/                     # ARCHITECTURE.md, PLAN.md
    │   ├── scripts/                  # gen_poseidon_params.py + poseidon2_{bn256,bls12}.json
    │   ├── LeanPoseidon.lean
    │   ├── LeanPoseidon/             # Field (Bn254Fr, Bls12Fr — shared) + Poseidon2/ (Params, LinearLayers, Permutation, Compress, Sponge)
    │   ├── LeanPoseidonTests/        # Kat, Ffi, Differential
    │   ├── FuzzMain.lean             # poseidon_fuzz exe root
    │   └── README.md
    └── LeanPoseidonProofs/           # standalone, NOT in the umbrella (mathlib-isolated)
        ├── lakefile.toml             # require ../LeanPoseidon + mathlib @ v4.29.1
        ├── lake-manifest.json        # committed — pins mathlib (+ transitive) revs
        ├── LeanPoseidonProofs.lean
        └── LeanPoseidonProofs/       # FpCommRing (CommRing (Fp p)), Equivalence (permute = permuteRef)
```

## Why this shape

**Four subpackages.** The pure-Lean SHA-256 reference
(`LeanSha256`) is reusable on its own — anyone wanting a verified
SHA-256 in Lean shouldn't have to depend on all of SSZ. The SSZ
library (`SizzLean`) is reusable beyond Ethereum — anyone with a
custom SSZ-shaped schema shouldn't have to pull in
consensus-spec containers. The Ethereum consensus types
(`LeanEthCS`) sit on top of SSZ and don't need to push their
weight onto SSZ-only consumers. `LeanPoseidon` is a *second*
pure-crypto primitive — a verified Poseidon2 — parallel to
`LeanSha256` rather than in the SSZ chain: it is a standalone
island that nothing here imports yet (a future SSZ↔Poseidon2
hasher bridge is deliberately deferred until EIP-7864 settles a
hash and an encoding). Splitting also lets each piece publish on
its own cadence later.

**An umbrella.** While the layers
are decoupled in principle, in practice every cross-layer change
needs to land coherently: a `SizzLean` cache-layer tweak that
breaks `LeanEthCS`'s deriving call sites should be fixed in one
commit, not three. The umbrella `lakefile.toml` `[[require]]`s
all four subpackages by relative path so `lake build` at the
root builds the SSZ dependency chain in order (and the
`LeanPoseidon` island alongside it). Per-package
publication repos will exist later; this is a development
monorepo.

**`SizzLean` and `LeanPoseidon` keep `lakefile.lean`; the others use
TOML.** Lake allows either form, but `lakefile.toml` is purely
declarative — it can't express a build target that compiles a `.c` file or
shells `cargo`. The FFI SHA-256 shim in `packages/SizzLean/csrc/` needs a
procedural target (`buildO` over the `.c` file plus an `extern_lib`
declaration linking to `libcrypto`), so `SizzLean`'s lakefile stays
`.lean`; likewise `LeanPoseidon`'s differential-test oracle needs a `cargo`
target + a C ABI shim + their `extern_lib`s. `LeanSha256` is pure-Lean (no
FFI) and `LeanEthCS` just consumes `SizzLean`; both use the simpler
`lakefile.toml`.

The procedural form on `SizzLean` is kept to the minimum: only
the C-shim target and the `extern_lib` block. Everything else
(package metadata, `lean_lib` declarations, dependencies)
remains declarative-style data, just expressed in Lean
syntax.

## Naming conventions

* **Directory name = package name = library name = module root.**
  `packages/SizzLean/` holds the `SizzLean` package, which
  declares a `SizzLean` library rooted at `SizzLean.lean`. The
  four names line up so the path-to-module mapping is mechanical.
* **PascalCase throughout** for directory and module names.
* **Per-package test / bench libs use a prefixed namespace**
  (`SizzLeanTests`, `SizzLeanBench`, `LeanSha256Tests`) so a
  multi-package umbrella build doesn't collide on a bare `Tests`
  module name.

## Where each piece lives

* The **FFI SHA-256 shim** (`csrc/sha256_shim.c` +
  `csrc/sha256_batch.c`) is in `SizzLean` because that's the
  package whose `Hasher/Sha256.lean` declares the `@[extern]`
  bindings that consume the C symbols.
* The **NIST CAVP test-vector fixtures** are in `LeanSha256`'s
  `cavp/` directory because `LeanSha256/Nist.lean` loads them at
  build time.
* The **per-fork consensus containers** live under
  `LeanEthCS/Forks/<Fork>/` (Phase 0, Altair, …, Gloas). Each
  fork directory has an `Inherited.lean` re-exporting types it
  carries over unchanged from earlier forks, so the CLI
  dispatcher in `LeanEthCS/Cli/Main.lean` never has to know
  *which* earlier fork originally defined a given type.
* The **bench reference fixture** for Fulu BeaconState
  (`SizzLeanBench/Fulu.lean`) is a bench-local *copy* of the
  LeanEthCS Fulu shape. `SizzLeanBench` cannot depend on
  LeanEthCS — that would close a cycle, since LeanEthCS already
  depends on SizzLean — so the bench keeps its own copy. The
  spec-accurate version lives in LeanEthCS; the bench version is
  a reference fixture, not expected to stay in sync.

## Dependency policy

* **`lake-manifest.json`** is committed at the umbrella level.
  Per-subpackage `lake-manifest.json` files are auto-regenerated
  by Lake when building from the umbrella and are gitignored.
* **External Lake dependencies** are pinned to a git rev (never
  a branch) in the relevant subpackage's lakefile. Adding a dep:
  add a `[[require]]` block, run `lake update`, commit the new
  `lake-manifest.json`.
* **Toolchain** is pinned at the repo root in `lean-toolchain`.
  Subpackages do not override it. Bumps cascade through CI and
  through every dep.

## Build menu

```bash
# Library targets (all built by `lake build` at the root):
lake build LeanSha256
lake build SizzLean
lake build LeanEthCS

# In-Lean test suites (run on demand):
lake build LeanSha256Tests
lake build SizzLeanTests
lake build LeanEthCSTests

# Executables:
lake build eth_ssz_vector_runner      # consensus-spec-tests harness driver
lake build ssz_bench                  # microbench grid (S1–S7)
lake build ssz_profile                # phase-by-phase profile

# Build a single subpackage in isolation:
cd packages/SizzLean && lake build
```

The repo's `Justfile` wraps the most common workflows
(`just build`, `just test`, `just bench`,
`just official-ssz-vector-tests-static`, …) — see `just --list`
for the full set.

## What stays at the root

* `README.md` — public-facing overview.
* `CLAUDE.md` — style and discipline conventions binding on all
  three subpackages.
* `Justfile` — task runner over the umbrella.
* `lakefile.toml` — umbrella declaration.
* `lean-toolchain` — pinned toolchain.
* `lake-manifest.json` — pinned external deps for the umbrella.
* `scripts/` — Python harnesses that drive the cross-package
  conformance runner.
* `.github/` — CI workflows.
* `LICENSE`, `CONTRIBUTING.md`, `SECURITY.md`,
  `CODE_OF_CONDUCT.md` — project-wide governance.

Per-subpackage design docs live under
`packages/<Pkg>/docs/` (currently only `SizzLean` has any —
ARCHITECTURE / PLAN / OPTIMISATION / research). When `LeanEthCS`
or `LeanSha256` grow their own design notes, they follow the
same convention.
