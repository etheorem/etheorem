# How the Etheorem monorepo is laid out

A reader's reference for the repo's physical structure: where
each piece of source lives, how Lake's umbrella + subpackage
arrangement is wired, and the conventions that keep the layout
stable. For *what* each subpackage does, see the per-package
READMEs and `packages/SizzLean/docs/ARCHITECTURE.md`.

## Subpackages under one umbrella

```
LeanSha256  ←  SizzLean  ←  EthCLLib  ←  EthCLSpecs        LeanPoseidon
   (pure)      (SSZ +        (consensus    (Fulu/Gloas        (pure Poseidon2,
               cache +       framework)     specs +            BN254 t=3,
               FFI hash)                    in-spec            standalone island)
                                            containers)
```

`LeanPoseidon` sits *outside* the `LeanSha256 → SizzLean → EthCLLib → EthCLSpecs`
chain: it is a second pure-crypto primitive, parallel to `LeanSha256`,
that nothing in the monorepo imports (and which imports nothing from it).
The umbrella `[[require]]`s it so `lake build` builds it, but there is no
edge into the SSZ side, see `packages/LeanPoseidon/docs/ARCHITECTURE.md`.

A fifth package, **`LeanPoseidonProofs`**, hangs off `LeanPoseidon` (it
`[[require]]`s the core + **mathlib**) and holds the machine-checked
fast-≡-reference equivalence proof. It is the monorepo's only mathlib
dependency and is **standalone**, deliberately *not* in the umbrella
`[[require]]`s, so mathlib (clone, olean cache, build) is contained to
that one package and its one CI job, leaving the root build and every
other package mathlib-free. Build it on its own:
`cd packages/LeanPoseidonProofs && lake build` (or `just
poseidon-proofs`).

```
<repo-root>/
├── lean-toolchain                    # single, repo-wide; subpackages don't override
├── lakefile.toml                     # umbrella; declares no Lean libraries of its own
├── lake-manifest.json                # committed (per the dep policy in CLAUDE.md)
├── .gitignore
├── README.md / CLAUDE.md             # repo-wide overview + style/discipline conventions
├── docs/                             # repo-wide design docs (this file)
├── Justfile                          # task runner over the umbrella
├── scripts/                          # shared Python harness deps (requirements.txt)
└── packages/
    ├── LeanSha256/                   # also published standalone — see "The LeanSha256 mirror"
    │   ├── lakefile.toml             # pure Lean, no C; carries the name/version/license the mirror ships
    │   ├── lean-toolchain            # pinned copy so the split-out repo builds on its own
    │   ├── LICENSE                   # pinned copy of the umbrella LGPL-3.0; keeps the mirror self-contained
    │   ├── LeanSha256.lean           # library root
    │   ├── LeanSha256/               # Core.lean, Nist.lean
    │   ├── cavp/                     # NIST CAVP fixtures consumed by Nist.lean
    │   ├── LeanSha256Tests/          # in-Lean conformance gates
    │   ├── scripts/                  # bump_patch.py (release tag), gen_sha256_cavp.py
    │   └── README.md                 # "issues belong in the umbrella" mirror notice
    ├── SizzLean/
    │   ├── lakefile.lean             # procedural — needed for the FFI C-shim target
    │   ├── csrc/                     # sha256_shim.c, sha256_batch.c
    │   ├── docs/                     # ARCHITECTURE.md, PLAN.md, OPTIMISATION.md, research/
    │   ├── SizzLean.lean
    │   ├── SizzLean/                 # Spec/, Repr/, Hasher/, Cache/, Proofs/
    │   ├── SizzLeanTests/            # property tests + acceptance gates
    │   ├── SizzLeanBench/            # microbench scenarios + Fulu reference fixture
    │   ├── PySpecTests/              # pytest harness for the ssz_generic suite (ssz_generic_runner)
    │   ├── bench/                    # session-output TSVs (gitignored)
    │   ├── MANUAL.md                 # user's guide to writing code against SizzLean
    │   └── README.md
    ├── EthCLLib/                     # consensus-spec framework; depends on SizzLean
    │   ├── lakefile.toml             # declarative
    │   ├── EthCLLib.lean
    │   └── EthCLLib/
    ├── EthCLSpecs/                   # Fulu/Gloas specs + in-spec containers; depends on EthCLLib
    │   ├── lakefile.toml             # declarative
    │   ├── EthCLSpecs.lean
    │   ├── EthCLSpecs/               # Fulu/, Gloas/, Forms.lean
    │   ├── PySpecTests/              # pytest harness for ssz_static + state transition (pyspec_server)
    │   ├── docs/                     # IMPLEMENTATION_NOTES.md, PLAN.md
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

**Layered subpackages.** The pure-Lean SHA-256 reference
(`LeanSha256`) is reusable on its own. Anyone wanting a verified
SHA-256 in Lean shouldn't have to depend on all of SSZ. The SSZ
library (`SizzLean`) is reusable beyond Ethereum. Anyone with a
custom SSZ-shaped schema shouldn't have to pull in
consensus-spec types. The Ethereum consensus framework
(`EthCLLib`) and the Fulu/Gloas specs built on it
(`EthCLSpecs`) sit on top of SSZ and don't need to push their
weight onto SSZ-only consumers. `LeanPoseidon` is a *second*
pure-crypto primitive, a verified Poseidon2, parallel to
`LeanSha256` rather than in the SSZ chain: it is a standalone
island that nothing here imports yet (a future SSZ↔Poseidon2
hasher bridge is deliberately deferred until EIP-7864 settles a
hash and an encoding). Splitting also lets each piece publish on
its own cadence later.

**An umbrella.** While the layers
are decoupled in principle, in practice every cross-layer change
needs to land coherently: a `SizzLean` cache-layer tweak that
breaks `EthCLSpecs`'s deriving call sites should be fixed in one
commit rather than three. The umbrella `lakefile.toml` `[[require]]`s
its subpackages by relative path so `lake build` at the
root builds the whole dependency chain in order, with the
`LeanPoseidon` island built alongside it. `LeanSha256`
already publishes standalone via a read-only subtree mirror (see
[The LeanSha256 mirror](#the-leansha256-mirror)); `SizzLean` and
the consensus packages may follow the same pattern. Either way the umbrella
stays the single source of truth. This is a development
monorepo.

**`SizzLean` and `LeanPoseidon` keep `lakefile.lean`; the others use
TOML.** Lake allows either form, but `lakefile.toml` is purely
declarative, it can't express a build target that compiles a `.c` file or
shells `cargo`. The FFI SHA-256 shim in `packages/SizzLean/csrc/` needs a
procedural target (`buildO` over the `.c` file plus an `extern_lib`
declaration linking to `libcrypto`), so `SizzLean`'s lakefile stays
`.lean`; likewise `LeanPoseidon`'s differential-test oracle needs a `cargo`
target + a C ABI shim + their `extern_lib`s. `LeanSha256` is pure-Lean (no
FFI) and the consensus packages (`EthCLLib`, `EthCLSpecs`) just consume
`SizzLean`; all use the simpler `lakefile.toml`.

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
* The **per-fork consensus containers** are declared in-spec
  under `EthCLSpecs/Fulu/` and `EthCLSpecs/Gloas/`. Gloas has an
  `Inherited.lean` re-exporting types it carries over unchanged
  from Fulu, so the `ssz_static` dispatcher in the `pyspec_server`
  exe never has to know *which* fork originally defined a given
  type.
* The **bench reference fixture** for Fulu BeaconState
  (`SizzLeanBench/Fulu.lean`) is a bench-local *copy* of the
  EthCLSpecs Fulu shape. `SizzLeanBench` cannot depend on
  EthCLSpecs, since that would close a cycle (EthCLSpecs already
  depends on SizzLean), so the bench keeps its own copy. The
  spec-accurate version lives in `EthCLSpecs.Fulu`; the bench
  version is a reference fixture, not expected to stay in sync.

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

## The LeanSha256 mirror

`packages/LeanSha256/` is published a second time as a standalone
repository at <https://github.com/etheorem/LeanSha256>. This is
the only subpackage mirrored today; the other subpackages
live only in the umbrella.

**Why a separate repo exists.** [Reservoir](https://reservoir.lean-lang.org),
the Lean package index, indexes repository *roots*. It cannot
see a package that sits in a monorepo subdirectory. For
`LeanSha256` to be independently discoverable and installable as
a Lake dependency, its source has to appear at the root of some
repo. The mirror is that repo.

**The mirror is one-way and read-only.** The umbrella is the
single source of truth: all development, issues, and PRs happen
here, under `packages/LeanSha256/`. The downstream repo is a
generated artifact. Its `README.md` carries a banner redirecting
contributions to the umbrella, and any direct push to its `main`
is overwritten by the next mirror run.

**It regenerates automatically.** The
[`.github/workflows/mirror-leansha256.yml`](../.github/workflows/mirror-leansha256.yml)
workflow runs on every push to the umbrella's `main` and on
`leansha256-v*` tags. It uses `git subtree split
--prefix=packages/LeanSha256` to produce a synthetic branch
containing only the commits that touched that subtree, with paths
re-rooted at the package directory and authorship/dates/messages
preserved, so the downstream carries real per-file history rather than
a single squashed import. The split tip is pushed to the
downstream `main` over SSH using a deploy key held in
`secrets.LEANSHA256_DEPLOY_KEY` (configured on the downstream
repo; this workflow is the only holder), guarded by a
`--force-with-lease` against the live downstream tip.

**Releases are tag-driven.** A `leansha256-vX.Y.Z` annotated tag
on the umbrella is translated by the same workflow into a plain
`vX.Y.Z` tag on the downstream, which Reservoir surfaces as a
release version. `just leansha256-bump-patch` (wrapping
`packages/LeanSha256/scripts/bump_patch.py`) automates the
high-frequency patch bump: it edits the `version` field in
`packages/LeanSha256/lakefile.toml`, commits, and creates the
`leansha256-v*` tag locally. It deliberately does *not* push, so
the maintainer reviews before publishing. Minor/major bumps are
done by hand.

**Why the package carries its own metadata.** The standalone
`lakefile.toml`, `lean-toolchain`, and `LICENSE` under
`packages/LeanSha256/` (noted in the tree above) exist *for* the
mirror: the split-out repo has no umbrella `lakefile.toml`,
`lean-toolchain`, or root `LICENSE` to inherit, so each must be
self-contained inside the package directory for the downstream to
build and for Reservoir to read its name/version/license. The
umbrella's root `LICENSE` remains the upstream copy; the
package-local copy is overwritten to match on each mirror run.

## Build menu

```bash
# Library targets (all built by `lake build` at the root):
lake build LeanSha256
lake build SizzLean
lake build EthCLLib
lake build EthCLSpecs

# In-Lean test suites (run on demand):
lake build LeanSha256Tests
lake build SizzLeanTests

# Executables:
lake build pyspec_server              # EthCLSpecs pyspec runner (ssz_static, state transition)
lake build ssz_generic_runner        # SizzLean pyspec runner (ssz_generic)
lake build ssz_bench                  # microbench grid (S1–S7)
lake build ssz_profile                # phase-by-phase profile

# Build a single subpackage in isolation:
cd packages/SizzLean && lake build
```

The repo's `Justfile` wraps the most common workflows
(`just build`, `just test`, `just sizzlean-bench`,
`just ethcl-pyspec`, `just sizzlean-pyspec`, …),
see `just --list` for the full set.

## What stays at the root

* `README.md`: public-facing overview.
* `CLAUDE.md`: style and discipline conventions binding on all
  subpackages.
* `Justfile`: task runner over the umbrella.
* `lakefile.toml`: umbrella declaration.
* `lean-toolchain`: pinned toolchain.
* `lake-manifest.json`: pinned external deps for the umbrella.
* `scripts/`: shared Python dependency pins (`requirements.txt`)
  for the per-package pytest pyspec harnesses.
* `docs/`: repo-wide design docs (this file). Distinct from the
  per-subpackage `packages/<Pkg>/docs/` below.
* `.github/`: CI (`lean_action_ci.yml`) plus the LeanSha256
  subtree-mirror workflow (`mirror-leansha256.yml`).
* `LICENSE`, `CONTRIBUTING.md`, `SECURITY.md`,
  `CODE_OF_CONDUCT.md`: project-wide governance.

Repo-wide design docs live in the root `docs/` (this file).
Per-subpackage design docs live under `packages/<Pkg>/docs/`
(`SizzLean` carries ARCHITECTURE / PLAN / OPTIMISATION /
research; `EthCLSpecs` carries IMPLEMENTATION_NOTES / PLAN).
When the other subpackages grow their own design notes, they
follow the same convention.
