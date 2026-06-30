![Etheorem](etheorem_owl.png)

# Etheorem

> **Status: early-stage, experimental, single-developer; personal
> project, not an EF release.** The libraries here pass the
> upstream consensus-spec test corpus and ship the three central
> SSZ theorems on a `BasicSupported` cut, but production-grade
> stability and a stable release line are not implied.

A Lean 4 implementation of the Ethereum consensus specification for the Fulu
and Gloas forks. It is executable. The SSZ container types, the full
beacon-chain state transition, the fork upgrade, and fork choice all run, and
they are checked against the pyspec
[`consensus-spec-tests`](https://github.com/ethereum/consensus-spec-tests)
vectors.

This is a Lean 4 monorepo that also includes SSZ
([Simple Serialize](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md))
with machine-checked correctness on the verified core and other Ethereum dependencies in Lean 4, and FFI bridges.

Upstream repository: <https://github.com/etheorem/etheorem>.

## Layout

```
LeanSha256 ─────────────┐
                        ├─→ SizzLean ──→ EthCLLib ──→ EthCLSpecs
LeanHazmatSha256 ───────┘   (SSZ +       (consensus    (Fulu / Gloas
   (FFI SHA-256)            cache)        framework)    fork bodies)

LeanHazmat* (FFI crypto family):  Sha256 · Bls · Kzg   (consumed à la carte)

LeanPoseidon (pure Poseidon2, standalone island, nothing depends on it yet)
```

Lake subpackages under `packages/`, each with its own lakefile and
independent build target:

- **[`packages/EthCLLib/`](packages/EthCLLib/)** +
  **[`packages/EthCLSpecs/`](packages/EthCLSpecs/README.md)**: the
  consensus-spec framework (the fork-authoring DSL, the effect monad, the SSZ
  container front-end, the pyspec driver) and the executable Fulu and
  Gloas fork bodies built on it. EthCLSpecs declares its containers in-spec and
  ships the `pyspec_server` runner that drives the state-transition,
  fork-choice, and `ssz_static` pyspec runs for both forks.
- **[`packages/LeanSha256/`](packages/LeanSha256/README.md)**: pure-Lean
  SHA-256 reference. NIST CAVP-validated, kernel-reducible. No FFI.
- **[`packages/SizzLean/`](packages/SizzLean/README.md)**: SSZ
  library: spec types, serialization, deserialization, Merkleization,
  the `SSZRepr` deriving handler, the cache layer, the `sszUpdate`
  macro, plus the `Hasher` typeclass + `Sha256` instance (delegating to
  the `LeanHazmatSha256` FFI binding) and the FFI ≡ spec equivalence
  axioms, the one layer importing both the FFI binding and the spec.
- **[`packages/LeanHazmat*/`](hazmat-docs/ARCHITECTURE.md)**: the FFI
  crypto family: one package per primitive family wrapping a
  battle-tested native library behind `@[extern]`. Consensus families
  ship today: `LeanHazmatSha256` (OpenSSL), `LeanHazmatBls` (blst),
  `LeanHazmatKzg` (c-kzg-4844), consumed à la carte. The aggregator
  meta-packages (`LeanHazmatConsensus`, …) and execution-layer families
  are deferred. See [`hazmat-docs/`](hazmat-docs/).
- **[`packages/LeanPoseidon/`](packages/LeanPoseidon/README.md)**:
  pure-Lean **Poseidon2** algebraic hash (BN254 *and* BLS12-381 scalar
  fields, `t = 3`): the permutation, the 2-to-1 `compress`, and a sponge.
  A *standalone island* parallel to `LeanSha256`, depending on nothing in
  the monorepo and nothing depends on it yet. Conformance-validated by a
  differential test against the HorizenLabs `zkhash` Rust oracle
  (test-only) plus committed KATs; the kernel-/`native_decide`-reducible
  core needs no Rust. A sibling **`LeanPoseidonProofs`** package (mathlib,
  standalone) proves `permute = permuteRef` (the shipped fast layers equal
  the textbook dense reference) with a clean axiom footprint.

The umbrella `lakefile.toml` declares no Lean libraries of its own. It
just coordinates the subpackages via `[[require]]` blocks
(`LeanPoseidonProofs` is built on its own, keeping mathlib out of the
root). Per-package publication repos will exist later; this is a
development monorepo.

**Status: pyspec-validated.** The Layer 1 spec
(total serialize / deserialize / hashTreeRoot), the `SSZRepr`
typeclass + deriving handler, the FFI SHA-256 backend, the
pure-Lean `Sha256Spec` reference, and the cache layer
(persistent `Node`, `Node.ofShape`, cached merkle walker,
gindex-driven `setManyAt`, fused commit `Node.commitAndHash`,
closure-based pending overlay, `sszUpdate` macro,
`SSZ.Box` user surface) are all landed. The executable consensus
spec covers the Fulu and Gloas forks (state transition, fork choice,
and the SSZ containers declared in-spec, including Fulu's
`proposer_lookahead` and the Gloas ePBS additions: the nine EIP-7732
`BeaconState` fields plus the `Builder` / `ExecutionPayloadBid` types).
Pyspec pinned at consensus-spec-tests
[v1.7.0-alpha.10](https://github.com/ethereum/consensus-spec-tests/releases/tag/v1.7.0-alpha.10)
in the pytest harnesses. The universal proof set
(`decode_encode`, `serialize_injective`, `encode_size_le_max`
over `SSZType.Supported`) and the AVX-512 SIMD inner loop for
`sha256BatchCombine` remain as planned follow-ups; see
[`packages/SizzLean/docs/PLAN.md`](packages/SizzLean/docs/PLAN.md)
for the staged plan.

## Documents

Per-subpackage design docs live next to the code they describe:

- [`packages/EthCLSpecs/docs/`](packages/EthCLSpecs/docs/README.md):
  the consensus-spec design of record. Read in order:
  [`SPEC_AUTHORING_MODEL.md`](packages/EthCLSpecs/docs/SPEC_AUTHORING_MODEL.md)
  (the author-versus-framework contract and glossary),
  [`FRAMEWORK_ARCHITECTURE.md`](packages/EthCLSpecs/docs/FRAMEWORK_ARCHITECTURE.md)
  (the EthCLLib framework and fork-authoring DSL), and
  [`SPECS_ARCHITECTURE.md`](packages/EthCLSpecs/docs/SPECS_ARCHITECTURE.md)
  (how the Fulu and Gloas specs are organized, ported, and tested).
  [`PLAN.md`](packages/EthCLSpecs/docs/PLAN.md) sequences the
  implementation phases; `IMPLEMENTATION_NOTES.md`, `DISCREPANCIES.md`,
  and `FUTURE_WORK.md` track deviations, spec disagreements, and
  deferred work.
- [`packages/SizzLean/docs/ARCHITECTURE.md`](packages/SizzLean/docs/ARCHITECTURE.md):
  the SSZ library's binding design (`SSZType` universe, `SSZRepr`
  typeclass + deriving, cached Merkle tree, FFI SHA-256, trust
  boundary, module layout).
- [`packages/SizzLean/docs/PLAN.md`](packages/SizzLean/docs/PLAN.md):
  SizzLean's stage-by-stage deliverables and acceptance.
- [`packages/SizzLean/docs/OPTIMISATION.md`](packages/SizzLean/docs/OPTIMISATION.md):
  implementation-level companion to ARCHITECTURE.md §6: the cache
  layer's data structures, how each Phase 17 sub-stage is wired,
  and the bench-gating story.
- [`packages/SizzLean/docs/research/`](packages/SizzLean/docs/research/):
  background research (`pre-research.md`, `cache-research.md`).
- [`packages/<Pkg>/README.md`](packages/): per-subpackage READMEs.

Repo-wide docs:

- [`docs/monorepo-arch.md`](docs/monorepo-arch.md): how the monorepo is
  laid out: the three-subpackage shape, which lakefiles are TOML vs
  procedural, where the FFI C shim lives, the LeanSha256 standalone
  mirror, and the naming / dep / build conventions.
- [`CLAUDE.md`](CLAUDE.md): style and discipline conventions, project-wide.
- [`docs/CODING_STYLE.md`](docs/CODING_STYLE.md): worked, example-driven
  elaboration of the CLAUDE.md conventions, currently a function-body section
  (paragraphing, local naming, intra-body comments, when to split).
- [`CONTRIBUTING.md`](CONTRIBUTING.md): PR / issue workflow,
  toolchain setup, code-style pointers.
- [`SECURITY.md`](SECURITY.md): vulnerability-disclosure policy.
- [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md): community guidelines.

## Prerequisites

On a fresh machine you need four things before `lake build` will
work. The Lean toolchain and `just` itself aren't installed by
the project. They are external tools the recipes assume.

1. **`elan`** (the Lean toolchain manager, provides `lake` /
   `lean`). The version in [`lean-toolchain`](lean-toolchain) is
   installed on first use.

   ```bash
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```

2. **`just`** (task runner; every workflow below is wrapped in
   a `just` recipe; `just doctor` won't run until `just` itself
   is installed). Install via your platform's package manager:
   `brew install just` (macOS), `cargo install just` (anywhere
   with Rust), or see <https://just.systems> for distro packages.

3. **OpenSSL 3.x + `pkg-config`** (system-level build deps for
   the SHA-256 FFI shim, see [Native dependencies](#native-dependencies)
   below for the per-platform one-liners). The Justfile's
   `doctor-native` recipe pinpoints what's missing.

4. **`python3` + `uv`** (only for the pyspec pytest harnesses).
   Run `just setup-python` once to create `.venv/` and install
   the harness deps.

Verify everything in one shot:

```bash
just doctor          # checks elan/lake/lean + pkg-config/OpenSSL + python3/uv
```

`just doctor` prints actionable platform-specific install hints
if anything's missing. The CI runs the slimmer `just doctor-native`
gate (build-time native deps only, the Lean toolchain is
installed by `leanprover/lean-action` later in the workflow).

## Build

Toolchain pinned in [`lean-toolchain`](lean-toolchain) (elan picks it up).

```bash
# From the repo root — common targets by name:
lake build EthCLSpecs       # consensus spec (Fulu / Gloas); pulls in EthCLLib + SizzLean
lake build SizzLean         # SSZ library (serialize / deserialize / Merkleization)
lake build LeanSha256       # pure-Lean SHA-256 reference
lake build LeanPoseidon     # standalone Poseidon2 island (fires its anchor KAT)

# Test suites (per package, run on demand):
lake build EthCLLibTests EthCLSpecsTests   # framework + spec self-tests
lake build SizzLeanTests
lake build LeanSha256Tests
lake build LeanPoseidonTests # committed Poseidon2 KATs (no Rust)
lake exe   poseidon_fuzz     # Poseidon2 differential test vs the zkhash oracle (needs cargo)
just poseidon-proofs    # mathlib equivalence proof permute = permuteRef (standalone; fetches olean cache)

# Bench + profile executables:
lake build ssz_bench       # microbench grid, S1–S7 (see SizzLeanBench.lean)
lake build ssz_profile     # phase-by-phase profile of one workload

# Pyspec runners the pytest harnesses drive:
lake build pyspec_server       # EthCLSpecs: state transition / fork choice / ssz_static
lake build ssz_generic_runner  # SizzLean: ssz_generic wire-format suite

# Or build a single subpackage in isolation:
cd packages/SizzLean && lake build
```

The repo's [`Justfile`](Justfile) wraps the common workflows
(`just build`, `just test`, `just sizzlean-bench`, `just ethcl-pyspec`,
`just sizzlean-pyspec`, …). See `just --list` for the full set.

CI runs `lake build` for each named library on the pinned
toolchain via `leanprover/lean-action`.

### Native dependencies

The FFI SHA-256 shim (`packages/LeanHazmatSha256/csrc/sha256_shim.c`,
used by SizzLean's hash path) links against OpenSSL's `libcrypto`,
discovered via `pkg-config` (Debian/Ubuntu fallback baked in). The Lake
build expects:

- **Linux (Debian/Ubuntu, including CI):** `libssl-dev` for the headers
  (`/usr/include/openssl/evp.h`) and the versioned `libcrypto.so.3`
  shared library, plus `pkg-config`. Install via:

  ```bash
  sudo apt-get install libssl-dev pkg-config
  ```

- **macOS:** `openssl@3` + `pkg-config` via Homebrew (the `pkg-config`
  discovery handles the keg-only include/lib paths).

Run `just doctor-native` to verify the build-time native deps
(`cc`, `git`, `pkg-config`, OpenSSL 3.x).

**Vendored crypto (the LeanHazmat BLS / KZG families).** `LeanHazmatBls`
(blst) and `LeanHazmatKzg` (c-kzg-4844) wrap *vendored* native libraries,
fetched at pinned tags by `just hazmat-bls-vendor` / `just hazmat-kzg-vendor` into
gitignored `vendor/` trees before `lake build` (never git submodules; see
[`hazmat-docs/ARCHITECTURE.md`](hazmat-docs/ARCHITECTURE.md) §6). `just
build` runs both vendor steps for you. The C / C++ compilers are invoked
through the Lean toolchain's `cc` wrapper, no separate configuration
required.

## Pyspec harnesses

Two `pytest-xdist` harnesses drive long-lived Lean servers against the
`ethereum/consensus-spec-tests` vectors. Each xdist worker holds one warm
server, so there is no per-vector Lean startup.

- **EthCLSpecs** (`packages/EthCLSpecs/PySpecTests/`, the `pyspec_server`
  runner): the Fulu and Gloas state transition, fork choice, and per-fork
  `ssz_static` container vectors.
- **SizzLean** (`packages/SizzLean/PySpecTests/`, the `ssz_generic_runner`):
  the fork-agnostic `ssz_generic` wire-format suite (uints, basic vectors,
  bitvectors, bitlists, bools, the test-only containers).

```bash
# One-time: create `.venv/` with the harness deps (cramjam, PyYAML, pytest,
# pytest-xdist). Wraps `uv venv` + `uv pip install -r scripts/requirements.txt`.
just setup-python

# Dev-subset smoke gates (a few cases per handler):
just ethcl-pyspec-smoke         # Fulu + Gloas: transition / fork choice / ssz_static
just sizzlean-pyspec-smoke   # ssz_generic

# Full sweeps:
just ethcl-pyspec-full               # both presets, both forks
just sizzlean-pyspec-full    # every in-scope wire-format vector
```

### Coverage

Pinned at consensus-spec-tests
[v1.7.0-alpha.10](https://github.com/ethereum/consensus-spec-tests/releases/tag/v1.7.0-alpha.10).

- **`ssz_generic`** (SizzLean): 2188 in-scope cases pass across every handler
  (uints, basic_vector, bitvector, bitlist, boolean, containers). The 292
  EIP-7495 / 7916 / 8016 progressive / stable / compatible cases are out of
  SizzLean's `SSZType` universe and xfail. The test-only container shapes
  (`VarTestStruct`, `ComplexTestStruct`, `BitsStruct`, …) are hard-coded in
  `packages/SizzLean/SszGenericRunner.lean`.
- **`ssz_static`** (EthCLSpecs, Fulu + Gloas): the consensus containers
  EthCLSpecs models pass at both the minimal and mainnet presets; the types it
  does not model (light-client, gossip-aggregation, networking identifiers,
  signing helpers) xfail as out of scope. Earlier forks (Phase 0 through
  Electra) are not covered: EthCLSpecs authors Fulu as the accumulated base,
  not a per-fork container set.
