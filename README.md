![Etheorem](etheorem_owl.png)

# Etheorem

> **Status: early-stage, experimental, single-developer; personal
> project, not an EF release.** The libraries here pass the
> upstream consensus-spec test corpus and ship the three central
> SSZ theorems on a `BasicSupported` cut, but production-grade
> stability and a stable release line are not implied.

A Lean 4 monorepo for Ethereum consensus-spec types and SSZ
([Simple Serialize](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md))
with machine-checked correctness on the verified core.

Upstream repository: <https://github.com/etheorem/etheorem>.

## Layout

```
LeanSha256 ─────────────┐
                        ├─→ SizzLean  ←  LeanEthCS
LeanHazmatSha256 ───────┘   (SSZ +        (consensus
   (FFI SHA-256)            cache)        containers,
                                          Phase0…Gloas)

LeanHazmat* (FFI crypto family):  Sha256 · Bls · Kzg   (consumed à la carte)

LeanPoseidon (pure Poseidon2, standalone island — nothing depends on it yet)
```

Lake subpackages under `packages/`, each with its own lakefile and
independent build target:

- **[`packages/LeanSha256/`](packages/LeanSha256/README.md)**: pure-Lean
  SHA-256 reference. NIST CAVP-validated, kernel-reducible. No FFI.
- **[`packages/SizzLean/`](packages/SizzLean/README.md)**: SSZ
  library: spec types, serialization, deserialization, Merkleization,
  the `SSZRepr` deriving handler, the cache layer, the `sszUpdate`
  macro, plus the `Hasher` typeclass + `Sha256` instance (delegating to
  the `LeanHazmatSha256` FFI binding) and the FFI ≡ spec equivalence
  axioms, the one layer importing both the FFI binding and the spec.
- **[`packages/LeanEthCS/`](packages/LeanEthCS/README.md)**:
  Ethereum consensus-spec containers from Phase 0 through Gloas,
  the preset-struct macro, and the `ssz_static` CLI runner
  (`eth_ssz_vector_runner`, driven by `scripts/run_conformance.py`).
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

**Status: conformance-validated.** The Layer 1 spec
(total serialize / deserialize / hashTreeRoot), the `SSZRepr`
typeclass + deriving handler, the FFI SHA-256 backend, the
pure-Lean `Sha256Spec` reference, and the cache layer
(persistent `Node`, `Node.ofShape`, cached merkle walker,
gindex-driven `setManyAt`, fused commit `Node.commitAndHash`,
closure-based pending overlay, `sszUpdate` macro,
`SSZ.Box` user surface) are all landed. Consensus containers
cover Phase 0 through Gloas, including Fulu's `proposer_lookahead`
and the full Gloas ePBS `BeaconState` (nine EIP-7732 fields plus
the supporting `Builder` / `ExecutionPayloadBid` types).
Conformance pinned at consensus-spec-tests
[v1.6.0-beta.0](https://github.com/ethereum/consensus-spec-tests/releases/tag/v1.6.0-beta.0)
in `scripts/run_conformance.py`. The universal proof set
(`decode_encode`, `serialize_injective`, `encode_size_le_max`
over `SSZType.Supported`) and the AVX-512 SIMD inner loop for
`sha256BatchCombine` remain as planned follow-ups; see
[`packages/SizzLean/docs/PLAN.md`](packages/SizzLean/docs/PLAN.md)
for the staged plan.

## Documents

Per-subpackage design docs live next to the code they describe:

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

4. **`python3` + `uv`** (only for `official-ssz-vector-tests*`).
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
lake build LeanSha256
lake build SizzLean
lake build LeanEthCS
lake build LeanPoseidon     # standalone Poseidon2 island (fires its anchor KAT)

# Test suites (per package, run on demand):
lake build LeanSha256Tests
lake build SizzLeanTests
lake build LeanEthCSTests
lake build LeanPoseidonTests # committed Poseidon2 KATs (no Rust)
lake exe   poseidon_fuzz     # Poseidon2 differential test vs the zkhash oracle (needs cargo)
just test-poseidon-proofs    # mathlib equivalence proof permute = permuteRef (standalone; fetches olean cache)

# Bench + profile executables:
lake build ssz_bench       # microbench grid, S1–S7 (see SizzLeanBench.lean)
lake build ssz_profile     # phase-by-phase profile of one workload

# ssz_static / ssz_generic CLI driver (consumed by scripts/run_conformance.py):
lake build eth_ssz_vector_runner

# Or build a single subpackage in isolation:
cd packages/SizzLean && lake build
```

The repo's [`Justfile`](Justfile) wraps the common workflows
(`just build`, `just test`, `just bench`,
`just official-ssz-vector-tests-static`, …). See `just --list`
for the full set.

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
fetched at pinned tags by `just vendor-bls` / `just vendor-kzg` into
gitignored `vendor/` trees before `lake build` (never git submodules; see
[`hazmat-docs/ARCHITECTURE.md`](hazmat-docs/ARCHITECTURE.md) §6). `just
build` runs both vendor steps for you. The C / C++ compilers are invoked
through the Lean toolchain's `cc` wrapper, no separate configuration
required.

## Conformance harness

`scripts/run_conformance.py` drives the Lean `eth_ssz_vector_runner` CLI against
`ethereum/consensus-spec-tests` release archives. Default mode runs
the **`ssz_generic`** suite (type-agnostic SSZ tests for `uints`,
`basic_vector`, `bitvector`, `bitlist`, `boolean`, `containers`),
with a `--limit N` subset cap by default.

```bash
# One-time: create `.venv/` with the harness deps (cramjam + PyYAML).
# Wraps `uv venv` + `uv pip install -r scripts/requirements.txt`.
just setup-python

# Default: ssz_generic subset (5 cases per handler/suite)
.venv/bin/python scripts/run_conformance.py

# Full ssz_generic sweep
.venv/bin/python scripts/run_conformance.py --all

# Switch to ssz_static (per-fork consensus types)
.venv/bin/python scripts/run_conformance.py --suite static

# Single-shape focus
.venv/bin/python scripts/run_conformance.py --include 'generic:uints/*'
```

### Current dispatch coverage

Numbers below are against consensus-spec-tests **v1.6.0-beta.0**
(the tag pinned in `scripts/run_conformance.py`). Both presets
green across every fork Phase 0 → Fulu. Gloas and EIP-7805 test
vectors exist in the corpus but aren't yet in the CLI dispatch
table or the harness's `FORKS` list.

- **`ssz_generic`**: **2188 / 2188 in-scope cases pass** across
  all handlers (uints, basic_vector, bitvector, bitlist, boolean,
  containers). 292 progressive-container cases are deliberately
  out of scope. The test-only structs (`SingleFieldTestStruct`,
  `SmallTestStruct`, `FixedTestStruct`, `VarTestStruct`,
  `ComplexTestStruct`, `BitsStruct`) have their SSZ shapes
  hardcoded in `packages/LeanEthCS/LeanEthCS/Cli/Main.lean`.
- **`ssz_static --config mainnet --all`**: **1585 / 1585 cases
  pass** across every fork Phase 0 → Fulu.
- **`ssz_static --config minimal --all`**: **38991 / 38991 cases
  pass** across every fork Phase 0 → Fulu, including
  variable-size composites (`Attestation`, `BeaconBlockBody`,
  `BeaconState`) and all fork deltas
  (Altair / Bellatrix / Capella / Deneb / Electra / Fulu).
- **One-command full sweep**: `just official-ssz-vector-tests-all`
  drives generic + static-mainnet + static-minimal end-to-end.
