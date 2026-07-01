# Etheorem — task runner.
#
# Run `just` (no args) to list every available recipe, grouped by package.
# Each recipe's comment line is its description in `just --list`.
#
# Global recipes (build / test / lint / doctor / setup) come first and carry
# no prefix. Package-specific recipes are prefixed by their package
# (`leansha256-`, `hazmat-*-`, `sizzlean-`, `ethcl-`, `poseidon-`) and tagged
# with a `[group(...)]` so `just --list` sections them.
#
# The pyspec recipes need a Python venv. Run `just setup-python` once first.

# List every recipe with its description
default:
    @just --list --unsorted

# ═════════════════════════════════════════════════════════════════════════
# General — cross-package build, test, lint, and environment recipes
# ═════════════════════════════════════════════════════════════════════════

# Compile every library: the SSZ chain (LeanSha256 → SizzLean → EthCLLib →
# EthCLSpecs), the LeanHazmat FFI crypto families, and the standalone
# LeanPoseidon island. The vendored families (LeanHazmatBls, LeanHazmatKzg) need
# their `hazmat-*-vendor` recipes first; the dependencies run them (idempotent)
# before building. `lake build EthCLSpecs` pulls in EthCLLib + SizzLean
# transitively.

# Build all packages
[group('general')]
build: hazmat-bls-vendor hazmat-kzg-vendor
    lake build LeanSha256
    lake build LeanHazmatSha256
    lake build LeanHazmatBls
    lake build LeanHazmatKzg
    lake build SizzLean
    lake build EthCLSpecs
    lake build LeanPoseidon

# Compile the pyspec runners the pytest harnesses drive: `pyspec_server`
# (EthCLSpecs state transition / fork choice / ssz_static) and
# `ssz_generic_runner` (SizzLean ssz_generic wire-format suite).

# Build the pyspec runner binaries (pyspec_server + ssz_generic_runner)
[group('general')]
build-cli:
    lake build pyspec_server ssz_generic_runner

# All local tests — SHA-256 spec + FFI CAVP + BLS + KZG KATs + SSZ library gates
# + Poseidon2 anchor KAT. The consensus-spec libraries (EthCLLib / EthCLSpecs)
# have their own `ethcl-test` recipe and CI job.

# Run every local property-test recipe (all packages)
[group('general')]
test: leansha256-test hazmat-sha256-test hazmat-bls-test hazmat-kzg-test sizzlean-test poseidon-test

# Reject committed `sorry`, `#eval`, `#check`, `#print` in Lean source
# per CLAUDE.md. `git grep` searches tracked files only and returns 1
# when no matches — avoids `xargs -r grep`'s empty-input ambiguity (which
# exits 0). The CI `lint` job calls this recipe verbatim.

# Lint Lean sources for forbidden tokens (sorry / #eval / #check / #print)
[group('general')]
lint:
    @if git grep -nE '(\bsorry\b|^[[:space:]]*#(eval|check|print)\b)' -- '*.lean'; then \
        printf "\nForbidden token found in committed Lean source (see lines above).\n" >&2 ; \
        printf "Per CLAUDE.md: no sorry / #eval / #check / #print in committed code.\n" >&2 ; \
        exit 1; \
    fi

# Check the *build-time native* dependencies only: `pkg-config` (used
# by lakefile.lean to discover OpenSSL link/cflags) + OpenSSL 3.x (the
# library the SHA-256 FFI shim links to). Designed to run on a fresh
# CI runner *before* the Lean toolchain action installs elan/lake/lean,
# so it deliberately ignores those. Local devs usually want the
# fuller `just doctor` below.

# Verify build-time native deps (pkg-config + OpenSSL 3.x — for CI)
[group('general')]
doctor-native:
    #!/usr/bin/env bash
    set -u
    fail=0
    info() { printf "  ok   %s\n"   "$1"; }
    miss() { printf "  MISS %s\n"   "$1" >&2; fail=1; }

    echo "checking build-time native dependencies"
    echo

    if command -v cc >/dev/null 2>&1; then
      info "cc                ($(cc --version 2>&1 | head -1))"
    else
      miss "cc                (C compiler — builds the SHA-256 / blst FFI shims)"
    fi

    if command -v git >/dev/null 2>&1; then
      info "git               ($(git --version 2>&1 | head -1))"
    else
      miss "git               (needed by \`just hazmat-*-vendor\` to fetch vendored crypto sources)"
    fi

    if command -v pkg-config >/dev/null 2>&1; then
      info "pkg-config        ($(pkg-config --version))"
    else
      miss "pkg-config        (needed to discover OpenSSL link flags at build time)"
    fi

    if command -v pkg-config >/dev/null 2>&1 && pkg-config --exists libcrypto 2>/dev/null; then
      v=$(pkg-config --modversion libcrypto)
      info "libcrypto         (${v})"
      major=${v%%.*}
      if [ -z "${major}" ] || [ "${major}" -lt 3 ] 2>/dev/null; then
        miss "libcrypto         < 3.0 — SizzLean expects OpenSSL 3.x"
      fi
    else
      miss "libcrypto         (OpenSSL 3.x development headers + shared library)"
    fi

    if [ "$fail" -ne 0 ]; then
      echo
      echo "Some required build-time deps are missing. Install hints:"
      case "$(uname -s)" in
        Linux)
          if [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*(debian|ubuntu)' /etc/os-release; then
            echo "  Debian / Ubuntu : sudo apt install libssl-dev pkg-config"
          elif [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*(fedora|rhel|centos)' /etc/os-release; then
            echo "  Fedora / RHEL   : sudo dnf install openssl-devel pkgconf-pkg-config"
          elif [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*arch' /etc/os-release; then
            echo "  Arch            : sudo pacman -S openssl pkgconf"
          elif [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*alpine' /etc/os-release; then
            echo "  Alpine          : sudo apk add openssl-dev pkgconf"
          else
            echo "  Linux           : install OpenSSL 3.x development headers + pkg-config"
          fi
          ;;
        Darwin)
          echo "  macOS (brew)    : brew install openssl@3 pkg-config"
          ;;
        *)
          echo "  See packages/SizzLean/README.md → Dependencies for non-Linux/macOS setup"
          ;;
      esac
      exit 1
    fi

    echo
    echo "build-time native deps OK"

# Verify every dev-time dependency is present: build-time native deps
# (via `doctor-native`) plus the Lean toolchain (elan/lake/lean) and
# the Python harness toolchain (python3/uv). Prints actionable
# platform-specific install hints when something is missing. Local
# devs should run this; CI uses `doctor-native` instead because
# lean-action installs the Lean toolchain after the doctor step.

# Verify all dev-time deps (build-time native + Lean toolchain + Python)
[group('general')]
doctor: doctor-native
    #!/usr/bin/env bash
    set -u
    fail=0
    info() { printf "  ok   %s\n"   "$1"; }
    warn() { printf "  WARN %s\n"   "$1" >&2; }
    miss() { printf "  MISS %s\n"   "$1" >&2; fail=1; }

    echo
    echo "[ Lean toolchain ]"
    for cmd in elan lake lean; do
      if command -v "$cmd" >/dev/null 2>&1; then
        info "$(printf '%-17s' "$cmd") ($("$cmd" --version 2>&1 | head -1))"
      else
        miss "$(printf '%-17s' "$cmd") (install via elan: https://elan.lean-lang.org)"
      fi
    done

    echo
    echo "[ pyspec harness — only needed for the *-pyspec* pytest recipes ]"
    for cmd in python3 uv; do
      if command -v "$cmd" >/dev/null 2>&1; then
        info "$(printf '%-17s' "$cmd") ($("$cmd" --version 2>&1 | head -1))"
      else
        warn "$(printf '%-17s' "$cmd") (only needed for the pyspec harness)"
      fi
    done

    if [ "$fail" -ne 0 ]; then
      echo
      case "$(uname -s)" in
        Linux|Darwin) echo "  Lean toolchain  : curl https://elan.lean-lang.org/elan-init.sh -sSf | sh" ;;
        *) ;;
      esac
      exit 1
    fi

    echo
    echo "all dev-time deps present"

# Wipe Lake build artefacts (`.lake/` everywhere)
[group('general')]
clean:
    lake clean

# Wipe Lake artefacts *and* the Python venv
[group('general')]
clean-all: clean
    rm -rf .venv

# Create `.venv/` and install Python dependencies (uses `uv`)
[group('general')]
setup-python:
    uv venv
    uv pip install -r scripts/requirements.txt

# Idempotent guard the `*-pyspec*` recipes depend on: build the venv via
# `setup-python` only when `.venv/bin/python` is absent, so a test run on a
# fresh checkout self-provisions, while an existing venv is left untouched (a
# plain `setup-python` dependency would wipe and reinstall on every run).
[private]
_ensure-venv:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -x "{{ justfile_directory() }}/.venv/bin/python" ]; then
      echo "no Python venv found — provisioning via \`just setup-python\`"
      just setup-python
    fi

# ═════════════════════════════════════════════════════════════════════════
# EthCLSpecs — consensus-spec framework + Fulu / Gloas fork bodies
#
# EthCLLib + EthCLSpecs (the consensus-spec framework + Fulu/Gloas bodies). The
# `*Tests` libs carry the framework + spec `#guard` / `native_decide` self-tests
# (inheritance replay, the crypto seam, the running step, the classify driver);
# building them fires the gates.
# ═════════════════════════════════════════════════════════════════════════

# EthCLLib + EthCLSpecs self-tests (framework + Fulu/Gloas spec gates)
[group('ethcl')]
ethcl-test:
    lake build EthCLLib EthCLLibTests EthCLSpecs EthCLSpecsTests

# EthCLSpecs upstream-vector pyspec run via the per-worker Lean server. Defaults
# to the dev subset (a few cases per handler) on Fulu minimal; pass pytest args
# for more, e.g. `just ethcl-pyspec "--subset=0 -n auto"` or `"--fork=gloas"`.

# Run EthCLSpecs pyspec vectors via the Lean server (dev subset by default; pass pytest args)
[group('ethcl')]
ethcl-pyspec args="": _ensure-venv
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q {{ args }}

# CI smoke gate for EthCLSpecs pyspec: the dev subset (a few cases per
# handler) at minimal for both forks. Currently-green formats pass; the rest
# xfail as the Phase-2 work-queue, so the run is green (exit 0) iff no in-scope
# vector hits a bug-smell or a real mismatch. Mainnet / full sweep run on demand.

# CI smoke gate: EthCLSpecs pyspec dev subset for all three forks at minimal
[group('ethcl')]
ethcl-pyspec-smoke: _ensure-venv
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --fork=fulu --subset=2
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --fork=gloas --subset=2
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --fork=heze --subset=2

# The complete in-scope sweep: every collected vector (`--subset=0`) for the
# full matrix of {fulu, gloas, heze} × {minimal, mainnet}, sharded across cores. The
# three minimal forks finish quickly; the three mainnet forks are the long poles
# (real-size SSZ + crypto). Each xdist worker holds its own warm `pyspec_server`.

# Full EthCLSpecs pyspec sweep: {fulu,gloas,heze} × {minimal,mainnet}, sharded across cores
[group('ethcl')]
ethcl-pyspec-full: _ensure-venv
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n auto --preset=minimal --fork=fulu
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n auto --preset=minimal --fork=gloas
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n auto --preset=minimal --fork=heze
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n auto --preset=mainnet --fork=fulu
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n auto --preset=mainnet --fork=gloas
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n auto --preset=mainnet --fork=heze

# ═════════════════════════════════════════════════════════════════════════
# SizzLean — SSZ library
#
# The ssz_generic pyspec recipes are driven by the SizzLean pytest harness
# (`packages/SizzLean/PySpecTests/`) + `ssz_generic_runner`, against the
# `general` archive of `ethereum/consensus-spec-tests`. They exercise the
# `SSZType` wire format directly (uints, basic_vector, bitvector, bitlist,
# boolean, the test-only containers); the EIP-7495 / 7916 / 8016 progressive /
# stable / compatible forms are out of `SizzLean`'s universe and xfail. The
# per-fork consensus-container `ssz_static` vectors run inside the EthCLSpecs
# `ethcl-pyspec*` recipes (Fulu + Gloas), not here.
# ═════════════════════════════════════════════════════════════════════════

# `SizzLeanTests.PendingListShrink` Cases 4/5/7 deliberately drive
# OOB `SSZList.set!` writes — `Array.set!` prints a panic message
# on stderr before returning the array unchanged, so `lake build`
# surfaces a few `info: …Error: index out of bounds` lines from
# native_decide evaluation. The banner below primes readers; the
# file's module docstring has the full story.

# In-Lean SSZ-library property tests (hasher equivalence, Merkle PRNG, cache machinery on example containers)
[group('sizzlean')]
sizzlean-test:
    @echo "  note: PendingListShrink.lean Cases 4/5/7 deliberately exercise"
    @echo "  out-of-bounds SSZList writes; a few \"Error: index out of bounds\""
    @echo "  info: lines in the output below are expected and not failures."
    @echo "  The final \"Build completed successfully\" line is authoritative."
    @echo
    lake build SizzLeanTests

# ssz_generic pyspec via the SizzLean harness. Defaults to a dev subset;
# pass pytest args, e.g. `just sizzlean-pyspec "--subset=0 -n auto"`.

# Run ssz_generic wire-format pyspec via the SizzLean harness (dev subset by default; pass pytest args)
[group('sizzlean')]
sizzlean-pyspec args="": _ensure-venv
    cd packages/SizzLean/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q {{ args }}

# CI smoke gate: a few cases per (handler, valid/invalid).
[group('sizzlean')]
sizzlean-pyspec-smoke: _ensure-venv
    cd packages/SizzLean/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=2

# Full sweep: every in-scope wire-format vector (the out-of-scope progressive
# forms xfail). 2188 passed / 292 xfailed at the pin.

# Full ssz_generic pyspec sweep: every in-scope wire-format vector
[group('sizzlean')]
sizzlean-pyspec-full: _ensure-venv
    cd packages/SizzLean/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0

# Microbenchmarks — measure-then-optimise gates for Stage 17. Output also
# prints to stdout so you can pipe / inspect inline. The bench is run from the
# compiled native binary at `packages/SizzLean/.lake/build/bin/ssz_bench` —
# `lake build` produces it, then we exec it directly (rather than via
# `lake exe`) so there's no ambiguity that we're measuring the compiled binary,
# not any wrapper. The library `SizzLeanBench` is built with
# `precompileModules := true` (see `packages/SizzLean/lakefile.lean`) so every
# imported function is native code; the C shims are built with `-O3
# -march=native`.

# Build + run all SizzLean microbenchmarks; TSV → packages/SizzLean/bench/<timestamp>.tsv
[group('sizzlean')]
sizzlean-bench:
    @mkdir -p packages/SizzLean/bench
    @ts=$(date -u +%Y%m%dT%H%M%SZ); \
      lake build ssz_bench && \
      packages/SizzLean/.lake/build/bin/ssz_bench \
        | tee "packages/SizzLean/bench/$ts.tsv"

# Aligned column output for readability; falls back to plain diff if
# `column` is unavailable.

# Diff two bench TSVs. Usage: `just sizzlean-bench-diff before.tsv after.tsv`
[group('sizzlean')]
sizzlean-bench-diff before after:
    @diff -u {{ before }} {{ after }} | column -t -s $'\t' || diff -u {{ before }} {{ after }}

# ═════════════════════════════════════════════════════════════════════════
# LeanSha256 — pure-Lean SHA-256 reference (no FFI)
# ═════════════════════════════════════════════════════════════════════════

# Full NIST CAVP byte-oriented SHA-256 vectors against the pure-Lean SPEC — 129 cases via native_decide, ~108s (the 3 anchor FIPS 180-4 §B gates already fire on `lake build LeanSha256` itself; this adds the full upstream suite)
[group('leansha256')]
leansha256-test:
    lake build LeanSha256Tests

# Re-generate the NIST CAVP vector table (pure-Lean spec) from `packages/LeanSha256/cavp/*.rsp`
[group('leansha256')]
leansha256-gen-cavp:
    .venv/bin/python packages/LeanSha256/scripts/gen_sha256_cavp.py

# Bump LeanSha256's patch (Z) version, commit, and create the release tag.
# Does not push — prints the exact `git push` commands at the end. The
# mirror workflow translates the tag to `vX.Y.Z` on the downstream repo.
# Stdlib-only Python; no .venv needed.

# Bump LeanSha256 patch version, commit, and tag the release
[group('leansha256')]
leansha256-bump-patch:
    python3 packages/LeanSha256/scripts/bump_patch.py

# ═════════════════════════════════════════════════════════════════════════
# LeanHazmat — FFI crypto families (SHA-256 / BLS / KZG)
#
# The vendor recipes shallow-clone a pinned tag into a gitignored `vendor/`
# tree (hazmat-docs/ARCHITECTURE.md §6); the build itself stays offline. Run
# the relevant `hazmat-*-vendor` recipe once before building a vendored family
# (and as a CI step before the Lean build). Never a git submodule — the pin
# lives here.
# ═════════════════════════════════════════════════════════════════════════

# Full NIST CAVP byte-oriented SHA-256 vectors against the OpenSSL FFI shim (LeanHazmatSha256) — 129 cases + the combine/batch anchor KAT, all via native_decide
[group('hazmat')]
hazmat-sha256-test:
    lake build LeanHazmatSha256Tests

# Re-generate the NIST CAVP vector table (OpenSSL FFI shim) from `packages/LeanHazmatSha256/cavp/*.rsp`. Stdlib-only Python; no .venv needed.
[group('hazmat')]
hazmat-sha256-gen-cavp:
    python3 packages/LeanHazmatSha256/scripts/gen_cavp.py

# blst pin: tag v0.3.16 (commit e7f90de5…). This is exactly the rev
# c-kzg-4844 v2.1.7 expects for its blst submodule, so LeanHazmatKzg can
# build c-kzg against THIS blst (hazmat-docs/ARCHITECTURE.md §4).

blst_tag := "v0.3.16"

# Vendor blst (BLS12-381) for LeanHazmatBls — shallow clone at the pinned tag
[group('hazmat')]
hazmat-bls-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/LeanHazmatBls/vendor/blst"
    if [ -d "$dir/.git" ]; then
      echo "blst already vendored at $dir ($(git -C "$dir" describe --tags 2>/dev/null || echo unknown))"
      exit 0
    fi
    rm -rf "$dir"
    mkdir -p "$(dirname "$dir")"
    git clone --depth 1 --branch "{{ blst_tag }}" https://github.com/supranational/blst "$dir"
    echo "vendored blst {{ blst_tag }} -> $dir"

# Consensus BLS Known-Answer-Tests against the blst FFI shim (LeanHazmatBls) — consensus-spec sign/verify anchors + self-contained aggregate round-trips. Needs `just hazmat-bls-vendor` first (run via the dependency).
[group('hazmat')]
hazmat-bls-test: hazmat-bls-vendor
    lake build LeanHazmatBlsTests

# c-kzg-4844 pin: tag v2.1.7. Its blst submodule rev is exactly {{blst_tag}}
# (the LeanHazmatBls pin), so LeanHazmatKzg builds c-kzg against
# LeanHazmatBls's blst rather than vendoring a second copy (§4). Do NOT
# fetch c-kzg's --recursive blst.

ckzg_tag := "v2.1.7"

# Vendor c-kzg-4844 (KZG / EIP-4844) for LeanHazmatKzg — shallow clone, no submodules
[group('hazmat')]
hazmat-kzg-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/LeanHazmatKzg/vendor/c-kzg-4844"
    if [ -d "$dir/.git" ]; then
      echo "c-kzg already vendored at $dir ($(git -C "$dir" describe --tags 2>/dev/null || echo unknown))"
      exit 0
    fi
    rm -rf "$dir"
    mkdir -p "$(dirname "$dir")"
    # No --recursive: c-kzg's bundled blst is deliberately NOT fetched; we
    # build against LeanHazmatBls's blst (hazmat-docs/ARCHITECTURE.md §4).
    git clone --depth 1 --branch "{{ ckzg_tag }}" https://github.com/ethereum/c-kzg-4844 "$dir"
    # The trusted setup is embedded into the shim at build time from
    # data/trusted_setup.txt; refresh that committed copy from the pin.
    cp "$dir/src/trusted_setup.txt" packages/LeanHazmatKzg/data/trusted_setup.txt
    echo "vendored c-kzg {{ ckzg_tag }} -> $dir (trusted setup copied to data/)"

# KZG Known-Answer / round-trip tests against the c-kzg-4844 FFI shim (LeanHazmatKzg) — EIP-4844 commit/prove/verify + Fulu cell & recovery round-trips. Needs both vendor recipes (c-kzg builds against Bls's blst).
[group('hazmat')]
hazmat-kzg-test: hazmat-bls-vendor hazmat-kzg-vendor
    lake build LeanHazmatKzgTests

# ═════════════════════════════════════════════════════════════════════════
# LeanPoseidon — pure-Lean Poseidon2 (BN254 t=3), standalone island
# ═════════════════════════════════════════════════════════════════════════

# Building the core fires the in-file anchor-KAT `native_decide` gate
# (input [0,1,2] → the known BN254 t=3 Poseidon2 output). Nothing in
# the monorepo depends on LeanPoseidon (standalone island), so unlike
# the SSZ-chain libs it isn't built transitively — this recipe is how
# the anchor gate fires in `test` / CI. No Rust. Analogous to
# LeanSha256's 3 FIPS §B gates firing on `lake build LeanSha256`.

# LeanPoseidon core build — fires the Poseidon2 anchor KAT (no Rust)
[group('poseidon')]
poseidon-test:
    lake build LeanPoseidon

# The broader batch of HorizenLabs `zkhash` BN254 t=3 fixed
# permutation/compress vectors via `native_decide`, in the separate
# `LeanPoseidonTests` lib. Heavier than the single anchor; kept out of
# the default `lake build LeanPoseidon` (mirrors LeanSha256's
# 129-vector CAVP batch). Needs no Rust toolchain.

# Poseidon2 committed KAT batch (native_decide, no Rust)
[group('poseidon')]
poseidon-vectors:
    lake build LeanPoseidonTests

# Runs the pure-Lean permutation and the Rust `zkhash` oracle on N
# seeded-random inputs and asserts equality. This is the only recipe
# needing a Rust toolchain (cargo); `build` / `poseidon-test` /
# `poseidon-vectors` do not. See packages/LeanPoseidon/README.md.

# Poseidon2 differential conformance vs the Rust zkhash oracle (needs cargo)
[group('poseidon')]
poseidon-fuzz:
    lake exe poseidon_fuzz

# The mathlib proofs: `permute = permuteRef` (fast layers = dense reference),
# `permute` is a bijection, `pad` is injective, `compress` is not injective,
# and the round-count `#guard`s. Lives in the standalone `LeanPoseidonProofs`
# package — the monorepo's only mathlib dependency, built on its own so the
# core and all other recipes stay mathlib-free. `cache get` fetches mathlib's
# prebuilt oleans (the v4.29.1 pin matches the repo toolchain), so nothing is
# compiled from scratch. Kept out of `test`/`build` (heavy; needs the cache).

# Poseidon2 structural-correctness + equivalence proofs (mathlib; fetches olean cache)
[group('poseidon')]
poseidon-proofs:
    cd packages/LeanPoseidonProofs && lake exe cache get && lake build LeanPoseidonProofs

# Emits packages/LeanPoseidon/LeanPoseidon/Params.lean from the pinned
# HorizenLabs `zkhash` reference. Stdlib-only Python; no .venv needed.

# Re-generate the BN254 t=3 Poseidon2 constants table
[group('poseidon')]
poseidon-gen-params:
    python3 packages/LeanPoseidon/scripts/gen_poseidon_params.py
