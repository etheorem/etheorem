# Etheorem, task runner.
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

# xdist worker count for the full pyspec sweeps; `auto` (one per core) is the
# historical default. Override on memory-constrained machines:
# `PYTEST_JOBS=2 just ethcl-pyspec-full`.
pytest_jobs := env_var_or_default("PYTEST_JOBS", "auto")

# The vector `just ethcl-profile` profiles when the caller names none: the Gloas
# mainnet `sanity/blocks` case the OPTIMISATION.md Stage 17d row table was
# measured on. Any extracted vector directory holding a `pre.ssz_snappy` works.
default_profile_case := env_var("HOME") + "/.cache/sizzlean/v1.7.0-alpha.11-mainnet/tests/mainnet/gloas/sanity/blocks/pyspec_tests/full_random_operations_0"

# List every recipe with its description
default:
    @just --list --unsorted

# ═════════════════════════════════════════════════════════════════════════
# General, cross-package build, test, lint, and environment recipes
# ═════════════════════════════════════════════════════════════════════════

# Compile every library: the SSZ chain (LeanSha256 → SizzLean → EthCLLib →
# EthCLSpecs), the LeanHazmat FFI crypto families (consensus + execution),
# the aggregators, and the standalone LeanPoseidon island. The vendored
# families need their `hazmat-*-vendor` recipes first; the dependencies run
# them (idempotent) before building. `lake build EthCLSpecs` pulls in
# EthCLLib + SizzLean transitively; `lake build LeanHazmat` pulls every
# crypto family + both aggregators.

# Build all packages
[group('general')]
build: hazmat-sha256-vendor hazmat-bls-vendor hazmat-kzg-vendor hazmat-keccak-vendor hazmat-secp256k1-vendor hazmat-bn254-vendor
    lake build LeanSha256
    lake build LeanHazmat
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

# All local tests, SHA-256 spec + FFI CAVP + BLS + KZG KATs + the seven
# execution-layer family KATs + SSZ library gates + Poseidon2 anchor KAT.
# The consensus-spec libraries (EthCLLib / EthCLSpecs) have their own
# `ethcl-test` recipe and CI job.

# Run every local property-test recipe (all packages)
[group('general')]
test: leansha256-test hazmat-sha256-test hazmat-bls-test hazmat-kzg-test hazmat-keccak-test hazmat-secp256k1-test hazmat-bn254-test hazmat-blake2f-test hazmat-ripemd160-test hazmat-modexp-test hazmat-p256-test sizzlean-test poseidon-test

# Reject committed `sorry`, `#eval`, `#check`, `#print` in Lean source
# per CLAUDE.md. `git grep` searches tracked files only and returns 1
# when no matches. That avoids `xargs -r grep`'s empty-input ambiguity
# (which exits 0). The CI `lint` job calls this recipe verbatim.

# Lint Lean sources for forbidden tokens (sorry / #eval / #check / #print)
[group('general')]
lint:
    @if git grep -nE '(\bsorry\b|^[[:space:]]*#(eval|check|print)\b)' -- '*.lean'; then \
        printf "\nForbidden token found in committed Lean source (see lines above).\n" >&2 ; \
        printf "Per CLAUDE.md: no sorry / #eval / #check / #print in committed code.\n" >&2 ; \
        exit 1; \
    fi

# Resolve every `File.lean:start-end` citation in
# `packages/EthCLSpecs/docs/PROOF_LEDGER.md` and the
# `EthCLSpecs/Proofs/` module docstrings against the declaration it names, and
# fail on a mismatch. Spans rot silently whenever a cited file grows above the
# declaration, and refreshing them per-PR leaves the table mixing fresh and
# stale rows. `--fix` rewrites the stale spans in place. Stdlib-only Python; no
# .venv needed. The CI `lint` job runs this next to `just lint`.

# Check the line-span citations into the spec bodies (pass --fix to rewrite them)
[group('general')]
check-citations args="":
    python3 scripts/check_citations.py {{ args }}

# Two facts about a spec constant have to match upstream, and neither is visible
# from the Lean source: its tier (preset file -> `Preset` class, config file ->
# `Config` class, constants table -> flat literal) and the fork that introduces
# it. Both rot silently at a re-pin, when upstream moves a value between tiers or
# a later fork takes over a constant an earlier one owned. A misfiled preset
# value is a correctness bug, not an untidiness: it can shape an SSZ cap, so the
# day the two preset files diverge it produces a wrong root and a green build.
# `--refresh` re-downloads the pinned specs and rewrites
# `scripts/constant_tiers.json`; run it whenever the pin moves. Stdlib-only
# Python; only `--refresh` needs the network.

# Check each spec constant's tier and owning fork (pass --refresh after a re-pin)
[group('general')]
check-constants args="":
    python3 scripts/check_constant_tiers.py {{ args }}

# How much of the executable spec is formally verified, read out of the built
# `.olean`s: every `forkdef` is the denominator, a theorem statement that mentions
# one puts it at the touched tier, and a `@[characterizes f]` tag puts it at the
# characterized tier. The report also audits every theorem's axioms and prints the
# `SizzLean` property matrix. Needs `lake build EthCLSpecs` first; it reads the
# compiled environment, so it costs seconds and never elaborates a proof again.

# Build the two libraries whose `.olean`s the report reads. Up to date, this
# costs a second; from cold it is the ordinary build. All three proof-coverage
# recipes depend on it, so the report can never read a stale environment.
[private]
proof-coverage-build:
    lake build SizzLean EthCLSpecs

# Report proof coverage of the fork bodies and the SSZ properties
[group('general')]
proof-coverage: proof-coverage-build
    lake env lean --run scripts/ProofCoverage.lean

# The ratchet. Exact equality against the committed baselines, one per package
# (`packages/EthCLSpecs/docs/` for the fork bodies, `packages/SizzLean/docs/` for
# the SSZ properties), in both directions: a lost proof fails, and a new proof
# fails until its author commits the bump. A floor-only count would miss a swap of
# one proof for another. The CI `ethcl` job runs this after the build.

# Fail when proof coverage drifts from the committed baseline
[group('general')]
proof-coverage-check: proof-coverage-build
    lake env lean --run scripts/ProofCoverage.lean -- --check

# Rewrite both baselines and the generated block in the `EthCLSpecs` README from
# the current build. Run it in the PR that adds or removes a proof, and commit
# the diff; that diff is the coverage change, under review.

# Rewrite the proof-coverage baselines and README block
[group('general')]
proof-coverage-update: proof-coverage-build
    lake env lean --run scripts/ProofCoverage.lean -- --update

# Check the *build-time native* dependencies. The default profile (`all`)
# probes everything the family builds need: `cc` and `git`, `pkg-config` +
# OpenSSL 3.x (which the lakefiles discover via `pkg-config`), the
# RIPEMD-160 capability (LeanHazmatRipemd160), a C++ compiler
# (LeanHazmatBn254), and `nasm` on x86_64 Linux (LeanHazmatSha256's
# ISA-L unit). The `consensus` profile drops the two execution-only
# probes (the RIPEMD-160 capability and the C++ compiler) for jobs whose
# build never compiles those families.
# Designed to run on a fresh CI runner *before* the Lean toolchain action
# installs elan/lake/lean, so it deliberately ignores those. Local devs
# usually want the fuller `just doctor` below.

# Verify build-time native deps (profile: all | consensus, default all)
[group('general')]
doctor-native profile="all":
    #!/usr/bin/env bash
    set -u
    case "{{ profile }}" in
      all|consensus) ;;
      *) echo "unknown profile '{{ profile }}' (all | consensus)" >&2; exit 2 ;;
    esac
    fail=0
    info() { printf "  ok   %s\n"   "$1"; }
    warn() { printf "  WARN %s\n"   "$1" >&2; }
    miss() { printf "  MISS %s\n"   "$1" >&2; fail=1; }

    echo "checking build-time native dependencies"
    echo

    if command -v cc >/dev/null 2>&1; then
      info "cc                ($(cc --version 2>&1 | head -1))"
    else
      miss "cc                (C compiler, builds every LeanHazmat FFI shim)"
    fi

    # LeanHazmatRipemd160 needs its digest computable by the linked
    # libcrypto. Probe in the shim's own order: the default provider
    # first (3.0.7+ serve RIPEMD-160 there), then the legacy module
    # named explicitly (3.0.0-3.0.6 keep it there; the CLI never
    # auto-loads it, so a plain probe would report MISS on hosts where
    # the shim itself would succeed). The `consensus` profile skips the
    # probe (no Ripemd160 in that build).
    if [ "{{ profile }}" = "all" ]; then
      cli=""
    if command -v pkg-config >/dev/null 2>&1 && pkg-config --exists libcrypto 2>/dev/null; then
      cand="$(pkg-config --variable=exec_prefix libcrypto 2>/dev/null)/bin/openssl"
      [ -x "$cand" ] && cli="$cand"
    fi
    if [ -z "$cli" ] && command -v openssl >/dev/null 2>&1; then
      cli="openssl"
    fi
    if [ -n "$cli" ]; then
      if printf '' | "$cli" dgst -rmd160 >/dev/null 2>&1; then
        info "ripemd160         (served by the default provider; LeanHazmatRipemd160 needs it)"
      elif printf '' | "$cli" dgst -rmd160 -provider default -provider legacy >/dev/null 2>&1; then
        info "ripemd160         (served via the legacy provider module; LeanHazmatRipemd160 loads it itself)"
      else
        miss "ripemd160         (not computable; OpenSSL 3.0.0-3.0.6 need the legacy provider module installed, 3.0.7+ serve it by default)"
      fi
    else
      warn "ripemd160         (no openssl CLI to probe; the build needs RIPEMD-160 servable by the pkg-config libcrypto)"
    fi
    fi

    # LeanHazmatBn254 compiles vendored mcl (the one C++ family) with
    # its C++ runtime compiled out; only a C++ *compiler* is needed,
    # and the check is Linux-only (the macOS build is untested; see
    # packages/hazmat/LeanHazmatBn254/docs/ARCHITECTURE.md). The `consensus`
    # profile skips the probe (no Bn254 in that build).
    if [ "{{ profile }}" = "all" ] && [ "$(uname -s)" = "Linux" ]; then
      if command -v c++ >/dev/null 2>&1; then
        info "c++               ($(c++ --version 2>&1 | head -1))"
      else
        miss "c++               (C++ compiler, builds the vendored mcl for LeanHazmatBn254)"
      fi
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
        miss "libcrypto         < 3.0, SizzLean expects OpenSSL 3.x"
      fi
    else
      miss "libcrypto         (OpenSSL 3.x development headers + shared library)"
    fi

    # x86_64 Linux only: LeanHazmatSha256 builds the vendored ISA-L
    # `sha256_mb` unit (the multi-buffer SHA-256 lanes are nasm
    # assembly). Every other host takes the OpenSSL loop and needs no
    # assembler.
    if [ "$(uname -s)" = "Linux" ] && [ "$(uname -m)" = "x86_64" ]; then
      if command -v nasm >/dev/null 2>&1; then
        info "nasm              ($(nasm -v 2>&1 | head -1))"
      else
        miss "nasm              (assembles the vendored ISA-L SHA-256 multi-buffer lanes; x86_64 Linux only)"
      fi
    fi

    if [ "$fail" -ne 0 ]; then
      echo
      echo "Some required build-time deps are missing. Install hints:"
      case "$(uname -s)" in
        Linux)
          if [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*(debian|ubuntu)' /etc/os-release; then
            echo "  Debian / Ubuntu : sudo apt install libssl-dev pkg-config nasm g++"
          elif [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*(fedora|rhel|centos)' /etc/os-release; then
            echo "  Fedora / RHEL   : sudo dnf install openssl-devel pkgconf-pkg-config nasm gcc-c++"
          elif [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*arch' /etc/os-release; then
            echo "  Arch            : sudo pacman -S openssl pkgconf nasm gcc"
          elif [ -r /etc/os-release ] && grep -qE '^ID(_LIKE)?=.*alpine' /etc/os-release; then
            echo "  Alpine          : sudo apk add openssl-dev pkgconf nasm g++"
          else
            echo "  Linux           : install OpenSSL 3.x development headers + pkg-config + a C++ toolchain (+ nasm on x86_64)"
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
    echo "[ pyspec harness, only needed for the *-pyspec* pytest recipes ]"
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
      echo "no Python venv found, provisioning via \`just setup-python\`"
      just setup-python
    fi

# ═════════════════════════════════════════════════════════════════════════
# EthCLSpecs, consensus-spec framework + Fulu / Gloas / Heze fork bodies
#
# EthCLLib + EthCLSpecs (the consensus-spec framework + Fulu/Gloas bodies). The
# `*Tests` libs carry the framework + spec `#guard` / `native_decide` self-tests
# (inheritance replay, the crypto seam, the running step, the classify driver);
# building them fires the gates.
# ═════════════════════════════════════════════════════════════════════════

# EthCLLib + EthCLSpecs self-tests (framework + fork spec gates)
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
# handler) at minimal for all three forks. Currently-green formats pass; the rest
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
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n {{ pytest_jobs }} --preset=minimal --fork=fulu
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n {{ pytest_jobs }} --preset=minimal --fork=gloas
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n {{ pytest_jobs }} --preset=minimal --fork=heze
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n {{ pytest_jobs }} --preset=mainnet --fork=fulu
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n {{ pytest_jobs }} --preset=mainnet --fork=gloas
    cd packages/EthCLSpecs/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0 -n {{ pytest_jobs }} --preset=mainnet --fork=heze

# The Stage 17d container profile: which consensus container types dominate
# encode / decode / root cost on a real mainnet state transition. Runs the
# `specs_profile` exe over one upstream vector, at the mainnet preset, and
# writes a TSV in the same column shape `just sizzlean-bench` emits, so
# `just sizzlean-bench-diff` compares a profile pair directly.
#
# `case` is a vector directory under the harness cache
# (`~/.cache/sizzlean/<tag>-mainnet/tests/mainnet/<fork>/...`); the default is
# the Gloas `sanity/blocks` case the OPTIMISATION.md row table was measured on.
# The archive must already be extracted: run any `ethcl-pyspec` recipe once
# first, which downloads it.

# Profile the consensus container types over one pyspec vector; TSV → packages/SizzLean/bench/specs-profile-<timestamp>.tsv
[group('ethcl')]
ethcl-profile case=default_profile_case: _ensure-venv
    @mkdir -p packages/SizzLean/bench
    @ts=$(date -u +%Y%m%dT%H%M%SZ); \
      tmp=$(mktemp -d); \
      paths=$({{ justfile_directory() }}/.venv/bin/python scripts/prepare_profile_vector.py "{{ case }}" "$tmp"); \
      lake build specs_profile && \
      packages/EthCLSpecs/.lake/build/bin/specs_profile $paths \
        | tee "packages/SizzLean/bench/specs-profile-$ts.tsv"; \
      rm -rf "$tmp"

# ═════════════════════════════════════════════════════════════════════════
# SizzLean, SSZ library
#
# The ssz_generic pyspec recipes are driven by the SizzLean pytest harness
# (`packages/SizzLean/PySpecTests/`) + `ssz_generic_runner`, against the
# `general` archive of `ethereum/consensus-spec-tests`. They exercise the
# `SSZType` wire format directly (uints, basic_vector, bitvector, bitlist,
# boolean, the test-only containers); the EIP-7495 / 7916 / 8016 progressive /
# stable / compatible forms are out of `SizzLean`'s universe and xfail. The
# per-fork consensus-container `ssz_static` vectors run inside the EthCLSpecs
# `ethcl-pyspec*` recipes (the fork bodies), not here.
# ═════════════════════════════════════════════════════════════════════════

# `SizzLeanTests.PendingListShrink` Cases 4/5/7 deliberately drive
# OOB `SSZList.set!` writes. `Array.set!` prints a panic message
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
# forms xfail). 2215 passed / 294 xfailed at the pin (`v1.7.0-alpha.13`, frozen; see
# `packages/SizzLean/PySpecTests/harness.py`).

# Full ssz_generic pyspec sweep: every in-scope wire-format vector
[group('sizzlean')]
sizzlean-pyspec-full: _ensure-venv
    cd packages/SizzLean/PySpecTests && {{ justfile_directory() }}/.venv/bin/python -m pytest -q --subset=0

# Microbenchmarks, measure-then-optimise gates for Stage 17. Output also
# prints to stdout so you can pipe / inspect inline. The bench is run from the
# compiled native binary at `packages/SizzLean/.lake/build/bin/ssz_bench`.
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

# Stage 17c heap bench: N resident states, hash-consing off vs on. Reports
# distinct tree cells (deterministic, allocator-independent) per config.

# Build + run the multi-state hash-consing heap bench; TSV → packages/SizzLean/bench/multistate-<timestamp>.tsv
[group('sizzlean')]
sizzlean-bench-multistate:
    @mkdir -p packages/SizzLean/bench
    @ts=$(date -u +%Y%m%dT%H%M%SZ); \
      lake build ssz_multistate && \
      packages/SizzLean/.lake/build/bin/ssz_multistate \
        | tee "packages/SizzLean/bench/multistate-$ts.tsv"

# The comparative benchmark against `ethereum/ssz-specs` and
# `lambdaclass/libssz`. The driver does the whole job: it builds SizzLean's
# harness, downloads and compiles both comparables at pinned revisions, emits
# the shared 2.9 MB `BeaconState`, runs the three harnesses, checks that they
# agree on every root, and writes the markdown report. It needs `cargo` and a
# Python 3.12 or later interpreter besides `lake`; on x86_64 Linux the Lean
# build also needs `nasm`, for the vendored ISA-L lanes, which is why this
# recipe runs `hazmat-sha256-vendor` first. `scripts/compbench/README.md`
# states the method. Each harness runs each scenario 100 times and the report
# gives the mean, which takes about four minutes. Extra arguments pass
# through, so `just sizzlean-comp-benchmark "--reps 20"` shortens the run and
# `--skip-build` re-measures without rebuilding.

# Comparative benchmark vs ssz-specs + libssz; markdown → packages/SizzLean/bench/comparative-<timestamp>.md
[group('sizzlean')]
sizzlean-comp-benchmark *args: hazmat-sha256-vendor
    python3 scripts/comparative_benchmark.py {{ args }}

# Aligned column output for readability; falls back to plain diff if
# `column` is unavailable.

# Diff two bench TSVs. Usage: `just sizzlean-bench-diff before.tsv after.tsv`
[group('sizzlean')]
sizzlean-bench-diff before after:
    @diff -u {{ before }} {{ after }} | column -t -s $'\t' || diff -u {{ before }} {{ after }}

# ═════════════════════════════════════════════════════════════════════════
# LeanSha256, pure-Lean SHA-256 reference (no FFI)
# ═════════════════════════════════════════════════════════════════════════

# Full NIST CAVP byte-oriented SHA-256 vectors against the pure-Lean SPEC, 129 cases via native_decide, ~108s (the 3 anchor FIPS 180-4 §B gates already fire on `lake build LeanSha256` itself; this adds the full upstream suite)
[group('leansha256')]
leansha256-test:
    lake build LeanSha256Tests

# Re-generate the NIST CAVP vector table (pure-Lean spec) from `packages/LeanSha256/cavp/*.rsp`
[group('leansha256')]
leansha256-gen-cavp:
    .venv/bin/python packages/LeanSha256/scripts/gen_sha256_cavp.py

# Bump LeanSha256's patch (Z) version, commit, and create the release tag.
# Does not push. Prints the exact `git push` commands at the end. The
# mirror workflow translates the tag to `vX.Y.Z` on the downstream repo.
# Stdlib-only Python; no .venv needed.

# Bump LeanSha256 patch version, commit, and tag the release
[group('leansha256')]
leansha256-bump-patch:
    python3 packages/LeanSha256/scripts/bump_patch.py

# ═════════════════════════════════════════════════════════════════════════
# LeanHazmat, FFI crypto families (consensus + execution layer)
#
# The vendor recipes shallow-clone a pinned tag (or rev) into a gitignored
# `vendor/` tree (packages/hazmat/docs/ARCHITECTURE.md §6); the build itself stays
# offline. Run the relevant `hazmat-*-vendor` recipe once before building a
# vendored family (and as a CI step before the Lean build). Never a git
# submodule. The pin lives here. The OpenSSL-backed families (Sha256,
# Ripemd160, Modexp, P256) and the in-repo Blake2f shim vendor nothing.
# ═════════════════════════════════════════════════════════════════════════

# ISA-L crypto pin: tag v2.26.1 (commit
# c353c2d021c03cfc6180ddf9e28a24b3b61e9760). Only its `sha256_mb` unit
# is built (the multi-buffer SHA-256 engine behind `sha256BatchCombine`
# on x86_64 Linux; every other host keeps the OpenSSL loop and never
# reads this tree). The recipe checks the vendored checkout's HEAD
# against this rev, so a stale tree from an older pin re-fetches
# instead of passing. The lakefile drives ISA-L's own `Makefile.unx`,
# which needs `nasm` on PATH (`just doctor-native` checks), and traces
# the `.pin` file so a re-vendor rebuilds.

isal_tag := "v2.26.1"
isal_rev := "c353c2d021c03cfc6180ddf9e28a24b3b61e9760"

# Vendor ISA-L crypto (multi-buffer SHA-256) for LeanHazmatSha256, shallow clone at the pinned tag
[group('hazmat')]
hazmat-sha256-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/hazmat/LeanHazmatSha256/vendor/isa-l_crypto"
    if [ -d "$dir/.git" ]; then
      rev=$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo unknown)
      if [ "$rev" = "{{ isal_rev }}" ]; then
        printf '%s\n' "{{ isal_rev }}" > "$dir/.pin"
        echo "isa-l_crypto already vendored at $dir ({{ isal_tag }})"
        exit 0
      fi
      echo "isa-l_crypto vendored at wrong rev ($rev), re-fetching" >&2
      rm -rf "$dir"
    fi
    mkdir -p "$(dirname "$dir")"
    git clone --depth 1 --branch "{{ isal_tag }}" https://github.com/intel/isa-l_crypto "$dir"
    rev=$(git -C "$dir" rev-parse HEAD)
    [ "$rev" = "{{ isal_rev }}" ] || { echo "fetched $rev, expected {{ isal_rev }}" >&2; exit 1; }
    printf '%s\n' "{{ isal_rev }}" > "$dir/.pin"
    echo "vendored isa-l_crypto {{ isal_tag }} -> $dir"

# Full NIST CAVP byte-oriented SHA-256 vectors against the FFI shim (LeanHazmatSha256), 129 cases + the combine/batch anchor KAT, all via native_decide. Needs `just hazmat-sha256-vendor` on x86_64 Linux (run via the dependency).
[group('hazmat')]
hazmat-sha256-test: hazmat-sha256-vendor
    lake build LeanHazmatSha256Tests

# Re-generate the NIST CAVP vector table (OpenSSL FFI shim) from `packages/hazmat/LeanHazmatSha256/cavp/*.rsp`. Stdlib-only Python; no .venv needed.
[group('hazmat')]
hazmat-sha256-gen-cavp:
    python3 packages/hazmat/LeanHazmatSha256/scripts/gen_cavp.py

# blst pin: tag v0.3.16 (commit
# e7f90de551e8df682f3cc99067d204d8b90d27ad). This is exactly the rev
# c-kzg-4844 v0.2.1 expects for its blst submodule, so LeanHazmatKzg
# can build c-kzg against THIS blst (packages/hazmat/docs/ARCHITECTURE.md
# §4). The recipe checks the vendored checkout's HEAD against this
# rev, so a stale tree from an older pin re-fetches instead of
# passing; the lakefiles trace the `.pin` file.

blst_tag := "v0.3.16"
blst_rev := "e7f90de551e8df682f3cc99067d204d8b90d27ad"

# Vendor blst (BLS12-381) for LeanHazmatBls, shallow clone at the pinned tag
[group('hazmat')]
hazmat-bls-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/hazmat/LeanHazmatBls/vendor/blst"
    if [ -d "$dir/.git" ]; then
      rev=$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo unknown)
      if [ "$rev" = "{{ blst_rev }}" ]; then
        printf '%s\n' "{{ blst_rev }}" > "$dir/.pin"
        echo "blst already vendored at $dir ({{ blst_tag }})"
        exit 0
      fi
      echo "blst vendored at wrong rev ($rev), re-fetching" >&2
      rm -rf "$dir"
    fi
    mkdir -p "$(dirname "$dir")"
    git clone --depth 1 --branch "{{ blst_tag }}" https://github.com/supranational/blst "$dir"
    rev=$(git -C "$dir" rev-parse HEAD)
    [ "$rev" = "{{ blst_rev }}" ] || { echo "fetched $rev, expected {{ blst_rev }}" >&2; exit 1; }
    printf '%s\n' "{{ blst_rev }}" > "$dir/.pin"
    echo "vendored blst {{ blst_tag }} -> $dir"

# Consensus BLS Known-Answer-Tests against the blst FFI shim (LeanHazmatBls), consensus-spec sign/verify anchors + self-contained aggregate round-trips. Needs `just hazmat-bls-vendor` first (run via the dependency).
[group('hazmat')]
hazmat-bls-test: hazmat-bls-vendor
    lake build LeanHazmatBlsTests

# c-kzg-4844 pin: tag v2.1.7. Its blst submodule rev is exactly {{blst_tag}}
# (the LeanHazmatBls pin), so LeanHazmatKzg builds c-kzg against
# LeanHazmatBls's blst rather than vendoring a second copy (§4). Do NOT
# fetch c-kzg's --recursive blst.

ckzg_tag := "v2.1.7"
ckzg_rev := "9f4bcc83cbb17b3dbc3432de7320790968143ab9"

# Vendor c-kzg-4844 (KZG / EIP-4844) for LeanHazmatKzg, shallow clone, no submodules
[group('hazmat')]
hazmat-kzg-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/hazmat/LeanHazmatKzg/vendor/c-kzg-4844"
    if [ -d "$dir/.git" ]; then
      rev=$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo unknown)
      if [ "$rev" = "{{ ckzg_rev }}" ]; then
        printf '%s\n' "{{ ckzg_rev }}" > "$dir/.pin"
        echo "c-kzg already vendored at $dir ({{ ckzg_tag }})"
        exit 0
      fi
      echo "c-kzg vendored at wrong rev ($rev), re-fetching" >&2
      rm -rf "$dir"
    fi
    mkdir -p "$(dirname "$dir")"
    # No --recursive: c-kzg's bundled blst is deliberately not fetched;
    # the build links LeanHazmatBls's blst instead (ARCHITECTURE.md 4).
    git clone --depth 1 --branch "{{ ckzg_tag }}" https://github.com/ethereum/c-kzg-4844 "$dir"
    rev=$(git -C "$dir" rev-parse HEAD)
    [ "$rev" = "{{ ckzg_rev }}" ] || { echo "fetched $rev, expected {{ ckzg_rev }}" >&2; exit 1; }
    printf '%s\n' "{{ ckzg_rev }}" > "$dir/.pin"

    # The trusted setup is embedded into the shim at build time from
    # data/trusted_setup.txt; refresh that committed copy from the pin.
    cp "$dir/src/trusted_setup.txt" packages/hazmat/LeanHazmatKzg/data/trusted_setup.txt
    echo "vendored c-kzg {{ ckzg_tag }} -> $dir"

# KZG Known-Answer / round-trip tests against the c-kzg-4844 FFI shim (LeanHazmatKzg), EIP-4844 commit/prove/verify + Fulu cell & recovery round-trips. Needs both vendor recipes (c-kzg builds against Bls's blst).
[group('hazmat')]
hazmat-kzg-test: hazmat-bls-vendor hazmat-kzg-vendor
    lake build LeanHazmatKzgTests

# ── Execution-layer families (packages/hazmat/docs/PLAN.md Phase 2) ────────────

# keccak-tiny pin: no upstream tags, so the pin is the commit rev. The
# vendor recipe fetches exactly this rev and checks it back.

keccak_tiny_rev := "64b6647514212b76ae7bca0dea9b7b197d1d8186"

# Vendor keccak-tiny (Keccak-256) for LeanHazmatKeccak, shallow fetch of the pinned rev
[group('hazmat')]
hazmat-keccak-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/hazmat/LeanHazmatKeccak/vendor/keccak-tiny"
    if [ -d "$dir/.git" ]; then
      rev=$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo unknown)
      if [ "$rev" = "{{ keccak_tiny_rev }}" ]; then
        printf '%s\n' "{{ keccak_tiny_rev }}" > "$dir/.pin"
        echo "keccak-tiny already vendored at $dir ($rev)"
        exit 0
      fi
      echo "keccak-tiny vendored at wrong rev ($rev), re-fetching" >&2
      rm -rf "$dir"
    fi
    mkdir -p "$(dirname "$dir")"
    # Upstream tags no releases, so fetch the pinned rev directly
    # (GitHub allows fetch-by-SHA) and check it out detached.
    git init -q "$dir"
    git -C "$dir" remote add origin https://github.com/coruus/keccak-tiny
    git -C "$dir" fetch -q --depth 1 origin "{{ keccak_tiny_rev }}"
    git -C "$dir" checkout -q --detach FETCH_HEAD
    rev=$(git -C "$dir" rev-parse HEAD)
    [ "$rev" = "{{ keccak_tiny_rev }}" ] || { echo "fetched $rev, expected {{ keccak_tiny_rev }}" >&2; exit 1; }
    printf '%s\n' "{{ keccak_tiny_rev }}" > "$dir/.pin"
    echo "vendored keccak-tiny {{ keccak_tiny_rev }} -> $dir"

# Keccak-256 Known-Answer-Tests against the keccak-tiny FFI shim (LeanHazmatKeccak), EVM canonical constants + published vectors + the EIP-155 address-derivation composition. Needs `just hazmat-keccak-vendor` (run via the dependency).
[group('hazmat')]
hazmat-keccak-test: hazmat-keccak-vendor
    lake build LeanHazmatKeccakTests

# libsecp256k1 pin: tag v0.8.0 (commit
# 6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d). The recipe checks the
# vendored checkout's HEAD against this rev, so a stale tree from an
# older pin (or an interrupted clone) re-fetches instead of passing.

secp256k1_tag := "v0.8.0"
secp256k1_rev := "6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d"

# Vendor libsecp256k1 (secp256k1 ECDSA) for LeanHazmatSecp256k1, shallow clone at the pinned tag
[group('hazmat')]
hazmat-secp256k1-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/hazmat/LeanHazmatSecp256k1/vendor/secp256k1"
    if [ -d "$dir/.git" ]; then
      rev=$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo unknown)
      if [ "$rev" = "{{ secp256k1_rev }}" ]; then
        printf '%s\n' "{{ secp256k1_rev }}" > "$dir/.pin"
        echo "libsecp256k1 already vendored at $dir ({{ secp256k1_tag }})"
        exit 0
      fi
      echo "libsecp256k1 vendored at wrong rev ($rev), re-fetching" >&2
      rm -rf "$dir"
    fi
    mkdir -p "$(dirname "$dir")"
    git clone --depth 1 --branch "{{ secp256k1_tag }}" https://github.com/bitcoin-core/secp256k1 "$dir"
    rev=$(git -C "$dir" rev-parse HEAD)
    [ "$rev" = "{{ secp256k1_rev }}" ] || { echo "fetched $rev, expected {{ secp256k1_rev }}" >&2; exit 1; }
    printf '%s\n' "{{ secp256k1_rev }}" > "$dir/.pin"
    echo "vendored libsecp256k1 {{ secp256k1_tag }} -> $dir"

# secp256k1 Known-Answer-Tests against the libsecp256k1 FFI shim (LeanHazmatSecp256k1), the EIP-155 example transaction + deterministic second signature + negatives. Needs `just hazmat-secp256k1-vendor` (run via the dependency).
[group('hazmat')]
hazmat-secp256k1-test: hazmat-secp256k1-vendor
    lake build LeanHazmatSecp256k1Tests

# mcl pin: tag v4.10 (commit
# cbb18eb08b86129cf936a6436b5e6c68a2ce8ddf; herumi/mcl, the alt_bn128
# reference). The recipe checks the vendored checkout's HEAD against
# this rev, so a stale tree from an older pin re-fetches instead of
# passing.

bn254_tag := "v4.10"
bn254_rev := "cbb18eb08b86129cf936a6436b5e6c68a2ce8ddf"

# Vendor herumi/mcl (BN254 / alt_bn128) for LeanHazmatBn254, shallow clone at the pinned tag
[group('hazmat')]
hazmat-bn254-vendor:
    #!/usr/bin/env bash
    set -euo pipefail
    dir="packages/hazmat/LeanHazmatBn254/vendor/mcl"
    if [ -d "$dir/.git" ]; then
      rev=$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo unknown)
      if [ "$rev" = "{{ bn254_rev }}" ]; then
        printf '%s\n' "{{ bn254_rev }}" > "$dir/.pin"
        echo "mcl already vendored at $dir ({{ bn254_tag }})"
        exit 0
      fi
      echo "mcl vendored at wrong rev ($rev), re-fetching" >&2
      rm -rf "$dir"
    fi
    mkdir -p "$(dirname "$dir")"
    git clone --depth 1 --branch "{{ bn254_tag }}" https://github.com/herumi/mcl "$dir"
    rev=$(git -C "$dir" rev-parse HEAD)
    [ "$rev" = "{{ bn254_rev }}" ] || { echo "fetched $rev, expected {{ bn254_rev }}" >&2; exit 1; }
    printf '%s\n' "{{ bn254_rev }}" > "$dir/.pin"
    echo "vendored mcl {{ bn254_tag }} -> $dir"

# BN254 Known-Answer-Tests against the mcl FFI shim (LeanHazmatBn254), EIP-196/197 point arithmetic + pairing checks (py_ecc ground truth) + negatives. Needs `just hazmat-bn254-vendor` (run via the dependency). The one C++ family: needs a C++ compiler.
[group('hazmat')]
hazmat-bn254-test: hazmat-bn254-vendor
    lake build LeanHazmatBn254Tests

# BLAKE2f Known-Answer-Tests against the in-repo RFC 7693 shim (LeanHazmatBlake2f), the EIP-152 vectors (rounds 0, 1, 12, 0xffffffff). Nothing to vendor.
[group('hazmat')]
hazmat-blake2f-test:
    lake build LeanHazmatBlake2fTests

# RIPEMD-160 Known-Answer-Tests against the OpenSSL shim (LeanHazmatRipemd160), the nine published vectors incl. the million-`a` case. Nothing to vendor.
[group('hazmat')]
hazmat-ripemd160-test:
    lake build LeanHazmatRipemd160Tests

# modexp Known-Answer-Tests against the OpenSSL BIGNUM shim (LeanHazmatModexp), the EIP-198 worked examples + fixed modular-arithmetic cases. Nothing to vendor.
[group('hazmat')]
hazmat-modexp-test:
    lake build LeanHazmatModexpTests

# P256VERIFY Known-Answer-Tests against the OpenSSL shim (LeanHazmatP256), official EIP-7951 vectors (Project Wycheproof) + negatives. Nothing to vendor.
[group('hazmat')]
hazmat-p256-test:
    lake build LeanHazmatP256Tests

# ═════════════════════════════════════════════════════════════════════════
# LeanPoseidon, pure-Lean Poseidon2 (BN254 t=3), standalone island
# ═════════════════════════════════════════════════════════════════════════

# Building the core fires the in-file anchor-KAT `native_decide` gate
# (input [0,1,2] → the known BN254 t=3 Poseidon2 output). Nothing in
# the monorepo depends on LeanPoseidon (standalone island), so unlike
# the SSZ-chain libs it isn't built transitively. This recipe is how
# the anchor gate fires in `test` / CI. No Rust. Analogous to
# LeanSha256's 3 FIPS §B gates firing on `lake build LeanSha256`.

# LeanPoseidon core build, fires the Poseidon2 anchor KAT (no Rust)
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
# package, the monorepo's only mathlib dependency, built on its own so the
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
