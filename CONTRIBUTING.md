# Contributing to Etheorem

Thanks for your interest. Etheorem is a Lean 4 implementation of
Ethereum's SSZ (Simple Serialize), the supporting cache layer,
and the consensus-spec containers, aiming for machine-checked
correctness on the verified core. Contributions are welcome.

## Quick start

```bash
# 1. Install elan (one-time). https://elan.lean-lang.org/
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# 2. Install native deps. On Debian/Ubuntu:
sudo apt-get install libssl-dev

# 3. Clone and build.
git clone https://github.com/etheorem/etheorem
cd etheorem
lake build
```

The pinned toolchain in `lean-toolchain` is picked up by elan
automatically. First build pulls Lake deps + compiles the FFI
SHA-256 shim against `libcrypto.so.3`.

## Running the test suites

```bash
just test                                    # all per-package in-Lean tests
just ethcl-conformance                       # consensus-spec-tests ssz_static suite (Fulu/Gloas)
just ssz-generic-conformance                 # consensus-spec-tests ssz_generic wire-format suite
just bench                                   # microbench (S1–S7)
```

Or via `lake build` directly:

```bash
lake build LeanSha256Tests
lake build SizzLeanTests
lake build pyspec_server                     # EthCLSpecs conformance runner (ssz_static, state transition)
lake build ssz_generic_runner               # SizzLean conformance runner (ssz_generic)
lake exe ssz_bench
```

The `Justfile` is the source of truth for common workflows; run
`just --list` to see everything available.

## Project layout

The SSZ subpackages under `packages/` form a layered
dependency chain:

```
LeanSha256  ←  SizzLean  ←  EthCLLib  ←  EthCLSpecs
```

See [`docs/monorepo-arch.md`](docs/monorepo-arch.md) for the full
layout: which lakefiles are procedural vs declarative, where the
FFI C shim lives, naming conventions, and the dep policy.

Per-subpackage design docs (currently only `SizzLean` has them):
- `packages/SizzLean/docs/ARCHITECTURE.md`: binding design.
- `packages/SizzLean/docs/PLAN.md`: staged deliverables.
- `packages/SizzLean/docs/OPTIMISATION.md`: cache-layer
  implementation-level companion.

### Inside `packages/SizzLean/`: where to look for what

A quick orientation map for the most-asked questions:

- **Fast backend (cached / FFI-hashed / production).** Lives in
  `packages/SizzLean/SizzLean/Cache/TreeBacked.lean`
  (`CachedSSZ H T`). User-facing smart constructor:
  `SSZ.FastBox` in `Cache/Box.lean`.
- **Pure backend (uncached / proof-friendly).** Lives in
  `packages/SizzLean/SizzLean/Cache/Uncached.lean`
  (`UncachedSSZ H T`). User-facing smart constructor:
  `SSZ.PureBox` in `Cache/Box.lean`.
- **The box that unifies them.**
  `packages/SizzLean/SizzLean/Cache/Box.lean`, `SSZ.Box H T`
  closes the two backends into one sum type, and its module
  docstring documents the brand axes; start here for the
  user-facing surface.
- **Central theorems.** `packages/SizzLean/SizzLean/Proofs/`,
  `Roundtrip.lean` (`decode_encode`), `Injective.lean`
  (`serialize_injective`), `SizeBound.lean`
  (`encode_size_le_max`). All three ship on the
  `SSZType.BasicSupported` cut defined in
  `packages/SizzLean/SizzLean/Spec/BasicSupported.lean`; the
  universally-quantified `Supported` form is open work tracked
  in `packages/SizzLean/docs/PLAN.md` Phase 5.
- **Trust boundary (FFI SHA-256).**
  `packages/SizzLean/SizzLean/Hasher/Sha256.lean`,
  `Sha256Equiv.lean`, and `Sha256Batch.lean`. The complete
  inventory (3 named `axiom`s plus 3 `@[extern] opaque`
  primitives) is recoverable with one grep. See SizzLean's
  README "Trust assumptions you can grep for".
- **Upstream-vector harnesses.** Two pytest harnesses drive the
  consensus-spec-tests vectors. The `ssz_static` per-fork
  containers run from `packages/EthCLSpecs/PySpecTests/` against
  the `pyspec_server` exe (Fulu and Gloas). The fork-agnostic
  `ssz_generic` wire-format primitives run from
  `packages/SizzLean/PySpecTests/` against the
  `ssz_generic_runner` exe. The one-command entry points are
  `just ethcl-conformance` and `just ssz-generic-conformance`;
  smaller subsets and per-suite recipes live in the `Justfile`.

## Code style and discipline

`CLAUDE.md` at the repo root documents the project's conventions
in detail. The short version:

- **Literate by default.** Comments teach the reader what the
  code does *and* the Lean idioms it uses; SSZ-spec readers
  shouldn't need to know advanced Lean to follow, and Lean readers
  shouldn't need to know SSZ.
- **Strict checking is a force multiplier.** `set_option autoImplicit false`
  per file, `decide` / `native_decide` for finite goals,
  structural recursion over `partial def` where it's expressible.
- **Single source of truth.** SSZ container shapes are defined
  once with `ssz_struct_for_presets` / `deriving SSZRepr`; never
  hand-mirrored across files.
- **Spec is the source of truth.** Behaviour comes from
  consensus-specs SSZ + the official test vectors; when other
  implementations disagree with the spec, the spec wins.

Read `CLAUDE.md`'s *Principles* and *Conventions* sections
before sending non-trivial PRs.

## Pull requests

- Keep the diff focused. One PR per logical change.
- Run `lake build` and the relevant test suite before pushing.
- New SSZ-shape coverage adds a `native_decide` or property test
  per shape; new tactic / proof code adds an `example` block that
  the typechecker keeps honest.
- If the change touches the spec → cache equivalence path
  (cache invariants, deriving handler, conformance gates),
  re-run `just ethcl-conformance` and note the
  result in the PR.
- If the change touches the bench-measured hot path, capture a
  fresh `lake exe ssz_bench` TSV pre- and post-change and quote
  the delta in the PR description.

The repo uses GitHub's standard PR review flow; one approval
from a maintainer is the gate. CI runs `lake build` on the
pinned toolchain on every PR.

## Reporting issues

- **Bugs in spec / SSZ / cache behaviour**: open a GitHub issue
  with a minimal reproducer (a Lean snippet + expected vs actual
  output). Include the upstream consensus-spec-tests release tag
  if the bug is conformance-related.
- **Security vulnerabilities**: do *not* file a public issue.
  See [`SECURITY.md`](SECURITY.md) for the responsible-disclosure
  process.
- **Performance regressions on the bench grid**: include the
  before / after TSVs (or the relevant rows) in the issue.

## Licensing

The project is licensed under LGPL-3.0-or-later (see
[`LICENSE`](LICENSE)). By contributing, you agree that your
contributions are licensed under the same terms.
