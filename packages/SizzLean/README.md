![SizzLean](sizzlean_cartoon.jpeg)

# SizzLean: serialization, part of a well verified breakfast.

> **Status: early-stage, experimental, single-developer; personal
> project, not an EF release.** The library passes the upstream
> consensus-spec test corpus and the three central theorems are
> landed on the `BasicSupported` cut (open work toward `Supported`
> is tracked in [`docs/PLAN.md`](docs/PLAN.md) Phase 5). Reviews,
> issues, and pull requests are welcome; production-grade
> stability and a stable release line are not implied.

A Lean 4 implementation of Ethereum's
[SSZ](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md)
(Simple Serialize): serialization, deserialization, Merkleization,
cached-tree machinery, and the `sszUpdate` macro surface, all of
it sharing one library between production code and machine-checked
theorems.

## Why SizzLean

- **Write once, pick your backend.** Code written against this
  library runs on either of two implementations under the hood, a
  heavily optimised cached Merkle tree for production speed, or a
  simple uncached version that's friendly to Lean proofs. You
  choose at the call site; the spec or state-transition function
  you wrote doesn't change. No duplicated source between the
  runtime path and the verification path.

- **Validated against Ethereum's test corpus.** Passes both
  upstream SSZ suites from `ethereum/consensus-spec-tests` (release
  `v1.6.0-beta.0`) end-to-end on **both** preset configurations:
  `ssz_generic` (2188 / 2188 in-scope cases, the wire-format
  tests; 292 progressive-container cases are deliberately out of
  scope, see the "deliberately not implemented" table below),
  `ssz_static --config mainnet` (1585 / 1585 cases), and
  `ssz_static --config minimal` (38991 / 38991 cases), every
  fork from Phase 0 through Fulu. SHA-256 passes the NIST CAVP
  vectors on every hasher the library ships.

- **Literate by default.** SizzLean sits at the intersection of
  two specialist worlds, SSZ and Lean 4, and most readers only
  know one. The library is written with comments that teach the
  reader what the code does *and* the Lean idioms it uses, so a
  Lean-fluent reader can pick up the SSZ semantics and an
  SSZ-fluent reader can pick up the Lean. The cost is paid once
  when the code is written; the dividend compounds with every new
  contributor.

- **Fast hash-tree-root.** Updates are incremental: only the
  path from a changed field to the root rehashes. Multi-field
  updates batch the work across overlapping paths.

- **Zero boilerplate per type.** Add `deriving SSZRepr` to your
  Lean structure and you get serialization, deserialization,
  hash-tree-root, and the central correctness theorems, for
  free, per type, with no hand-written proofs.

- **Machine-checked correctness across most of SSZ.** The three
  central theorems, encode/decode roundtrip, non-malleability,
  and a schema-derived static size bound, are proved for every
  SSZ shape *except* variable-field containers:
  `uintN 8 / 16 / 32 / 64`, `bool`, fixed-size `vector` and
  `list`, `bitvector`, `bitlist`, and `container` over fixed-size
  fields (recursively). Mixed-field containers are pending, see
  [Proof coverage](#proof-coverage) for the per-constructor
  table.

- **Trust assumptions you can grep for.** Every reliance on the
  C SHA-256 implementation is a named Lean `axiom` (or its
  `@[extern] opaque` FFI declaration) in `SizzLean/Hasher/`, and
  shows up in the trust footprint of any proof that transitively
  uses it. The complete inventory is recoverable with one grep:

  ```bash
  grep -rEn '^axiom |^@\[extern' packages/SizzLean --include='*.lean'
  ```

  Today this returns three `axiom`s (`sha256Hash_eq_spec`,
  `sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec`) plus
  three `@[extern] opaque` FFI primitives (`sha256Hash`,
  `sha256Combine`, `sha256BatchCombine`), six real declarations,
  all under `SizzLean/Hasher/`. The grep also surfaces a handful
  of docstring mirrors (the same lines repeated inside a `/-! … -/`
  module-docstring block where the surrounding prose explains
  them); those are intentional, not extra trust commitments.
  Each `@[extern]` declaration is replaceable later by a
  `@[csimp]`-proved theorem; each equivalence `axiom` is
  replaceable by a plain proved `theorem`. Either swap leaves
  dependent theorem statements unchanged.

  *One additional trust class, auto-injected by tactics rather
  than hand-written.* The `decode_encode` and
  `serialize_injective` theorems' `.uintN 16 / 32 / 64` arms close
  via Lean core's `bv_decide` tactic, which adds one per-theorem
  `_native.bv_decide.ax_*` axiom (an LRAT SAT certificate cached
  as a Boolean reduction, same trust class as `native_decide`'s
  `Lean.ofReduceBool`). Visible via `#print axioms
  SizzLean.Proofs.decode_encode`. `encode_size_le_max` is
  axiom-free over the standard kernel axioms.

  *Out of central-theorem scope.* The cache layer
  (`Cache/MerkleTree/`) carries its own local trust commitments.
  These are `@[implemented_by]` on `zeroHashes` (substitutes a
  memoised `unsafeBaseIO` reader for the kernel-visible recurrence;
  equivalent by construction) and two `partial def`s
  (`Node.rootOf`, `Node.commitAndHash`). Test gates under
  `SizzLeanTests/` use `native_decide` (one `Lean.ofReduceBool`
  axiom per call). Neither enters the trust footprint of the
  central theorems (`decode_encode` / `serialize_injective` /
  `encode_size_le_max`), but a global audit of the library
  should account for them too.

- **Pluggable hash function.** Today it's SHA-256. Tomorrow it
  can be Poseidon2, or whatever the Beam Chain redesign settles
  on, without rewriting your containers, your proofs, or your
  cache logic.

- **Every Ethereum consensus fork covered.** Phase 0 through
  Gloas, including the new ePBS containers.

## Scope

Provides the SSZ *library*, types and primitives. Consensus-spec
container definitions live in the sibling `EthCLSpecs` package
(Fulu and Gloas), built on the `EthCLLib` framework.

## Status

**Experimental, pyspec-validated.** Every SSZ type used by
the Ethereum consensus spec from Phase 0 through Gloas is
implemented. Upstream test suites (`ethereum/consensus-spec-tests
v1.6.0-beta.0`) pass clean on **both** preset configurations:

* `ssz_generic --all`: **2188 / 2188** in-scope cases passed,
  0 failed. Plus **292** deliberately skipped progressive-container
  cases (see the "deliberately not implemented" table); the
  pyspec harness classifies them as `out of library scope`,
  not failures.
* `ssz_static --config mainnet --all`: **1585 / 1585** cases
  passed across every fork Phase 0 → Fulu.
* `ssz_static --config minimal --all`: **38991 / 38991** cases
  passed across every fork Phase 0 → Fulu.

Per-PR CI runs the dev-subset smoke; the full sweeps are the
umbrella `just sizzlean-pyspec-full` (wire-format) and
`just ethcl-pyspec-full` (per-fork containers) targets.

The per-fork consensus-container vectors are covered by the
`EthCLSpecs` pyspec harness for the Fulu and Gloas forks.
Coverage of those forks lives in `EthCLSpecs`, the SSZ library
itself implements every wire-format type they need.

### SSZ types implemented

| Type | Notes |
|---|---|
| `uintN` for `N ∈ {8, 16, 32, 64, 128, 256}` | Per spec; covers all currently-used widths |
| `boolean` | Single-byte `0x00` / `0x01` |
| `Vector[T, N]` | Fixed-length list |
| `List[T, N]` | Variable-length list with cap `N` and mix-in-length root |
| `Bitvector[N]` | Fixed-length bit array |
| `Bitlist[N]` | Variable-length bit array with trailing-`1` delimiter |
| `Container` | Heterogeneous record / struct, every consensus container is one of these |

### SSZ types deliberately *not* implemented

These forms appear in the SSZ spec but are not used by any
consensus-spec fork through Gloas, so the library omits them
to keep the core proof obligation small:

| Type | Source | Status here |
|---|---|---|
| `Union[T₁, …, Tₙ]` | core SSZ spec | unimplemented, no fork uses it |
| `ProgressiveContainer(active_fields=[…])` | EIP-7495 | unimplemented, no fork adopted EIP-7495 |
| `StableContainer[N]` + `Profile` | EIP-7495 (legacy form) | unimplemented |
| `ProgressiveList[T]` / `ProgressiveBitlist` | EIP-7916 | unimplemented |
| `CompatibleUnion({sel: type, …})` | EIP-8016 | unimplemented |

ARCHITECTURE.md §8 carries the recipe for reintroducing any of
these the day a fork adopts them. They slot back into `SSZType`
as new constructors without disrupting the existing layers.

### Proof coverage

The three central theorems, `decode_encode` (roundtrip),
`serialize_injective` (non-malleability), and
`encode_size_le_max` (size bound), are landed on the
`SSZType.BasicSupported` cut (`Spec/BasicSupported.lean`).
Per-constructor breakdown:

| `SSZType` constructor | `decode_encode` | `serialize_injective` | `encode_size_le_max` | Notes |
|---|:---:|:---:|:---:|---|
| `.uintN 8` | ✅ | ✅ | ✅ | closes by `rfl` after one `unfold` |
| `.uintN 16` | ✅ ¹ | ✅ ¹ | ✅ | `bv_decide` on the LE identity |
| `.uintN 32` | ✅ ¹ | ✅ ¹ | ✅ | `bv_decide` |
| `.uintN 64` | ✅ ¹ | ✅ ¹ | ✅ | `bv_decide` |
| `.bool` | ✅ | ✅ | ✅ | exhaustive `cases` + `rfl` |
| `.vector t n` | ✅ ² | ✅ ² | ✅ ² | needs `0 < n` + `BasicSupported t` + `t.isFixedSize = true` |
| `.list t cap` | ✅ ³ | ✅ ³ | ✅ ³ | needs `BasicSupported t` + `t.isFixedSize = true` + `0 < t.fixedByteSize` |
| `.bitvector n` | ✅ ⁴ | ✅ ⁴ | ✅ | needs `0 < n`; bit-packing inverse in `Proofs/BitPack.lean` |
| `.bitlist cap` | ✅ ⁴ | ✅ ⁴ | ✅ | bit-packing inverse + `msbPos` delimiter recovery |
| `.container fs` | see below | see below | see below | — |

¹ Adds one `_native.bv_decide.ax_*` axiom per arm (SAT certificate
for the multi-byte LE identity). `decode_encode`'s and
`serialize_injective`'s overall trust footprint is exactly these
three axioms plus the standard kernel axioms (`propext`,
`Classical.choice`, `Quot.sound`); `encode_size_le_max` adds
none.
² Recurses on the element type's `BasicSupported` witness via
the mutual `decode_encode` ↔ `decode_encode_containerFixed_aux`
block.
³ Same recursion shape as `.vector`.
⁴ Byte-level bit identities close by kernel `decide` over the
finite chunk shapes (`Proofs/BitPack.lean`), so the bit arms add
no axioms beyond the standard kernel three.

`serialize_injective` is a direct corollary of `decode_encode`
(via `Except.ok.inj` + `Prod.mk.inj`), so its coverage tracks
`decode_encode` exactly.

#### `.container fs`: per-field type

A container `.container fs` is in `BasicSupported` exactly when
every field type is itself `BasicSupported` *and* fixed-size.
Allowed and excluded field types:

| Field type | Allowed as a container field? | Why |
|---|:---:|---|
| `.uintN 8 / 16 / 32 / 64` | ✅ | basic + fixed |
| `.bool` | ✅ | basic + fixed |
| `.vector t' n` (with `n > 0`, fixed-size `t'`, `BasicSupported t'`) | ✅ | nested vector, `(.vector t' n).isFixedSize = t'.isFixedSize` |
| `.container fs'` (with `BasicSupportedFieldsFixed fs'`) | ✅ | nested container, `(.container fs').isFixedSize = allFixedSize fs'` |
| `.bitvector n` (with `n > 0`) | ✅ | bit-packed + fixed, `(.bitvector n).fixedByteSize = ⌈n/8⌉` |
| `.list t' cap` | ❌ | `(.list _ _).isFixedSize = false`, structurally excluded |
| `.bitlist cap` | ❌ | `(.bitlist _).isFixedSize = false`, structurally excluded |

For `.list` and `.bitlist` the exclusion is *structural*: they're
variable-size by SSZ definition, so they cannot satisfy
`BasicSupportedFieldsFixed`'s `t.isFixedSize = true` precondition.
Mixed-field containers (containers with at least one variable-size
field) are **outside `SSZType.Supported` entirely**, not just
outside `BasicSupported`. The spec layer flags this as
`TODO(stage-3-deferral)` in `Spec/Deserialize.lean`; closing it
requires extending `Supported` with a `containerVar` constructor
plus an offset-table-invariants proof.

In one line: containers with fields drawn from `{uintN8, uintN16,
uintN32, uintN64, bool, vectorFixed, bitvector,
containerFixed (recursively)}` are proved; containers with any
`list` or `bitlist` field are not.

### Track in progress

**Phase 5 formal-verification widening:** the three central
theorems (roundtrip, non-malleability, size bound) are landed on
the `BasicSupported` cut, which now covers `uintN 8 / 16 / 32 /
64`, `bool`, fixed-size `vector` and `list`, `bitvector`,
`bitlist`, and `container` over fixed-size fields (recursively).
Widening to a universal statement over `SSZType.Supported`
requires extending `Supported` itself to admit mixed-field
containers (spec-layer follow-up). The library itself is
complete; this track only closes the proof obligation.

See [`docs/PLAN.md`](docs/PLAN.md) for the staged plan and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the design
contract.

## Prerequisites

On a fresh machine you need four things before `lake build` will
work. The Lean toolchain and `just` itself aren't installed by
the project, they're external tools the recipes assume.

1. **`elan`** (Lean toolchain manager, provides `lake` /
   `lean`). The version in [`../../lean-toolchain`](../../lean-toolchain)
   is installed on first use.

   ```bash
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```

2. **`just`** (task runner, every workflow below is wrapped in
   a `just` recipe; `just doctor` won't run until `just` itself
   is installed). Install via your platform's package manager
   (`brew install just`, `cargo install just`, distro package,
   …), see <https://just.systems>.

3. **OpenSSL 3.x + `pkg-config`** (system-level build deps for
   the SHA-256 FFI shim, see [Dependencies → System-level](#system-level-build-time-native-deps)
   below for the per-platform one-liners).

4. **`python3` + `uv`** (only for the `just sizzlean-pyspec*`
   and `just ethcl-pyspec*` recipes). Run `just setup-python`
   from the umbrella root once to create `.venv/` and install the
   harness deps.

From the umbrella root, verify everything in one shot:

```bash
just doctor          # checks elan/lake/lean + pkg-config/OpenSSL + python3/uv
```

## Dependencies

### Lean-level

* `LeanSha256`: sibling subpackage, pure-Lean SHA-256 reference
  (used by the kernel-reducible `Hasher.Sha256Spec` instance).
  Pulled in transitively via the umbrella's
  [`lake-manifest.json`](../../lake-manifest.json).

### System-level (build-time native deps)

The production `Hasher.Sha256` instance is an FFI shim
(`csrc/sha256_shim.c`) that links to **OpenSSL 3.x**. Lake
discovers the right link flags via `pkg-config --libs libcrypto`
at build time, so the same `lake build` works on Debian/Ubuntu
multiarch, Fedora `/usr/lib64`, Arch, Alpine, macOS Homebrew
(where `openssl@3` is keg-only), and NixOS store paths, since
pkg-config does the platform discrimination for us. If `pkg-config`
itself isn't installed, the build falls back to the hardcoded
Debian-multiarch values, which keeps existing `apt`-only
environments working.

You need two system packages:

* **OpenSSL 3.x development files:** both the shared library
  (`libcrypto.so.3` / `libcrypto.3.dylib` / …) and the headers
  (`<openssl/evp.h>`).
* **`pkg-config`:** the canonical Unix discovery tool the build
  uses to find the above.

| Platform | One-liner |
|---|---|
| Debian / Ubuntu | `sudo apt install libssl-dev pkg-config` |
| Fedora / RHEL   | `sudo dnf install openssl-devel pkgconf-pkg-config` |
| Arch            | `sudo pacman -S openssl pkgconf` |
| Alpine          | `sudo apk add openssl-dev pkgconf` |
| macOS (Homebrew) | `brew install openssl@3 pkg-config` |
| NixOS           | add `openssl pkg-config` to your `shell.nix` / `flake.nix` |

To verify your machine is set up, both system deps and the Lean
toolchain, run from the umbrella root:

```bash
just doctor         # checks pkg-config + OpenSSL + elan/lake/lean + uv/python3
just doctor-native  # checks only pkg-config + OpenSSL (the CI gate)
```

`just doctor` prints actionable platform-specific install hints if
anything's missing. The CI `test` and `pyspec` jobs run
`just doctor-native` as their first step.

### Why a procedural lakefile

The FFI shim build (`csrc/sha256_shim.c` + `csrc/sha256_batch.c`)
needs a `target … : FilePath := do …` step that the declarative
`lakefile.toml` syntax can't express. The procedural `lakefile.lean`
also hosts the `pkg-config` discovery (a `BaseIO` call at lakefile-
load time via `unsafeBaseIO`); both reasons keep this subpackage on
`lakefile.lean` even though the umbrella and the two sibling
subpackages stay on declarative TOML.

## Module overview

* `Spec/`: `SSZType` universe, `interp`, `serialize`,
  `deserialize`, `hashTreeRoot`. The verified core.
* `Repr/`: the `SSZRepr` typeclass + deriving handler.
* `Hasher/`: abstract `Hasher` typeclass; `Sha256` (FFI) +
  `Sha256Spec` (pure-Lean) instances; `Sha256Equiv` /
  `Sha256Batch` (the named equivalence axioms, see "Trust
  assumptions you can grep for" above).
* `Cache/`: both backends and the box layer that unifies them:
  * `Cache/TreeBacked.lean`: the **fast / cached** backend
    (`CachedSSZ H T`): production-side, FFI-hashed, O(log N)
    incremental updates.
  * `Cache/Uncached.lean`: the **pure / uncached** backend
    (`UncachedSSZ H T`): proof-side, no cache invariant, kernel-
    reducible when paired with `Sha256Spec`.
  * `Cache/Box.lean`: `SSZ.Box H T` closes the two backends
    into one user-facing sum type, and defines the four smart
    constructors (`SSZ.FastBox` / `SSZ.PureBox` /
    `SSZ.CachedBox` / `SSZ.UncachedBox`). Its module docstring
    documents the brand axes; start here for the user-facing
    surface.
  * `Cache/MerkleTree/`: the tree machinery the fast backend
    sits on; `Cache/Update.lean` is the `sszUpdate` macro.
* `Proofs/`: central proof artefacts and `@[ssz_simp]` set.
  The three central theorems (`decode_encode`,
  `serialize_injective`, `encode_size_le_max`) live in
  `Proofs/Roundtrip.lean`, `Proofs/Injective.lean`, and
  `Proofs/SizeBound.lean` respectively. All three are landed on
  the `SSZType.BasicSupported` cut (defined in
  `Spec/BasicSupported.lean`); the universally-quantified
  `Supported` form is open work, see
  [`docs/PLAN.md`](docs/PLAN.md) Phase 5.
* `Conformance/`: SSZ-library property-test gates (Sha256
  vectors, hasher equivalence, `setAt` randomised tests, cache
  machinery on example containers).

The CLI runner for the fork-agnostic `ssz_generic` wire-format
corpus (`ssz_generic_runner`) lives in this package and is driven
by the pytest harness in [`PySpecTests/`](PySpecTests). The
per-fork `ssz_static` corpus is driven by the `EthCLSpecs`
harness against its `pyspec_server` exe. Use the one-command
`just sizzlean-pyspec` and `just ethcl-pyspec`
entry points documented in [Build / test](#build--test).

## Build / test

```bash
just doctor                 # one-time sanity check on a fresh machine
lake build SizzLean         # compile the library
```

`just doctor` is the first thing to run on a new clone, it verifies
OpenSSL 3.x and `pkg-config` are present (the build-time native deps
the FFI shim links against, see [Dependencies](#dependencies)) plus
the Lean toolchain (elan / lake / lean) and the Python harness
toolchain (python3 / uv) used by the pyspec recipes below. A
failed check prints the install command for your platform.

Three test surfaces, all driven from the umbrella `just` interface
at the repo root. The first two are quick; the third runs against
the downloaded upstream archive.

```bash
# SizzLean-internal property tests (Sha256 vectors, hasher
# equivalence, randomised setAt, cache coherence, sszUpdate cases —
# all fire as native_decide examples at build time)
just sizzlean-test

# Full NIST CAVP SHA-256 vectors — 129 byte-oriented cases
# (lives in the sibling LeanSha256 package, ~108s of native_decide)
just leansha256-test

# Upstream `ethereum/consensus-spec-tests`. Pytest harnesses
# drive a Lean CLI against the pyspec archives. A tqdm progress
# bar shows live per-case throughput. Quick dev subset:
just sizzlean-pyspec
# Full `ssz_generic` wire-format sweep:
just sizzlean-pyspec-full
# Per-fork `ssz_static` consensus-container suite (Fulu/Gloas),
# quick dev subset:
just ethcl-pyspec
# The complete in-scope EthCLSpecs sweep (both forks, both presets):
just ethcl-pyspec-full
```

For the full menu, the protocol the harness uses, and how to
write code that targets `SSZ.FastBox` (production cache) or
`SSZ.PureBox` (proof-friendly uncached) on a *single* spec body,
see [`MANUAL.md`](MANUAL.md).

## Requiring this package

`SizzLean` lives as a subpackage of the [`etheorem` umbrella
repository](https://github.com/etheorem/etheorem). To depend on it
from another Lake project, add a `[[require]]` block to your
`lakefile.toml`:

```toml
[[require]]
name = "SizzLean"
git = "https://github.com/etheorem/etheorem"
subDir = "packages/SizzLean"
rev = "main"  # pin to a specific commit hash for reproducible builds
```

Then run `lake update` to refresh `lake-manifest.json`. Per the
umbrella's [`CLAUDE.md`](../../CLAUDE.md) dependency policy, prefer
pinning `rev` to a specific commit hash over tracking a branch once
you've validated a working pair, since branch-tracking turns every
upstream change into a silent dep bump.

SizzLean's only Lean-level dependency outside Lean core is the
sibling [`LeanSha256`](../LeanSha256) subpackage in the same umbrella;
adding the `[[require]]` above transitively pulls it in via the
umbrella's `lake-manifest.json`. The native build-time dependencies
(OpenSSL 3.x + `pkg-config`, used by the FFI SHA-256 shim) are listed
under [Dependencies](#dependencies); a stranger building from a clean
clone needs both the Lean-level `require` *and* those system packages.
