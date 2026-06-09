# LeanSha256

> [!IMPORTANT]
> **Issues and pull requests belong in the
> [`etheorem` monorepo](https://github.com/etheorem/etheorem), not
> here.** `LeanSha256` is developed inside the umbrella repo under
> `packages/LeanSha256/`; this repository is a **read-only
> subtree mirror** regenerated on every push to the umbrella's
> `main`. Issues filed here, and pull requests opened against this
> repo's branches, will not be acted on. Please redirect them to
> the umbrella. Any direct pushes to this repo's `main` are
> overwritten by the next mirror run.
>
> The mirror exists so the package is independently discoverable
> on [Reservoir](https://reservoir.lean-lang.org) (which indexes
> repository roots, not monorepo subdirectories). The umbrella
> remains the single source of truth.

## Where to file issues / contribute

→ **[github.com/etheorem/etheorem](https://github.com/etheorem/etheorem)**
(the monorepo). Look under `packages/LeanSha256/` for this
library's source; the umbrella's `CLAUDE.md` documents the
project-wide conventions.

---

A pure-Lean SHA-256 reference implementation. Two functions in the
public surface (`hash` and `combine`); NIST CAVP-validated against
the FIPS 180-4 published vectors; kernel-reducible (no FFI, no
opaque calls, no SSZ coupling) so kernel `decide` closes goals about
it without trusting the compiler.

## Status

Stable. NIST CAVP byte-oriented short-message and long-message
test suites pass via build-time `native_decide` gates inside
`LeanSha256Tests/Nist.lean`. At version `0.1.0`, the two-function
public API is intended to remain stable; internal modules under
`LeanSha256.Core` (round functions, message schedule, helper
lemmas) may evolve.

## Dependencies

None. Pure Lean 4 + the standard library. No `mathlib`, no
`batteries`, no native shims.

## Modules

* `LeanSha256.Core`: the SHA-256 algorithm (initial state, message
  schedule, compression function, padding, multi-block driver).
  Kernel-reducible.
* `LeanSha256Tests.Nist`: NIST CAVP byte-oriented test vectors as
  `native_decide` gates over `LeanSha256.Core`. Lives in the
  separate `LeanSha256Tests` library so the ~108 s build cost is
  opt-in.

## Public API

```lean
namespace LeanSha256

/-- Single SHA-256 digest. Equivalent to FIPS 180-4 §6.2. -/
def hash    : ByteArray → ByteArray

/-- Sibling combine: `hash (a ++ b)`. Exported separately because
    Merkle-tree consumers (e.g. SSZ `hash_tree_root`) call it on the
    hot path and want a direct, allocation-free entry point. -/
def combine : ByteArray → ByteArray → ByteArray

end LeanSha256
```

Both functions are total, structurally terminating, and return a
32-byte `ByteArray`. The `Core` module also exposes a handful of
structural conformance lemmas (e.g. that `hash` agrees with a
single-block compression on inputs ≤ 55 bytes). See its module
docstring for the full list.

## Trust assumptions

* Kernel-reducible: every definition reduces in Lean's trusted
  kernel. Closing a goal with `decide` against `LeanSha256.hash`
  adds **no** compiler-trust axiom, only Lean's core kernel is
  trusted.
* For speed, consumers normally close hash-equality goals with
  `native_decide`, which trusts the Lean compiler via
  `Lean.ofReduceBool`. The full `LeanSha256Tests` library
  (`LeanSha256Tests.Nist`) does this. See its `#axioms` output.
* No `sorry`, no `axiom` declarations, no FFI calls anywhere in
  the library.

## Build / test

```bash
# From the umbrella repo root:
lake build LeanSha256
# (3 anchor FIPS 180-4 §B gates fire at build time via
# native_decide inside LeanSha256.Core; if any case regresses,
# the build fails.)

# Full NIST CAVP byte-oriented suite — 129 short-message +
# long-message cases via native_decide, ~108 s. The `Justfile`
# at the umbrella root wraps this:
just test-sha256
# …which is exactly `lake build LeanSha256Tests`.

# Or from this subpackage's directory:
cd packages/LeanSha256 && lake build
```

The CAVP vector files (`SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`,
`SHA256Monte.rsp`) live under `cavp/` in this subpackage and are
the upstream NIST artefacts unmodified. A stranger can verify
the byte-for-byte match against the
[NIST CSRC CAVP archive](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing).

To regenerate `LeanSha256Tests/Nist.lean` after refreshing the
`.rsp` files, run the in-package script (or its umbrella wrapper):

```bash
python3 packages/LeanSha256/scripts/gen_sha256_cavp.py
# or, from the umbrella root:
just gen-cavp
```

## Requiring this package

`LeanSha256` is published as a standalone Lake package at
[`etheorem/LeanSha256`](https://github.com/etheorem/LeanSha256) (a
subtree mirror of `packages/LeanSha256/` from the
[`etheorem` umbrella repo](https://github.com/etheorem/etheorem)).
Downstream Lake projects can require it directly:

```toml
[[require]]
name = "LeanSha256"
git = "https://github.com/etheorem/LeanSha256"
rev = "v0.1.0"  # pin to a release tag or a specific commit sha
```

The mirror exposes `vX.Y.Z` tags for each release. The umbrella's
own release tags use a `leansha256-vX.Y.Z` prefix; the mirror
workflow strips the prefix.

Either form (mirror or umbrella) can also be required by `subDir`
if you want the package directly from the monorepo source, useful
during development. For general consumption the mirror is the
canonical address:

```toml
# Source the package from the monorepo (for development / debugging):
[[require]]
name = "LeanSha256"
git = "https://github.com/etheorem/etheorem"
subDir = "packages/LeanSha256"
rev = "<commit-sha>"
```

**From a local copy, via path** (vendoring or `git submodule`):

```toml
[[require]]
name = "LeanSha256"
path = "vendor/LeanSha256"
```

Then run `lake update` to refresh `lake-manifest.json`. Per the
umbrella's [`CLAUDE.md`](../../CLAUDE.md) dependency policy,
prefer pinning `rev` to a specific commit hash or release tag over
tracking a branch.

## Licence

LGPL-3.0-only. The package ships a local copy of the licence text
at `LICENSE`, pinned from the umbrella repo's root `LICENSE`. The
mirror workflow refreshes the local copy on every push to keep it
in sync.
