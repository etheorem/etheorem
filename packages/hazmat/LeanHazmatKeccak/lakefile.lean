-- LeanHazmatKeccak subpackage: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because it compiles vendored C
-- into an `extern_lib`. keccak-tiny is vendored, `just hazmat-keccak-vendor`
-- fetches the pinned commit rev into `vendor/keccak-tiny/` before
-- `lake build` (packages/hazmat/docs/ARCHITECTURE.md §6); the build below stays
-- offline. Upstream tags no releases, so the pin is a rev, checked
-- after the fetch.
--
-- Build shape: ONE object. `csrc/keccak_shim.c` `#include`s the
-- vendored `keccak-tiny.c` unmodified (the sponge it needs is
-- `static`), so the shim target compiles the whole family surface.
-- The vendored file is not an input of the `cc` invocation, so its
-- *content* is folded into the target's trace explicitly (the
-- `zipWith` below), keeping the build cache honest across a
-- re-vendor.

import Lake
open Lake DSL System

package LeanHazmatKeccak where
  -- SPDX identifier; LICENSE lives at the umbrella root until/unless this
  -- family is promoted to a standalone mirror (ARCHITECTURE.md §12).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../../LICENSE"]
  -- No `moreLinkArgs`: keccak-tiny is self-contained (no system
  -- library), so the `extern_lib` archive below carries everything.

/-- The vendored keccak-tiny checkout (absent until `just
hazmat-keccak-vendor` runs). -/
def keccakTinyDir (pkg : Package) : FilePath :=
  pkg.dir / "vendor" / "keccak-tiny"

/-- The pinned rev, written by `just hazmat-keccak-vendor` on every
fetch. Folding it into the target's trace makes a re-vendor rebuild
the shim object even when the vendored `.c` content happens to be
unchanged. -/
def keccakPin (pkg : Package) : FilePath :=
  keccakTinyDir pkg / ".pin"

-- The Lean-facing Keccak shim + the vendored implementation in one
-- object (the shim `#include`s the vendored `.c`). Needs the vendored
-- directory on the include path for the `#include "keccak-tiny.c"`,
-- and the Lean runtime headers for `lean/lean.h`.
target keccak_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "keccak_shim.c"
  let vendored := keccakTinyDir pkg / "keccak-tiny.c"
  unless (← vendored.pathExists) do
    error s!"keccak-tiny not vendored, run `just hazmat-keccak-vendor` (expected {vendored})"
  unless (← (keccakPin pkg).pathExists) do
    error s!"keccak-tiny pin missing, run `just hazmat-keccak-vendor` (expected {keccakPin pkg})"
  let obj := pkg.buildDir / "csrc" / "keccak_shim.o"
  let leanInclude ← getLeanIncludeDir
  -- `inputTextFile` on the vendored file puts its content hash in the
  -- trace (the shim `.c` alone would not; the file reaches the compiler
  -- through `#include`, invisible to a single-input trace). The pin is
  -- part of the trace too, so a re-vendor rebuilds even when the
  -- fetched content is unchanged. Per Lake's `buildO` contract
  -- (Lake/Build/Common.lean): only `traceArgs` join the
  -- dependency-trace hash, `weakArgs` do not, so the portable flags
  -- (`-fPIC`, `-O2`) go in `traceArgs` and a flag change rebuilds; the
  -- discovered `-I` paths stay `weakArgs`.
  let srcJob ← inputTextFile src
  let vendoredJob ← inputTextFile vendored
  let pinJob ← inputTextFile (keccakPin pkg)
  buildO obj
    ((srcJob.zipWith (fun p _ => p) vendoredJob).zipWith (fun p _ => p) pinJob)
    #["-I", leanInclude.toString, "-I", (keccakTinyDir pkg).toString]
    #["-fPIC", "-O2"] "cc" getLeanTrace

-- The family's native archive. Lake links this `.a` into any
-- precompiled library or executable that (transitively) `require`s
-- this package.
extern_lib libleanhazmat_keccak pkg := do
  let shimO ← keccak_shim.o.fetch
  let lib := pkg.staticLibDir / nameToStaticLib "leanhazmat_keccak"
  buildStaticLib lib #[shimO]

@[default_target]
lean_lib LeanHazmatKeccak where
  -- Ship as a precompiled shared lib so importers link native code
  -- rather than recompiling the binding. Default globs (root module
  -- only) suffice: `LeanHazmatKeccak.lean` imports
  -- `LeanHazmatKeccak.Ffi`, which is built transitively.
  precompileModules := true

-- Byte-level Known-Answer-Test gate against published Keccak-256
-- vectors (EVM canonical constants included). Self-contained, no
-- upstream deps, so this package validates standalone when split to a
-- mirror. Built explicitly via `lake build LeanHazmatKeccakTests`.
lean_lib LeanHazmatKeccakTests where
  roots := #[`LeanHazmatKeccakTests]
  globs := #[.andSubmodules `LeanHazmatKeccakTests]
