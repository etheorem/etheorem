-- LeanHazmatBls subpackage: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because it compiles vendored C
-- + assembly into an `extern_lib`. blst is vendored, `just vendor-bls`
-- shallow-clones the pinned tag (v0.3.16) into `vendor/blst/` before
-- `lake build` (hazmat-docs/ARCHITECTURE.md §6); the build below stays
-- offline.
--
-- blst's "build" is just two compiler invocations over its own
-- amalgamation (`src/server.c` #includes every other `.c`;
-- `build/assembly.S` dispatches the pre-generated per-platform asm) plus
-- an `ar`. PLAN.md Stage 2 sanctions compiling that amalgamation
-- directly; we do so as Lake `buildO` targets (fully trace-cached) rather
-- than shelling out to `build.sh`. The flags mirror blst's own default
-- `CFLAGS` (`-O2 -fno-builtin -fPIC`, minus its `-Wall -Wextra -Werror`,
-- which we don't impose on vendored code) plus `-D__BLST_PORTABLE__`.
--
-- `-D__BLST_PORTABLE__` compiles both the ADX and non-ADX code paths
-- with a runtime CPUID dispatch, so the archive runs on any x86-64 host
-- (and is why build.sh's compile-time CPU detection is unnecessary). For
-- the same portability reason this package does NOT add `-march=native`.

import Lake
open Lake DSL System

package LeanHazmatBls where
  -- SPDX identifier; LICENSE lives at the umbrella root until/unless this
  -- family is promoted to a standalone mirror (ARCHITECTURE.md §12).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  -- No `moreLinkArgs`: blst is self-contained (no system library), so the
  -- `extern_lib` archive below carries everything. No `-march=native`:
  -- the archive is built portable (`-D__BLST_PORTABLE__`).

/-- blst's compiler flags, its own default `CFLAGS` minus `-Werror`,
plus the portability define. Shared by the two blst objects. -/
def blstFlags : Array String :=
  #["-O2", "-fno-builtin", "-fPIC", "-D__BLST_PORTABLE__"]

-- blst amalgamation: `src/server.c` transitively includes the whole C
-- source tree. One object for the entire field/curve/pairing library.
-- The `vendor/blst/` path is absent until `just vendor-bls` runs; the
-- existence check turns a missing checkout into an actionable message.
target blst_server.o pkg : FilePath := do
  let src := pkg.dir / "vendor" / "blst" / "src" / "server.c"
  unless (← src.pathExists) do
    error s!"blst not vendored — run `just vendor-bls` (expected {src})"
  let obj := pkg.buildDir / "blst" / "server.o"
  buildO obj (← inputTextFile src) blstFlags #[] "cc" getLeanTrace

-- blst pre-generated assembly. `build/assembly.S` is a dispatcher that
-- `#include`s the correct per-platform `.s` files (ELF on Linux, etc.)
-- based on compiler-predefined macros; `cc` runs the preprocessor on the
-- capital-`.S` extension automatically.
target blst_assembly.o pkg : FilePath := do
  let src := pkg.dir / "vendor" / "blst" / "build" / "assembly.S"
  unless (← src.pathExists) do
    error s!"blst not vendored — run `just vendor-bls` (expected {src})"
  let obj := pkg.buildDir / "blst" / "assembly.o"
  buildO obj (← inputTextFile src) blstFlags #[] "cc" getLeanTrace

-- The Lean-facing BLS shim. Needs blst's `bindings/` on the include path
-- for `blst.h`, and the Lean runtime headers for `lean/lean.h`. No
-- `-march=native` (keeps the archive portable, matching blst).
target bls_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "bls_shim.c"
  let bindings := pkg.dir / "vendor" / "blst" / "bindings"
  unless (← bindings.pathExists) do
    error s!"blst not vendored — run `just vendor-bls` (expected {bindings})"
  let obj := pkg.buildDir / "csrc" / "bls_shim.o"
  let leanInclude ← getLeanIncludeDir
  let flags := #["-fPIC", "-O2", "-I", leanInclude.toString,
                 "-I", bindings.toString]
  buildO obj (← inputTextFile src) flags #[] "cc" getLeanTrace

-- One archive carrying the shim + the whole of blst. Lake links it into
-- any precompiled library or executable that (transitively) `require`s
-- this package, including `LeanHazmatKzg`, which builds c-kzg against
-- this same blst.
extern_lib libleanhazmat_bls pkg := do
  let serverO   ← blst_server.o.fetch
  let assemblyO ← blst_assembly.o.fetch
  let shimO     ← bls_shim.o.fetch
  let name := nameToStaticLib "leanhazmat_bls"
  buildStaticLib (pkg.staticLibDir / name) #[shimO, serverO, assemblyO]

@[default_target]
lean_lib LeanHazmatBls where
  -- Precompiled shared lib so importers link native code. Default globs
  -- (root only) suffice. `LeanHazmatBls.lean` imports `…Bls.Ffi`.
  precompileModules := true

-- Byte-level Known-Answer-Test gate against the consensus-spec BLS
-- vectors. Self-contained (no upstream deps); built explicitly via
-- `lake build LeanHazmatBlsTests`.
lean_lib LeanHazmatBlsTests where
  roots := #[`LeanHazmatBlsTests]
  globs := #[.andSubmodules `LeanHazmatBlsTests]
