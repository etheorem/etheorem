-- LeanHazmatSecp256k1 subpackage: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because it compiles vendored C
-- into an `extern_lib`. libsecp256k1 is vendored, `just
-- hazmat-secp256k1-vendor` shallow-clones the pinned tag (v0.8.0) into
-- `vendor/secp256k1/` before `lake build` (packages/hazmat/docs/ARCHITECTURE.md
-- §6); the build below stays offline.
--
-- Build shape: the library's own amalgamation (`src/secp256k1.c`
-- transitively #includes the whole C tree) plus the Lean shim. One
-- define matters:
--   * `-DENABLE_MODULE_RECOVERY`, the recovery module is a
--     compile-time module gate in v0.8.0; without it
--     `secp256k1_ecdsa_recover` does not exist.
-- `SECP256K1_BUILD` is deliberately NOT passed: the amalgamation
-- defines it itself (`src/secp256k1.c`, before it includes the public
-- header), and a command-line copy only produces a
-- `"SECP256K1_BUILD" redefined` warning. The shim compiles as a plain
-- consumer of the header, also without the define.

import Lake
open Lake DSL System

package LeanHazmatSecp256k1 where
  -- SPDX identifier; LICENSE lives at the umbrella root until/unless this
  -- family is promoted to a standalone mirror (ARCHITECTURE.md §12).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../../LICENSE"]
  -- `-lpthread`: the shim's `pthread_once` lives in libpthread on
  -- glibc older than 2.34 (libc carries it on 2.34+, musl, macOS);
  -- `--as-needed` drops the flag where it is not needed. Covers this
  -- package's own test-lib link.
  moreLinkArgs := #["-lpthread"]

/-- The library's compiler flags: its portable defaults (mirroring the
autotools `-O2` build) plus the define above. Per Lake's `buildO`
contract (Lake/Build/Common.lean) these all go in the `traceArgs`
position: they join the dependency-trace hash, so a flag change
rebuilds. Only discovered `-I` paths belong in the untraced `weakArgs`
position. -/
def secp256k1Flags : Array String :=
  #["-O2", "-fPIC", "-DENABLE_MODULE_RECOVERY"]

/-- The vendored libsecp256k1 checkout (absent until `just
hazmat-secp256k1-vendor` runs). -/
def secp256k1Dir (pkg : Package) : FilePath :=
  pkg.dir / "vendor" / "secp256k1"

/-- The pinned rev, written by `just hazmat-secp256k1-vendor` on every
fetch. Folding it into each target's trace makes a re-vendor at a new
pin rebuild every object, even though the compile sees only the
top-level source files (the amalgamation pulls in most of the library
through `#include`, invisible to a single-input trace). The pin is the
supported change path: the trace covers the top-level sources and the
`.pin` only, so a hand edit to some other vendored file does not by
itself trigger a rebuild. -/
def secp256k1Pin (pkg : Package) : FilePath :=
  secp256k1Dir pkg / ".pin"

/-- The vendor guard, shared by every target below: fails the build
with the fetch hint when `path` is absent. -/
def requireVendored (path : FilePath) (what : String) : IO Unit := do
  if !(← path.pathExists) then
    error s!"{what}, run `just hazmat-secp256k1-vendor` (expected {path})"

-- libsecp256k1 amalgamation. `src/secp256k1.c` transitively includes
-- the whole library; do NOT compile the individual `*_impl.h` users
-- (they would duplicate symbols). The two `precomputed_ecmult*.c`
-- translation units are the (committed) generated ecmult tables the
-- core references; upstream's own build compiles both alongside the
-- amalgamation.
target libsecp256k1.o pkg : FilePath := do
  let src := secp256k1Dir pkg / "src" / "secp256k1.c"
  requireVendored src "libsecp256k1 not vendored"
  requireVendored (secp256k1Pin pkg) "libsecp256k1 pin missing"
  let obj := pkg.buildDir / "secp256k1" / "secp256k1.o"
  let coreJob ← inputTextFile src
  let pinJob ← inputTextFile (secp256k1Pin pkg)
  buildO obj (coreJob.zipWith (fun p _ => p) pinJob) #[] secp256k1Flags "cc" getLeanTrace

-- The ecmult window tables (see above). Same flags as the core; one
-- target per translation unit, both land in the family archive, and
-- both carry the pin in their trace.
target libsecp256k1_pre_g.o pkg : FilePath := do
  let src := secp256k1Dir pkg / "src" / "precomputed_ecmult.c"
  requireVendored src "libsecp256k1 not vendored"
  requireVendored (secp256k1Pin pkg) "libsecp256k1 pin missing"
  let obj := pkg.buildDir / "secp256k1" / "precomputed_ecmult.o"
  let srcJob ← inputTextFile src
  let pinJob ← inputTextFile (secp256k1Pin pkg)
  buildO obj (srcJob.zipWith (fun p _ => p) pinJob) #[] secp256k1Flags "cc" getLeanTrace

-- The generator-multiplication window table (`secp256k1_ecmult_gen_prec_table`).
target libsecp256k1_ecmult_gen.o pkg : FilePath := do
  let src := secp256k1Dir pkg / "src" / "precomputed_ecmult_gen.c"
  requireVendored src "libsecp256k1 not vendored"
  requireVendored (secp256k1Pin pkg) "libsecp256k1 pin missing"
  let obj := pkg.buildDir / "secp256k1" / "precomputed_ecmult_gen.o"
  let srcJob ← inputTextFile src
  let pinJob ← inputTextFile (secp256k1Pin pkg)
  buildO obj (srcJob.zipWith (fun p _ => p) pinJob) #[] secp256k1Flags "cc" getLeanTrace

-- The Lean-facing secp256k1 shim. Needs the library's `include/` on
-- the include path for `<secp256k1.h>`, and the Lean runtime headers
-- for `lean/lean.h`.
target secp256k1_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "secp256k1_shim.c"
  let incDir := secp256k1Dir pkg / "include"
  requireVendored incDir "libsecp256k1 not vendored"
  requireVendored (secp256k1Pin pkg) "libsecp256k1 pin missing"
  let obj := pkg.buildDir / "csrc" / "secp256k1_shim.o"
  let leanInclude ← getLeanIncludeDir
  -- The pin is part of the trace: the shim compiles against the vendored
  -- `include/`, so a re-vendor at a new pin must rebuild it.
  let srcJob ← inputTextFile src
  let pinJob ← inputTextFile (secp256k1Pin pkg)
  buildO obj (srcJob.zipWith (fun p _ => p) pinJob)
    #["-I", leanInclude.toString, "-I", incDir.toString]
    #["-fPIC", "-O2"] "cc" getLeanTrace

-- One archive carrying the shim + the whole of libsecp256k1. Lake
-- links it into any precompiled library or executable that
-- (transitively) `require`s this package.
extern_lib libleanhazmat_secp256k1 pkg := do
  let libO    ← libsecp256k1.o.fetch
  let preGO   ← libsecp256k1_pre_g.o.fetch
  let genO    ← libsecp256k1_ecmult_gen.o.fetch
  let shimO   ← secp256k1_shim.o.fetch
  let name := nameToStaticLib "leanhazmat_secp256k1"
  buildStaticLib (pkg.staticLibDir / name) #[shimO, libO, preGO, genO]

@[default_target]
lean_lib LeanHazmatSecp256k1 where
  -- Precompiled shared lib so importers link native code. Default
  -- globs (root only) suffice. `LeanHazmatSecp256k1.lean` imports
  -- `…Secp256k1.Ffi`.
  precompileModules := true

-- Byte-level Known-Answer-Test gate against the published vectors
-- (EIP-155 example + deterministic second signature + negatives).
-- Self-contained (no upstream deps); built explicitly via
-- `lake build LeanHazmatSecp256k1Tests`.
lean_lib LeanHazmatSecp256k1Tests where
  roots := #[`LeanHazmatSecp256k1Tests]
  globs := #[.andSubmodules `LeanHazmatSecp256k1Tests]
