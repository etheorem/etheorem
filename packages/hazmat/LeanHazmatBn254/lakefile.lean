-- LeanHazmatBn254 subpackage: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because it compiles vendored
-- C++ into an `extern_lib`. herumi/mcl is vendored, `just
-- hazmat-bn254-vendor` shallow-clones the pinned tag (v4.10) into
-- `vendor/mcl/` before `lake build` (packages/hazmat/docs/ARCHITECTURE.md §6);
-- the build below stays offline.
--
-- This is the one LeanHazmat family with a **C++** compiler in the
-- build: mcl is C++, so `src/fp.cpp` and the shim compile with `c++`.
-- The C++ *runtime* is compiled out: the flags below (exceptions,
-- RTTI, threadsafe statics, string, CSPRNG, Xbyak all off) leave the
-- compiled code referencing only libc and libgcc, verified by `nm -u`
-- at design time. The archive is therefore as self-contained as the C
-- families: a consumer needs no `-lstdc++` / `-lc++` and no C++
-- toolchain at link time.

import Lake
open Lake DSL System

package LeanHazmatBn254 where
  -- SPDX identifier; LICENSE lives at the umbrella root until/unless
  -- this family is promoted to a standalone mirror (ARCHITECTURE.md §12).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../../LICENSE"]
  -- `-lpthread`: the shim's `pthread_once` lives in libpthread on
  -- glibc older than 2.34 (libc carries it on 2.34+, musl, macOS);
  -- `--as-needed` drops the flag where it is not needed. The compiled
  -- mcl references no C++ runtime, so no other consumer flags exist.
  -- Covers this package's own test-lib link.
  moreLinkArgs := #["-lpthread"]

/-- mcl's compiler flags. The bit-size defines select the alt_bn128
instantiation; `MCL_BINT_ASM=0` selects the portable C bignum
primitives (upstream's default needs x64 assembly or LLVM-IR objects);
`MCL_DONT_USE_XBYAK` skips the JIT assembler path; and the
exceptions / RTTI / string / CSPRNG defines compile out every C++
runtime dependency, down to libc + libgcc only. -/
def mclFlags : Array String :=
  #["-O2", "-fPIC", "-std=c++14",
    "-fno-exceptions", "-fno-rtti", "-fno-threadsafe-statics",
    "-DCYBOZU_DONT_USE_EXCEPTION", "-DCYBOZU_DONT_USE_STRING",
    "-DMCL_DONT_USE_CSPRNG", "-DMCL_DONT_USE_XBYAK",
    "-DMCL_FP_BIT=256", "-DMCL_FR_BIT=256", "-DMCL_BINT_ASM=0"]

/-- The vendored mcl checkout (absent until `just
hazmat-bn254-vendor` runs). -/
def mclDir (pkg : Package) : FilePath := pkg.dir / "vendor" / "mcl"

/-- The pinned rev, written by `just hazmat-bn254-vendor` on every
fetch. Folding it into each target's trace makes a re-vendor at a new
pin rebuild every object, even though the compile sees only the
top-level source files (`fp.cpp` pulls in most of the library through
`#include`, invisible to a single-input trace). The pin is the
supported change path: the trace covers the top-level sources and the
`.pin` only, so a hand edit to some other vendored file does not by
itself trigger a rebuild. -/
def mclPin (pkg : Package) : FilePath :=
  mclDir pkg / ".pin"

/-- The vendor guard, shared by every target below: fails the build
with the fetch hint when `path` is absent. -/
def requireVendored (path : FilePath) (what : String) : IO Unit := do
  if !(← path.pathExists) then
    error s!"{what}, run `just hazmat-bn254-vendor` (expected {path})"

-- mcl's single translation unit: all `mclBn*` symbols for the 256-bit
-- instantiation. Do NOT compile other `src/*.cpp` files (she_c256 is
-- an unrelated library; bn_c256 is an empty placeholder).
target mcl_fp.o pkg : FilePath := do
  let src := mclDir pkg / "src" / "fp.cpp"
  requireVendored src "mcl not vendored"
  requireVendored (mclPin pkg) "mcl pin missing"
  let obj := pkg.buildDir / "mcl" / "fp.o"
  let srcJob ← inputTextFile src
  let pinJob ← inputTextFile (mclPin pkg)
  -- Per Lake's `buildO` contract (Lake/Build/Common.lean): only
  -- `traceArgs` join the dependency-trace hash, `weakArgs` do not. The
  -- mcl defines and no-runtime flags go in `traceArgs` (a flag change
  -- rebuilds); the discovered `-I` path stays `weakArgs`.
  buildO obj (srcJob.zipWith (fun p _ => p) pinJob)
    #["-I", (mclDir pkg / "include").toString] mclFlags "c++" getLeanTrace

-- The Lean-facing BN254 shim (C++, `extern "C"` entry points). Needs
-- mcl's `include/` on the include path (and the same defines,
-- `mcl/bn.h` refuses to compile without the bit sizes), plus the Lean
-- runtime headers. The shim itself uses no exceptions, so the
-- no-exception flags apply here too.
target bn254_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "bn254_shim.cpp"
  let incDir := mclDir pkg / "include"
  requireVendored incDir "mcl not vendored"
  requireVendored (mclPin pkg) "mcl pin missing"
  let obj := pkg.buildDir / "csrc" / "bn254_shim.o"
  let leanInclude ← getLeanIncludeDir
  let srcJob ← inputTextFile src
  let pinJob ← inputTextFile (mclPin pkg)
  buildO obj (srcJob.zipWith (fun p _ => p) pinJob)
    #["-I", leanInclude.toString, "-I", incDir.toString] mclFlags
    "c++" getLeanTrace

-- One archive carrying the shim + the whole of mcl. Lake links it
-- into any precompiled library or executable that (transitively)
-- `require`s this package.
extern_lib libleanhazmat_bn254 pkg := do
  let fpO   ← mcl_fp.o.fetch
  let shimO ← bn254_shim.o.fetch
  let name := nameToStaticLib "leanhazmat_bn254"
  buildStaticLib (pkg.staticLibDir / name) #[shimO, fpO]

@[default_target]
lean_lib LeanHazmatBn254 where
  -- Precompiled shared lib so importers link native code. Default
  -- globs (root only) suffice. `LeanHazmatBn254.lean` imports
  -- `…Bn254.Ffi`.
  precompileModules := true

-- Byte-level Known-Answer-Test gate against the EIP-196/197 vectors
-- (generated from ethereum/py_ecc, the EIP-referenced reference
-- implementation). Self-contained (no upstream deps); built explicitly
-- via `lake build LeanHazmatBn254Tests`.
lean_lib LeanHazmatBn254Tests where
  roots := #[`LeanHazmatBn254Tests]
  globs := #[.andSubmodules `LeanHazmatBn254Tests]
