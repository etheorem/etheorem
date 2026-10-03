-- LeanHazmatBlake2f subpackage: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because the in-repo C shim
-- (`csrc/blake2f_shim.c`, the RFC 7693 `F` compression) needs a build
-- target the declarative TOML form cannot express. Unlike the other
-- vendored families there is **no `vendor/` tree and no fetch recipe**:
-- the whole native surface is this one `.c` file.

import Lake
open Lake DSL System

package LeanHazmatBlake2f where
  -- SPDX identifier; the LICENSE file lives at the umbrella root
  -- until/unless this family is promoted to a standalone mirror
  -- (packages/hazmat/docs/ARCHITECTURE.md §12).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../../LICENSE"]
  -- Self-contained C, no system library, no `-march=native` (the shim
  -- is portable scalar code and the precompile is not on a hot path).

-- The Lean-facing BLAKE2f shim. Needs only the Lean runtime headers.
-- Per Lake's `buildO` contract (Lake/Build/Common.lean): only
-- `traceArgs` join the dependency-trace hash, `weakArgs` do not, so
-- the portable flags (defines, `-f`/`-O`) go in `traceArgs` and a flag
-- change rebuilds. The discovered `-I` paths stay `weakArgs`: they
-- vary by system without changing what the code means.
target blake2f_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "blake2f_shim.c"
  let obj := pkg.buildDir / "csrc" / "blake2f_shim.o"
  let leanInclude ← getLeanIncludeDir
  buildO obj (← inputTextFile src)
    #["-I", leanInclude.toString]
    #["-fPIC", "-O2"] "cc" getLeanTrace

-- The family's native archive. Lake links this `.a` into any
-- precompiled library or executable that (transitively) `require`s
-- this package.
extern_lib libleanhazmat_blake2f pkg := do
  let shimO ← blake2f_shim.o.fetch
  let lib := pkg.staticLibDir / nameToStaticLib "leanhazmat_blake2f"
  buildStaticLib lib #[shimO]

@[default_target]
lean_lib LeanHazmatBlake2f where
  -- Ship as a precompiled shared lib so importers link native code
  -- rather than recompiling the binding. Default globs (root module
  -- only) suffice: `LeanHazmatBlake2f.lean` imports
  -- `LeanHazmatBlake2f.Ffi`, which is built transitively.
  precompileModules := true

-- Byte-level Known-Answer-Test gate against the official EIP-152
-- vectors. Self-contained, no upstream deps, so this package validates
-- standalone when split to a mirror. Built explicitly via
-- `lake build LeanHazmatBlake2fTests`; the default `lake build` skips it.
lean_lib LeanHazmatBlake2fTests where
  roots := #[`LeanHazmatBlake2fTests]
  globs := #[.andSubmodules `LeanHazmatBlake2fTests]
