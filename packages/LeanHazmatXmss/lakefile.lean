-- LeanHazmatXmss: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because building xmss-reference's C
-- sources needs `buildO` targets and pkg-config-driven OpenSSL discovery.
-- `hash.c` in xmss-reference calls OpenSSL's `SHA256()` for the SHA-2
-- parameter sets; `fips202.c` provides pure SHAKE for the SHAKE variants.
--
-- xmss-reference is vendored: `just hazmat-xmss-vendor` clones the pinned
-- commit into `vendor/xmss-reference/` before `lake build`. We compile the
-- simple (non-BDS) core (`xmss_core.c`) and exclude `randombytes.c`; the shim
-- reaches the seeded keygen path directly, so it never needs it (see
-- `csrc/xmss_shim.c`).
--
-- Per hazmat-docs/ARCHITECTURE.md §3.3, the pkg-config helpers are duplicated
-- per-lakefile (a lakefile cannot import another package's Lean code during
-- the build-graph construction phase).

import Lake
open Lake DSL System

/-- Hardcoded Debian/Ubuntu fallback. Used when `pkg-config` itself
isn't installed (rare on Linux distros, common on minimal Docker
images). The Linux-only `-l:libcrypto.so.3` GNU-ld syntax and the
multiarch `-L/usr/lib/x86_64-linux-gnu` path are deliberately the
last-resort values; when `pkg-config` is available it produces
portable equivalents for Fedora, Arch, macOS Homebrew, Nix, etc. -/
private def opensslFallbackLinkArgs : Array String :=
  #["-L/usr/lib/x86_64-linux-gnu", "-l:libcrypto.so.3"]

/-- Helper: run `pkg-config <args>` at lakefile-load time and return
its stdout split on whitespace. Returns `fallback` if pkg-config
isn't installed, exits non-zero, or returns an empty result. -/
unsafe def runPkgConfig (args : Array String) (fallback : Array String) : Array String :=
  Id.run <| unsafeBaseIO do
    let result ← (IO.Process.output { cmd := "pkg-config", args }).toBaseIO
    match result with
    | .ok r =>
        if r.exitCode == 0 then
          let out := r.stdout.trimAscii.toString
          if out.isEmpty then return fallback
          return (out.splitOn " ").toArray.filter (fun a => !a.isEmpty)
        else return fallback
    | .error _ => return fallback

/-- OpenSSL link args via `pkg-config`. We *always* prepend an explicit
`-L<libdir>` from `pkg-config --variable=libdir libcrypto`, because Lean
ships its own `lld` whose default library search path does **not** include
the system directories a native `cc` would search. Without the explicit
`-L`, the `-lcrypto` in the fallback resolves on a normal toolchain but
fails under Lean's `lld`. The explicit `-L` makes the location unambiguous. -/
unsafe def opensslLinkArgs : Array String :=
  let libDir := runPkgConfig #["--variable=libdir", "libcrypto"] #[]
  let libs   := runPkgConfig #["--libs", "libcrypto"] opensslFallbackLinkArgs
  libDir.map (fun d => "-L" ++ d) ++ libs

unsafe def opensslCFlags : Array String :=
  runPkgConfig #["--cflags", "libcrypto"] #[]

package LeanHazmatXmss where
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  -- hash.c calls OpenSSL's SHA256(); libcrypto must be linked.
  moreLinkArgs := unsafe opensslLinkArgs

-- C flags for xmss-reference library sources. Every file gets the vendor dir
-- on the include path; OpenSSL cflags are appended for the files that include
-- <openssl/sha.h> (applied to all files for simplicity — harmless on others).
def xmssLibFlags (vendorDir : FilePath) : Array String :=
  #["-fPIC", "-O2", "-I", vendorDir.toString] ++ (unsafe opensslCFlags)

def xmssShimFlags (vendorDir : FilePath) (leanInclude : FilePath) : Array String :=
  #["-fPIC", "-O2", "-I", vendorDir.toString, "-I", leanInclude.toString]
    ++ (unsafe opensslCFlags)

-- Vendor-presence guard message.
private def xmssVendorError (vendorDir : FilePath) : String :=
  s!"xmss-reference not vendored — run `just hazmat-xmss-vendor` (expected {vendorDir})"

/-- Compile one vendored xmss-reference source `<stem>.c` to `<stem>.o`.
Every library object shares this body (vendor-presence guard + `buildO` with
the shared flags); the per-source `target`s below are two lines each. -/
def compileXmssObj (pkg : Package) (stem : String) : FetchM (Job FilePath) := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / (stem ++ ".o"))
    (← inputTextFile (v / (stem ++ ".c"))) (xmssLibFlags v) #[] "cc" getLeanTrace

-- xmss-reference sources (simple core; excludes randombytes.c). Matches
-- XMSS_SOURCES from the reference Makefile minus randombytes.c. `xmss_core.c`
-- (not `_fast.c`) provides the simple signing path and `xmss.c` the OID
-- wrapper the shim calls into.
target xmss_hash.o     pkg : FilePath := compileXmssObj pkg "hash"
target xmss_fips202.o  pkg : FilePath := compileXmssObj pkg "fips202"
target xmss_hashaddr.o pkg : FilePath := compileXmssObj pkg "hash_address"
target xmss_params.o   pkg : FilePath := compileXmssObj pkg "params"
target xmss_utils.o    pkg : FilePath := compileXmssObj pkg "utils"
target xmss_wots.o     pkg : FilePath := compileXmssObj pkg "wots"
target xmss_core.o     pkg : FilePath := compileXmssObj pkg "xmss_core"
target xmss_commons.o  pkg : FilePath := compileXmssObj pkg "xmss_commons"
target xmss_main.o     pkg : FilePath := compileXmssObj pkg "xmss"

-- Lean-facing shim: keygen/sign/verify wrappers + the weak randombytes stub.
target xmss_shim.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  let leanInclude ← getLeanIncludeDir
  buildO (pkg.buildDir / "csrc" / "xmss_shim.o")
    (← inputTextFile (pkg.dir / "csrc" / "xmss_shim.c"))
    (xmssShimFlags v leanInclude) #[] "cc" getLeanTrace

-- Single static archive: all xmss-reference objects + our shim.
extern_lib libleanhazmat_xmss pkg := do
  let objs := #[← xmss_hash.o.fetch, ← xmss_fips202.o.fetch,
               ← xmss_hashaddr.o.fetch, ← xmss_params.o.fetch,
               ← xmss_utils.o.fetch, ← xmss_wots.o.fetch,
               ← xmss_core.o.fetch, ← xmss_commons.o.fetch,
               ← xmss_main.o.fetch, ← xmss_shim.o.fetch]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanhazmat_xmss") objs

@[default_target]
lean_lib LeanHazmatXmss where
  precompileModules := true
  -- Include submodules so `LeanHazmatXmss.Kat` (test-support SHAKE, not
  -- re-exported by the root) is precompiled and its native symbol is
  -- resolvable under `native_decide`.
  globs := #[.andSubmodules `LeanHazmatXmss]

lean_lib LeanHazmatXmssTests where
  roots := #[`LeanHazmatXmssTests]
  globs := #[.andSubmodules `LeanHazmatXmssTests]
