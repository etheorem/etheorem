-- LeanHazmatXMSS: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because building xmss-reference C
-- sources requires `buildO` targets and pkg-config-driven OpenSSL discovery.
-- `hash.c` in xmss-reference calls OpenSSL's `SHA256()` for SHA-2 parameter
-- sets; fips202.c provides pure SHAKE for the SHAKE-based variants.
--
-- xmss-reference is vendored: `just hazmat-xmss-vendor` shallow-clones the
-- pinned commit into `vendor/xmss-reference/` before `lake build`. We compile
-- the simple (non-BDS) core (`xmss_core.c`) and exclude `randombytes.c`,
-- replacing it with deterministic seeding in `csrc/xmss_shim.c`.
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
last-resort values, when `pkg-config` is available it produces
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

unsafe def opensslLinkArgs : Array String :=
  let libDir := runPkgConfig #["--variable=libdir", "libcrypto"] #[]
  let libs   := runPkgConfig #["--libs", "libcrypto"] opensslFallbackLinkArgs
  libDir.map (fun d => "-L" ++ d) ++ libs

unsafe def opensslCFlags : Array String :=
  runPkgConfig #["--cflags", "libcrypto"] #[]

package LeanHazmatXMSS where
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

-- xmss-reference sources (simple core; excludes randombytes.c).
-- Matches XMSS_SOURCES from the reference Makefile minus randombytes.c.
-- xmss_core.c (not _fast.c) provides the simple signing path and defines
-- xmss_xmssmt_core_sk_bytes used by params.c.

target xmss_hash.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "hash.o") (← inputTextFile (v / "hash.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_fips202.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "fips202.o") (← inputTextFile (v / "fips202.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_hashaddr.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "hash_address.o") (← inputTextFile (v / "hash_address.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_params.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "params.o") (← inputTextFile (v / "params.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_utils.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "utils.o") (← inputTextFile (v / "utils.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_wots.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "wots.o") (← inputTextFile (v / "wots.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_core.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "xmss_core.o") (← inputTextFile (v / "xmss_core.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_commons.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "xmss_commons.o") (← inputTextFile (v / "xmss_commons.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

target xmss_main.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  buildO (pkg.buildDir / "xmss" / "xmss.o") (← inputTextFile (v / "xmss.c"))
    (xmssLibFlags v) #[] "cc" getLeanTrace

-- Lean-facing shim: randombytes replacement + keygen/sign/verify wrappers.
target xmss_shim.o pkg : FilePath := do
  let v := pkg.dir / "vendor" / "xmss-reference"
  unless (← v.pathExists) do error (xmssVendorError v)
  let leanInclude ← getLeanIncludeDir
  buildO (pkg.buildDir / "csrc" / "xmss_shim.o")
    (← inputTextFile (pkg.dir / "csrc" / "xmss_shim.c"))
    (xmssShimFlags v leanInclude) #[] "cc" getLeanTrace

-- Single static archive: all xmss-reference objects + our shim.
extern_lib libleanhazmat_xmss pkg := do
  let hashO     ← xmss_hash.o.fetch
  let fips202O  ← xmss_fips202.o.fetch
  let hashaddrO ← xmss_hashaddr.o.fetch
  let paramsO   ← xmss_params.o.fetch
  let utilsO    ← xmss_utils.o.fetch
  let wotsO     ← xmss_wots.o.fetch
  let coreO     ← xmss_core.o.fetch
  let commonsO  ← xmss_commons.o.fetch
  let mainO     ← xmss_main.o.fetch
  let shimO     ← xmss_shim.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanhazmat_xmss")
    #[hashO, fips202O, hashaddrO, paramsO, utilsO, wotsO, coreO, commonsO, mainO, shimO]

@[default_target]
lean_lib LeanHazmatXMSS where
  precompileModules := true

lean_lib LeanHazmatXMSSTests where
  roots := #[`LeanHazmatXMSSTests]
  globs := #[.andSubmodules `LeanHazmatXMSSTests]
