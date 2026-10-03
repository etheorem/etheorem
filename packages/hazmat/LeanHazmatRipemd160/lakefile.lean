-- LeanHazmatRipemd160 subpackage: Lake configuration.
--
-- Uses `lakefile.lean` rather than `lakefile.toml` because the RIPEMD-160
-- shim (`csrc/ripemd160_shim.c`) needs a `buildO` target over a `.c`
-- file plus `pkg-config`-driven OpenSSL discovery, which the
-- declarative TOML form cannot express.
--
-- Per packages/hazmat/docs/ARCHITECTURE.md §3.3 the pkg-config helpers below
-- are deliberately *duplicated* from the sibling OpenSSL-backed
-- families (LeanHazmatSha256, LeanHazmatModexp, LeanHazmatP256)
-- rather than shared: a `lakefile.lean` cannot import another
-- package's code, and the duplicated surface is small and stable.

import Lake
open Lake DSL System

/-- Helper: run `pkg-config <args>` at lakefile-load time and return
its stdout split on whitespace. Returns `fallback` (default empty)
when pkg-config isn't installed, exits non-zero, or prints nothing;
call sites decide whether empty is an error. -/
unsafe def runPkgConfig (args : Array String)
    (fallback : Array String) : Array String :=
  Id.run <| unsafeBaseIO do
    let result ← (IO.Process.output { cmd := "pkg-config", args }).toBaseIO
    match result with
    | .ok r =>
        if r.exitCode == 0 then
          let out := r.stdout.trimAscii.toString
          if out.isEmpty then return fallback
          return (out.splitOn " ").toArray.filter (fun a => !a.isEmpty)
        else
          return fallback
    | .error _ => return fallback

/-- OpenSSL link args via `pkg-config`, always with an explicit
`-L<libdir>`: Lean's bundled `lld` does not search the system's
default library paths (full rationale in LeanHazmatSha256's
lakefile). On a pkg-config failure this returns the empty array; the
shim target below checks for that and fails the build with the
actionable message (a lakefile-load-time `error` is not available in
a plain definition). -/
unsafe def opensslLinkArgs : Array String :=
  let libs   := runPkgConfig #["--libs",            "libcrypto"] #[]
  let libDir := runPkgConfig #["--variable=libdir", "libcrypto"] #[]
  if libs.isEmpty then
    -- The shim target turns the empty array into the build error with
    -- the install hint; nothing else consumes this value.
    #[]
  else
    libDir.map (fun d => "-L" ++ d) ++ libs

/-- OpenSSL `-I<dir>` flags, for the OpenSSL headers on systems where
they are not in the compiler's default search path (macOS Homebrew,
Nix). -/
unsafe def opensslCFlags : Array String :=
  runPkgConfig #["--cflags", "libcrypto"] #[]

package LeanHazmatRipemd160 where
  -- SPDX identifier; the LICENSE file lives at the umbrella root
  -- until/unless this family is promoted to a standalone mirror
  -- (packages/hazmat/docs/ARCHITECTURE.md §12).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../../LICENSE"]
  -- OpenSSL link args, discovered at lakefile-load time, so this
  -- package's own test lib links `libcrypto`. Link args do NOT
  -- propagate across `require` (packages/hazmat/docs/PLAN.md Stage 0).
  -- `-lpthread`: the shim's `pthread_once` lives in libpthread on
  -- glibc older than 2.34 (libc carries it on 2.34+, musl, macOS);
  -- `--as-needed` drops the flag where it is not needed.
  moreLinkArgs := unsafe opensslLinkArgs ++ #["-lpthread"]

-- Per Lake's `buildO` contract (Lake/Build/Common.lean): only
-- `traceArgs` join the dependency-trace hash, `weakArgs` do not, so
-- the portable flags (`-fPIC`, `-O2`) go in `traceArgs` and a flag
-- change rebuilds. The discovered `-I` paths stay `weakArgs`: they
-- vary by system without changing what the code means.
def cShimTraceFlags : Array String := #["-fPIC", "-O2"]

def cShimIncludeArgs (leanInclude : FilePath) : Array String :=
  #["-I", leanInclude.toString] ++ (unsafe opensslCFlags)

-- The Lean-facing RIPEMD-160 shim.
target ripemd160_shim.o pkg : FilePath := do
  if ((unsafe opensslLinkArgs).isEmpty) then
    error "OpenSSL link flags not found: install pkg-config with the OpenSSL development package (Debian/Ubuntu: libssl-dev; Fedora/RHEL: openssl-devel; Arch: openssl; Alpine: openssl-dev; macOS: brew install openssl@3 pkg-config)"
  let src := pkg.dir / "csrc" / "ripemd160_shim.c"
  let obj := pkg.buildDir / "csrc" / "ripemd160_shim.o"
  let leanInclude ← getLeanIncludeDir
  buildO obj (← inputTextFile src) (cShimIncludeArgs leanInclude) cShimTraceFlags "cc" getLeanTrace

-- The family's native archive (the shim only; libcrypto is a system
-- library reached at link time through `moreLinkArgs`).
extern_lib libleanhazmat_ripemd160 pkg := do
  let shimFile ← ripemd160_shim.o.fetch
  let lib := pkg.staticLibDir / nameToStaticLib "leanhazmat_ripemd160"
  buildStaticLib lib #[shimFile]

@[default_target]
lean_lib LeanHazmatRipemd160 where
  -- Ship as a precompiled shared lib so importers link native code
  -- rather than recompiling the binding. Default globs (root module
  -- only) suffice.
  precompileModules := true

-- Byte-level Known-Answer-Test gate against the published RIPEMD-160
-- vectors. Self-contained, no upstream deps, so this package validates
-- standalone when split to a mirror. Built explicitly via
-- `lake build LeanHazmatRipemd160Tests`; the default `lake build`
-- skips it.
lean_lib LeanHazmatRipemd160Tests where
  roots := #[`LeanHazmatRipemd160Tests]
  globs := #[.andSubmodules `LeanHazmatRipemd160Tests]
