-- LeanHazmatSha256 subpackage: Lake configuration.
--
-- Uses `lakefile.lean` rather than `lakefile.toml` because the FFI
-- SHA-256 shims (`csrc/sha256_*.c`) need procedural build targets
-- (`buildO` over `.c` files), `pkg-config`-driven OpenSSL discovery,
-- and, on x86_64 Linux, a delegated build of the vendored ISA-L
-- `sha256_mb` unit; the declarative TOML form can express none of
-- these.
--
-- Per hazmat-docs/ARCHITECTURE.md §3.3 the pkg-config / glob helpers
-- below are deliberately *duplicated* across family lakefiles rather
-- than shared: a `lakefile.lean` cannot import another package's code
-- (it defines the build graph before anything in it is built), and
-- the duplicated surface is small and stable.

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

/-- OpenSSL link args via `pkg-config`. We *always* prepend an
explicit `-L<libdir>` from `pkg-config --variable=libdir libcrypto`
even when `pkg-config --libs` omits it: the Lean toolchain bundles
its own `lld` whose default library search path does **not** include
the system's standard locations (`/usr/lib`, `/usr/lib/x86_64-linux-gnu`,
`/usr/lib64`, …), so an unqualified `-lcrypto` fails with
`unable to find library -lcrypto` even though `libcrypto.so` is where
the system would expect. The explicit `-L` makes the location
unambiguous to Lean's `lld`.

On Debian/Ubuntu `pkg-config --variable=libdir libcrypto` returns
`/usr/lib/x86_64-linux-gnu`; on Fedora `/usr/lib64`; on macOS
Homebrew `/opt/homebrew/opt/openssl@3/lib`; on Nix the store path.
All transparent to this code. pkg-config does the platform
discrimination for us. -/
unsafe def opensslLinkArgs : Array String :=
  let libDir := runPkgConfig #["--variable=libdir", "libcrypto"] #[]
  let libs   := runPkgConfig #["--libs",            "libcrypto"]
                  opensslFallbackLinkArgs
  let libDirFlags := libDir.map (fun d => "-L" ++ d)
  libDirFlags ++ libs

/-- OpenSSL `-I<dir>` flags via `pkg-config --cflags libcrypto`,
appended to `cShimFlags` so the C shims find `<openssl/evp.h>`. On
Debian / Ubuntu the headers live at `/usr/include` and no explicit
`-I` is needed; on macOS Homebrew openssl@3 is keg-only and the `.pc`
file's `-I/opt/homebrew/opt/openssl@3/include` is required. Empty
fallback keeps Debian working when pkg-config is missing. -/
unsafe def opensslCFlags : Array String :=
  runPkgConfig #["--cflags", "libcrypto"] #[]

package LeanHazmatSha256 where
  -- SPDX identifier; the LICENSE file lives at the umbrella root
  -- until/unless this family is promoted to a standalone mirror
  -- (hazmat-docs/ARCHITECTURE.md §12), at which point a local
  -- LICENSE copy replaces the `../../` reference.
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  -- OpenSSL link args, discovered at lakefile-load time. Required so
  -- this package's *own* test lib (`LeanHazmatSha256Tests`, which
  -- evaluates the FFI under `native_decide`) links `libcrypto`. Lake
  -- does NOT propagate these args to dependent packages across
  -- `require` (settled by hazmat-docs/PLAN.md Stage 0; SizzLean and
  -- EthCLSpecs each keep their own discovery), but the `extern_lib`
  -- archive below *does* propagate.
  moreLinkArgs := unsafe opensslLinkArgs
  -- Expose the host's SHA-NI / AVX2 extensions to the Lean→C path,
  -- matching the rest of the monorepo. Bakes in the build host's ISA
  -- (fine for local dev / CI); for a portable artefact switch to
  -- `-march=x86-64-v3`.
  moreLeancArgs := #["-march=native"]

-- C optimisation flags for the SHA-256 shims. `-O3` enables full
-- optimisation (default `cc` is `-O0`); `-march=native` lets the
-- compiler emit SHA-NI / AVX2 intrinsics matching the build host.
-- The trailing `opensslCFlags` adds the `-I<dir>` paths from
-- `pkg-config --cflags libcrypto` so the shims find
-- `<openssl/evp.h>` on systems (macOS Homebrew, Nix) where it isn't
-- in the compiler's default search path.
def cShimFlags (leanInclude : FilePath) : Array String :=
  #["-fPIC", "-O3", "-march=native", "-I", leanInclude.toString]
    ++ (unsafe opensslCFlags)

target sha256_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "sha256_shim.c"
  let obj := pkg.buildDir / "csrc" / "sha256_shim.o"
  let leanInclude ← getLeanIncludeDir
  buildO obj (← inputTextFile src) (cShimFlags leanInclude) #[] "cc" getLeanTrace

/-! ## Batched combine backend: ISA-L on x86_64 Linux, OpenSSL elsewhere

`csrc/sha256_batch.c` has two backends behind one symbol. On x86_64
Linux it uses Intel ISA-L crypto's `sha256_mb` multi-buffer engine
(4 / 8 / 16 lanes, CPUID-dispatched at run time); everywhere else it
keeps the OpenSSL EVP loop. This lakefile makes that choice once, in
`useIsal`, and passes it to the C file as `-DLEAN_HAZMAT_SHA256_ISAL`,
so the compiled code and the archive contents cannot disagree.

ISA-L is vendored (`just hazmat-sha256-vendor`, pinned tag, gitignored
`vendor/isa-l_crypto/`), like blst and c-kzg. Its SHA-256 lanes are
`nasm` assembly, so the x86_64 Linux build needs `nasm` on `PATH`
(`just doctor-native` checks). Per hazmat-docs/ARCHITECTURE.md §6 the
Lake target delegates to ISA-L's own `Makefile.unx` for the one
`sha256_mb` unit rather than re-deriving its flags; the resulting
objects are folded into this package's single archive, so no new link
flag is needed here or in any dependent package. -/

/-- Use the ISA-L backend on x86_64 Linux only. ISA-L's `sha256_mb`
also builds on macOS x86_64, but that target is not worth a second
assembler configuration; it takes the OpenSSL loop. -/
def useIsal : Bool :=
  System.Platform.target.startsWith "x86_64"
    && !System.Platform.isWindows && !System.Platform.isOSX

/-- The vendored ISA-L crypto checkout (absent until `just
hazmat-sha256-vendor` runs). -/
def isalDir (pkg : Package) : FilePath := pkg.dir / "vendor" / "isa-l_crypto"

/-- Extra C flags for `sha256_batch.c` when the ISA-L backend is on:
the backend switch plus the vendored public headers
(`<isa-l_crypto/sha256_mb.h>`). -/
def isalShimFlags (pkg : Package) : Array String :=
  if useIsal then
    #["-DLEAN_HAZMAT_SHA256_ISAL", "-I", (isalDir pkg / "include").toString]
  else
    #[]

-- Build ISA-L's `sha256_mb` unit through its own `Makefile.unx`
-- (`units=sha256_mb lib`), in place under `vendor/isa-l_crypto/bin/`.
-- `CC=cc -fPIC` because the archive is linked into precompiled shared
-- libraries; ISA-L's plain `lib` target compiles its C without PIC.
-- ISA-L's own runtime CPUID dispatch keeps the objects portable, so
-- no `-march` is passed. The job's trace is `make.inc` (it carries the
-- ISA-L version); `make` does its own incremental work per file.
-- Returns the unit's archive; the `extern_lib` below folds the
-- objects next to it into the family archive.
target isal_sha256_mb.a pkg : FilePath := do
  let dir := isalDir pkg
  let makefile := dir / "Makefile.unx"
  unless (← makefile.pathExists) do
    error s!"ISA-L crypto not vendored — run `just hazmat-sha256-vendor` (expected {makefile})"
  let archive := dir / "bin" / "isa-l_crypto.a"
  let makeInc ← inputTextFile (dir / "make.inc")
  buildFileAfterDep archive makeInc fun _ => do
    -- `quiet`: ISA-L echoes one line per file; keep that out of the
    -- default build log (Lake would replay it on every build).
    proc (quiet := true) {
      cmd := "make"
      cwd := dir
      args := #["-f", "Makefile.unx", "units=sha256_mb", "lib", "CC=cc -fPIC", "-j4"]
    }

/-- The object files ISA-L's `make lib` left next to its archive. Only
the requested unit was built, so every `.o` under `bin/` belongs to
`sha256_mb`. -/
def isalObjects (archive : FilePath) : IO (Array FilePath) := do
  let some bin := archive.parent
    | throw <| IO.userError s!"ISA-L archive has no parent directory: {archive}"
  let entries ← bin.readDir
  return entries.filterMap fun e =>
    if e.path.extension == some "o" then some e.path else none

-- Batched SHA-256 sibling combine. Same compilation shape as
-- `sha256_shim.o`, plus the backend switch from `isalShimFlags`; the
-- `.o` files are linked into one static lib (below) so a single
-- `extern_lib` carries the whole family.
target sha256_batch.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "sha256_batch.c"
  let obj := pkg.buildDir / "csrc" / "sha256_batch.o"
  let leanInclude ← getLeanIncludeDir
  let flags := cShimFlags leanInclude ++ isalShimFlags pkg
  buildO obj (← inputTextFile src) flags #[] "cc" getLeanTrace

-- The family's native archive. Lake links this `.a` into any
-- precompiled library or executable that (transitively) `require`s
-- this package. That is how SizzLean's hash path, and downstream
-- exes, pick up the native symbols. On x86_64 Linux the ISA-L
-- `sha256_mb` objects are folded into the same archive, so dependents
-- see one self-contained library on every platform.
extern_lib libleanhazmat_sha256 pkg := do
  let shimFile  ← sha256_shim.o.fetch
  let batchFile ← sha256_batch.o.fetch
  let lib := pkg.staticLibDir / nameToStaticLib "leanhazmat_sha256"
  if useIsal then
    let isalArchive ← isal_sha256_mb.a.fetch
    let deps := Job.collectArray #[shimFile, batchFile, isalArchive] "objs"
    deps.mapM fun files => do
      let art ← buildArtifactUnlessUpToDate lib (ext := "a") (restore := true) do
        let isalObjs ← isalObjects files[2]!
        compileStaticLib lib (#[files[0]!, files[1]!] ++ isalObjs) (← getLeanAr)
      return art.path
  else
    buildStaticLib lib #[shimFile, batchFile]

@[default_target]
lean_lib LeanHazmatSha256 where
  -- Ship as a precompiled shared lib so importers (SizzLean) link
  -- native code rather than recompiling the bindings. Default globs
  -- (root module only) suffice: `LeanHazmatSha256.lean` imports
  -- `LeanHazmatSha256.Ffi`, which is built transitively.
  precompileModules := true

-- Byte-level Known-Answer-Test gate. Built explicitly via
-- `lake build LeanHazmatSha256Tests`; the default `lake build` skips
-- it. Self-contained, no LeanSha256 / SizzLean dependency, so this
-- package validates standalone when split to a mirror.
lean_lib LeanHazmatSha256Tests where
  roots := #[`LeanHazmatSha256Tests]
  globs := #[.andSubmodules `LeanHazmatSha256Tests]
