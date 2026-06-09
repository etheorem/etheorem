-- SizzLean subpackage: Lake configuration.
--
-- Uses `lakefile.lean` rather than `lakefile.toml` for the
-- `pkg-config`-driven OpenSSL discovery (`opensslLinkArgs`) and the
-- one-directory-deep glob auto-discovery (`globsUnder`), neither of
-- which the declarative TOML form can express.
--
-- The FFI SHA-256 binding itself no longer lives here: it was moved
-- to the `LeanHazmatSha256` package (hazmat-docs/ARCHITECTURE.md §9,
-- PLAN.md Stage 1). SizzLean now `require`s that package for the FFI
-- shim and keeps only the *spec-side* machinery, the `Hasher`
-- typeclass, the `Sha256` tag + instance, and the FFI ≡ pure-Lean
-- equivalence axioms, the one place entitled to import both the FFI
-- binding and the `LeanSha256` spec.
--
-- SizzLean still discovers OpenSSL link args because Lake does NOT
-- propagate a dependency's `moreLinkArgs` across `require` (PLAN.md
-- Stage 0): the `LeanHazmatSha256` `extern_lib` *archive* is linked
-- into SizzLean's executables (`ssz_bench`, `ssz_profile`)
-- transitively, but the `-lcrypto` flag that archive needs is not, so
-- SizzLean re-supplies it here for its own exes.

import Lake
open Lake DSL System

/-- Auto-discover lib contents one directory level deep. See the
umbrella's `docs/monorepo-arch.md` for the layout context. -/
unsafe def globsUnder
    (srcDir : System.FilePath) (rootName : Lean.Name)
    (exclude : Array String := #[]) : Array Glob :=
  Id.run <| unsafeBaseIO do
    let entries ← (System.FilePath.readDir srcDir).toBaseIO
    let .ok entries := entries
      | return #[]
    let mut out : Array Glob := #[]
    for e in entries do
      let name := e.fileName
      if exclude.contains name then continue
      let isDirRes : Except IO.Error Bool ←
        (e.path.isDir : IO Bool).toBaseIO
      let isDir : Bool := isDirRes.toOption.getD false
      if isDir then
        out := out.push (.submodules (Lean.Name.str rootName name))
      else if e.path.extension == some "lean" then
        let stem : String := (name.dropEnd 5).copy
        if exclude.contains stem then continue
        out := out.push (.one (Lean.Name.str rootName stem))
    return out

/-- Hardcoded Debian/Ubuntu fallback. Used when `pkg-config` itself
isn't installed (rare on Linux distros, common on minimal Docker
images). The Linux-only `-l:libcrypto.so.3` GNU-ld syntax and the
multiarch `-L/usr/lib/x86_64-linux-gnu` path are deliberately the
last-resort values. When `pkg-config` is available it produces
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
`unable to find library -lcrypto` even though `libcrypto.so` is
where the system would expect. The explicit `-L` makes the location
unambiguous to Lean's `lld`.

On Debian/Ubuntu `pkg-config --variable=libdir libcrypto` returns
`/usr/lib/x86_64-linux-gnu`; on Fedora `/usr/lib64`; on macOS
Homebrew `/opt/homebrew/opt/openssl@3/lib`; on Nix the store path.
All transparent to this code, pkg-config does the platform
discrimination for us. -/
unsafe def opensslLinkArgs : Array String :=
  let libDir := runPkgConfig #["--variable=libdir", "libcrypto"] #[]
  let libs   := runPkgConfig #["--libs",            "libcrypto"]
                  opensslFallbackLinkArgs
  let libDirFlags := libDir.map (fun d => "-L" ++ d)
  libDirFlags ++ libs

package SizzLean where
  -- SPDX identifier; the LICENSE file lives at the umbrella root.
  -- Reservoir requires a single-identifier SPDX expression.
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  -- Discovered at lakefile-load time via `pkg-config --libs libcrypto`;
  -- see `opensslLinkArgs` above for the rationale and the fallback.
  moreLinkArgs := unsafe opensslLinkArgs
  -- Lake's leanc default is already `-O3 -DNDEBUG -fPIC` with the
  -- usual hardening flags. We add `-march=native` so the host's
  -- AVX2/AVX-512/SHA-NI extensions are visible to the Lean→C path.
  -- Without this, leanc emits generic x86-64 baseline code that can't
  -- autovectorise the per-byte / per-word loops the Std `ByteArray` /
  -- `Array` IR walks the most. Cascades to every `lean_lib` (incl.
  -- `SizzLean`, `SizzLeanTests`, `SizzLeanBench`) and `lean_exe`
  -- (incl. `ssz_bench`) in this package.
  --
  -- Same `-march=native` caveat as the C-shim flags: bakes in the
  -- build host's ISA, fine for local dev and bench; for a shipped
  -- binary switch to a portable baseline (`-march=x86-64-v3`).
  moreLeancArgs := #["-march=native"]

-- The pure-Lean SHA-256 spec. SizzLean is the layer that imports
-- both this and the FFI binding below, and holds the equivalence
-- axioms tying them together (hazmat-docs/ARCHITECTURE.md §9).
require LeanSha256 from "../LeanSha256"

-- The FFI SHA-256 binding (OpenSSL `libcrypto`). Provides the
-- `LeanHazmat.Sha256.sha256Hash` / `sha256Combine` / `sha256BatchCombine`
-- externs that the `Hasher Sha256` instance and the equivalence
-- axioms delegate to. Its `extern_lib` archive is linked
-- transitively into SizzLean's executables.
require LeanHazmatSha256 from "../LeanHazmatSha256"

@[default_target]
lean_lib SizzLean where
  precompileModules := true
  globs :=
    #[.one `SizzLean] ++
    unsafe globsUnder ("SizzLean" : FilePath) `SizzLean

-- Tests live at the package root level (sibling of `SizzLean/`),
-- forming a separate `SizzLeanTests.*` module hierarchy. The `SizzLeanTests.lean`
-- index file re-exports the individual test files.
lean_lib SizzLeanTests where
  roots := #[`SizzLeanTests]
  globs := #[.andSubmodules `SizzLeanTests]

-- Microbenchmarks live in a third sibling lib, `SizzLeanBench`.
-- Built via `lake build SizzLeanBench`; run via `lake exe ssz_bench`
-- (the `just bench` recipe wraps the redirection to a TSV file).
-- Each scenario's measurement column lives in its own
-- `SizzLeanBench/Scenarios/<Name>.lean` file.
--
-- `precompileModules := true` is load-bearing for the bench: without
-- it, the scenario for-loops and the `runBench` driver run as
-- bytecode through Lean's interpreter even though `ssz_bench` is a
-- native binary, measuring the interpreter, not the library. With
-- it, every imported module is compiled to native code via `leanc`,
-- and the timings reflect compiled `sszUpdate` / `box.hashTreeRoot`
-- through compiled `Std.TreeMap` / compiled `Thunk` plumbing.
lean_lib SizzLeanBench where
  precompileModules := true

-- The bench driver. `SizzLeanBench/Main.lean` exposes `def main : IO Unit`
-- that prints the TSV header and invokes each bench file's `runAll`
-- in declaration order. Stdout is the bench output stream; stderr is
-- reserved for setup errors. `lake exe ssz_bench` always invokes the
-- compiled native binary (Lake's standard semantics); combined with
-- `precompileModules := true` on `SizzLeanBench` above, every module
-- the binary loads is also native code, not bytecode-interpreted.
--
-- `supportInterpreter := true` matches `LeanEthCS`'s
-- `eth_ssz_vector_runner`, needed when the exe root is a submodule
-- of a `precompileModules` library to avoid a Lake build-graph cycle
-- (the `:shared` and `:export` targets self-reference otherwise).
-- The runtime cost is a small unused interpreter dispatch table in
-- the binary; the bench still executes as compiled native code.
lean_exe ssz_bench where
  root := `SizzLeanBench.Main
  supportInterpreter := true

-- Ad-hoc profile driver. `SizzLeanBench/ProfileMain.lean` runs the
-- phase-by-phase profile of S10's cached path (overlay accumulation
-- vs setManyAt commit vs final Merkle hash). Kept separate from
-- `ssz_bench` because profiling runs are ad-hoc; including them in
-- the regular bench would double its wall-clock for no day-to-day
-- value. Same `supportInterpreter := true` rationale as `ssz_bench`.
lean_exe ssz_profile where
  root := `SizzLeanBench.ProfileMain
  supportInterpreter := true
