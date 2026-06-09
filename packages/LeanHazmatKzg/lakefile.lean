-- LeanHazmatKzg subpackage: Lake configuration.
--
-- Procedural `lakefile.lean` (not TOML) because it compiles vendored C
-- into an `extern_lib`. c-kzg-4844 is vendored, `just vendor-kzg`
-- shallow-clones the pinned tag (v2.1.7) into `vendor/c-kzg-4844/` (NOT
-- its `--recursive` blst), and copies the trusted setup into `data/`.
--
-- This is the one LeanHazmat family that `require`s another: it shares
-- LeanHazmatBls's single compiled **blst** archive rather than vendoring
-- a second copy (hazmat-docs/ARCHITECTURE.md §4). c-kzg v2.1.7 pins blst
-- exactly at v0.3.16, the LeanHazmatBls pin, so the headers and ABI
-- match. At compile time c-kzg needs blst's `bindings/` on the include
-- path; the `blst_*` symbols come from LeanHazmatBls's archive.
--
-- Build shape (verified): compile c-kzg's own single-TU amalgamation
-- `src/ckzg.c` (it `#include`s every other `.c`) plus the Lean shim, and
-- embed the trusted setup via `.incbin`. No `-D` flags for c-kzg itself.

import Lake
open Lake DSL System

/-- Absolute path to LeanHazmatBls's build lib directory (where Lake puts
`libleanhazmat_bls.{a,so}`), computed at lakefile-load time. The repo root
is found by walking up from the CWD (the repo root for an umbrella build,
or this package's dir for a standalone build) to the directory containing
`packages/LeanHazmatBls`. The artefacts need not exist yet at load time,
LeanHazmatBls builds first as a `require`d dependency. -/
unsafe def blsLibDir : String := Id.run <| unsafeBaseIO do
  let rel : FilePath := "packages" / "LeanHazmatBls" / ".lake" / "build" / "lib"
  let marker : FilePath := "packages" / "LeanHazmatBls"
  let cwd ← (IO.currentDir).toBaseIO
  let mut dir : FilePath := cwd.toOption.getD "."
  for _ in [0:8] do
    if (← (dir / marker).pathExists) then
      return (dir / rel).toString
    match dir.parent with
    | some p => dir := p
    | none   => break
  -- Fallback: relative to CWD (correct when building from the repo root).
  return rel.toString

package LeanHazmatKzg where
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  -- Make this package's *shared* lib depend on LeanHazmatBls's shared lib
  -- so the precompiled module `.so` resolves c-kzg's `blst_*` references
  -- at load: `-l:libleanhazmat_bls.so` adds a `DT_NEEDED`, `-L` finds it
  -- at link, and the `-rpath` finds it at `dlopen`. This mirrors exactly
  -- how LeanHazmatSha256's `.so` gains `NEEDED libcrypto.so.3`. blst lives
  -- in Bls's archive (not duplicated here), so the final exe link still
  -- sees one blst copy via normal `extern_lib` propagation, no
  -- duplicate symbols. (Monorepo path; a standalone Kzg mirror resolves
  -- Bls through its git `require`.)
  moreLinkArgs := Id.run do
    let d := unsafe blsLibDir
    #["-L" ++ d, "-l:libleanhazmat_bls.so", "-Wl,-rpath," ++ d]

-- Shares LeanHazmatBls's blst, the single blst owner for the family.
require LeanHazmatBls from "../LeanHazmatBls"

/-- blst's headers, vendored under the sibling LeanHazmatBls package.
Needed on the include path to *compile* c-kzg and the shim. (Monorepo
sibling layout; a standalone Kzg mirror would resolve this through its
git `require` of Bls.) -/
def blstBindings (pkg : Package) : FilePath :=
  pkg.dir / ".." / "LeanHazmatBls" / "vendor" / "blst" / "bindings"

/-- c-kzg's own source dir (its `#include`s are `src`-relative). -/
def ckzgSrc (pkg : Package) : FilePath :=
  pkg.dir / "vendor" / "c-kzg-4844" / "src"

-- c-kzg-4844 amalgamation. `src/ckzg.c` includes the whole library; do
-- NOT compile the individual `common/`/`eip*/`/`setup/` `.c` files (they
-- would duplicate symbols). Two include dirs: c-kzg's `src/` and blst's
-- `bindings/`. No `-D` required.
target ckzg.o pkg : FilePath := do
  let src := ckzgSrc pkg / "ckzg.c"
  unless (← src.pathExists) do
    error s!"c-kzg not vendored — run `just vendor-kzg` (expected {src})"
  let bindings := blstBindings pkg
  unless (← bindings.pathExists) do
    error s!"blst not vendored — run `just vendor-bls` (expected {bindings})"
  let obj := pkg.buildDir / "ckzg" / "ckzg.o"
  let flags := #["-O2", "-fPIC", "-I", (ckzgSrc pkg).toString,
                 "-I", bindings.toString]
  buildO obj (← inputTextFile src) flags #[] "cc" getLeanTrace

-- The Lean-facing KZG shim. Same include paths as c-kzg, plus the Lean
-- runtime headers for `lean/lean.h`.
target kzg_shim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "kzg_shim.c"
  let bindings := blstBindings pkg
  unless (← bindings.pathExists) do
    error s!"blst not vendored — run `just vendor-bls` (expected {bindings})"
  let obj := pkg.buildDir / "csrc" / "kzg_shim.o"
  let leanInclude ← getLeanIncludeDir
  let flags := #["-O2", "-fPIC", "-I", leanInclude.toString,
                 "-I", (ckzgSrc pkg).toString, "-I", bindings.toString]
  buildO obj (← inputTextFile src) flags #[] "cc" getLeanTrace

-- Embed the trusted setup. `.incbin` copies `data/trusted_setup.txt`'s
-- bytes into `.rodata` at assemble time; the path is supplied as an
-- absolute string via the `TRUSTED_SETUP_PATH` macro (the `.S` extension
-- runs the C preprocessor first). The setup is pinned/fixed, so the `.S`
-- input trace is a sufficient cache key in practice; a setup change comes
-- with a c-kzg pin bump (and `just vendor-kzg` re-copies the file).
target trusted_setup.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "trusted_setup_incbin.S"
  let data := pkg.dir / "data" / "trusted_setup.txt"
  unless (← data.pathExists) do
    error s!"trusted setup missing — run `just vendor-kzg` (expected {data})"
  let dataAbs ← IO.FS.realPath data
  let obj := pkg.buildDir / "csrc" / "trusted_setup.o"
  let flags := #[s!"-DTRUSTED_SETUP_PATH=\"{dataAbs}\""]
  buildO obj (← inputTextFile src) flags #[] "cc" getLeanTrace

-- This package's archive: the shim + c-kzg + the embedded setup. blst is
-- deliberately NOT included here, it propagates from LeanHazmatBls, so
-- the final exe link sees one blst copy. (The shared lib reaches blst via
-- `moreLinkArgs` linking Bls's `.so` instead; see `blsLibDir`.)
extern_lib libleanhazmat_kzg pkg := do
  let ckzgO  ← ckzg.o.fetch
  let shimO  ← kzg_shim.o.fetch
  let setupO ← trusted_setup.o.fetch
  let name := nameToStaticLib "leanhazmat_kzg"
  let staticJob ← buildStaticLib (pkg.staticLibDir / name) #[shimO, ckzgO, setupO]
  -- Order LeanHazmatBls's *shared* lib before this archive (and therefore
  -- before the `.so` derived from it). Our shared lib references it via
  -- `moreLinkArgs` (`-l:libleanhazmat_bls.so`), but that path is invisible
  -- to Lake's scheduler, so a clean parallel build can otherwise link this
  -- `.so` before Bls's `.so` exists ("unable to find -l:libleanhazmat_bls.so").
  -- `Job.zipWith` folds Bls's shared-lib build into this job's dependency
  -- trace (keeping this archive's path as the value), making the ordering
  -- explicit.
  match ← findExternLib? `libleanhazmat_bls with
  | some blsLib =>
      let blsShared ← blsLib.shared.fetch
      return staticJob.zipWith (fun p _ => p) blsShared
  | none => return staticJob

@[default_target]
lean_lib LeanHazmatKzg where
  -- Precompiled so `native_decide` (here and downstream) finds the KZG
  -- externs as loaded precompiled symbols. The module `.so` resolves
  -- `blst_*` at load via the `DT_NEEDED` + `-rpath` on Bls's shared lib
  -- that `moreLinkArgs` adds.
  precompileModules := true

-- KAT gate against the consensus-spec KZG vectors + self-contained
-- round-trips. Built explicitly via `lake build LeanHazmatKzgTests`.
lean_lib LeanHazmatKzgTests where
  roots := #[`LeanHazmatKzgTests]
  globs := #[.andSubmodules `LeanHazmatKzgTests]
