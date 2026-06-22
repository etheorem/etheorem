-- LeanPoseidon subpackage: Lake configuration.
--
-- Uses `lakefile.lean` rather than `lakefile.toml` because the
-- conformance oracle (Phase 2) links a Rust `staticlib` produced by
-- `cargo`, which needs a procedural build target (`target` shelling
-- `cargo build` + an `extern_lib` adopting the archive) that TOML
-- cannot express. This mirrors `SizzLean`'s procedural lakefile (its
-- C SHA-256 shim); the difference is cargo *emits* the archive, so we
-- adopt it with `extern_lib` rather than `buildStaticLib`-ing our own
-- objects. See `docs/ARCHITECTURE.md` §8 / §11.
--
-- The shipped core (`lean_lib LeanPoseidon`) and the equivalence
-- proofs (`LeanPoseidonProofs`, a sibling package) need *no* Rust:
-- `lake build LeanPoseidon` is pure Lean. The Rust toolchain is
-- confined to the `LeanPoseidonTests` lib / `poseidon_fuzz` exe added
-- in Phase 2.

import Lake
open Lake DSL System

package LeanPoseidon where
  -- SPDX identifier; the LICENSE file lives at the umbrella root
  -- (this package is not subtree-mirror-published, so it has no local
  -- copy, see ARCHITECTURE.md §11).
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  -- Match the monorepo's sibling libraries (`LeanSha256`, `SizzLean`,
  -- `EthCLSpecs`): expose the host's ISA to the Lean→C path so the
  -- compiled `native_decide` evaluation of the anchor KAT (a full
  -- Poseidon2 permutation over GMP-backed `Nat`) runs at native speed.
  -- Same `-march=native` caveat as elsewhere, bakes in the build
  -- host's ISA; switch to `-march=x86-64-v3` for a portable binary.
  moreLeancArgs := #["-march=native"]

@[default_target]
lean_lib LeanPoseidon where
  -- NOT precompiled, deliberately. A precompiled lean_lib's *shared*
  -- facet links **every** `externLib` in its package (Lake
  -- `Library.lean`'s `recBuildShared`), which here would pull the Rust
  -- `extern_lib` (and thus a `cargo build`) into `lake build
  -- LeanPoseidon`. Leaving the core non-precompiled keeps it Rust-free:
  -- `lake build LeanPoseidon` produces only `.olean`s and fires the
  -- anchor-KAT `native_decide` gate (which compiles `permute` on its
  -- own, not via the package link). The oracle is linked *only* into
  -- the `poseidon_fuzz` executable below. There are no downstream
  -- consumers (standalone island), so precompilation would buy nothing.

-- Conformance gates, package-prefixed (the monorepo's namespace-
-- disambiguation convention) so they don't collide with `SizzLeanTests`
-- / `LeanSha256Tests` in the umbrella build. Non-precompiled: the
-- committed-KAT `native_decide` gates (`Kat.lean`) evaluate the pure-Lean
-- `permute`, so `lake build LeanPoseidonTests` needs no Rust. The Rust
-- `@[extern]` bindings (`Ffi.lean`) are only *linked* when the
-- `poseidon_fuzz` executable is built (below).
lean_lib LeanPoseidonTests where
  roots := #[`LeanPoseidonTests]
  globs := #[.andSubmodules `LeanPoseidonTests]

/-! ## Conformance oracle (Rust + a thin C ABI shim, test-only)

Two pieces, both linked **only** into the `poseidon_fuzz` exe (so
`lake build LeanPoseidon` / `LeanPoseidonTests` stay Rust-free):

1. The HorizenLabs `zkhash` crate, vendored under `rust-oracle/` and built
   by `cargo` into `libposeidon_oracle.a` (cargo *emits* the archive; the
   `extern_lib` *adopts* it, we do not `buildStaticLib` its objects).
2. A small C shim (`csrc/poseidon_shim.c`, the `SizzLean` pattern) that
   marshals Lean's `ByteArray` to/from the raw-pointer Rust entrypoint.
   The shim is needed because Lean's `ByteArray` accessors
   (`lean_alloc_sarray`, `lean_sarray_cptr`) are `static inline` in
   `lean.h`, not linkable symbols a pure-Rust `@[extern]` could call. The
   shim is declared **before** the oracle so the static link resolves the
   shim's reference to the Rust archive left-to-right.

See `docs/ARCHITECTURE.md` §8. -/

-- (1a) Compile the C ABI shim against `lean.h`.
target poseidonShim.o pkg : FilePath := do
  let src := pkg.dir / "csrc" / "poseidon_shim.c"
  let obj := pkg.buildDir / "csrc" / "poseidon_shim.o"
  let leanInclude ← getLeanIncludeDir
  buildO obj (← inputTextFile src) #["-fPIC", "-O3", "-I", leanInclude.toString]
    #[] "cc" getLeanTrace

-- (1b) Static lib holding the shim object. Declared first ⇒ linked first.
extern_lib libposeidon_shim pkg := do
  let shim ← poseidonShim.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "poseidon_shim") #[shim]

-- (2a) Build the Rust oracle archive via cargo. Tracing the shim source
-- triggers rebuilds; `cargo` tracks `Cargo.toml` / `Cargo.lock` / deps
-- incrementally on each invocation.
target poseidonOracle pkg : FilePath := do
  let oracleDir := pkg.dir / "rust-oracle"
  let archive := oracleDir / "target" / "release" / "libposeidon_oracle.a"
  let srcJob ← inputTextFile (oracleDir / "src" / "lib.rs")
  buildFileAfterDep archive srcJob fun _ => do
    proc {
      cmd := "cargo"
      args := #["build", "--release",
                "--manifest-path", (oracleDir / "Cargo.toml").toString]
    }

-- (2b) Adopt the cargo archive. (`_pkg` binder unused, the fetch needs
-- no package context.)
extern_lib libposeidon_oracle _pkg := poseidonOracle.fetch

/-! ## Differential test executable

Runs the pure-Lean `permute` and the Rust oracle on N seeded-random inputs
and asserts equality. `moreLinkArgs` supplies the Rust runtime's native
deps the static archive references (`-lpthread -ldl -lm`); the analogue of
`SizzLean`'s libcrypto link args. The unwinder Rust's panic machinery
needs (`_Unwind_*`) is already satisfied by the Lean toolchain's own
`-lunwind` on the link line, note we deliberately do **not** add
`-lgcc_s`, whose system linker script would pull an unfindable `-lgcc`. -/

lean_exe poseidon_fuzz where
  -- `FuzzMain` is a dedicated top-level root *outside* any lean_lib glob,
  -- so Lake compiles an object that emits the C `main` (a module that is
  -- also a library member would instead contribute its symbol-export
  -- object, which has none).
  root := `FuzzMain
  moreLinkArgs := #["-lpthread", "-ldl", "-lm"]
