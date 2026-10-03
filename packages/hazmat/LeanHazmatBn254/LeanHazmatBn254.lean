import LeanHazmatBn254.Ffi

/-!
# `LeanHazmatBn254`: library root

FFI bindings for the **alt_bn128 (BN254) curve**, the execution
layer's pairing-friendly group: the EIP-196 add/mul precompiles, the
EIP-197 / EIP-1108 G2 operations and pairing check. Wrapped behind
`@[extern]` under the `LeanHazmat.Bn254` brand namespace. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) crypto family.

`import LeanHazmatBn254` brings the public surface into scope:

* `g1Add` / `g1Mul`: EIP-196 primitives (64-byte G1 points).
* `g2Add` / `g2Mul`: EIP-197 G2 primitives (128-byte points,
  imaginary-first encoding).
* `millerLoopVec` / `finalExp` / `gtIsOne`: the pairing pieces; the
  EIP-197 check is `gtIsOne (finalExp (millerLoopVec pairs))`.

See [`LeanHazmatBn254/Ffi.lean`](LeanHazmatBn254/Ffi.lean) for the
bindings, encodings, and trust assumptions, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's
trust boundary (library, version pin, validation vectors).

## The one C++ family

mcl is C++, so this package is the LeanHazmat family with a C++
compiler in the build: the shim is `.cpp` with `extern "C"` entry
points, and mcl's whole API comes out of one translation unit
(`src/fp.cpp` at the 256-bit instantiation, no GMP). The C++ *runtime*
is compiled out (`-fno-exceptions`, `-fno-rtti`, the CYBOZU /
`MCL_DONT_USE_*` defines; see `csrc/bn254_shim.cpp`), so the compiled
code references only libc and libgcc. The archive ships like every
other family, with no consumer flags.

## Vendoring

herumi/mcl is **vendored**: `just hazmat-bn254-vendor` shallow-clones
the pinned tag (v4.10) into a gitignored `vendor/mcl/` before
`lake build` (packages/hazmat/docs/ARCHITECTURE.md §6).

## Trust boundary

No pure-Lean reference exists; each binding is an opaque `@[extern]`
boundary validated only against the published EIP-196/197 vectors
(`LeanHazmatBn254Tests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatBn254Tests`); the default `lake build` skips them and they
fire via `lake build LeanHazmatBn254Tests`.
-/
