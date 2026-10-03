import LeanHazmatBlake2f.Ffi

/-!
# `LeanHazmatBlake2f`: library root

FFI binding for the **execution-layer BLAKE2f precompile primitive**
(EIP-152): the rounds-parametrized BLAKE2b `F` compression function of
RFC 7693, written in-repo (no vendored library) and exposed under the
`LeanHazmat.Blake2f` brand namespace. Part of the
[LeanHazmat](../docs/ARCHITECTURE.md) crypto family.

`import LeanHazmatBlake2f` brings the public surface into scope:

* `blake2fCompress`: `F(h, m, t0, t1, last, rounds)` → the updated
  64-byte chaining state.

See [`LeanHazmatBlake2f/Ffi.lean`](LeanHazmatBlake2f/Ffi.lean) for the
binding and its trust assumption, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's trust
boundary (no library, in-repo shim, EIP-152 validation vectors).

## Why no vendored library

EIP-152 needs raw `F` with arbitrary `rounds` and the final-block
flag; BLAKE2 libraries (libb2, OpenSSL) expose only a `blake2b` hash
API and never the raw compression. The function is ~60 lines of
RFC 7693, so the plan's BLAKE2f decision ("hand-rolled F-compression,
no libb2") applies: the shim is this package's own `csrc/` file, and
the EIP-152 vectors pin it completely.

## Trust boundary

The single empirical assumption, *that our ~60 lines implement RFC
7693's `F` correctly*, is validated by `LeanHazmatBlake2fTests` against
the official EIP-152 vectors. Known-Answer-Test gates live in a
separate `lean_lib` (`LeanHazmatBlake2fTests`); the default `lake
build` skips them and they fire via `lake build LeanHazmatBlake2fTests`.
-/
