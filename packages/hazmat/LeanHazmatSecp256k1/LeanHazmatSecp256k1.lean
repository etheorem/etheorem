import LeanHazmatSecp256k1.Ffi

/-!
# `LeanHazmatSecp256k1`: library root

FFI bindings for **secp256k1 ECDSA**, the execution layer's signature
system: transaction sender recovery and the ecRecover precompile (0x01)
both recover the public key from a compact `(r, s)` signature. Wrapped
behind `@[extern]` under the `LeanHazmat.Secp256k1` brand namespace.
Part of the [LeanHazmat](../docs/ARCHITECTURE.md) crypto
family.

`import LeanHazmatSecp256k1` brings the public surface into scope:

* `ecdsaRecover`: `(msgHash, r, s, recId)` → the 64-byte uncompressed
  public key (`x ‖ y`, big-endian).
* `ecdsaVerify`: `(msgHash, r, s, pubkey)` → `Bool`.

See
[`LeanHazmatSecp256k1/Ffi.lean`](LeanHazmatSecp256k1/Ffi.lean) for the
bindings and their trust assumptions, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's trust
boundary (library, version pin, validation vectors).

## Why no address derivation here

The ecRecover precompile composes recovery with `keccak256` and a
truncation (`keccak256(pk)[12:32]`). Per the LeanHazmat "raw
primitives, not assembled precompiles" rule
(packages/hazmat/docs/ARCHITECTURE.md §4), this package exposes the raw
recovered key and does **not** depend on `LeanHazmatKeccak`; address
derivation lives with the caller.

## Vendoring

bitcoin-core libsecp256k1 is **vendored**: `just
hazmat-secp256k1-vendor` shallow-clones the pinned tag (v0.8.0) into a
gitignored `vendor/secp256k1/` before `lake build`
(packages/hazmat/docs/ARCHITECTURE.md §6). (The plan's "system lib if
available" branch is unrealized today: the shim always builds the
vendored tree, which keeps one pinned source of truth. A pkg-config
branch is a later refinement if a consumer wants it.)

## Trust boundary

No pure-Lean reference exists; each binding is an opaque `@[extern]`
boundary validated only against the published vectors
(`LeanHazmatSecp256k1Tests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatSecp256k1Tests`); the default `lake build` skips them and
they fire via `lake build LeanHazmatSecp256k1Tests`.
-/
