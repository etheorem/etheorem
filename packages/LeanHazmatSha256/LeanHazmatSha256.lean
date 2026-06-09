import LeanHazmatSha256.Ffi

/-!
# `LeanHazmatSha256`: library root

The FFI counterpart to the pure-Lean `LeanSha256` reference: this
package links the system OpenSSL `libcrypto` and exposes NIST FIPS
180-4 SHA-256 as three `@[extern]` primitives under the `LeanHazmat.Sha256`
brand namespace. It is the one LeanHazmat family that needs **no**
vendoring, `libcrypto` is discovered via `pkg-config` at build time.

`import LeanHazmatSha256` brings the public surface into scope:

* `LeanHazmat.Sha256.sha256Hash`: single-input 32-byte digest.
* `LeanHazmat.Sha256.sha256Combine`: digest of two concatenated inputs (the
  inner SSZ Merkle step).
* `LeanHazmat.Sha256.sha256BatchCombine`: level-batched sibling combine.

See [`LeanHazmatSha256/Ffi.lean`](LeanHazmatSha256/Ffi.lean) for the
bindings and their trust assumptions, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for this family's
trust boundary. The cross-family view is in
[`../../hazmat-docs/ARCHITECTURE.md`](../../hazmat-docs/ARCHITECTURE.md).

## What lives elsewhere

This package holds *only* the raw FFI primitives. The abstract
`Hasher` typeclass, the `Sha256` instance tag, and the FFI ≡
pure-Lean equivalence axioms (`sha256Hash_eq_spec`,
`sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec`) live in
`SizzLean`, which is the only layer that imports both this package
and the pure-Lean spec `LeanSha256` (ARCHITECTURE.md §9). Keeping the
bindings spec-free is what makes this package independently
mirror-publishable.

Byte-level Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatSha256Tests`); the default `lake build` skips them and
they fire via `lake build LeanHazmatSha256Tests`.
-/
