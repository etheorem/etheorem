import LeanHazmatBls.Ffi

/-!
# `LeanHazmatBls`: library root

FFI bindings for **Ethereum consensus-layer BLS12-381 signatures**
(minimal-pubkey-size, ciphersuite
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`), wrapping
supranational/blst behind `@[extern]` under the `LeanHazmat.Bls` brand
namespace. Part of the [LeanHazmat](../../hazmat-docs/ARCHITECTURE.md)
crypto family.

`import LeanHazmatBls` brings the public surface into scope (all in
namespace `LeanHazmat.Bls`):

* `sign` / `verify`: single-key sign and verify.
* `skToPk`: derive a public key from a secret key.
* `aggregate` / `ethAggregatePubkeys`: signature and pubkey point sums.
* `aggregateVerify`: distinct-message pairing check.
* `fastAggregateVerify` / `ethFastAggregateVerify`: same-message
  aggregate verify (the latter with the consensus empty-list /
  infinity-signature special case).
* `keyValidate`: pubkey validity predicate.

See [`LeanHazmatBls/Ffi.lean`](LeanHazmatBls/Ffi.lean) for the bindings
and their trust assumptions, and [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
for this family's trust boundary (library, version pin, validation
vectors).

## Vendoring

blst is **vendored** (not a system package): `just hazmat-bls-vendor`
shallow-clones the pinned tag into a gitignored `vendor/blst/` before
`lake build` (hazmat-docs/ARCHITECTURE.md §6). `LeanHazmatBls` is the
single blst owner for the family, `LeanHazmatKzg` builds c-kzg against
*this* blst rather than vendoring its own.

## Trust boundary

Unlike SHA-256, BLS has no pure-Lean reference; each binding is an
opaque `@[extern]` boundary validated only against the official
consensus-spec BLS test vectors (`LeanHazmatBlsTests`).

Known-Answer-Test gates live in a separate `lean_lib`
(`LeanHazmatBlsTests`); the default `lake build` skips them and they
fire via `lake build LeanHazmatBlsTests`.
-/
