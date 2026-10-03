import LeanHazmatSha256
import LeanHazmatBls
import LeanHazmatKzg

/-!
# `LeanHazmatConsensus`: the consensus crypto layer in one import

The aggregator meta-package over the three consensus LeanHazmat
families (packages/hazmat/docs/ARCHITECTURE.md §3.4). It declares no code of
its own; importing it brings every consensus family's
`LeanHazmat.*` names into scope:

* `LeanHazmat.Sha256`, FFI SHA-256 (OpenSSL): `sha256Hash`,
  `sha256Combine`, `sha256BatchCombine`.
* `LeanHazmat.Bls`, BLS12-381 signatures (blst): `sign`, `verify`,
  `aggregate`, `aggregateVerify`, `fastAggregateVerify`,
  `ethFastAggregateVerify`, `keyValidate`, `skToPk`.
* `LeanHazmat.Kzg`, KZG commitments / proofs (c-kzg-4844): the six
  EIP-4844 functions and the three Fulu PeerDAS cell functions.

Families stay consumable alone (`import LeanHazmatBls`); this package
is the "all consensus crypto in one `require`" convenience.

For the execution-layer families, see `LeanHazmatExecution`; for
everything at once, the top-level `LeanHazmat` umbrella.

## The import gate

The `example`s at the bottom pin every family's `LeanHazmat.*` name:
drop an `import` above and the build fails here, instead of staying
green with a family silently missing from the surface.

The vendored families need their `just hazmat-*-vendor` fetches before
`lake build`, see each package's README.
-/

set_option autoImplicit false

-- One type-level pin per family (definitional, never evaluated).
example : ByteArray → ByteArray := LeanHazmat.Sha256.sha256Hash
example : ByteArray → ByteArray → ByteArray :=
  LeanHazmat.Sha256.sha256Combine
example : ByteArray → ByteArray → ByteArray := LeanHazmat.Bls.sign
example : ByteArray → ByteArray :=
  LeanHazmat.Kzg.blobToKzgCommitment
