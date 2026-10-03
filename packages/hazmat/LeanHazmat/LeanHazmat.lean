import LeanHazmatConsensus
import LeanHazmatExecution

/-!
# `LeanHazmat`: every Ethereum-protocol crypto family in one import

The top umbrella over the LeanHazmat family packages
(packages/hazmat/docs/ARCHITECTURE.md §3.4). It declares no code of its own;
importing it brings the whole `LeanHazmat.*` surface into scope:

* **Consensus** (via `LeanHazmatConsensus`): `LeanHazmat.Sha256`,
  `LeanHazmat.Bls`, `LeanHazmat.Kzg`.
* **Execution** (via `LeanHazmatExecution`): `LeanHazmat.Keccak`,
  `LeanHazmat.Secp256k1`, `LeanHazmat.Bn254`, `LeanHazmat.Blake2f`,
  `LeanHazmat.Ripemd160`, `LeanHazmat.Modexp`, `LeanHazmat.P256`.

Consumers wanting a subset should require the sub-aggregator or the
single family package instead; this umbrella compiles and links every
family. The vendored families need their `just hazmat-*-vendor`
fetches before `lake build`.

## The import gate

The `example`s below pin one family per `require` above: remove a
`require` and the build fails here, instead of staying green with a
whole layer silently missing. The per-family pins live in the two
sub-aggregator roots.
-/

set_option autoImplicit false

-- One type-level pin per `require` above (definitional, never evaluated).
example : ByteArray → ByteArray → ByteArray := LeanHazmat.Bls.sign
example : ByteArray → ByteArray := LeanHazmat.Keccak.keccak256
