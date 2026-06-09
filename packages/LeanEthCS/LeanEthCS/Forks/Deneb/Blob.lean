import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Deneb.Blob`: Deneb blob-sidecar containers

* `BlobIdentifier`: `(block_root, blob_index)` pair used in
  request/response protocols. Preset-invariant.
* `BlobSidecar`: one blob's full witness: the blob itself, its KZG
  commitment + proof, the signed block header it belongs to, and the
  Merkle inclusion proof of the commitment in the block. The
  `kzg_commitment_inclusion_proof` depth is preset-sensitive at the
  v1.5.0 spec release (the proof depth derives from `BeaconBlockBody`'s
  generalized-index layout, which is fork-and-preset specific).

## Constants

* `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH`: 10 minimal / 17 mainnet
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Deneb

open SizzLean

open LeanEthCS
open LeanEthCS.Forks.Phase0 (SignedBeaconBlockHeader)
open LeanEthCS.Macros

/-- `BlobIdentifier`: `(block_root, blob_index)`. -/
structure BlobIdentifier where
  blockRoot : Root
  index     : BlobIndex
  deriving SSZRepr

ssz_struct_for_presets BlobSidecar in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  index                       : BlobIndex,
  blob                        : Blob,
  kzgCommitment               : KZGCommitment,
  kzgProof                    : KZGProof,
  signedBlockHeader           : SignedBeaconBlockHeader,
  kzgCommitmentInclusionProof : Vector Bytes32 @@KZG_COMMITMENT_INCLUSION_PROOF_DEPTH

end LeanEthCS.Forks.Deneb
