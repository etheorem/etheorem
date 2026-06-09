import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Fulu.Primitives
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Fulu.DataColumn`: Fulu data-column sidecar containers

Fulu's PeerDAS introduces per-column blob distribution. Each
`DataColumnSidecar` carries one column's worth of cells + KZG
witnesses, plus the inclusion proof linking it to the block header.

* `DataColumnSidecar`: preset-variant via
  `MAX_BLOB_COMMITMENTS_PER_BLOCK` (the same preset-variant cap that
  appears in Deneb's `BeaconBlockBody.blob_kzg_commitments`).
* `MatrixEntry`: preset-invariant.
* `DataColumnsByRootIdentifier`: preset-invariant cap `NUMBER_OF_COLUMNS = 128`.

## Constants

* `NUMBER_OF_COLUMNS = 128` (preset-invariant)
* `KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH = 4` (preset-invariant at v1.5.0)
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Fulu

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Phase0 (SignedBeaconBlockHeader)
open LeanEthCS.Macros

ssz_struct_for_presets DataColumnSidecar in LeanEthCS.Forks.Fulu
    for [minimal, mainnet] where
  index                           : ColumnIndex,
  column                          : SSZList Cell @@MAX_BLOB_COMMITMENTS_PER_BLOCK,
  kzgCommitments                  : SSZList KZGCommitment @@MAX_BLOB_COMMITMENTS_PER_BLOCK,
  kzgProofs                       : SSZList KZGProof @@MAX_BLOB_COMMITMENTS_PER_BLOCK,
  signedBlockHeader               : SignedBeaconBlockHeader,
  kzgCommitmentsInclusionProof    : Vector Bytes32 4

/-- `MatrixEntry`: one (cell, kzg_proof, column, row) record. -/
structure MatrixEntry where
  cell        : Cell
  kzgProof    : KZGProof
  columnIndex : ColumnIndex
  rowIndex    : RowIndex
  deriving SSZRepr

/-- `DataColumnsByRootIdentifier`: `(block_root, [column_indices])`. -/
structure DataColumnsByRootIdentifier where
  blockRoot : Root
  columns   : SSZList ColumnIndex 128
  deriving SSZRepr

end LeanEthCS.Forks.Fulu
