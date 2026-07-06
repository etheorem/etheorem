-- Build-ordering import (not for any Lean symbol): this package's
-- precompiled `.so` links Bls's shared lib (`moreLinkArgs`'s
-- platform-specific `-l`) for the `blst_*` symbols c-kzg references.
-- Importing the Bls module makes the Bls package, and so its shared
-- lib, a build prerequisite of this module, ordering it before this
-- package's link step (otherwise a clean parallel build can race and the
-- KZG `.so` link fails with "unable to find" the missing lib).
import LeanHazmatBls

/-!
# `LeanHazmatKzg.Ffi`: Ethereum consensus KZG behind `@[extern]`

`@[extern] opaque` bindings to the C shim in `csrc/kzg_shim.c`, which
wraps ethereum/c-kzg-4844 for the consensus KZG / polynomial-commitment
surface:

* **EIP-4844** (Deneb): blob commitments, point/blob proofs, single and
  batch verification.
* **EIP-7594 / Fulu** (PeerDAS): extension-blob cells and their proofs,
  cell-proof batch verification, and erasure recovery.

c-kzg is built against `LeanHazmatBls`'s blst (the single blst owner;
hazmat-docs/ARCHITECTURE.md §4). The KZG **trusted setup**, the fixed
EIP-4844 ceremony output, is embedded into the archive and loaded once
at library load, so there is no runtime file lookup.

## Sizes & encodings

A *blob* is `FIELD_ELEMENTS_PER_BLOB = 4096` field elements ×32 bytes =
**131072** bytes. A *commitment* and a *proof* are each a 48-byte
compressed G1 point. A field element (`z`, `y`) is 32 bytes. A Fulu
*cell* is `FIELD_ELEMENTS_PER_CELL = 64` ×32 = **2048** bytes; an
extension blob has `CELLS_PER_EXT_BLOB = 128` cells.

## Conventions

* Byte arguments are `@&`-borrowed. Point/byte results are fresh
  `ByteArray`s; an **empty** `ByteArray` (or `#[]` array / a pair of
  these) is the error sentinel, signalling bad input length, an internal
  c-kzg failure, or the trusted setup failing to load. Check `.isEmpty`.
* Verification returns `Bool`; `false` is a legitimate "does not verify"
  or invalid input (a c-kzg `C_KZG_RET` error collapses to `false`).

## Trust boundary (ARCHITECTURE.md §10)

No pure-Lean reference exists for KZG; each binding is an opaque
`@[extern]` boundary. The empirical trust assumption, *that c-kzg-4844
(+ blst) implements EIP-4844 / EIP-7594 correctly*, is validated only
against the spec KAT in `LeanHazmatKzgTests`.
-/

set_option autoImplicit false

namespace LeanHazmat.Kzg

/-! ### Byte-length constants (consensus spec) -/

/-- Bytes in a serialized blob: 4096 field elements × 32. -/
def bytesPerBlob : Nat := 131072
/-- Bytes in a KZG commitment / proof (compressed G1 point). -/
def bytesPerCommitment : Nat := 48
/-- Bytes in a field element (`z`, `y`). -/
def bytesPerFieldElement : Nat := 32
/-- Bytes in a Fulu cell: 64 field elements × 32. -/
def bytesPerCell : Nat := 2048
/-- Cells in an extension blob (Fulu PeerDAS). -/
def cellsPerExtBlob : Nat := 128

/-! ### EIP-4844 -/

/-- `blob_to_kzg_commitment(blob)` → 48-byte commitment. Empty on error.

Runtime: `csrc/kzg_shim.c`'s `lean_hazmat_kzg_blob_to_commitment`. -/
@[extern "lean_hazmat_kzg_blob_to_commitment"]
opaque blobToKzgCommitment (blob : @& ByteArray) : ByteArray

/-- `compute_kzg_proof(blob, z)` → `(proof, y)`: a 48-byte proof and the
32-byte evaluation `y = p(z)`. `(empty, empty)` on error.

Runtime: `lean_hazmat_kzg_compute_proof`. -/
@[extern "lean_hazmat_kzg_compute_proof"]
opaque computeKzgProof (blob : @& ByteArray) (z : @& ByteArray) :
    ByteArray × ByteArray

/-- `compute_blob_kzg_proof(blob, commitment)` → 48-byte proof. Empty on
error.

Runtime: `lean_hazmat_kzg_compute_blob_proof`. -/
@[extern "lean_hazmat_kzg_compute_blob_proof"]
opaque computeBlobKzgProof (blob : @& ByteArray) (commitment : @& ByteArray) :
    ByteArray

/-- `verify_kzg_proof(commitment, z, y, proof)` → `Bool`: does the proof
attest `p(z) = y` for the committed polynomial?

Runtime: `lean_hazmat_kzg_verify_proof`. -/
@[extern "lean_hazmat_kzg_verify_proof"]
opaque verifyKzgProof
    (commitment : @& ByteArray) (z : @& ByteArray)
    (y : @& ByteArray) (proof : @& ByteArray) : Bool

/-- `verify_blob_kzg_proof(blob, commitment, proof)` → `Bool`.

Runtime: `lean_hazmat_kzg_verify_blob_proof`. -/
@[extern "lean_hazmat_kzg_verify_blob_proof"]
opaque verifyBlobKzgProof
    (blob : @& ByteArray) (commitment : @& ByteArray)
    (proof : @& ByteArray) : Bool

/-- `verify_blob_kzg_proof_batch(blobs, commitments, proofs)` → `Bool`.
The three arrays must share one length; verifies all blobs at once.

Runtime: `lean_hazmat_kzg_verify_blob_proof_batch`. -/
@[extern "lean_hazmat_kzg_verify_blob_proof_batch"]
opaque verifyBlobKzgProofBatch
    (blobs : @& Array ByteArray) (commitments : @& Array ByteArray)
    (proofs : @& Array ByteArray) : Bool

/-! ### EIP-7594 / Fulu PeerDAS -/

/-- `compute_cells_and_kzg_proofs(blob)` → `(cells, proofs)`, each an
array of `cellsPerExtBlob = 128` items (cells are 2048 bytes, proofs 48).
`(#[], #[])` on error.

Runtime: `lean_hazmat_kzg_compute_cells_and_proofs`. -/
@[extern "lean_hazmat_kzg_compute_cells_and_proofs"]
opaque computeCellsAndKzgProofs (blob : @& ByteArray) :
    Array ByteArray × Array ByteArray

/-- `verify_cell_kzg_proof_batch(commitments, cellIndices, cells, proofs)`
→ `Bool`. All four arrays share one length `num_cells`; `commitments[i]`
is the commitment for `cells[i]` (at extension-blob index
`cellIndices[i]`).

Runtime: `lean_hazmat_kzg_verify_cell_proof_batch`. -/
@[extern "lean_hazmat_kzg_verify_cell_proof_batch"]
opaque verifyCellKzgProofBatch
    (commitments : @& Array ByteArray) (cellIndices : @& Array UInt64)
    (cells : @& Array ByteArray) (proofs : @& Array ByteArray) : Bool

/-- `recover_cells_and_kzg_proofs(cellIndices, cells)` → `(cells, proofs)`:
from a ≥50% known subset (`cells[i]` at index `cellIndices[i]`), recover
all `cellsPerExtBlob = 128` cells and their proofs. `(#[], #[])` on error.

Runtime: `lean_hazmat_kzg_recover_cells_and_proofs`. -/
@[extern "lean_hazmat_kzg_recover_cells_and_proofs"]
opaque recoverCellsAndKzgProofs
    (cellIndices : @& Array UInt64) (cells : @& Array ByteArray) :
    Array ByteArray × Array ByteArray

end LeanHazmat.Kzg
