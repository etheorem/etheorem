import LeanHazmatKzg

/-!
# `LeanHazmatKzgTests.Vectors`: KZG Known-Answer / round-trip tests

Self-contained validation of the c-kzg-4844 FFI surface. KZG has no
pure-Lean reference, so these round-trips are the family's entire
trust-validation surface (hazmat-docs/ARCHITECTURE.md §10). They also
exercise the embedded trusted setup loading (no runtime file lookup).

Two layers:

* **EIP-4844**: commit → prove → verify on a blob, the point-evaluation
  proof (`computeKzgProof` / `verifyKzgProof`), and the batch verifier,
  each with a negative (corrupted) case.
* **EIP-7594 / Fulu**: `computeCellsAndKzgProofs` → `verifyCellKzgProofBatch`
  over all 128 cells, and an erasure-recovery round-trip
  (`recoverCellsAndKzgProofs` from a 64-cell subset reproduces all 128).

Checks are grouped into a few aggregate `Bool`s so each `native_decide`
runs the (relatively heavy) c-kzg computations once per group rather than
once per assertion.

## Lean idioms used here

* `native_decide` runs the compiled c-kzg FFI at proof-check time (one
  `Lean.ofReduceBool` axiom per group), the acceptable KAT regime.
* The blob is a 131072-byte all-zero `ByteArray`, a valid blob (all
  field elements zero); a self-contained input needing no vendored data.
-/

set_option autoImplicit false
-- The Fulu cell groups build 128×2048-byte arrays and run MSMs over 4096
-- points under native_decide; give the elaborator headroom.
set_option maxHeartbeats 1000000

namespace LeanHazmatKzgTests.Vectors

open LeanHazmat.Kzg

/-! ### Inputs -/

/-- A valid all-zero blob (every field element is 0). -/
private def zeroBlob : ByteArray := ByteArray.mk (Array.replicate bytesPerBlob 0)

/-- A 32-byte big-endian field element with value 2 (a valid evaluation
point `z`, well below the BLS modulus). -/
private def zPoint : ByteArray := ByteArray.mk ((Array.replicate 31 0).push 2)

/-- Flip one byte so a valid commitment/proof/cell becomes invalid.
`Array.modify` is a no-op if the index is out of range. -/
private def corrupt (b : ByteArray) : ByteArray :=
  ByteArray.mk (b.data.modify 5 (· ^^^ 0xff))

/-! ### EIP-4844 -/

/-- commit → blob-proof → verify (+ corrupted-proof and corrupted-blob
negatives), plus the point-evaluation proof and the single-element batch
verifier. One `native_decide` runs the whole chain. -/
private def eip4844Checks : Bool := Id.run do
  let commitment := blobToKzgCommitment zeroBlob
  let blobProof  := computeBlobKzgProof zeroBlob commitment
  -- point-evaluation proof at z: (proof, y) with y = p(z)
  let (ptProof, y) := computeKzgProof zeroBlob zPoint
  let checks : List Bool := [
    -- well-formed outputs
    commitment.size == bytesPerCommitment,
    blobProof.size  == bytesPerProof,
    ptProof.size    == bytesPerProof,
    y.size          == bytesPerFieldElement,
    -- blob proof verifies, and the single-element batch agrees
    verifyBlobKzgProof zeroBlob commitment blobProof,
    verifyBlobKzgProofBatch #[zeroBlob] #[commitment] #[blobProof],
    -- point-evaluation proof verifies
    verifyKzgProof commitment zPoint y ptProof,
    -- negatives
    !verifyBlobKzgProof zeroBlob commitment (corrupt blobProof),
    !verifyBlobKzgProof zeroBlob (corrupt commitment) blobProof,
    !verifyKzgProof commitment zPoint (corrupt y) ptProof ]
  return checks.all (· == true)
where bytesPerProof : Nat := bytesPerCommitment  -- both 48-byte G1 points

example : eip4844Checks = true := by native_decide

/-! ### EIP-7594 / Fulu cells -/

/-- `computeCellsAndKzgProofs` yields 128 cells + 128 proofs, and
`verifyCellKzgProofBatch` accepts all of them under the blob's single
commitment. A tampered cell is rejected. -/
private def fuluCellChecks : Bool := Id.run do
  let commitment := blobToKzgCommitment zeroBlob
  let (cells, proofs) := computeCellsAndKzgProofs zeroBlob
  let indices : Array UInt64 := (Array.range cellsPerExtBlob).map (·.toUInt64)
  let commitments : Array ByteArray := Array.replicate cellsPerExtBlob commitment
  let checks : List Bool := [
    cells.size  == cellsPerExtBlob,
    proofs.size == cellsPerExtBlob,
    (cells.all (·.size == bytesPerCell)),
    (proofs.all (·.size == bytesPerCommitment)),
    verifyCellKzgProofBatch commitments indices cells proofs,
    -- tamper with cell 0 → batch must reject
    !verifyCellKzgProofBatch commitments indices
        (cells.modify 0 corrupt) proofs ]
  return checks.all (· == true)

example : fuluCellChecks = true := by native_decide

/-- Erasure recovery: from the first 64 of 128 cells (exactly 50%),
`recoverCellsAndKzgProofs` reproduces all 128 original cells. -/
private def fuluRecoverChecks : Bool := Id.run do
  let (cells, _proofs) := computeCellsAndKzgProofs zeroBlob
  let half := cellsPerExtBlob / 2
  let knownIdx : Array UInt64 := (Array.range half).map (·.toUInt64)
  let knownCells : Array ByteArray := (Array.range half).map (fun i => cells[i]!)
  let (recovered, recProofs) := recoverCellsAndKzgProofs knownIdx knownCells
  let checks : List Bool := [
    recovered.size  == cellsPerExtBlob,
    recProofs.size  == cellsPerExtBlob,
    -- recovered cells match the originals
    recovered == cells ]
  return checks.all (· == true)

example : fuluRecoverChecks = true := by native_decide

end LeanHazmatKzgTests.Vectors
