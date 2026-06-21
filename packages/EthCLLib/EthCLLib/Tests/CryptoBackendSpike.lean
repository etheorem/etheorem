import EthCLLib.Spec.Crypto

/-!
# `EthCLLib.Tests.CryptoBackendSpike`: the `[CryptoBackend]` seam self-test

Graduates the Phase 0.3 spike into `EthCLLib` (`PLAN.md` §0.3). It confirms the
seam binds cleanly over the committed crypto FFI for both arms, the signature
primitive and the commitment primitive, by calling through `[CryptoBackend]`,
never the FFI directly.

**Marshalling at the seam** (recorded in `IMPLEMENTATION_NOTES.md`): every buffer
is a raw `ByteArray` of the wire size, sk 32, pubkey 48, signature 96, blob
131072, commitment 48, cell 2048, proof 48 bytes, cell index `UInt64`. BLS
`verify` takes (pubkey, message, signature) and returns `Bool`; the KZG batch
takes four equal-length arrays and returns `Bool`. The spec converts its
SSZ-typed byte vectors to `ByteArray` before calling, so the seam stays
SSZ-free.

The `bls_setting: 2` verify-off mode is exercised too: `CryptoBackend.verifyOff`
returns `true` for any BLS input, so a dummy-signature invalid vector is not
falsely rejected.
-/

open EthCLLib.Spec
open LeanHazmat

namespace EthCLLib.Tests.CryptoBackendSpike

/-- A toy step that verifies through the seam, never the FFI directly. -/
def toyVerify [CryptoBackend] (pubkey message signature : ByteArray) : Bool :=
  CryptoBackend.verify pubkey message signature

/-- A toy step that runs the KZG cell-proof batch through the seam. -/
def toyKzg [CryptoBackend] (commitments : Array ByteArray) (cellIndices : Array UInt64)
    (cells proofs : Array ByteArray) : Bool :=
  CryptoBackend.kzgVerifyCellProofBatch commitments cellIndices cells proofs

/-! ## BLS: a sign → verify round-trip through the seam

`sk = 1` is a valid 32-byte big-endian scalar; `skToPk` and `sign` produce a
matching pubkey / signature pair the seam's `verify` must accept. -/

private def sk : ByteArray := ⟨(Array.replicate 31 (0 : UInt8)).push 1⟩
private def message : ByteArray := "EthCLLib crypto-backend spike".toUTF8
private def pubkey : ByteArray := Bls.skToPk sk
private def signature : ByteArray := Bls.sign sk message

/-- The seam's `verify` accepts a genuine signature (FFI backend). -/
example : @toyVerify CryptoBackend.ffi pubkey message signature = true := by
  native_decide

/-- The verify-off backend accepts anything (the `bls_setting: 2` mode). -/
example : @toyVerify CryptoBackend.verifyOff pubkey message ByteArray.empty = true := by
  native_decide

/-! ## KZG: a compute-cells → verify-batch round-trip through the seam

The all-zero blob's cells and proofs verify against its commitment, replicated
across all 128 extension-blob cell indices. This is the batch array shape the
seam carries, not a single-cell call. -/

private def zeroBlob : ByteArray := ⟨Array.replicate Kzg.bytesPerBlob (0 : UInt8)⟩
private def commitment : ByteArray := Kzg.blobToKzgCommitment zeroBlob
private def cellsAndProofs : Array ByteArray × Array ByteArray :=
  Kzg.computeCellsAndKzgProofs zeroBlob
private def commitments : Array ByteArray := Array.replicate Kzg.cellsPerExtBlob commitment
private def cellIndices : Array UInt64 :=
  (Array.range Kzg.cellsPerExtBlob).map (·.toUInt64)

/-- The seam's KZG batch verifies the zero blob's cells (FFI backend). -/
example :
    @toyKzg CryptoBackend.ffi commitments cellIndices cellsAndProofs.1 cellsAndProofs.2 = true := by
  native_decide

end EthCLLib.Tests.CryptoBackendSpike
