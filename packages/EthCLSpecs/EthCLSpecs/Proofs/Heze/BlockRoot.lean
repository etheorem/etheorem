import EthCLSpecs.Heze.Block
import SizzLean.Proofs.Merkle.HashTreeRoot
import SizzLean.Proofs.Merkle.Naive
import SizzLean.Proofs.Merkle.Chunk

/-!
# `EthCLSpecs.Proofs.Heze.BlockRoot`: a block root is the root of its header

A `BeaconBlock` and its `BeaconBlockHeader` share the first four fields. The block holds
the body, and the header holds the body root. SSZ merkleizes a container over its field
roots, so the two roots agree when the last field roots agree
(`htr_eq_htr_headerOf`).

The last field root of the header is the root of a 32-byte vector. That root is the 32
bytes themselves: one chunk, and no hashing (`hashTreeRoot_bytes32`). The body root goes
into that vector through `bytesToRoot`, which keeps every byte of a 32-byte buffer
(`mk_bytesToRoot`). So the proof needs the body root to have 32 bytes.

The body is a container with more than one field, so its root is a Merkle root of
positive depth, and the top of that tree is a `combine` (`merkleize_size_of_pos`). The
`Hasher` class states no output width. So the theorems take the combine-width law as a
hypothesis: every `combine` returns 32 bytes. A SHA-256 digest has 32 bytes.

`SlotsIncrease.lean` uses the result. `processBlockHeader` checks a block against the
header in the state, and a block names its parent by the parent's block root.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open SizzLean (Hasher)
open SizzLean.Spec (SSZType merkleize chunkify padToChunk chunkDepth bytesToChunkCount
  BYTES_PER_CHUNK)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset BeaconBlock BeaconBlockHeader)

/-- The serialization of a byte list lays the bytes out in order. -/
theorem serializeFixedElems_uint8 (l : List UInt8) :
    SSZType.serializeFixedElems (.uintN 8) l = ⟨l.toArray⟩ := by
  induction l with
  | nil =>
    unfold SSZType.serializeFixedElems
    apply ByteArray.ext
    simp
  | cons x xs ih =>
    unfold SSZType.serializeFixedElems
    rw [ih]
    apply ByteArray.ext
    simp [SSZType.serialize]

/-- A 32-byte buffer is one chunk. -/
theorem chunkify_of_size_32 (b : ByteArray) (h : b.size = 32) : chunkify b = [b] := by
  unfold chunkify
  simp only [h, BYTES_PER_CHUNK]
  simp only [Nat.reduceAdd, chunkify.go, Nat.zero_mul, Nat.zero_add]
  unfold padToChunk
  have hx : b.extract 0 32 = b := by
    apply ByteArray.ext
    simp [h]
  simp [hx, h, BYTES_PER_CHUNK]

/-- The root of a 32-byte vector is its bytes: one chunk, and no hashing. -/
theorem hashTreeRoot_bytes32 (H : Type) [Hasher H] (v : Vector UInt8 32) :
    SSZType.hashTreeRoot H (.vector (.uintN 8) 32) v = ⟨v.toArray⟩ := by
  have hser : SSZType.serialize (.vector (.uintN 8) 32) v = ⟨v.toArray⟩ := by
    unfold SSZType.serialize
    rw [if_pos (show (SSZType.uintN 8).isFixedSize = true from rfl),
      serializeFixedElems_uint8]
    apply ByteArray.ext
    simp [Vector.toList]
  have hsz : (ByteArray.mk v.toArray).size = 32 := by
    show v.toArray.size = 32
    simp
  -- `v` is a byte vector, and the vector arm reads it as a vector of `uintN 8` values.
  rw [SizzLean.Proofs.Merkle.hashTreeRoot_vectorFixed H (.uintN 8) 32 rfl
      (v : Vector (SSZType.interp (.uintN 8)) 32), hser, chunkify_of_size_32 _ hsz, hsz]
  exact SizzLean.Proofs.Merkle.merkleize_single H _

section Width
variable (H : Type) [Hasher H] (hw : ∀ a b : ByteArray, (Hasher.combine (H := H) a b).size = 32)

include hw in
/-- Under the combine-width law, a naive root above the leaves has 32 bytes: its top is a
`combine`. -/
theorem naiveRootAt_succ_size (cs : List ByteArray) (lvl d : Nat) :
    (SizzLean.Proofs.naiveRootAt H cs lvl (d + 1)).size = 32 := by
  cases cs with
  | nil =>
    simp only [SizzLean.Proofs.naiveRootAt]
    exact hw _ _
  | cons c cs =>
    simp only [SizzLean.Proofs.naiveRootAt]
    exact hw _ _

include hw in
/-- Under the combine-width law, a Merkle root of positive depth has 32 bytes. -/
theorem merkleize_size_of_pos (cs : List ByteArray) (d : Nat) (hd : 0 < d)
    (hlen : cs.length ≤ 2 ^ d) : (merkleize H cs d).size = 32 := by
  rw [SizzLean.Proofs.merkleize_eq_naiveRoot H cs d hlen]
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  exact naiveRootAt_succ_size H hw cs 0 d'

include hw in
/-- Under the combine-width law, the root of a container with at least two fields has 32
bytes. -/
theorem hashTreeRoot_container_size (fs : List SSZType) (vs : SSZType.interpFields fs)
    (hfs : 2 ≤ fs.length) : (SSZType.hashTreeRoot H (.container fs) vs).size = 32 := by
  rw [SizzLean.Proofs.Merkle.hashTreeRoot_container]
  have hlen : (SSZType.hashTreeRootFields H fs vs).length = fs.length := by
    rw [← SizzLean.Proofs.Merkle.hashTreeRootFields_eq_map]
    simp
  have hpow := SizzLean.Proofs.Merkle.le_two_pow_chunkDepth fs.length
  apply merkleize_size_of_pos H hw
  · by_cases h0 : chunkDepth fs.length = 0
    · rw [h0] at hpow
      omega
    · omega
  · rw [hlen]
    exact hpow

end Width

/-- The root of a byte vector, through its `SSZRepr`, is its bytes. -/
theorem ssz_hashTreeRoot_bytes32 (H : Type) [Hasher H] (v : Vector UInt8 32) :
    SizzLean.SSZ.hashTreeRoot H v = ⟨v.toArray⟩ := by
  simp only [SizzLean.SSZ.hashTreeRoot, SizzLean.Spec.hashTreeRoot]
  dsimp only [SizzLean.SSZRepr.shape, SizzLean.SSZRepr.toRepr]
  rw [Vector.map_id]
  exact hashTreeRoot_bytes32 H v

/-- `bytesToRoot` keeps every byte of a 32-byte buffer. -/
theorem mk_bytesToRoot (r : ByteArray) (h : r.size = 32) :
    (⟨(bytesToRoot r).toArray⟩ : ByteArray) = r := by
  apply ByteArray.ext
  apply Array.ext
  · simp [bytesToRoot, bytesToVec, h]
  · intro i h1 h2
    simp only [bytesToRoot, bytesToVec, Vector.toArray_ofFn, Array.getElem_ofFn,
      ByteArray.get!]
    exact getElem!_pos r.data i (by omega)

section
variable [Preset] [HasherTag]

/-- The header of a block: the same four leading fields, and the root of the body. -/
def headerOf (b : BeaconBlock) : BeaconBlockHeader :=
  ⟨b.slot, b.proposerIndex, b.parentRoot, b.stateRoot, htr b.body⟩

/-- The root of a block is the Merkle root of its five field roots. -/
theorem blockRoot_fields (b : BeaconBlock) :
    SizzLean.SSZ.hashTreeRoot HasherTag.H b
      = merkleize HasherTag.H
          [SizzLean.SSZ.hashTreeRoot HasherTag.H b.slot,
            SizzLean.SSZ.hashTreeRoot HasherTag.H b.proposerIndex,
            SizzLean.SSZ.hashTreeRoot HasherTag.H b.parentRoot,
            SizzLean.SSZ.hashTreeRoot HasherTag.H b.stateRoot,
            SizzLean.SSZ.hashTreeRoot HasherTag.H b.body] (chunkDepth 5) := by
  simp only [SizzLean.SSZ.hashTreeRoot, SizzLean.Spec.hashTreeRoot]
  dsimp only [SizzLean.SSZRepr.shape, SizzLean.SSZRepr.toRepr]
  rw [SizzLean.Proofs.Merkle.hashTreeRoot_container]
  simp only [SizzLean.Proofs.Merkle.hashTreeRootFields_cons,
    SizzLean.Proofs.Merkle.hashTreeRootFields_nil]
  rfl

/-- The root of a header is the Merkle root of its five field roots. -/
theorem headerRoot_fields (h : BeaconBlockHeader) :
    SizzLean.SSZ.hashTreeRoot HasherTag.H h
      = merkleize HasherTag.H
          [SizzLean.SSZ.hashTreeRoot HasherTag.H h.slot,
            SizzLean.SSZ.hashTreeRoot HasherTag.H h.proposerIndex,
            SizzLean.SSZ.hashTreeRoot HasherTag.H h.parentRoot,
            SizzLean.SSZ.hashTreeRoot HasherTag.H h.stateRoot,
            SizzLean.SSZ.hashTreeRoot HasherTag.H h.bodyRoot] (chunkDepth 5) := by
  simp only [SizzLean.SSZ.hashTreeRoot, SizzLean.Spec.hashTreeRoot]
  dsimp only [SizzLean.SSZRepr.shape, SizzLean.SSZRepr.toRepr]
  rw [SizzLean.Proofs.Merkle.hashTreeRoot_container]
  simp only [SizzLean.Proofs.Merkle.hashTreeRootFields_cons,
    SizzLean.Proofs.Merkle.hashTreeRootFields_nil]
  rfl

variable (hw : ∀ a b : ByteArray, (Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- Under the combine-width law, the root of a block body has 32 bytes. -/
theorem bodyRoot_size (body : EthCLSpecs.Heze.BeaconBlockBody) :
    (SizzLean.SSZ.hashTreeRoot HasherTag.H body).size = 32 := by
  simp only [SizzLean.SSZ.hashTreeRoot, SizzLean.Spec.hashTreeRoot]
  dsimp only [SizzLean.SSZRepr.shape, SizzLean.SSZRepr.toRepr]
  exact hashTreeRoot_container_size _ hw _ _ (by simp)

include hw in
/-- A block root is the root of its header (`headerOf`), under the combine-width law. The
two containers differ only in the last field. The block holds the body, and the header
holds the body root. The root of a 32-byte vector is its bytes, and the body root has 32
bytes, so the two last field roots agree. -/
theorem htr_eq_htr_headerOf (b : BeaconBlock) : htr b = htr (headerOf b) := by
  unfold htr
  rw [blockRoot_fields, headerRoot_fields]
  have hbody : SizzLean.SSZ.hashTreeRoot HasherTag.H (headerOf b).bodyRoot
      = SizzLean.SSZ.hashTreeRoot HasherTag.H b.body := by
    rw [ssz_hashTreeRoot_bytes32]
    exact mk_bytesToRoot _ (bodyRoot_size hw b.body)
  rw [hbody]
  rfl

end

end EthCLSpecs.Proofs.Heze
