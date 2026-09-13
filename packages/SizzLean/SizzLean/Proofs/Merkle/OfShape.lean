import SizzLean.Spec.HashTreeRoot
import SizzLean.Spec.BasicSupported
import SizzLean.Cache.MerkleTree.Build
import SizzLean.Proofs.Merkle.Build
import SizzLean.Proofs.Merkle.Chunk
import SizzLean.Proofs.SerializeSize
import SizzLean.Proofs.BitPack

/-!
# `SizzLean.Proofs.Merkle.OfShape`: the shape walker roots like the spec

`Node.ofShape` walks an SSZ schema and a value, assembling a `Node`
whose interior mirrors the shape. This file proves the byte-identity
contract the cache layer was built on, for every shape the codec
implements:

    (Node.ofShape H s x).root H = SSZType.hashTreeRoot H s x

together with the coherence half, the builder preserves
`Node.Coherent`. Both are gated by `SSZType.BasicSupported` and
proved as one mutual block over the predicate's derivation, in the
same shape the serialization proofs use: the two field-list members
descend on their own derivations, and the element-list agreements
live outside the block as standalone lemmas that take the
per-element root fact as a hypothesis, which the dispatcher arms
supply from their sub-derivations.

Why `BasicSupported` and not the broader `SSZType.Supported`: the
`listFixed` basic-element arm consumes
`size_serialize_eq_fixedByteSize` (`Proofs/SerializeSize.lean`),
which is itself gated by `BasicSupported`. `Supported` would grade
the same matrix cells and add the zero-width shapes, where both
sides agree; widening this block means widening the size lemma
first.

Lean idiom, annotated once: `Node.ofShape` and
`SSZType.hashTreeRoot` are compiled by well-founded recursion, so
they do not reduce definitionally; every arm unfolds them by their
equation lemmas (`simp only [Node.ofShape]`, and so on). The two
`if t.isBasicType` dispatches appear on both sides of each
collection arm, so the positive branches rewrite with `if_pos hb`
twice and the negative branches with `if_neg hb` twice.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec
open SizzLean.Cache.MerkleTree (Node zeroLeaf)

/-! ### Bookkeeping -/

/-- A basic shape is fixed-size: the two dispatch predicates agree
on the `uintN` and `bool` constructors, and disagree only where
`isBasicType` is false. -/
theorem isFixedSize_of_isBasicType (t : SSZType) (h : t.isBasicType = true) :
    t.isFixedSize = true := by
  cases t with
  | uintN n => simp [SSZType.isFixedSize]
  | bool => simp [SSZType.isFixedSize]
  | vector t n => simp [SSZType.isBasicType] at h
  | list t cap => simp [SSZType.isBasicType] at h
  | bitvector n => simp [SSZType.isBasicType] at h
  | bitlist cap => simp [SSZType.isBasicType] at h
  | container fs => simp [SSZType.isBasicType] at h

/-- The sub-tree list holds one tree per field. -/
theorem length_subtreesForFields (H : Type) [Hasher H] :
    ∀ (fs : List SSZType) (vs : SSZType.interpFields fs),
      (Node.subtreesForFields H fs vs).length = fs.length := by
  intro fs
  induction fs with
  | nil => intro _; rw [Node.subtreesForFields]; rfl
  | cons t ts ih =>
      intro vs
      rw [Node.subtreesForFields, List.length_cons, ih vs.2, List.length_cons]

/-- The accumulator form holds a sub-tree per element. -/
theorem length_subtreesForListComposite (H : Type) [Hasher H] (t : SSZType) :
    ∀ (xs : List t.interp) (acc : List Node),
      (Node.subtreesForListComposite H t xs acc).length = acc.length + xs.length := by
  intro xs
  induction xs with
  | nil => intro acc; rw [Node.subtreesForListComposite]; simp
  | cons x xs ih =>
      intro acc
      rw [Node.subtreesForListComposite, ih (Node.ofShape H t x :: acc),
        List.length_cons, List.length_cons]
      omega

/-- Per-element roots of the shape walker are the spec's element
merkleizations, with the accumulator reversed on both sides. The
per-element root fact is a hypothesis, so this stands outside the
dispatcher's mutual block. -/
theorem subtreesForListComposite_roots (H : Type) [Hasher H] (t : SSZType)
    (h_root : ∀ y : t.interp, (Node.ofShape H t y).root H = SSZType.hashTreeRoot H t y) :
    ∀ (xs : List t.interp) (acc : List Node),
      (Node.subtreesForListComposite H t xs acc).map (Node.root H)
        = SSZType.hashTreeRootListComposite H t xs (acc.map (Node.root H)) := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      rw [Node.subtreesForListComposite, SSZType.hashTreeRootListComposite,
        List.map_reverse]
  | cons x xs ih =>
      intro acc
      rw [Node.subtreesForListComposite,
        ih (Node.ofShape H t x :: acc), SSZType.hashTreeRootListComposite,
        List.map_cons, h_root x]

/-- Per-element sub-trees of the shape walker are coherent,
including the carried accumulator. Same hypothesis shape as
`subtreesForListComposite_roots`. -/
theorem subtreesForListComposite_coherent (H : Type) [Hasher H] (t : SSZType)
    (h_coh : ∀ y : t.interp, (Node.ofShape H t y).Coherent H) :
    ∀ (xs : List t.interp) (acc : List Node), (∀ m ∈ acc, m.Coherent H) →
      ∀ n ∈ Node.subtreesForListComposite H t xs acc, n.Coherent H := by
  intro xs
  induction xs with
  | nil =>
      intro acc hacc n hn
      rw [Node.subtreesForListComposite, List.mem_reverse] at hn
      exact hacc n hn
  | cons x xs ih =>
      intro acc hacc n hn
      rw [Node.subtreesForListComposite] at hn
      exact ih (Node.ofShape H t x :: acc)
        (fun m hm => by
          cases hm with
          | head => exact h_coh x
          | tail _ hm => exact hacc m hm) n hn

/-- The chunk count of the packed bit-list body stays under the
cap-derived chunk count's tree capacity. -/
theorem le_two_pow_chunkDepth_bitlist (a cap : Nat) (h : a ≤ cap) :
    bytesToChunkCount ((a + 7) / 8) ≤ 2 ^ chunkDepth (bitsToChunkCount cap) := by
  have hd : 8 * ((a + 7) / 8) ≤ a + 7 := by omega
  calc bytesToChunkCount ((a + 7) / 8)
      ≤ bitsToChunkCount cap := by
        show ((a + 7) / 8 + 31) / 32 ≤ (cap + 255) / 256
        have h1 : ((a + 7) / 8 + 31) / 32 ≤ ((cap + 255) / 8) / 32 :=
          Nat.div_le_div_right (by omega)
        have h2 : ((cap + 255) / 8) / 32 = (cap + 255) / 256 :=
          Nat.div_div_eq_div_mul (cap + 255) 8 32
        exact Nat.le_trans h1 (by rw [h2]; exact Nat.le_refl _)
    _ ≤ 2 ^ chunkDepth (bitsToChunkCount cap) := le_two_pow_chunkDepth _

/-! ### The dispatcher: root agreement and coherence -/

mutual

/-- The shape walker's structural root is the spec's merkleization,
for every shape the codec implements. -/
theorem ofShape_root (H : Type) [Hasher H] : ∀ {s : SSZType}, SSZType.BasicSupported s →
    ∀ x : s.interp, (Node.ofShape H s x).root H = SSZType.hashTreeRoot H s x
  | _, .uintN8, x => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root]
  | _, .uintN16, x => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root, SSZType.serialize,
        uint16LE]
  | _, .uintN32, x => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root, SSZType.serialize,
        uint32LE]
  | _, .uintN64, x => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root, SSZType.serialize,
        uint64LE]
  | _, .uintN128, x => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root]
  | _, .uintN256, x => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root]
  | _, .bool, b => by
      simp only [Node.ofShape, SSZType.hashTreeRoot, Node.root]
  | _, .bitvector (n := n) _, bv => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      rw [ofLeaves_root H
        (chunkify (SSZType.serialize (SSZType.bitvector n) bv))
        (chunkDepth (bytesToChunkCount ((n + 7) / 8)))
        (by rw [length_chunkify, size_serialize_bitvector]
            exact le_two_pow_chunkDepth _)]
  | _, .bitlist (cap := cap), bs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      rw [mixInLength_root H
        (Node.ofLeaves H
          (chunkify (SSZType.serialize (SSZType.bitvector bs.val.size)
            (BitVec.ofNat bs.val.size (bitsToNatLE bs.val.toList))))
          (chunkDepth (bitsToChunkCount cap))) bs.val.size
        (ofLeaves_coherent H _ _),
        ofLeaves_root H
          (chunkify (SSZType.serialize (SSZType.bitvector bs.val.size)
            (BitVec.ofNat bs.val.size (bitsToNatLE bs.val.toList))))
          (chunkDepth (bitsToChunkCount cap))
          (by rw [length_chunkify, size_serialize_bitvector]
              exact le_two_pow_chunkDepth_bitlist bs.val.size cap bs.property)]
  | _, .vectorFixed (t := t) (n := n) _ h_t _, v => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      by_cases hb : t.isBasicType = true
      · rw [if_pos hb,
          ofLeaves_root H (chunkify (SSZType.serialize (SSZType.vector t n) v))
            (chunkDepth (bytesToChunkCount
              (SSZType.serialize (SSZType.vector t n) v).size))
            (by rw [length_chunkify]; exact le_two_pow_chunkDepth _),
          if_pos hb]
      · rw [if_neg hb,
          ofSubtrees_root H (Node.subtreesForListComposite H t v.toList)
            (chunkDepth n) (by
            rw [length_subtreesForListComposite, List.length_nil, Nat.zero_add,
              Vector.length_toList]
            exact le_two_pow_chunkDepth n),
          subtreesForListComposite_roots H t
            (fun y => ofShape_root H h_t y) v.toList [],
          if_neg hb]
        rfl
  | _, .vectorVar (t := t) (n := n) _ h_t h_var, v => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      by_cases hb : t.isBasicType = true
      · have h_fixed := isFixedSize_of_isBasicType t hb
        rw [h_fixed] at h_var
        simp at h_var
      · rw [if_neg hb,
          ofSubtrees_root H (Node.subtreesForListComposite H t v.toList)
            (chunkDepth n) (by
            rw [length_subtreesForListComposite, List.length_nil, Nat.zero_add,
              Vector.length_toList]
            exact le_two_pow_chunkDepth n),
          subtreesForListComposite_roots H t
            (fun y => ofShape_root H h_t y) v.toList [],
          if_neg hb]
        rfl
  | _, .listFixed (t := t) (cap := cap) h_t h_t_fixed _, xs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      by_cases hb : t.isBasicType = true
      · have hbound : (chunkify (SSZType.serializeFixedElems t xs.val.toList)).length
            ≤ 2 ^ chunkDepth (bytesToChunkCount (cap * t.fixedByteSize)) := by
          rw [length_chunkify, serializeFixedElems_size_aux t t.fixedByteSize
            (fun y => size_serialize_eq_fixedByteSize h_t h_t_fixed y)]
          have hlen : xs.val.toList.length = xs.val.size := Array.length_toList
          have hcap : xs.val.size ≤ cap := xs.property
          have hmul : xs.val.toList.length * t.fixedByteSize
              ≤ cap * t.fixedByteSize :=
            Nat.mul_le_mul_right t.fixedByteSize (by rw [hlen]; exact hcap)
          calc bytesToChunkCount (xs.val.toList.length * t.fixedByteSize)
              ≤ bytesToChunkCount (cap * t.fixedByteSize) := by
                show (xs.val.toList.length * t.fixedByteSize + BYTES_PER_CHUNK - 1)
                  / BYTES_PER_CHUNK
                  ≤ (cap * t.fixedByteSize + BYTES_PER_CHUNK - 1)
                    / BYTES_PER_CHUNK
                exact Nat.div_le_div_right (Nat.add_le_add_right hmul
                  (BYTES_PER_CHUNK - 1))
            _ ≤ 2 ^ chunkDepth (bytesToChunkCount (cap * t.fixedByteSize)) :=
                le_two_pow_chunkDepth _
        rw [if_pos hb,
          mixInLength_root H
            (Node.ofLeaves H
              (chunkify (SSZType.serializeFixedElems t xs.val.toList))
              (chunkDepth (bytesToChunkCount (cap * t.fixedByteSize))))
            xs.val.size (ofLeaves_coherent H _ _),
          ofLeaves_root H
            (chunkify (SSZType.serializeFixedElems t xs.val.toList))
            (chunkDepth (bytesToChunkCount (cap * t.fixedByteSize))) hbound,
          if_pos hb]
      · rw [if_neg hb,
          mixInLength_root H
            (Node.ofSubtrees H (Node.subtreesForListComposite H t xs.val.toList)
              (chunkDepth cap)) xs.val.size
            (ofSubtrees_coherent H _ _ fun s hs =>
              subtreesForListComposite_coherent H t
                (fun y => ofShape_coherent H h_t y) xs.val.toList []
                (fun m hm => by cases hm) s hs),
          ofSubtrees_root H (Node.subtreesForListComposite H t xs.val.toList)
            (chunkDepth cap) (by
            rw [length_subtreesForListComposite, List.length_nil, Nat.zero_add,
              Array.length_toList]
            calc xs.val.size ≤ cap := xs.property
              _ ≤ 2 ^ chunkDepth cap := le_two_pow_chunkDepth cap),
          subtreesForListComposite_roots H t
            (fun y => ofShape_root H h_t y) xs.val.toList [],
          if_neg hb]
        rfl
  | _, .listVar (t := t) (cap := cap) h_t h_var, xs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      by_cases hb : t.isBasicType = true
      · have h_fixed := isFixedSize_of_isBasicType t hb
        rw [h_fixed] at h_var
        simp at h_var
      · rw [if_neg hb,
          mixInLength_root H
            (Node.ofSubtrees H (Node.subtreesForListComposite H t xs.val.toList)
              (chunkDepth cap)) xs.val.size
            (ofSubtrees_coherent H _ _ fun s hs =>
              subtreesForListComposite_coherent H t
                (fun y => ofShape_coherent H h_t y) xs.val.toList []
                (fun m hm => by cases hm) s hs),
          ofSubtrees_root H (Node.subtreesForListComposite H t xs.val.toList)
            (chunkDepth cap) (by
            rw [length_subtreesForListComposite, List.length_nil, Nat.zero_add,
              Array.length_toList]
            calc xs.val.size ≤ cap := xs.property
              _ ≤ 2 ^ chunkDepth cap := le_two_pow_chunkDepth cap),
          subtreesForListComposite_roots H t
            (fun y => ofShape_root H h_t y) xs.val.toList [],
          if_neg hb]
        rfl
  | _, .containerVar (fs := fs) h_fs _, vs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      rw [ofSubtrees_root H (Node.subtreesForFields H fs vs)
        (chunkDepth fs.length) (by
        rw [length_subtreesForFields]
        exact le_two_pow_chunkDepth fs.length),
        subtreesForFields_roots H h_fs vs]
  | _, .containerFixed (fs := fs) h_fs, vs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      rw [ofSubtrees_root H (Node.subtreesForFields H fs vs)
        (chunkDepth fs.length) (by
        rw [length_subtreesForFields]
        exact le_two_pow_chunkDepth fs.length),
        subtreesForFieldsFixed_roots H h_fs vs]

/-- The shape walker builds coherent trees, for every shape the
codec implements. -/
theorem ofShape_coherent (H : Type) [Hasher H] : ∀ {s : SSZType}, SSZType.BasicSupported s →
    ∀ x : s.interp, (Node.ofShape H s x).Coherent H
  | _, .uintN8, x => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .uintN16, x => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .uintN32, x => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .uintN64, x => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .uintN128, x => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .uintN256, x => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .bool, b => by
      simp only [Node.ofShape]
      exact Node.Coherent.leaf _
  | _, .bitvector (n := n) _, bv => by
      simp only [Node.ofShape]
      exact ofLeaves_coherent H _ _
  | _, .bitlist (cap := cap), bs => by
      simp only [Node.ofShape]
      exact (mixInLength_root_coherent H _ _ (ofLeaves_coherent H _ _)).2
  | _, .vectorFixed (t := t) (n := n) _ h_t _, v => by
      simp only [Node.ofShape]
      by_cases hb : t.isBasicType = true
      · rw [if_pos hb]
        exact ofLeaves_coherent H _ _
      · rw [if_neg hb]
        exact ofSubtrees_coherent H _ _ fun s hs =>
          subtreesForListComposite_coherent H t
            (fun y => ofShape_coherent H h_t y) v.toList []
            (fun m hm => by cases hm) s hs
  | _, .vectorVar (t := t) (n := n) _ h_t h_var, v => by
      simp only [Node.ofShape]
      by_cases hb : t.isBasicType = true
      · have h_fixed := isFixedSize_of_isBasicType t hb
        rw [h_fixed] at h_var
        simp at h_var
      · rw [if_neg hb]
        exact ofSubtrees_coherent H _ _ fun s hs =>
          subtreesForListComposite_coherent H t
            (fun y => ofShape_coherent H h_t y) v.toList []
            (fun m hm => by cases hm) s hs
  | _, .listFixed (t := t) (cap := cap) h_t _ _, xs => by
      simp only [Node.ofShape]
      by_cases hb : t.isBasicType = true
      · rw [if_pos hb]
        exact (mixInLength_root_coherent H _ _ (ofLeaves_coherent H _ _)).2
      · rw [if_neg hb]
        exact (mixInLength_root_coherent H _ _ (ofSubtrees_coherent H _ _
          fun s hs => subtreesForListComposite_coherent H t
            (fun y => ofShape_coherent H h_t y) xs.val.toList []
            (fun m hm => by cases hm) s hs)).2
  | _, .listVar (t := t) (cap := cap) h_t h_var, xs => by
      simp only [Node.ofShape]
      by_cases hb : t.isBasicType = true
      · have h_fixed := isFixedSize_of_isBasicType t hb
        rw [h_fixed] at h_var
        simp at h_var
      · rw [if_neg hb]
        exact (mixInLength_root_coherent H _ _ (ofSubtrees_coherent H _ _
          fun s hs => subtreesForListComposite_coherent H t
            (fun y => ofShape_coherent H h_t y) xs.val.toList []
            (fun m hm => by cases hm) s hs)).2
  | _, .containerVar (fs := fs) h_fs _, vs => by
      simp only [Node.ofShape]
      exact ofSubtrees_coherent H _ _ fun s hs =>
        subtreesForFields_coherent H h_fs vs s hs
  | _, .containerFixed (fs := fs) h_fs, vs => by
      simp only [Node.ofShape]
      exact ofSubtrees_coherent H _ _ fun s hs =>
        subtreesForFieldsFixed_coherent H h_fs vs s hs

/-- Per-field roots for an all-fixed field list: the mutual
partner of the `containerFixed` arm, descending on the field-list
derivation. -/
theorem subtreesForFieldsFixed_roots (H : Type) [Hasher H] : ∀ {fs : List SSZType},
    SSZType.BasicSupportedFieldsFixed fs → ∀ vs : SSZType.interpFields fs,
      (Node.subtreesForFields H fs vs).map (Node.root H)
        = SSZType.hashTreeRootFields H fs vs
  | [], .nil, vs => by
      rw [Node.subtreesForFields, SSZType.hashTreeRootFields]
      rfl
  | t :: ts, .cons h_t _ h_ts, vs => by
      rw [Node.subtreesForFields, SSZType.hashTreeRootFields, List.map_cons,
        ofShape_root H h_t vs.1, subtreesForFieldsFixed_roots H h_ts vs.2]

/-- Per-field coherence for an all-fixed field list. -/
theorem subtreesForFieldsFixed_coherent (H : Type) [Hasher H] : ∀ {fs : List SSZType},
    SSZType.BasicSupportedFieldsFixed fs → ∀ vs : SSZType.interpFields fs,
      ∀ n ∈ Node.subtreesForFields H fs vs, n.Coherent H
  | [], .nil, vs, n, hn => by
      rw [Node.subtreesForFields] at hn
      cases hn
  | t :: ts, .cons h_t _ h_ts, vs, n, hn => by
      rw [Node.subtreesForFields] at hn
      cases hn with
      | head => exact ofShape_coherent H h_t vs.1
      | tail _ hn => exact subtreesForFieldsFixed_coherent H h_ts vs.2 n hn

/-- Per-field roots for a mixed field list: the mutual partner of
the `containerVar` arm. Merkleization never reads the fixed/variable
distinction, so the proof is the all-fixed one with one witness
fewer. -/
theorem subtreesForFields_roots (H : Type) [Hasher H] : ∀ {fs : List SSZType},
    SSZType.BasicSupportedFields fs → ∀ vs : SSZType.interpFields fs,
      (Node.subtreesForFields H fs vs).map (Node.root H)
        = SSZType.hashTreeRootFields H fs vs
  | [], .nil, vs => by
      rw [Node.subtreesForFields, SSZType.hashTreeRootFields]
      rfl
  | t :: ts, .cons h_t h_ts, vs => by
      rw [Node.subtreesForFields, SSZType.hashTreeRootFields, List.map_cons,
        ofShape_root H h_t vs.1, subtreesForFields_roots H h_ts vs.2]

/-- Per-field coherence for a mixed field list. -/
theorem subtreesForFields_coherent (H : Type) [Hasher H] : ∀ {fs : List SSZType},
    SSZType.BasicSupportedFields fs → ∀ vs : SSZType.interpFields fs,
      ∀ n ∈ Node.subtreesForFields H fs vs, n.Coherent H
  | [], .nil, vs, n, hn => by
      rw [Node.subtreesForFields] at hn
      cases hn
  | t :: ts, .cons h_t h_ts, vs, n, hn => by
      rw [Node.subtreesForFields] at hn
      cases hn with
      | head => exact ofShape_coherent H h_t vs.1
      | tail _ hn => exact subtreesForFields_coherent H h_ts vs.2 n hn

end

end SizzLean.Proofs.Merkle
