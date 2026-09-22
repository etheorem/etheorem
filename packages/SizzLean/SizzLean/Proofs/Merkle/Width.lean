import SizzLean.Proofs.Merkle.Chunk
import SizzLean.Proofs.Merkle.Opening
import SizzLean.Proofs.Merkle.HashTreeRoot
import SizzLean.Spec.Supported

/-!
# `SizzLean.Proofs.Merkle.Width`: every root is 32 bytes

`isValidMerkleBranch` takes root-typed leaves and siblings, so a branch proof
about a container needs each field root's width. This file proves it for the
merkleizer and then for `SSZType.hashTreeRoot` at every arm.

`merkleizeAt_size` needs no length bound, unlike `merkleize_size` in
`Proofs/Merkle/Opening.lean`. Each arm of the recursion returns a `combine`, a
zero-tower root, or a chunk the caller supplied. The overflow arm reads the head
of its own list.
-/

set_option autoImplicit false

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec

/-- The zero tower is 32 bytes at every depth. -/
theorem zeroHashAt_size (H : Type) [Hasher H] [CombineWidth32 H] (d : Nat) :
    (Spec.zeroHashAt H d).size = 32 := by
  cases d with
  | zero => rfl
  | succ _ => exact CombineWidth32.size (H := H) _ _

/-- Promoting a 32-byte root through zero levels keeps it 32 bytes. Each step is
a `combine`, so only the zero-step case reads the input's width. -/
theorem promoteThroughZeros_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ (k : Nat) (c : ByteArray) (lvl : Nat), c.size = 32 →
      (Spec.promoteThroughZeros H c lvl k).size = 32 := by
  intro k
  induction k with
  | zero => intro c _ hc; exact hc
  | succ k ih =>
      intro c lvl _
      exact ih _ (lvl + 1) (CombineWidth32.size (H := H) _ _)

/-- Every entry of a pointwise `combine` is 32 bytes. Induction on the left
list, since `zipWith` stops at the shorter one. -/
private theorem mem_zipWith_combine (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ (ls rs : List ByteArray) (c : ByteArray),
      c ∈ List.zipWith (Hasher.combine (H := H)) ls rs → c.size = 32 := by
  intro ls
  induction ls with
  | nil => intro rs c hc; simp at hc
  | cons _ ls ih =>
      intro rs c hc
      cases rs with
      | nil => simp at hc
      | cons _ rs =>
          rw [List.zipWith_cons_cons, List.mem_cons] at hc
          rcases hc with h | h
          · subst h; exact CombineWidth32.size (H := H) _ _
          · exact ih rs c h

/-- One level up is all `combine`s, so every entry is 32 bytes. The class law
`batchCombine_eq` lets this ignore a batched override. -/
theorem combineLayerAt_size (H : Type) [Hasher H] [CombineWidth32 H]
    (lvl : Nat) (cs : List ByteArray) :
    ∀ c ∈ Spec.combineLayerAt H lvl cs, c.size = 32 := by
  intro c hc
  simp only [Spec.combineLayerAt, Hasher.batchCombine_eq, Array.toList_zipWith] at hc
  exact mem_zipWith_combine H _ _ c hc

/-- The merkleizer returns 32 bytes whenever its chunks do, at any level and any
remaining depth. Induction on `remaining`: the recursive arm hands
`combineLayerAt` its own 32-byte output back, so the chunk hypothesis survives
the step. -/
theorem merkleizeAt_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ (remaining : Nat) (cs : List ByteArray) (lvl : Nat),
      (∀ c ∈ cs, c.size = 32) → (Spec.merkleizeAt H cs lvl remaining).size = 32 := by
  intro remaining
  induction remaining with
  | zero =>
      intro cs lvl hcs
      match cs with
      | []      => exact zeroHashAt_size H 0
      | [c]     => exact hcs c (List.mem_cons_self ..)
      | c :: _ :: _ =>
          show (List.head? (c :: _) |>.getD Spec.zero32).size = 32
          exact hcs c (List.mem_cons_self ..)
  | succ r ih =>
      intro cs lvl hcs
      match cs with
      | []  => exact zeroHashAt_size H (r + 1)
      | [c] => exact promoteThroughZeros_size H (r + 1) c lvl (hcs c (List.mem_cons_self ..))
      | c :: d :: rest =>
          show (Spec.merkleizeAt H (Spec.combineLayerAt H lvl (c :: d :: rest))
            (lvl + 1) r).size = 32
          exact ih _ (lvl + 1) (combineLayerAt_size H lvl _)

/-- `Spec.merkleize` returns 32 bytes whenever its chunks do, whatever the depth
and however many chunks there are. -/
theorem merkleize_size_of_chunks (H : Type) [Hasher H] [CombineWidth32 H]
    (cs : List ByteArray) (depth : Nat) (hcs : ∀ c ∈ cs, c.size = 32) :
    (Spec.merkleize H cs depth).size = 32 :=
  merkleizeAt_size H depth cs 0 hcs

/-- A length mix-in is a `combine`, so it is 32 bytes whatever it wraps. -/
theorem mixInLength_size (H : Type) [Hasher H] [CombineWidth32 H]
    (root : ByteArray) (n : Nat) : (Spec.mixInLength H root n).size = 32 :=
  CombineWidth32.size (H := H) _ _

/-! ### Every `hashTreeRoot` is 32 bytes

`Supported` is mutually inductive with its two field-list predicates, so
`induction` refuses it. `Proofs/SerializeSize.lean` already solved this: a
`mutual` block of theorems that `cases` on the predicate and recurse
structurally on it, one partner per predicate.

An unsupported shape can merkleize chunks that are not 32 bytes wide, so the
proof needs the `Supported` gate. `scripts/ProofCoverage.lean` reads the same
gate. -/

mutual

/-- Every root the spec computes is 32 bytes.

The arms divide three ways. A basic arm is a `padToChunk`, and `size_padToChunk`
gives its width once the input fits a chunk. A bit or packed arm merkleizes
`chunkify` output, whose entries are 32 bytes by `size_mem_chunkify`. A composite
arm merkleizes element roots, which this theorem covers recursively, and a
mix-in over either is a `combine`.

`hashTreeRoot`'s degenerate `uintN` arm returns `zero32`, but `Supported` has no
constructor for a non-spec width, so no case here reaches it. -/
theorem hashTreeRoot_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ {s : SSZType}, SSZType.Supported s → ∀ x : s.interp,
      (SSZType.hashTreeRoot H s x).size = 32 := by
  intro s hs x
  cases hs with
  | uintN8 =>
      rw [hashTreeRoot_uintN8]
      exact size_padToChunk _ (by simp [SSZType.serialize, BYTES_PER_CHUNK])
  | uintN16 =>
      rw [hashTreeRoot_uintN16]
      exact size_padToChunk _ (by simp [SSZType.serialize, uint16LE, BYTES_PER_CHUNK])
  | uintN32 =>
      rw [hashTreeRoot_uintN32]
      exact size_padToChunk _ (by simp [SSZType.serialize, uint32LE, BYTES_PER_CHUNK])
  | uintN64 =>
      rw [hashTreeRoot_uintN64]
      exact size_padToChunk _ (by simp [SSZType.serialize, uint64LE, BYTES_PER_CHUNK])
  | uintN128 =>
      simp only [SSZType.hashTreeRoot]
      exact size_padToChunk _ (by simp [size_natToChunk])
  | uintN256 =>
      simp only [SSZType.hashTreeRoot]
      exact size_padToChunk _ (by simp [size_natToChunk])
  | bool =>
      rw [hashTreeRoot_bool]
      exact size_padToChunk _ (by simp [SSZType.serialize, BYTES_PER_CHUNK])
  | bitvector =>
      rw [hashTreeRoot_bitvector]
      exact merkleize_size_of_chunks H _ _ (size_mem_chunkify _)
  | bitlist =>
      rw [hashTreeRoot_bitlist]
      exact mixInLength_size H _ _
  | vectorFixed h_t _ => exact hashTreeRoot_vector_size H h_t x
  | vectorVar h_t _ => exact hashTreeRoot_vector_size H h_t x
  | @listFixed t cap _ _ =>
      by_cases hb : t.isBasicType
      · rw [hashTreeRoot_listBasic H t cap hb]; exact mixInLength_size H _ _
      · rw [hashTreeRoot_listComposite H t cap (by simpa using hb)]
        exact mixInLength_size H _ _
  | @listVar t cap _ _ =>
      by_cases hb : t.isBasicType
      · rw [hashTreeRoot_listBasic H t cap hb]; exact mixInLength_size H _ _
      · rw [hashTreeRoot_listComposite H t cap (by simpa using hb)]
        exact mixInLength_size H _ _
  | containerFixed h_fs =>
      rw [hashTreeRoot_container]
      exact merkleize_size_of_chunks H _ _ (hashTreeRootFields_size_fix H h_fs x)
  | containerVar h_fs _ =>
      rw [hashTreeRoot_container]
      exact merkleize_size_of_chunks H _ _ (hashTreeRootFields_size H h_fs x)

/-- The vector arm, split off so both `Supported` vector constructors share it.
A basic element type packs into chunks. A composite one merkleizes the element
roots, which the main theorem sizes. -/
theorem hashTreeRoot_vector_size (H : Type) [Hasher H] [CombineWidth32 H]
    {t : SSZType} {n : Nat} (h_t : SSZType.Supported t)
    (v : (SSZType.vector t n).interp) :
    (SSZType.hashTreeRoot H (.vector t n) v).size = 32 := by
  by_cases hb : t.isBasicType
  · rw [hashTreeRoot_vectorFixed H t n hb v]
    exact merkleize_size_of_chunks H _ _ (size_mem_chunkify _)
  · rw [hashTreeRoot_vectorComposite H t n (by simpa using hb) v]
    refine merkleize_size_of_chunks H _ _ ?_
    rw [hashTreeRootListComposite_eq]
    intro c hc
    simp only [List.reverse_nil, List.nil_append, List.mem_map] at hc
    obtain ⟨y, _, hy⟩ := hc
    rw [← hy]
    exact hashTreeRoot_size H h_t y

/-- Every field root of a `SupportedFields` container is 32 bytes. -/
theorem hashTreeRootFields_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ {fs : List SSZType}, SSZType.SupportedFields fs →
      ∀ (vs : SSZType.interpFields fs),
        ∀ c ∈ SSZType.hashTreeRootFields H fs vs, c.size = 32 := by
  intro fs h_fs vs c hc
  cases h_fs with
  | nil => rw [hashTreeRootFields_nil] at hc; exact absurd hc (by simp)
  | cons h_t h_ts =>
      rw [hashTreeRootFields_cons, List.mem_cons] at hc
      rcases hc with h | h
      · subst h; exact hashTreeRoot_size H h_t vs.1
      · exact hashTreeRootFields_size H h_ts vs.2 c h

/-- The same for `SupportedFieldsFixed`, whose extra `isFixedSize` witness this
proof does not read. -/
theorem hashTreeRootFields_size_fix (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ {fs : List SSZType}, SSZType.SupportedFieldsFixed fs →
      ∀ (vs : SSZType.interpFields fs),
        ∀ c ∈ SSZType.hashTreeRootFields H fs vs, c.size = 32 := by
  intro fs h_fs vs c hc
  cases h_fs with
  | nil => rw [hashTreeRootFields_nil] at hc; exact absurd hc (by simp)
  | cons h_t _ h_ts =>
      rw [hashTreeRootFields_cons, List.mem_cons] at hc
      rcases hc with h | h
      · subst h; exact hashTreeRoot_size H h_t vs.1
      · exact hashTreeRootFields_size_fix H h_ts vs.2 c h

end

end SizzLean.Proofs.Merkle
