import EthCLLib.Proofs.MerkleBranch
import SizzLean.Proofs.Merkle.Width

/-!
# `EthCLLib.Proofs.ContainerBranch`: a branch to a container field

`isValidMerkleBranch_of_merkleize_idx` accepts the opening of a chunk list. A
container's chunk list is its field roots, so the theorems below read as claims
about a field: the branch to field `k` verifies against the container's own
`hashTreeRoot`.

Two depths are covered. `isValidMerkleBranch_of_container` opens one field.
`isValidMerkleBranch_of_container₂` opens a field of a field, the shape behind
`FINALIZED_ROOT_GINDEX` (`finalized_checkpoint.root`) and
`EXECUTION_BLOCK_HASH_GINDEX` (`execution_payload.block_hash`). Its branch is the
outer opening followed by the inner one, and `foldOpening_append` splits the fold
at that seam.

The spec's call sites pass `floorlog2(gindex)` and `get_subtree_index(gindex)`,
which are `Nat.log2 g` and `g % 2 ^ Nat.log2 g`. The `_gindex` forms take the
`g` that `SSZType.generalizedIndex` returns and state the check at that pair.

`Supported` gates every statement. The proofs read the gate for the widths: the
check takes 32-byte siblings, and `hashTreeRoot_size` supplies them.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean
open SizzLean.Spec
open SizzLean.Proofs.Merkle
open EthCLLib.Spec

/-- The container's chunk list has one entry per field. -/
theorem length_hashTreeRootFields (H : Type) [Hasher H] (fs : List SSZType)
    (vs : SSZType.interpFields fs) :
    (SSZType.hashTreeRootFields H fs vs).length = fs.length := by
  rw [← hashTreeRootFields_eq_map, List.length_map, List.length_range]

/-- Entry `k` of the chunk list is field `k`'s root. `hashTreeRootFields_eq_map`
states the list as a mapped range, and `k` indexes that range at `k`. -/
theorem getElem?_hashTreeRootFields (H : Type) [Hasher H] (fs : List SSZType)
    (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) :
    (SSZType.hashTreeRootFields H fs vs)[k]?.getD Spec.zero32
      = fieldRoot H fs vs k := by
  rw [← hashTreeRootFields_eq_map, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact hk)]
  simp

/-- A field root of a `SupportedFields` container is 32 bytes. It is an entry of
the chunk list, and `hashTreeRootFields_size` sizes every entry. -/
theorem fieldRoot_size (H : Type) [Hasher H] [CombineWidth32 H] {fs : List SSZType}
    (hfs : SSZType.SupportedFields fs) (vs : SSZType.interpFields fs) (k : Nat)
    (hk : k < fs.length) :
    (fieldRoot H fs vs k).size = 32 := by
  have hk' : k < (SSZType.hashTreeRootFields H fs vs).length := by
    rw [length_hashTreeRootFields]; exact hk
  rw [← getElem?_hashTreeRootFields H fs vs k hk, List.getElem?_eq_getElem hk',
    Option.getD_some]
  exact hashTreeRootFields_size H hfs vs _ (List.getElem_mem hk')

/-- The branch to field `k`, top down: the sibling roots along the field's path in
the container's chunk tree. The path is the bit path of the field's generalized
index `2 ^ chunkDepth fs.length + k`. -/
def containerOpening (H : Type) [Hasher H] (fs : List SSZType)
    (vs : SSZType.interpFields fs) (k : Nat) : List ByteArray :=
  naiveOpeningAt H (SSZType.hashTreeRootFields H fs vs) 0 (chunkDepth fs.length)
    (SizzLean.Cache.MerkleTree.gindexBits (2 ^ chunkDepth fs.length + k))

/-- The field's path has one bit per level of the container's chunk tree. -/
theorem length_gindexBits_field (fs : List SSZType) (k : Nat) (hk : k < fs.length) :
    (SizzLean.Cache.MerkleTree.gindexBits (2 ^ chunkDepth fs.length + k)).length
      = chunkDepth fs.length := by
  rw [gindexBits_pow_add _ k (Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length))]
  simp

/-- The branch to a field has one sibling per level. -/
theorem length_containerOpening (H : Type) [Hasher H] (fs : List SSZType)
    (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) :
    (containerOpening H fs vs k).length = chunkDepth fs.length :=
  naiveOpeningAt_length H _ _ 0 _ (length_gindexBits_field fs k hk)

/-- Every sibling in the branch to a field is 32 bytes. -/
theorem size_mem_containerOpening (H : Type) [Hasher H] [CombineWidth32 H]
    {fs : List SSZType} (hfs : SSZType.SupportedFields fs)
    (vs : SSZType.interpFields fs) (k : Nat) :
    ∀ s ∈ containerOpening H fs vs k, s.size = 32 :=
  fun s hs => naiveOpeningAt_size H _ _ 0 _ s (hashTreeRootFields_size H hfs vs) hs

/-- The branch to field `k` folds from the field's root back to the container's
root. `foldOpening_openingAt` does the fold on the chunk list, and
`naiveLeafAt_gindexBits` names the leaf as chunk `k`, which is field `k`'s root.
It takes no width hypothesis, because the fold compares `ByteArray`s. -/
theorem foldOpening_containerOpening (H : Type) [Hasher H] (fs : List SSZType)
    (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) :
    foldOpening H (fieldRoot H fs vs k) (containerOpening H fs vs k)
        (SizzLean.Cache.MerkleTree.gindexBits (2 ^ chunkDepth fs.length + k))
      = SSZType.hashTreeRoot H (.container fs) vs := by
  have hlen : (SSZType.hashTreeRootFields H fs vs).length ≤ 2 ^ chunkDepth fs.length := by
    rw [length_hashTreeRootFields]
    exact le_two_pow_chunkDepth fs.length
  have hindex : k < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length)
  rw [hashTreeRoot_container, ← getElem?_hashTreeRootFields H fs vs k hk]
  exact foldOpening_openingAt H _ (chunkDepth fs.length) hlen _ _ (by
    rw [gindexBits_pow_add (chunkDepth fs.length) k hindex]
    exact naiveLeafAt_gindexBits H (chunkDepth fs.length) _ k hindex)

/-- **A branch to a container field verifies.** Open the container at field `k`
and `isValidMerkleBranch` accepts, against the container's own `hashTreeRoot`.

The chunk list is the field roots, so this is
`isValidMerkleBranch_of_merkleize_idx` with `hashTreeRoot_container` rewriting
the root and `getElem?_hashTreeRootFields` naming the leaf. The depth is
`chunkDepth fs.length`, the depth the merkleizer itself uses, and
`le_two_pow_chunkDepth` puts `k` inside it.

**Axiom use**: at `Sha256`, `CombineWidth32` carries `sha256Combine_eq_spec`. At
`Sha256Spec`, the theorem uses no axiom. -/
theorem isValidMerkleBranch_of_container [HasherTag] [CombineWidth32 HasherTag.H]
    {fs : List SSZType} (hfs : SSZType.SupportedFields fs)
    (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) :
    isValidMerkleBranch
        (bytesToRoot (fieldRoot HasherTag.H fs vs k))
        ((containerOpening HasherTag.H fs vs k).map bytesToRoot).toArray.reverse
        (chunkDepth fs.length) k
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container fs) vs))
      = true := by
  have hlen : (SSZType.hashTreeRootFields HasherTag.H fs vs).length
      ≤ 2 ^ chunkDepth fs.length := by
    rw [length_hashTreeRootFields]
    exact le_two_pow_chunkDepth fs.length
  have hindex : k < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length)
  have hchunks : ∀ c ∈ SSZType.hashTreeRootFields HasherTag.H fs vs, c.size = 32 :=
    hashTreeRootFields_size HasherTag.H hfs vs
  rw [hashTreeRoot_container,
    ← getElem?_hashTreeRootFields HasherTag.H fs vs k hk]
  exact isValidMerkleBranch_of_merkleize _ (chunkDepth fs.length) k hlen hindex
    hchunks _ (by
      rw [gindexBits_pow_add (chunkDepth fs.length) k hindex]
      exact naiveLeafAt_gindexBits HasherTag.H (chunkDepth fs.length) _ k hindex)

/-- **The same, at the gindex a caller holds.** `g` is what `get_generalized_index`
returns for field `k`, and the check runs at `floorlog2(g)` and
`get_subtree_index(g)`. `generalizedIndex_field_top` puts `g` at
`2 ^ chunkDepth fs.length + k`, so the pair is the one the theorem above takes. -/
theorem isValidMerkleBranch_of_container_gindex [HasherTag] [CombineWidth32 HasherTag.H]
    {fs : List SSZType} (hfs : SSZType.SupportedFields fs)
    (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) (g : Nat)
    (hg : (SSZType.container fs).generalizedIndex [.field k] = some g) :
    isValidMerkleBranch
        (bytesToRoot (fieldRoot HasherTag.H fs vs k))
        ((containerOpening HasherTag.H fs vs k).map bytesToRoot).toArray.reverse
        (Nat.log2 g) (g % 2 ^ Nat.log2 g)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container fs) vs))
      = true := by
  have hindex : k < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length)
  rw [generalizedIndex_field_top fs k hk, Option.some.injEq] at hg
  subst hg
  rw [log2_two_pow_add hindex, Nat.add_mod_left, Nat.mod_eq_of_lt hindex]
  exact isValidMerkleBranch_of_container hfs vs k hk

/-! ### A field of a field

The outer container's field `k₁` holds the container `gs` with value `ws`. The
branch runs through both chunk trees: the outer opening at `k₁`, then the inner
opening at `k₂`. The index concatenates the two slots, `k₁ * 2 ^ d₂ + k₂`, where
`d₂` is the inner depth. -/

/-- The composed index fits the composed depth. `k₁` fills at most `2 ^ d₁ - 1`
blocks of `2 ^ d₂`, and `k₂` stays inside one block. -/
theorem index_lt_two_pow_add {d₁ d₂ k₁ k₂ : Nat} (h₁ : k₁ < 2 ^ d₁) (h₂ : k₂ < 2 ^ d₂) :
    k₁ * 2 ^ d₂ + k₂ < 2 ^ (d₁ + d₂) := by
  rw [Nat.pow_add]
  calc k₁ * 2 ^ d₂ + k₂ < (k₁ + 1) * 2 ^ d₂ := by rw [Nat.succ_mul]; omega
    _ ≤ 2 ^ d₁ * 2 ^ d₂ := Nat.mul_le_mul_right _ h₁

/-- The composed path is the outer field's path followed by the inner field's.
`gindexBits_append_step` splits the gindex `(2 ^ d₁ + k₁) * 2 ^ d₂ + k₂` there. -/
theorem gindexBits_two_pow_add_two_pow_add {d₁ d₂ k₁ k₂ : Nat} (h₂ : k₂ < 2 ^ d₂) :
    SizzLean.Cache.MerkleTree.gindexBits (2 ^ (d₁ + d₂) + (k₁ * 2 ^ d₂ + k₂))
      = SizzLean.Cache.MerkleTree.gindexBits (2 ^ d₁ + k₁)
        ++ SizzLean.Cache.MerkleTree.gindexBits (2 ^ d₂ + k₂) := by
  have hshape : 2 ^ (d₁ + d₂) + (k₁ * 2 ^ d₂ + k₂) = (2 ^ d₁ + k₁) * 2 ^ d₂ + k₂ := by
    rw [Nat.add_mul, Nat.pow_add, Nat.add_assoc]
  have hpos : 0 < 2 ^ d₁ + k₁ :=
    Nat.lt_of_lt_of_le (Nat.two_pow_pos d₁) (Nat.le_add_right _ _)
  rw [hshape, gindexBits_append_step hpos h₂, gindexBits_pow_add d₂ k₂ h₂]

/-- **A branch to a field of a field verifies.** Open field `k₁` of `fs`, then
field `k₂` of the container `gs` it holds, and `isValidMerkleBranch` accepts
against the outer container's `hashTreeRoot`.

`hinner` says field `k₁` holds the container value `ws`. At a concrete schema,
`fieldRoot` unfolds to that field's `hashTreeRoot`, so `hinner` closes by `rfl`.

`foldOpening_append` splits the fold at the seam. The inner fold returns `gs`'s
root, `hinner` turns it into field `k₁`'s root, and the outer fold returns `fs`'s
root.

**Axiom use**: at `Sha256`, `CombineWidth32` carries `sha256Combine_eq_spec`. At
`Sha256Spec`, the theorem uses no axiom. -/
theorem isValidMerkleBranch_of_container₂ [HasherTag] [CombineWidth32 HasherTag.H]
    {fs gs : List SSZType} (hfs : SSZType.SupportedFields fs)
    (hgs : SSZType.SupportedFields gs)
    (vs : SSZType.interpFields fs) (ws : SSZType.interpFields gs)
    (k₁ k₂ : Nat) (hk₁ : k₁ < fs.length) (hk₂ : k₂ < gs.length)
    (hinner : fieldRoot HasherTag.H fs vs k₁
      = SSZType.hashTreeRoot HasherTag.H (.container gs) ws) :
    isValidMerkleBranch
        (bytesToRoot (fieldRoot HasherTag.H gs ws k₂))
        ((containerOpening HasherTag.H fs vs k₁
            ++ containerOpening HasherTag.H gs ws k₂).map bytesToRoot).toArray.reverse
        (chunkDepth fs.length + chunkDepth gs.length)
        (k₁ * 2 ^ chunkDepth gs.length + k₂)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container fs) vs))
      = true := by
  have h₁ : k₁ < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk₁ (le_two_pow_chunkDepth fs.length)
  have h₂ : k₂ < 2 ^ chunkDepth gs.length :=
    Nat.lt_of_lt_of_le hk₂ (le_two_pow_chunkDepth gs.length)
  have hlen₁ := length_containerOpening HasherTag.H fs vs k₁ hk₁
  have hlen₂ := length_containerOpening HasherTag.H gs ws k₂ hk₂
  -- Every sibling on either side is 32 bytes, so root-typing them loses nothing.
  have hsibs : ∀ s ∈ containerOpening HasherTag.H fs vs k₁
      ++ containerOpening HasherTag.H gs ws k₂, s.size = 32 := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact size_mem_containerOpening HasherTag.H hfs vs k₁ s hs
    · exact size_mem_containerOpening HasherTag.H hgs ws k₂ s hs
  have hmapback : ((containerOpening HasherTag.H fs vs k₁
        ++ containerOpening HasherTag.H gs ws k₂).map bytesToRoot).map vecToBytes
      = containerOpening HasherTag.H fs vs k₁ ++ containerOpening HasherTag.H gs ws k₂ := by
    rw [List.map_map]
    exact (List.map_congr_left fun s hs => vecToBytes_bytesToRoot s (hsibs s hs)).trans
      (List.map_id' _)
  -- The outer container's root is a `merkleize` of 32-byte chunks.
  have hroot : (SSZType.hashTreeRoot HasherTag.H (.container fs) vs).size = 32 := by
    rw [hashTreeRoot_container]
    exact merkleize_size HasherTag.H _ _
      (by rw [length_hashTreeRootFields]; exact le_two_pow_chunkDepth fs.length)
      (hashTreeRootFields_size HasherTag.H hfs vs)
  apply isValidMerkleBranch_of_foldOpening _ _ _ _ _
    (by rw [List.length_map, List.length_append, hlen₁, hlen₂])
    (index_lt_two_pow_add h₁ h₂)
  rw [hmapback, vecToBytes_bytesToRoot _ (fieldRoot_size HasherTag.H hgs ws k₂ hk₂),
    gindexBits_two_pow_add_two_pow_add h₂,
    foldOpening_append _ _ _ _ _ _ (by rw [hlen₁, length_gindexBits_field fs k₁ hk₁]),
    foldOpening_containerOpening HasherTag.H gs ws k₂ hk₂, ← hinner,
    foldOpening_containerOpening HasherTag.H fs vs k₁ hk₁]
  exact (vecToBytes_bytesToRoot _ hroot).symm

/-- **The same, at the gindex a caller holds.** `g` is what `get_generalized_index`
returns for the two-step path, and the check runs at `floorlog2(g)` and
`get_subtree_index(g)`. `hfield` gives the inner step its type, and
`generalizedIndex_field_field` then computes `g`. -/
theorem isValidMerkleBranch_of_container₂_gindex [HasherTag] [CombineWidth32 HasherTag.H]
    {fs gs : List SSZType} (hfs : SSZType.SupportedFields fs)
    (hgs : SSZType.SupportedFields gs)
    (vs : SSZType.interpFields fs) (ws : SSZType.interpFields gs)
    (k₁ k₂ : Nat) (hk₁ : k₁ < fs.length) (hk₂ : k₂ < gs.length)
    (hfield : fs[k₁] = .container gs)
    (hinner : fieldRoot HasherTag.H fs vs k₁
      = SSZType.hashTreeRoot HasherTag.H (.container gs) ws)
    (g : Nat)
    (hg : (SSZType.container fs).generalizedIndex [.field k₁, .field k₂] = some g) :
    isValidMerkleBranch
        (bytesToRoot (fieldRoot HasherTag.H gs ws k₂))
        ((containerOpening HasherTag.H fs vs k₁
            ++ containerOpening HasherTag.H gs ws k₂).map bytesToRoot).toArray.reverse
        (Nat.log2 g) (g % 2 ^ Nat.log2 g)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container fs) vs))
      = true := by
  have h₁ : k₁ < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk₁ (le_two_pow_chunkDepth fs.length)
  have h₂ : k₂ < 2 ^ chunkDepth gs.length :=
    Nat.lt_of_lt_of_le hk₂ (le_two_pow_chunkDepth gs.length)
  have hidx := index_lt_two_pow_add h₁ h₂
  have hshape : (2 ^ chunkDepth fs.length + k₁) * 2 ^ chunkDepth gs.length + k₂
      = 2 ^ (chunkDepth fs.length + chunkDepth gs.length)
        + (k₁ * 2 ^ chunkDepth gs.length + k₂) := by
    rw [Nat.add_mul, Nat.pow_add, Nat.add_assoc]
  rw [generalizedIndex_field_field fs gs k₁ k₂ hk₁ hk₂ hfield, Option.some.injEq,
    hshape] at hg
  subst hg
  rw [log2_two_pow_add hidx, Nat.add_mod_left, Nat.mod_eq_of_lt hidx]
  exact isValidMerkleBranch_of_container₂ hfs hgs vs ws k₁ k₂ hk₁ hk₂ hinner

end EthCLLib.Proofs
