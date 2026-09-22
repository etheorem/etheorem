import EthCLLib.Proofs.MerkleBranch
import SizzLean.Proofs.Merkle.Width

/-!
# `EthCLLib.Proofs.ContainerBranch`: a branch to a container field

`isValidMerkleBranch_of_merkleize_idx` accepts the opening of a chunk list. A
container's chunk list is its field roots, so the theorem below reads as a claim
about a field: the branch to field `k` verifies against the container's own
`hashTreeRoot`.

The generalized index of field `k` is `2 ^ chunkDepth fs.length + k`
(`SSZType.generalizedIndex`, `SizzLean/Spec/GeneralizedIndex.lean`), which is the
index this statement opens at.

`Supported` gates the statement. The proof reads the gate once, to get
`hashTreeRoot_size` on the field roots. The branch check needs those roots 32
bytes wide.
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
        ((naiveOpeningAt HasherTag.H (SSZType.hashTreeRootFields HasherTag.H fs vs) 0
            (chunkDepth fs.length)
            (SizzLean.Cache.MerkleTree.gindexBits
              (2 ^ chunkDepth fs.length + k))).map bytesToRoot).toArray.reverse
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

end EthCLLib.Proofs
