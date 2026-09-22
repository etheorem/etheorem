import EthCLLib.Proofs.MerkleBranch

/-!
# `EthCLLib.Tests.MerkleWitness`: the branch-length guard rejects

`isValidMerkleBranch_of_merkleize` covers what the check accepts. Completeness
says nothing about what it rejects, so these two witnesses pin the length guard
`branch.size = depth` in both directions.

Both start from an honest opening of the pure-path tree over two chunks at depth
1 and change only the branch length: the first adds a sibling, the second
removes one. The leaf and the root stay honest, so the guard is the only reason
for the `false`.

Nothing here hashes. The guard runs before the fold, so `naiveOpeningAt_length`
closes both goals from the length alone. A `decide` would instead drive the
whole opening through the kernel.
-/

set_option autoImplicit false

namespace EthCLLib.Tests

open SizzLean
open SizzLean.Hasher
open SizzLean.Proofs.Merkle
open EthCLLib.Spec
open EthCLLib.Proofs

/-- The tree's first chunk. The two chunks differ, so a wrong sibling changes
the root, and both are 32 bytes as the merkleizer requires. -/
private def chunkZero : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- The second chunk, all ones. -/
private def chunkOne : ByteArray := ByteArray.mk (Array.replicate 32 1)

/-- The witness tree's chunks: a two-leaf tree, so depth 1. -/
private def witnessChunks : List ByteArray := [chunkZero, chunkOne]

/-- The path bits for leaf `index` in a depth-1 tree. -/
private def witnessBits (index : Nat) : List Bool :=
  Cache.MerkleTree.gindexBits (2 ^ 1 + index)

/-- The honest branch for leaf `index`: the opening root-typed and reversed,
exactly the array `isValidMerkleBranch` takes. -/
private def witnessBranch (index : Nat) : Array (Vector UInt8 32) :=
  ((naiveOpeningAt Sha256Spec witnessChunks 0 1
    (witnessBits index)).map bytesToRoot).toArray.reverse

/-- The honest leaf for `index`, root-typed. -/
private def witnessLeaf (index : Nat) : Vector UInt8 32 :=
  bytesToRoot (witnessChunks[index]?.getD Spec.zero32)

/-- The tree's honest root, root-typed. -/
private def witnessRoot : Vector UInt8 32 :=
  bytesToRoot (Spec.merkleize Sha256Spec witnessChunks 1)

/-- A depth-1 path is one bit long, whichever leaf it addresses. -/
private theorem witnessBits_length (index : Nat) (h : index < 2 ^ 1) :
    (witnessBits index).length = 1 := by
  rw [witnessBits, gindexBits_pow_add 1 index h]
  simp

/-- The honest branch holds one sibling, which both witnesses below change. -/
private theorem witnessBranch_size (index : Nat) (h : index < 2 ^ 1) :
    (witnessBranch index).size = 1 := by
  simp [witnessBranch,
    naiveOpeningAt_length Sha256Spec 1 witnessChunks 0 (witnessBits index)
      (witnessBits_length index h)]

/-- **Rejection witness: a branch one sibling too long.** `branch.size` exceeds
`depth` and the guard rejects, as the spec's `depth != len(branch)` check
does. -/
example :
    @isValidMerkleBranch pureHasherTag
        (witnessLeaf 0)
        ((witnessBranch 0).push (bytesToRoot chunkOne))
        1 0 witnessRoot
      = false := by
  have hsz : ((witnessBranch 0).push (bytesToRoot chunkOne)).size ≠ 1 := by
    rw [Array.size_push, witnessBranch_size 0 (by decide)]
    decide
  simp only [isValidMerkleBranch, if_neg hsz]

/-- **Rejection witness: a branch one sibling too short.** `branch.size = 0`
against `depth = 1`, with an honest leaf and root. The guard rejects it, as the
spec's `depth != len(branch)` check does. The fold never reads past the end. -/
example :
    @isValidMerkleBranch pureHasherTag
        (witnessLeaf 1)
        (witnessBranch 1).pop
        1 1 witnessRoot
      = false := by
  have hsz : (witnessBranch 1).pop.size ≠ 1 := by
    rw [Array.size_pop, witnessBranch_size 1 (by decide)]
    decide
  simp only [isValidMerkleBranch, if_neg hsz]

end EthCLLib.Tests
