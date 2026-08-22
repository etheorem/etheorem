import EthCLLib.Proofs.MerkleOpening
import EthCLLib.Proofs.MerkleBranch
import EthCLLib.Spec.SigningRoot

/-!
# `EthCLLib.Tests.MerkleWitness`: Merkle-branch length-guard witnesses

Two rejection witnesses for `isValidMerkleBranch`, an over-length branch and a
short one, pinning the guard in both directions.

The spec returns early on `depth != len(branch)`
(`specs/phase0/beacon-chain.md:809`). Completeness covers only the branches an
honest opening produces, so it says nothing about this direction. These two
statements are the ones `Proofs/MerkleBranch.lean` does not imply.

The guard settles both before any hashing, so they close by `simp` and carry no
compiler axiom.
-/

set_option autoImplicit false

namespace EthCLLib.Tests

open SizzLean SizzLean.Hasher SizzLean.Cache.MerkleTree
open EthCLLib.Spec EthCLLib.Proofs

/-- **Over-length rejection.** The spec's `is_valid_merkle_branch` guards
`depth != len(branch)` (`specs/phase0/beacon-chain.md:809`), so it rejects a
branch longer than `depth` outright. Padding the depth-1 witness's honest branch
with an extra sibling makes `branch.size = 2 ≠ 1 = depth`, so the check returns
`false`.

The guard decides this before the fold runs. Nothing hashes, and the root
argument never forces. `simp` closes it on the branch's size alone. Plain
`decide` does not: its `Decidable` instance will not reduce through
`siblingPath`. -/
example :
    let z : ByteArray := (ByteArray.mk (Array.replicate 32 0))
    let o : ByteArray := (ByteArray.mk (Array.replicate 32 1))
    letI : HasherTag := fastHasherTag
    let tree : Node := .pair (.leaf z) (.leaf o) none
    isValidMerkleBranch
        (honestLeaf Sha256 tree 1 0)
        ((honestBranch Sha256 tree 1 0).push (bytesToRoot o))
        1 0
        (bytesToRoot (Node.merkleRoot Sha256 tree))
      = false := by
  simp [isValidMerkleBranch, honestBranch, siblingPath, routeRight]

/-- **Short-branch rejection.** The same guard cuts the other way. The spec
compares `depth != len(branch)`, so it rejects a branch *shorter* than `depth`
too. Popping the depth-1 witness's single sibling leaves `branch.size = 0 ≠ 1 =
depth`, so the check returns `false` even though the leaf and root are the honest
ones. `simp` closes it for the same reason as above.

**Why index 1 and not 0.** At index 1 the removed sibling is the left child `z`,
32 zero bytes. That is exactly what an unguarded `branch[0]!` returns on an empty
array. The reconstruction would therefore still succeed, so the guard alone
accounts for the `false`. At index 0 the sibling is `o`, the reconstruction fails
on its own, and the test no longer isolates the guard. -/
example :
    let z : ByteArray := (ByteArray.mk (Array.replicate 32 0))
    let o : ByteArray := (ByteArray.mk (Array.replicate 32 1))
    letI : HasherTag := fastHasherTag
    let tree : Node := .pair (.leaf z) (.leaf o) none
    isValidMerkleBranch
        (honestLeaf Sha256 tree 1 1)
        ((honestBranch Sha256 tree 1 1).pop)
        1 1
        (bytesToRoot (Node.merkleRoot Sha256 tree))
      = false := by
  simp [isValidMerkleBranch, honestBranch, siblingPath, routeRight]

end EthCLLib.Tests
