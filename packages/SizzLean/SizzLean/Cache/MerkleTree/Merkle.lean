import SizzLean.Hasher.Class
import SizzLean.Hasher.Sha256
import SizzLean.Cache.MerkleTree.Node
import SizzLean.Cache.MerkleTree.Zero
import SizzLean.Spec.Constants
import SizzLean.Spec.HashTreeRoot
import SizzLean.Repr.Class
import SizzLean.Repr.Instances

/-!
# `SizzLean.Cache.MerkleTree.Merkle`: the cached Merkle root walker

Walks a `Node` to compute its Merkle root, filling the cache slot
on every `pair` it crosses. If a `pair`'s cache slot is already
`some r`, the walk short-circuits, that subtree's hashes are
reused unchanged.

This is the production fast path. The spec's
`SSZType.hashTreeRoot` remains the verified reference;
`merkleRootWithCache` is asserted equivalent and property-tested
against it.

## The trust story

There is no in-kernel proof that
`merkleRootWithCache = hashTreeRoot`. The conformance vectors
validate `hashTreeRoot` against 38991 upstream cases; this file's
acceptance section re-grounds the equivalence empirically by
running both paths on the same small trees and asserting byte
equality. A future `@[csimp]`-style proof of exact equivalence
would close the loop entirely, out of scope for the cache layer
itself; the interesting verification work is on the spec side.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

open SizzLean.Hasher

open SizzLean

/-- Walk `n` to compute its root, filling `pair` caches as we go.

* `leaf b → (b, leaf b)`: leaves are their own root; no work.
* `pair _ _ (some r) → (r, n)`: cache hit; the subtree is returned
  unchanged.
* `pair l r none → recurse both, combine, return a new pair with
  the freshly cached root.

Termination is structural on `Node`. -/
def Node.merkleRootWithCache (H : Type) [Hasher H] :
    Node → ByteArray × Node
  | .leaf b => (b, .leaf b)
  | .pair l r (some root) => (root, .pair l r (some root))
  | .pair l r none =>
      let (rootL, l') := Node.merkleRootWithCache H l
      let (rootR, r') := Node.merkleRootWithCache H r
      let root := Hasher.combine (H := H) rootL rootR
      (root, .pair l' r' (some root))

/-- The root only, dropping the cache-filled `Node`. Convenient at
call sites that just need the digest. -/
def Node.merkleRoot (H : Type) [Hasher H] (n : Node) : ByteArray :=
  (n.merkleRootWithCache H).1

/-! ### Acceptance: cached path matches the spec oracle

Two small hand-built trees, each compared against
`Spec.SSZType.hashTreeRoot` of an equivalent SSZ value. The spec
oracle is itself validated by 38991 upstream conformance vectors,
so byte-equality here grounds the cached path in the same
empirical evidence.

`native_decide` adds a `Lean.ofReduceBool` axiom per call. This is
allowed in conformance-style smoke tests, kept off the
verified-by-induction proof path.

We pick `Vector (Vector UInt8 32) n` shapes for the SSZ side: each
inner `Vector UInt8 32` (= `Bytes32`) is a 32-byte basic-byte
vector whose HTR is `zero32` when all-zero, identical to a `zero32`
leaf in our tree. The outer `Vector ... n` then merkleizes the
element roots at `chunkDepth n` depth, padding with `ZERO_HASHES`.
This matches `Node.ofLeaves H (List.replicate n zeroBytes32) d`
when `2^d ≥ n`.
-/

/-- 32-byte all-zero `ByteArray`. Mirrors `Tree.Zero.zero32` but kept
local because the latter is `private`. -/
private def zeroBytes32 : ByteArray :=
  let rec build : Nat → ByteArray → ByteArray
    | 0,     acc => acc
    | k + 1, acc => build k (acc.push 0)
  build 32 ByteArray.empty

/-- A `Vector UInt8 32` of all-zero bytes, the SSZ-side
representation of the zero leaf. -/
private def zeroBytes32Vec : Vector UInt8 32 :=
  Vector.replicate 32 0

-- 4 zero leaves at depth 2, the simplest non-trivial case.
example :
    (Node.ofLeaves Sha256
        [zeroBytes32, zeroBytes32, zeroBytes32, zeroBytes32] 2).merkleRoot Sha256
      =
    SizzLean.SSZ.hashTreeRoot Sha256
        (Vector.replicate 4 zeroBytes32Vec) := by
  native_decide

-- 8 zero leaves at depth 3, exact power-of-two, no zero-padding.
example :
    (Node.ofLeaves Sha256
        (List.replicate 8 zeroBytes32) 3).merkleRoot Sha256
      =
    SizzLean.SSZ.hashTreeRoot Sha256
        (Vector.replicate 8 zeroBytes32Vec) := by
  native_decide

-- 4 *distinct* leaves at depth 2, catches any accidental zero-leaf
-- shortcut. Each leaf is 32 bytes of a single constant `k ∈ {1..4}`.
private def constByteLeaf (b : UInt8) : ByteArray :=
  let rec build : Nat → UInt8 → ByteArray → ByteArray
    | 0,     _,  acc => acc
    | k + 1, b', acc => build k b' (acc.push b')
  build 32 b ByteArray.empty

private def constByteVec (b : UInt8) : Vector UInt8 32 :=
  Vector.replicate 32 b

example :
    (Node.ofLeaves Sha256
        [constByteLeaf 1, constByteLeaf 2,
         constByteLeaf 3, constByteLeaf 4] 2).merkleRoot Sha256
      =
    SizzLean.SSZ.hashTreeRoot Sha256
        #v[constByteVec 1, constByteVec 2,
           constByteVec 3, constByteVec 4] := by
  native_decide

end SizzLean.Cache.MerkleTree
