import SizzLean.Hasher.Class
import SizzLean.Hasher.Sha256
import SizzLean.Cache.MerkleTree.Node
import SizzLean.Cache.MerkleTree.Zero
import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.Serialize
import SizzLean.Spec.HashTreeRoot

/-!
# `SizzLean.Cache.MerkleTree.Build`: shape-driven `Node` construction

The `Node.ofShape` mutual block walks an `SSZType` and the
corresponding `s.interp` value, emitting a `Node` whose interior
mirrors the SSZ shape:

* basic-type values (`uintN`, `bool`) become a single `.leaf` of
  the chunk-padded encoding;
* `bitvector` / `bitlist` chunk-pack their packed bytes into
  leaves of a balanced subtree, with `bitlist` also
  mix-in-length-wrapping the body;
* `vector t n` / `list t cap` with **basic** `t` flatten the
  serialised body into chunks (same byte path as the spec);
* `vector t n` / `list t cap` with **composite** `t` recurse
  per element into sub-trees, then balance them as the leaves of
  an `ofSubtrees` tree (depth `chunkDepth n` / `chunkDepth cap`);
* `container fs` recurses per field into sub-trees, balanced via
  `ofSubtrees` at depth `chunkDepth fs.length`.

Every arm mirrors a corresponding arm of
`Spec.SSZType.hashTreeRoot` (mutual block at
`Spec/HashTreeRoot.lean:352`). The byte-identity contract is:

    (Node.ofShape H s x).merkleRoot H = SSZType.hashTreeRoot H s x

verified empirically by `Conformance/TreeBackedCoherence.lean`.

## Why structural mutual recursion (not higher-order)

The arms that recurse over a field list (`container fs`) or an
element list (composite-element `vector` / `list`) need to traverse
those `List` arguments. Lean 4.29.1 rejects passing `Node.ofShape`
itself as a higher-order argument to `List.map`; the mutual-helper
shape used by `Spec.hashTreeRoot` (`hashTreeRootFields`,
`hashTreeRootListComposite`) is the workaround we mirror here.
-/

set_option autoImplicit false
-- Same elaborator heat-budget escalation as `Spec/HashTreeRoot.lean`
-- and `Spec/Deserialize.lean`, the dependent match in `ofShape`
-- refines `s.interp` against `interp`'s own per-constructor
-- recursion, which drives the elaborator past the 200k default.
set_option maxHeartbeats 5000000

namespace SizzLean.Cache.MerkleTree

open SizzLean.Repr

open SizzLean.Hasher

open SizzLean
open SizzLean.Spec

/-! ### Helpers shared across arms -/

/-- Build a balanced binary tree of `2^depth` leaf-slots from a
list of *sub-trees* (not raw bytes), padding the right with
`zeroLeaf` of the appropriate depth.

This is the `List Node → Node` analogue of `Node.ofLeaves`. They
share the split-at-`2^d` shape and the right-padding rule; the
only difference is whether the recursion's base case is `.leaf b`
(from `ofLeaves`) or the supplied sub-tree (here). -/
def Node.ofSubtrees (H : Type) [Hasher H] :
    (subs : List Node) → (depth : Nat) → Node
  | [],         0     => zeroLeaf H 0
  | s :: _,     0     => s    -- depth 0 holds exactly one sub-tree
  | subs,       d + 1 =>
      let half := 2 ^ d
      let leftSubs  := subs.take half
      let rightSubs := subs.drop half
      let leftNode  := Node.ofSubtrees H leftSubs d
      let rightNode :=
        if rightSubs.isEmpty then zeroLeaf H d
        else Node.ofSubtrees H rightSubs d
      -- Compute the parent's root inline so the constructed pair is
      -- already cached. Saves the later `merkleRootWithCache` from
      -- having to re-allocate this pair with the cache filled in.
      let root := Hasher.combine (H := H)
        (Node.rootOf H leftNode) (Node.rootOf H rightNode)
      .pair leftNode rightNode (some root)

/-- Wrap an existing tree with a length-chunk sibling, producing the
`mix-in-length` SSZ root pattern. The combined root is
`Hasher.combine (root of n) (natToChunk count)`. We compute and
embed the root in the resulting pair's cache slot so the caller
gets a fully-cached tree out. -/
def Node.mixInLength (H : Type) [Hasher H] (n : Node) (count : Nat) : Node :=
  let lenLeaf : Node := .leaf (natToChunk count)
  let root := Hasher.combine (H := H) (Node.rootOf H n) (Node.rootOf H lenLeaf)
  .pair n lenLeaf (some root)

/-! ### The shape-driven builder

Mutual block mirroring `Spec.SSZType.hashTreeRoot` arm-for-arm.
Where the spec calls `merkleize chunks depth`, this calls
`Node.ofLeaves chunks depth`; where the spec calls `merkleize
roots depth` after `hashTreeRootListComposite`, this calls
`Node.ofSubtrees subTrees depth`. -/

mutual

/-- Build a `Node` whose `merkleRoot` matches `Spec.hashTreeRoot`'s
output for the same `(s, x)`. -/
def Node.ofShape (H : Type) [Hasher H] :
    (s : SSZType) → s.interp → Node
  | .uintN 8,    x  =>
      let x' : UInt8 := x
      .leaf (padToChunk (ByteArray.empty.push x'))
  | .uintN 16,   x  =>
      let x' : UInt16 := x
      .leaf (padToChunk (SSZType.serialize (.uintN 16) x'))
  | .uintN 32,   x  =>
      let x' : UInt32 := x
      .leaf (padToChunk (SSZType.serialize (.uintN 32) x'))
  | .uintN 64,   x  =>
      let x' : UInt64 := x
      .leaf (padToChunk (SSZType.serialize (.uintN 64) x'))
  | .uintN 128,  x  =>
      let x' : BitVec 128 := x
      .leaf (padToChunk (natToChunk x'.toNat))
  | .uintN 256,  x  =>
      let x' : BitVec 256 := x
      .leaf (padToChunk (natToChunk x'.toNat))
  | .uintN _,    _  =>
      -- Non-spec uintN width, degenerate case, single zero chunk.
      .leaf (padToChunk ByteArray.empty)
  | .bool,       b  =>
      let b' : Bool := b
      .leaf (padToChunk (ByteArray.empty.push (if b' then 1 else 0)))
  | .bitvector n, bv =>
      let bv' : BitVec n := bv
      let body := SSZType.serialize (.bitvector n) bv'
      Node.ofLeaves H (chunkify body)
        (chunkDepth (bytesToChunkCount ((n + 7) / 8)))
  | .bitlist cap, bs =>
      -- Bitlist body is the bits *without* the trailing-delimiter
      -- bit. Mirror `Spec.hashTreeRoot`'s `.bitlist` arm: serialize
      -- the bits as a `.bitvector` of the actual length, chunkify,
      -- merkleize at depth `chunkDepth (bitsToChunkCount cap)`,
      -- then mix-in length.
      let bs' : { xs : Array Bool // xs.size ≤ cap } := bs
      let xs := bs'.val
      let bv : BitVec xs.size := BitVec.ofNat xs.size (bitsToNatLE xs.toList)
      let bytes := SSZType.serialize (.bitvector xs.size) bv
      let bodyTree := Node.ofLeaves H (chunkify bytes)
        (chunkDepth (bitsToChunkCount cap))
      Node.mixInLength H bodyTree xs.size
  | .vector t n, v  =>
      let v' : Vector t.interp n := v
      if t.isBasicType then
        let body := SSZType.serialize (.vector t n) v'
        Node.ofLeaves H (chunkify body)
          (chunkDepth (bytesToChunkCount body.size))
      else
        let subs := Node.subtreesForListComposite H t v'.toList
        Node.ofSubtrees H subs (chunkDepth n)
  | .list t cap, xs =>
      let xs' : { ys : Array t.interp // ys.size ≤ cap } := xs
      let actualLen := xs'.val.size
      if t.isBasicType then
        let body := SSZType.serializeFixedElems t xs'.val.toList
        let perElem := t.fixedByteSize
        let capChunks := bytesToChunkCount (cap * perElem)
        let bodyTree := Node.ofLeaves H (chunkify body) (chunkDepth capChunks)
        Node.mixInLength H bodyTree actualLen
      else
        let subs := Node.subtreesForListComposite H t xs'.val.toList
        let bodyTree := Node.ofSubtrees H subs (chunkDepth cap)
        Node.mixInLength H bodyTree actualLen
  | .container fs, vs =>
      let subs := Node.subtreesForFields H fs vs
      Node.ofSubtrees H subs (chunkDepth fs.length)

/-- Per-field sub-trees for a `container fs` value. Mirrors the
spec's `hashTreeRootFields` (lines 450–458 of `HashTreeRoot.lean`)
arm-for-arm. -/
def Node.subtreesForFields (H : Type) [Hasher H] :
    (fs : List SSZType) → SSZType.interpFields fs → List Node
  | [],      _  => []
  | t :: ts, vs =>
      Node.ofShape H t vs.1 :: Node.subtreesForFields H ts vs.2

/-- Per-element sub-trees for a composite-element `vector` /
`list`. Mirrors `hashTreeRootListComposite`. -/
def Node.subtreesForListComposite (H : Type) [Hasher H] :
    (t : SSZType) → List t.interp → List Node
  | _, []      => []
  | t, x :: xs =>
      Node.ofShape H t x :: Node.subtreesForListComposite H t xs

end

end SizzLean.Cache.MerkleTree
