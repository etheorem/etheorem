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
  `ofSubtrees` at depth `chunkDepth fs.length`;
* `progressiveContainer active fs` recurses per field into sub-trees
  and places them in the `merkleize_progressive` shelves, with a zero
  leaf at each inactive mask bit (`ofProgressiveSubtrees`).

Every arm mirrors a corresponding arm of
`Spec.SSZType.hashTreeRoot` (mutual block at
`Spec/HashTreeRoot.lean:352`). The byte-identity contract is:

    (Node.ofShape H s x).merkleRoot H = SSZType.hashTreeRoot H s x

proved in `Proofs/Merkle/OfShape.lean` (`ofShape_root`,
`ofShape_coherent`) and exercised by
`Conformance/TreeBackedCoherence.lean`.

## Why structural mutual recursion (not higher-order)

The arms that recurse over a field list (`container fs`) or an
element list (composite-element `vector` / `list`) need to traverse
those `List` arguments. Lean 4.34.1 rejects passing `Node.ofShape`
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
      -- Split tail-recursively via `List.splitAt`: core's `List.take` is not
      -- tail-recursive, so `subs.take half` would recurse `half` frames deep
      -- and overflow the stack for the large mainnet sub-tree counts (a
      -- 262144-element composite list splits 131072 at the top). Same
      -- `(take, drop)` result, one constant-stack pass.
      let (leftSubs, rightSubs) := subs.splitAt half
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

/-- `mix_in_active_fields` as a cached pair. The right leaf is
`pack(active_fields)`, right-padded to one chunk. -/
def Node.mixInActiveFields (H : Type) [Hasher H] (n : Node) (active : List Bool) : Node :=
  let mask : Node := .leaf (padToChunk (packBitsLE active))
  let root := Hasher.combine (H := H) (Node.rootOf H n) (Node.rootOf H mask)
  .pair n mask (some root)

/-- Cached tree for `merkleize_progressive`. Mirrors
`Spec.merkleizeProgressiveAux`: the empty chunk list is a zero
leaf, and a non-empty list pairs the balanced shelf with the
progressive tree of the remainder. -/
def Node.ofProgressiveAux (H : Type) [Hasher H] :
    Nat → List ByteArray → Nat → Node
  | _, [], _ => .leaf zero32
  | 0, _, _ => .leaf zero32
  | fuel + 1, chunks, numLeaves =>
      let n := max numLeaves 1
      let left := Node.ofLeaves H (chunks.take n) (chunkDepth n)
      let right := Node.ofProgressiveAux H fuel (chunks.drop n) (n * 4)
      let root := Hasher.combine (H := H)
        (Node.rootOf H left) (Node.rootOf H right)
      .pair left right (some root)

/-- `merkleize_progressive` over chunk bytes, rooted at shelf width 1. -/
def Node.ofProgressive (H : Type) [Hasher H] (chunks : List ByteArray) : Node :=
  Node.ofProgressiveAux H chunks.length chunks 1

/-- `merkleize_progressive` over sub-trees. The shelves are the ones
`Node.ofProgressiveAux` builds, but each shelf is an `ofSubtrees` tree,
so the supplied sub-trees stay in the result. A write below one of them
then replaces one path, and the other shelves keep their cache slots.
`Proofs/Merkle/Progressive.lean` proves that the root equals the
`ofProgressiveAux` root over the sub-trees' roots. -/
def Node.ofProgressiveSubtreesAux (H : Type) [Hasher H] :
    Nat → List Node → Nat → Node
  | _, [], _ => .leaf zero32
  | 0, _, _ => .leaf zero32
  | fuel + 1, subs, numLeaves =>
      let n := max numLeaves 1
      let left := Node.ofSubtrees H (subs.take n) (chunkDepth n)
      let right := Node.ofProgressiveSubtreesAux H fuel (subs.drop n) (n * 4)
      let root := Hasher.combine (H := H)
        (Node.rootOf H left) (Node.rootOf H right)
      .pair left right (some root)

/-- `merkleize_progressive` over sub-trees, rooted at shelf width 1. -/
def Node.ofProgressiveSubtrees (H : Type) [Hasher H] (subs : List Node) : Node :=
  Node.ofProgressiveSubtreesAux H subs.length subs 1

/-- The chunk sub-trees of a progressive container: the field sub-trees
in mask order, with a zero leaf at each inactive mask bit. -/
def placeActiveSubtrees : List Bool → List Node → List Node
  | [], _ => []
  | false :: bits, nodes => .leaf zero32 :: placeActiveSubtrees bits nodes
  | true :: bits, n :: ns => n :: placeActiveSubtrees bits ns
  | true :: bits, [] => .leaf zero32 :: placeActiveSubtrees bits []

/-! ### Paths into a progressive tree

A progressive tree has no classic generalized index: shelf `k` holds
`4 ^ k` chunks and hangs `k` right turns below the root. The functions
below give the bit path (`false` = left) from the root of
`Node.ofProgressiveSubtrees` to one chunk, and from the root of a
progressive container to one field. The `sszUpdate` elaborator calls
`progressiveFieldBits` to key a pending write, and
`Proofs/Merkle/Progressive.lean` proves that the path reaches the
field's sub-tree. -/

/-- The path to chunk `pos` of a progressive tree whose current shelf
holds `width` chunks. At the shelf that holds `pos`, the path turns left
and then reads the `chunkDepth` low bits of `pos`, most significant
first. Otherwise it turns right and continues at the next shelf. `fuel`
bounds the shelf count. -/
def progressiveChunkBitsAux : Nat → Nat → Nat → List Bool
  | 0, _, _ => []
  | fuel + 1, pos, width =>
      let n := max width 1
      if pos < n then
        false :: (List.range (chunkDepth n)).reverse.map (pos.testBit ·)
      else
        true :: progressiveChunkBitsAux fuel (pos - n) (n * 4)

/-- The path to chunk `pos` of `Node.ofProgressiveSubtrees`. Each shelf
holds at least one chunk, so `pos + 1` shelves are enough fuel. -/
def progressiveChunkBits (pos : Nat) : List Bool :=
  progressiveChunkBitsAux (pos + 1) pos 1

/-- The mask position of active field `k`: the index of the `k`-th
`true` bit of `active`. -/
def activeChunkPos : List Bool → Nat → Nat
  | [], _ => 0
  | false :: bits, k => activeChunkPos bits k + 1
  | true :: _, 0 => 0
  | true :: bits, k + 1 => activeChunkPos bits k + 1

/-- The path from the root of a progressive container to field `k`. The
leading `false` steps into the body of the `mix_in_active_fields` pair. -/
def progressiveFieldBits (active : List Bool) (k : Nat) : List Bool :=
  false :: progressiveChunkBits (activeChunkPos active k)

/-- Shelf 0 holds chunk 0, shelf 1 holds chunks 1 to 4, and shelf 2
starts at chunk 5. -/
example : progressiveChunkBits 0 = [false] := by decide
example : progressiveChunkBits 1 = [true, false, false, false] := by decide
example : progressiveChunkBits 4 = [true, false, true, true] := by decide
example : progressiveChunkBits 5 =
    [true, true, false, false, false, false, false] := by decide
/-- Field 1 of the mask `[1, 0, 1]` sits at position 2, after the gap. -/
example : progressiveFieldBits [true, false, true] 1
    = [false, true, false, false, true] := by decide

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
  | .progressiveList t, xs =>
      let xs' : Array t.interp := xs
      if t.isBasicType then
        let body := SSZType.serializeFixedElems t xs'.toList
        let bodyTree := Node.ofProgressive H (chunkify body)
        Node.mixInLength H bodyTree xs'.size
      else
        let subs := Node.subtreesForListComposite H t xs'.toList
        let chunks := subs.map (Node.rootOf H)
        let bodyTree := Node.ofProgressive H chunks
        Node.mixInLength H bodyTree xs'.size
  | .progressiveBitlist, bs =>
      let bs' : Array Bool := bs
      let bv : BitVec bs'.size := BitVec.ofNat bs'.size (bitsToNatLE bs'.toList)
      let bytes := SSZType.serialize (.bitvector bs'.size) bv
      let bodyTree := Node.ofProgressive H (chunkify bytes)
      Node.mixInLength H bodyTree bs'.size
  | .progressiveContainer active fs, vs =>
      -- The field sub-trees stay in the tree, so `sszUpdate` can write
      -- below one field at its `progressiveFieldBits` path.
      let subs := Node.subtreesForFields H fs vs
      let body := Node.ofProgressiveSubtrees H (placeActiveSubtrees active subs)
      Node.mixInActiveFields H body active

/-- Per-field sub-trees for a `container fs` value. Mirrors the
spec's `hashTreeRootFields` (lines 450–458 of `HashTreeRoot.lean`)
arm-for-arm. -/
def Node.subtreesForFields (H : Type) [Hasher H] :
    (fs : List SSZType) → SSZType.interpFields fs → List Node
  | [],      _  => []
  | t :: ts, vs =>
      Node.ofShape H t vs.1 :: Node.subtreesForFields H ts vs.2

/-- Per-element sub-trees for a composite-element `vector` /
`list`. Mirrors `hashTreeRootListComposite`.

Tail-recursive over the element list (the `deserializeFixedElems`
accumulator pattern): the plain `ofShape … :: subtrees …` spelling
holds a frame per element and overflows the OS stack for the large
mainnet lists (`pendingConsolidations` at 262144 elements). The
accumulator form is constant-stack; the base case reverses it, so the
sub-tree order is unchanged. `acc` defaults to `[]` so call sites pass
only `(t, elems)`. -/
def Node.subtreesForListComposite (H : Type) [Hasher H] :
    (t : SSZType) → List t.interp → (acc : List Node := []) → List Node
  | _, [],      acc => acc.reverse
  | t, x :: xs, acc =>
      Node.subtreesForListComposite H t xs (Node.ofShape H t x :: acc)

end

end SizzLean.Cache.MerkleTree
