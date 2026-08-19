import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Hasher.CombineWidth

/-!
# `SizzLean.Proofs.Perfect`: perfect combine-trees

The tree-shape vocabulary Merkle-proof theorems quantify over. `IsPerfect` says a
`Node` is a perfect binary combine-tree of a given depth under a hasher. Three
shape facts follow. `merkleRoot_pair` collapses the cached and uncached readings
of a pair. `rootOf_eq_merkleRoot` licenses reading any cache observation as the
honest root. `merkleRoot_size` gives every root in such a tree 32 bytes.

The path vocabulary sits one layer up, in `EthCLLib.Proofs.MerkleOpening`.
`IsOpenable`, `leafAt` and `siblingPath` all route by a convention that
`is_valid_merkle_branch` owns, and that check is a consensus-spec function rather
than an SSZ-document one. SizzLean therefore states shape and width, and the
framework states openings.

Pure `Node` vocabulary, hasher-generic. The declarations sit in the
`SizzLean.Cache.MerkleTree` namespace, where `Node` and the cache walkers live,
while the file sits under `SizzLean/Proofs/`.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

open SizzLean.Hasher

/-- A `Node` that is a *perfect* binary combine-tree of depth `d` under hasher
`H`. Leaves at depth `0` carry exactly 32 bytes. Interior nodes at depth `d+1`
are pairs of depth-`d` perfect subtrees whose cache slot, *if populated*, holds
the honest `combine` of the children's roots.

The cache-validity side condition (`hc`) lets these theorems reach cached trees.
For an uncached pair (`c = none`) `hc` is vacuous. For a cached pair it pins the
stored root to `combine (merkleRoot H l) (merkleRoot H r)`, the value
`merkleRootWithCache` computes. `Node.merkleRoot` therefore agrees either way
(`merkleRoot_pair`).

Two shapes fall outside the predicate. A `zeroLeaf`-padded subtree caches
Sha256-specific zero-hash bytes, so it meets `hc` only for that hasher.
`Node.mixInLength` pairs a depth-`d` subtree with a depth-0 length leaf. Above
`d = 0` its two children sit at different depths, so it is not `IsPerfect`. At
`d = 0` both children are depth-0 leaves and it is, which nothing here depends
on.

The hasher `H` is a parameter because the invariant refers to
`Node.merkleRoot H`. -/
inductive IsPerfect (H : Type) [Hasher H] : Node → Nat → Prop where
  | leaf (b : ByteArray) (hsz : b.size = 32) : IsPerfect H (.leaf b) 0
  | pair {l r : Node} {d : Nat} {c : Option ByteArray}
      (hl : IsPerfect H l d) (hr : IsPerfect H r d)
      (hc : ∀ root, c = some root →
        root = Hasher.combine (H := H) (Node.merkleRoot H l) (Node.merkleRoot H r)) :
      IsPerfect H (.pair l r c) (d + 1)

/-- The root of a valid perfect pair is the honest `combine` of the children's
roots, at a populated cache slot and an empty one alike. For `none` this is
`merkleRootWithCache`'s own recursion. For `some root` the cache-validity witness
`hc` pins the stored value.

The tree-walking proofs go through this bridge instead of unfolding
`merkleRootWithCache` on an uncached node. They therefore apply unchanged to the
cached trees the constructors emit. -/
theorem merkleRoot_pair (H : Type) [Hasher H] {l r : Node} {c : Option ByteArray}
    (hc : ∀ root, c = some root →
      root = Hasher.combine (H := H) (Node.merkleRoot H l) (Node.merkleRoot H r)) :
    Node.merkleRoot H (.pair l r c)
      = Hasher.combine (H := H) (Node.merkleRoot H l) (Node.merkleRoot H r) := by
  cases c with
  | none => exact Node.merkleRoot_pair_none H l r
  | some root =>
      rw [Node.merkleRoot_pair_some H l r root]
      exact hc root rfl

/-- `Node.rootOf` agrees with `Node.merkleRoot` on **every** `Node`, with no
shape or cache-validity hypothesis: the two are the same structural recursion.
Neither inspects whether a populated cache slot is honest, so this holds for a
tree carrying poisoned caches too, both read the same poison.

Both walkers are `@[irreducible]`, since unfolding either in a tactic walks a
real 262144-leaf tree. Every arm therefore enters by its named equation lemma,
and not by `simp [Node.rootOf]` or `simp [Node.merkleRoot]`. -/
theorem rootOf_eq_merkleRoot (H : Type) [Hasher H] (n : Node) :
    Node.rootOf H n = Node.merkleRoot H n := by
  induction n with
  | leaf b => rw [Node.rootOf_leaf, Node.merkleRoot_leaf]
  | pair l r c ihl ihr =>
      cases c with
      | some x => rw [Node.rootOf_pair_some, Node.merkleRoot_pair_some]
      | none =>
          rw [Node.rootOf_pair_none, Node.merkleRoot_pair_none, ihl, ihr]

/-- Every root in a perfect tree is 32 bytes. Leaves are 32 by `IsPerfect.leaf`.
Interior nodes are `combine` outputs, 32 by the `CombineWidth32` contract. The
proof reaches that contract through `merkleRoot_pair`, which covers a cached pair
and an uncached one alike.

The contract arrives as a `[CombineWidth32 H]` instance, so this theorem
introduces no axiom of its own. An instantiation costs whatever the supplied
instance rests on (see `SizzLean/Hasher/Class.lean`). -/
theorem merkleRoot_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ {n : Node} {depth : Nat}, IsPerfect H n depth →
      (Node.merkleRoot H n).size = 32 := by
  intro n depth hp
  induction hp with
  | leaf b hsz => simpa [Node.merkleRoot_leaf] using hsz
  | @pair l r d c hl hr hc ihl ihr =>
      rw [merkleRoot_pair H hc]
      exact CombineWidth32.size _ _

end SizzLean.Cache.MerkleTree
