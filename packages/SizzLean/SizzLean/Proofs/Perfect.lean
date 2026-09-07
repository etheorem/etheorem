import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Cache.MerkleTree.Build
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

/-- `Node.merkleRoot` on a leaf returns the leaf bytes. Local alias for
`Node.merkleRoot_leaf`, which sits beside the definition. -/
theorem merkleRoot_leaf (H : Type) [Hasher H] (b : ByteArray) :
    Node.merkleRoot H (.leaf b) = b := Node.merkleRoot_leaf H b

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

/-- The `zeroLeaf` pad's root is 32 bytes. `hzero` supplies the width through
`merkleRoot_size`. -/
theorem rootOf_zeroLeaf_size_of_isPerfect (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero : ∀ d, IsPerfect H (zeroLeaf H d) d) (d : Nat) :
    (Node.rootOf H (zeroLeaf H d)).size = 32 := by
  rw [rootOf_eq_merkleRoot]
  exact merkleRoot_size H (hzero d)

/-! ### Trees the builders produce -/

/-- The `hc` obligation for a node the builders cached honestly. Every
constructor in `Cache/MerkleTree/Build.lean` fills the slot with
`combine (rootOf l) (rootOf r)`, which `rootOf_eq_merkleRoot` turns into
`combine (merkleRoot l) (merkleRoot r)`. -/
theorem cached_root_honest (H : Type) [Hasher H] (l r : Node) :
    ∀ root,
      some (Hasher.combine (H := H) (Node.rootOf H l) (Node.rootOf H r)) = some root →
        root = Hasher.combine (H := H) (Node.merkleRoot H l) (Node.merkleRoot H r) := by
  intro root heq
  rw [Option.some.injEq] at heq
  rw [← heq]
  simp only [rootOf_eq_merkleRoot]

/-- `zeroLeaf` trees are perfect for any hasher whose `combine` agrees with the
FFI `sha256Combine` that populated the memo. `hcomb` is `rfl` for `Sha256`.

**Axiom use**: inherits `sha256Combine_eq_spec` (`Hasher/Sha256Equiv.lean`)
through `zeroHashAt_size`, at every hasher. -/
theorem zeroLeaf_isPerfect_of_combine (H : Type) [Hasher H]
    (hcomb : ∀ a b, Hasher.combine (H := H) a b = LeanHazmat.Sha256.sha256Combine a b) :
    ∀ (d : Nat), IsPerfect H (zeroLeaf H d) d := by
  intro d
  induction d with
  | zero =>
      rw [zeroLeaf_zero]
      exact .leaf _ (zeroHashAt_size H 0)
  | succ k ih =>
      have hkp : IsPerfect H (zeroLeaf H k) k := ih
      -- The depth-`k` zero subtree's root is the table entry, carried by the
      -- leaf's own bytes or by the pair's pre-filled cache slot.
      have hroot : Node.merkleRoot H (zeroLeaf H k) = zeroHashAt H k := by
        cases k with
        | zero => rw [zeroLeaf_zero, merkleRoot_leaf]
        | succ j =>
            rw [zeroLeaf_succ, Node.merkleRoot_pair_some]
      rw [zeroLeaf_succ]
      refine .pair hkp hkp ?_
      intro root heq
      rw [Option.some.injEq] at heq
      rw [← heq, hroot, hcomb, zeroHashAt_succ H k]

/-- `zeroLeaf` perfection at `Sha256`, where `combine` is `sha256Combine` and
`hcomb` is `rfl`. Discharges the `hzero` hypothesis the padded-tree theorems
carry.

**Axiom use**: inherits `sha256Combine_eq_spec` (`Hasher/Sha256Equiv.lean`)
through `zeroHashAt_size`. -/
theorem zeroLeaf_isPerfect_sha256 (d : Nat) :
    IsPerfect Sha256 (zeroLeaf Sha256 d) d :=
  zeroLeaf_isPerfect_of_combine Sha256 (fun _ _ => rfl) d

/-- Every `ofSubtrees` tree has a 32-byte root, given its sub-trees do. Interior
levels are `combine` outputs, 32 by `CombineWidth32`. Depth 0 is either a
supplied sub-tree or the `zeroLeaf` pad, whose width comes from `hzero`. A single
`cases` on the depth, no induction. -/
theorem merkleRoot_ofSubtrees_size (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero : ∀ d, IsPerfect H (zeroLeaf H d) d) :
    ∀ (depth : Nat) (subs : List Node),
      (∀ s ∈ subs, (Node.rootOf H s).size = 32) →
      (Node.merkleRoot H (Node.ofSubtrees H subs depth)).size = 32 := by
  intro depth subs hsz
  cases depth with
  | zero =>
      cases subs with
      | nil => exact merkleRoot_size H (hzero 0)
      | cons s tl =>
          rw [show Node.ofSubtrees H (s :: tl) 0 = s from rfl, ← rootOf_eq_merkleRoot]
          exact hsz s (by simp)
  | succ d =>
      unfold Node.ofSubtrees
      simp only [List.splitAt_eq]
      rw [merkleRoot_pair H (cached_root_honest H _ _)]
      exact CombineWidth32.size _ _

end SizzLean.Cache.MerkleTree
