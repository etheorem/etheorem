import SizzLean.Spec.HashTreeRoot
import SizzLean.Cache.MerkleTree.Build
import SizzLean.Proofs.Merkle.Naive
import SizzLean.Proofs.Merkle.Zero
import SizzLean.Proofs.Merkle.Coherent
import SizzLean.Proofs.Merkle.Chunk

/-!
# `SizzLean.Proofs.Merkle.Build`: the builders agree with the spec

Three cache-side builders construct the trees the shape walker
`Node.ofShape` assembles, and each has a spec-side counterpart:

* `Node.ofLeaves` pads a chunk list with zero subtrees and combines
  depth-first, which is `naiveRoot` with `zeroLeaf` padding.
* `Node.ofSubtrees` does the same over already-built sub-trees, so
  its leaf list is the sub-trees' own structural roots.
* `Node.mixInLength` wraps a tree with the length chunk, the
  cache-side `Spec.mixInLength`.

For every builder this file proves the structural root agrees with
the spec root, and the builder preserves `Coherent`. The two
statements are proved in separate inductions: coherence needs no
fit bound, and the root induction reuses it (`rootOf_eq_root`) to
turn each filled slot into the `pair_some` shape.
Lean idiom, annotated once: every `Hasher.combine` here takes the
explicit `(H := H)`. `Hasher`'s parameter is a phantom tag the
method's types do not mention, so instance synthesis cannot recover
it from the value arguments.

Everything rests on the zero tower (`Proofs/Merkle/Zero.lean`: the
cache and spec towers agree, and both are the empty naive tree) and
on the fold agreement (`merkleize_eq_naiveRoot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec
open SizzLean.Cache.MerkleTree (Node zeroLeaf rootOf_eq_root)

/-! ### The zero leaf -/

/-- The padding leaf's structural root is the spec's zero tower.
Induction on `d`; the interior step pairs two copies of the depth-`d`
leaf, so the root is the tower's own recurrence. -/
theorem zeroLeaf_root (H : Type) [Hasher H] :
    ∀ d : Nat, (zeroLeaf H d).root H = Spec.zeroHashAt H d := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      show SizzLean.Hasher.combine (H := H) (Node.root H (zeroLeaf H d))
            (Node.root H (zeroLeaf H d)) = _
      rw [ih, Spec.zeroHashAt]

/-- The padding leaf is coherent: its pre-filled slot is the
depth-`d + 1` tower, which is the two children's roots combined. -/
theorem zeroLeaf_coherent (H : Type) [Hasher H] :
    ∀ d : Nat, (zeroLeaf H d).Coherent H := by
  intro d
  induction d with
  | zero => exact Node.Coherent.leaf zero32
  | succ d ih =>
      show Node.Coherent H (Node.pair (zeroLeaf H d) (zeroLeaf H d)
        (some (SizzLean.Cache.MerkleTree.zeroHashAt H (d + 1))))
      have hz : SizzLean.Cache.MerkleTree.zeroHashAt H (d + 1)
          = SizzLean.Hasher.combine (H := H)
              (Node.root H (zeroLeaf H d)) (Node.root H (zeroLeaf H d)) := by
        rw [cache_zeroHashAt_eq_spec, zeroLeaf_root H d, Spec.zeroHashAt]
      rw [hz]
      exact Node.Coherent.pair_some ih ih

/-! ### One naive-tree step, stated over `take` / `drop` -/

/-- One naive-tree step at the chunk level: split at `2 ^ d`,
recurse into the halves. `splitAt` and `take` / `drop` are the same
split (`List.splitAt_eq`), so the statement is over `take` / `drop`,
where it holds for every list shape: an empty or one-element `ls`
takes the empty-respectively-promote arm on both sides alike. -/
theorem naiveRootAt_succ (H : Type) [Hasher H] (ls : List ByteArray) (d : Nat) :
    naiveRootAt H ls 0 (d + 1)
      = SizzLean.Hasher.combine (H := H)
          (naiveRootAt H (ls.take (2 ^ d)) 0 d)
          (naiveRootAt H (ls.drop (2 ^ d)) 0 d) := by
  match ls with
  | [] =>
      rw [naiveRootAt.eq_2, List.take_nil, List.drop_nil]
  | [c] =>
      have h1 : List.length [c] ≤ 2 ^ d := by
        have := Nat.one_le_two_pow (n := d)
        simpa using this
      rw [naiveRootAt.eq_4, List.splitAt_eq]
      simp
  | c :: e :: rs =>
      simp only [naiveRootAt.eq_4, List.splitAt_eq]

/-! ### `Node.ofLeaves` -/

/-- The chunk builder preserves coherence, for every list, with no
fit bound: the filled slot is the children's `rootOf`, which agrees
with their structural root by the children's own coherence. -/
theorem ofLeaves_coherent (H : Type) [Hasher H] :
    ∀ (d : Nat) (ls : List ByteArray), (Node.ofLeaves H ls d).Coherent H := by
  intro d
  induction d with
  | zero =>
      intro ls
      match ls with
      | [] => exact Node.Coherent.leaf _
      | _ :: _ => exact Node.Coherent.leaf _
  | succ d ih =>
      intro ls
      rw [Node.ofLeaves]
      simp only [List.splitAt_eq]
      by_cases hr : (ls.drop (2 ^ d)).isEmpty
      · rw [if_pos hr, rootOf_eq_root (ih _), rootOf_eq_root (zeroLeaf_coherent H d)]
        exact Node.Coherent.pair_some (ih _) (zeroLeaf_coherent H d)
      · rw [if_neg hr, rootOf_eq_root (ih _), rootOf_eq_root (ih _)]
        exact Node.Coherent.pair_some (ih _) (ih _)

/-- The chunk builder's root is the naive tree over the same
leaves. Induction on `d`; the empty-right-half case pads with the
depth-`d` zero leaf, whose root is the empty naive tree's root, the
zero tower. -/
theorem ofLeaves_naiveRoot (H : Type) [Hasher H] :
    ∀ (d : Nat) (ls : List ByteArray), ls.length ≤ 2 ^ d →
      (Node.ofLeaves H ls d).root H = naiveRoot H ls d := by
  intro d
  induction d with
  | zero =>
      intro ls h
      have h1 : ls.length ≤ 1 := by simpa using h
      match ls, h1 with
      | [], _ =>
          show Node.root H (zeroLeaf H 0) = naiveRoot H ([] : List ByteArray) 0
          rw [zeroLeaf, Node.root, cache_zero32_eq_spec, naiveRoot,
            naiveRootAt.eq_1, naiveZero_eq_zeroHashAt, Spec.zeroHashAt]
      | [l], _ =>
          show Node.root H (Node.leaf l) = naiveRoot H [l] 0
          rw [naiveRoot, naiveRootAt.eq_3 H _ 0 (by simp),
            List.head?_cons, Option.getD_some, Node.root]
  | succ d ih =>
      intro ls h
      rw [Nat.pow_succ] at h
      have hL : (ls.take (2 ^ d)).length ≤ 2 ^ d := by
        rw [List.length_take]
        exact Nat.min_le_left _ _
      have hRlen : (ls.drop (2 ^ d)).length ≤ 2 ^ d := by
        rw [List.length_drop]
        omega
      by_cases hr : (ls.drop (2 ^ d)).isEmpty
      · -- Empty right half: the builder padded with the depth-`d`
        -- zero leaf, the naive tree's empty right child.
        have hd : ls.drop (2 ^ d) = [] := by
          rw [List.isEmpty_iff] at hr
          exact hr
        have e : Node.ofLeaves H ls (d + 1)
            = Node.pair (Node.ofLeaves H (ls.take (2 ^ d)) d) (zeroLeaf H d)
                (some (SizzLean.Hasher.combine (H := H)
                  (Node.rootOf H (Node.ofLeaves H (ls.take (2 ^ d)) d))
                  (Node.rootOf H (zeroLeaf H d)))) := by
          rw [Node.ofLeaves]
          simp only [List.splitAt_eq]
          rw [if_pos hr]
        rw [e, Node.root, naiveRoot, naiveRootAt_succ, hd,
          naiveRootAt_nil, Nat.zero_add, ih _ hL, zeroLeaf_root H d]
        rfl
      · -- Both halves non-trivial: the induction hypothesis twice.
        have e : Node.ofLeaves H ls (d + 1)
            = Node.pair (Node.ofLeaves H (ls.take (2 ^ d)) d)
                (Node.ofLeaves H (ls.drop (2 ^ d)) d)
                (some (SizzLean.Hasher.combine (H := H)
                  (Node.rootOf H (Node.ofLeaves H (ls.take (2 ^ d)) d))
                  (Node.rootOf H (Node.ofLeaves H (ls.drop (2 ^ d)) d)))) := by
          rw [Node.ofLeaves]
          simp only [List.splitAt_eq]
          rw [if_neg hr]
        rw [e, Node.root, naiveRoot, naiveRootAt_succ,
          ih _ hL, ih _ hRlen]
        rfl

/-- The chunk builder's root is the spec's merkleizer over the same
leaves: the naive-tree equation rewritten with the fold agreement. -/
theorem ofLeaves_root (H : Type) [Hasher H] (ls : List ByteArray) (d : Nat)
    (h : ls.length ≤ 2 ^ d) :
    (Node.ofLeaves H ls d).root H = Spec.merkleize H ls d :=
  (ofLeaves_naiveRoot H d ls h).trans (merkleize_eq_naiveRoot H ls d h).symm

/-! ### `Node.ofSubtrees` -/

/-- The sub-tree builder preserves coherence, given coherence of
every supplied sub-tree. -/
theorem ofSubtrees_coherent (H : Type) [Hasher H] :
    ∀ (d : Nat) (subs : List Node), (∀ s ∈ subs, s.Coherent H) →
      (Node.ofSubtrees H subs d).Coherent H := by
  intro d
  induction d with
  | zero =>
      intro subs hc
      match subs with
      | [] => exact zeroLeaf_coherent H 0
      | s :: _ => exact hc s (by simp [List.mem_cons])
  | succ d ih =>
      intro subs hc
      rw [Node.ofSubtrees]
      simp only [List.splitAt_eq]
      by_cases hr : (subs.drop (2 ^ d)).isEmpty
      · rw [if_pos hr,
          rootOf_eq_root (ih _ fun s hs => hc s (List.mem_of_mem_take hs)),
          rootOf_eq_root (zeroLeaf_coherent H d)]
        exact Node.Coherent.pair_some
          (ih _ fun s hs => hc s (List.mem_of_mem_take hs))
          (zeroLeaf_coherent H d)
      · rw [if_neg hr,
          rootOf_eq_root (ih _ fun s hs => hc s (List.mem_of_mem_take hs)),
          rootOf_eq_root (ih _ fun s hs => hc s (List.mem_of_mem_drop hs))]
        exact Node.Coherent.pair_some
          (ih _ fun s hs => hc s (List.mem_of_mem_take hs))
          (ih _ fun s hs => hc s (List.mem_of_mem_drop hs))

/-- The sub-tree builder's root is the naive tree over the supplied
sub-trees' own structural roots. Same induction as the chunk
builder; the leaf list is `subs.map (Node.root H)`, and `map`
distributes over `take` / `drop`. No coherence is needed: the root
equation never reads a cache slot. -/
theorem ofSubtrees_naiveRoot (H : Type) [Hasher H] :
    ∀ (d : Nat) (subs : List Node), subs.length ≤ 2 ^ d →
      (Node.ofSubtrees H subs d).root H
        = naiveRoot H (subs.map (Node.root H)) d := by
  intro d
  induction d with
  | zero =>
      intro subs h
      have h1 : subs.length ≤ 1 := by simpa using h
      match subs, h1 with
      | [], _ =>
          show Node.root H (zeroLeaf H 0)
              = naiveRoot H ([] : List ByteArray) 0
          rw [zeroLeaf, Node.root, cache_zero32_eq_spec, naiveRoot,
            naiveRootAt.eq_1, naiveZero_eq_zeroHashAt, Spec.zeroHashAt]
      | [s], _ =>
          show Node.root H s = naiveRoot H [Node.root H s] 0
          rw [naiveRoot, naiveRootAt.eq_3 H _ 0 (by simp),
            List.head?_cons, Option.getD_some]
  | succ d ih =>
      intro subs h
      rw [Nat.pow_succ] at h
      have hL : (subs.take (2 ^ d)).length ≤ 2 ^ d := by
        rw [List.length_take]
        exact Nat.min_le_left _ _
      have hR : (subs.drop (2 ^ d)).length ≤ 2 ^ d := by
        rw [List.length_drop]
        omega
      by_cases hr : (subs.drop (2 ^ d)).isEmpty
      · -- Empty right half: pad with the depth-`d` zero leaf.
        have hd : subs.drop (2 ^ d) = [] := by
          rw [List.isEmpty_iff] at hr
          exact hr
        have e : Node.ofSubtrees H subs (d + 1)
            = Node.pair (Node.ofSubtrees H (subs.take (2 ^ d)) d) (zeroLeaf H d)
                (some (SizzLean.Hasher.combine (H := H)
                  (Node.rootOf H (Node.ofSubtrees H (subs.take (2 ^ d)) d))
                  (Node.rootOf H (zeroLeaf H d)))) := by
          rw [Node.ofSubtrees]
          simp only [List.splitAt_eq]
          rw [if_pos hr]
        rw [e, Node.root, naiveRoot, naiveRootAt_succ, ← List.map_take,
          ← List.map_drop, hd, List.map_nil, naiveRootAt_nil, Nat.zero_add,
          ih _ hL, zeroLeaf_root H d]
        rfl
      · -- Both halves non-trivial: the induction hypothesis twice.
        have e : Node.ofSubtrees H subs (d + 1)
            = Node.pair (Node.ofSubtrees H (subs.take (2 ^ d)) d)
                (Node.ofSubtrees H (subs.drop (2 ^ d)) d)
                (some (SizzLean.Hasher.combine (H := H)
                  (Node.rootOf H (Node.ofSubtrees H (subs.take (2 ^ d)) d))
                  (Node.rootOf H (Node.ofSubtrees H (subs.drop (2 ^ d)) d)))) := by
          rw [Node.ofSubtrees]
          simp only [List.splitAt_eq]
          rw [if_neg hr]
        rw [e, Node.root, naiveRoot, naiveRootAt_succ, ← List.map_take,
          ← List.map_drop, ih _ hL, ih _ hR]
        rfl

/-- The sub-tree builder's root is the spec's merkleizer over the
sub-trees' roots, for a list that fits the depth: the naive-tree
equation rewritten with the fold agreement. -/
theorem ofSubtrees_root (H : Type) [Hasher H] (subs : List Node) (d : Nat)
    (h : subs.length ≤ 2 ^ d) :
    (Node.ofSubtrees H subs d).root H = Spec.merkleize H (subs.map (Node.root H)) d :=
  (ofSubtrees_naiveRoot H d subs h).trans
    (merkleize_eq_naiveRoot H (subs.map (Node.root H)) d (by
      rw [List.length_map]; exact h)).symm

/-! ### `Node.mixInLength` -/

/-- The mix-in wrapper's structural root is the spec's mix-in over
the wrapped tree's structural root, and the wrapper is coherent
when the wrapped tree is. -/
theorem mixInLength_root_coherent (H : Type) [Hasher H] (n : Node) (count : Nat)
    (hc : n.Coherent H) :
    (Node.mixInLength H n count).root H = Spec.mixInLength H (n.root H) count
      ∧ (Node.mixInLength H n count).Coherent H := by
  have e : Node.mixInLength H n count
      = Node.pair n (Node.leaf (Spec.natToChunk count))
          (some (SizzLean.Hasher.combine (H := H)
            (Node.rootOf H n)
            (Node.rootOf H (Node.leaf (Spec.natToChunk count))))) := rfl
  rw [e, Node.root, rootOf_eq_root hc, rootOf_eq_root (Node.Coherent.leaf _)]
  exact ⟨rfl, Node.Coherent.pair_some hc (Node.Coherent.leaf _)⟩

/-- The mix-in wrapper's structural root is the spec's mix-in. -/
theorem mixInLength_root (H : Type) [Hasher H] (n : Node) (count : Nat)
    (hc : n.Coherent H) :
    (Node.mixInLength H n count).root H = Spec.mixInLength H (n.root H) count :=
  (mixInLength_root_coherent H n count hc).1

end SizzLean.Proofs.Merkle
