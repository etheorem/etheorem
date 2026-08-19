import SizzLean.Cache.MerkleTree.Build
import SizzLean.Proofs.Perfect

/-!
# `SizzLean.Proofs.Merkleize`: the spec merkleizer builds the cache tree

`Spec.merkleize` is breadth-first. It folds one whole layer at a time with
`combineLayerAt`, pads an odd tail with the level's zero hash, and
short-circuits a singleton. `Node.ofLeaves` is
depth-first: split at `2 ^ d`, recurse, pad the right with `zeroLeaf`. This file
proves the two agree.

Hasher-generic, under one hypothesis: that the cache layer's zero tower and the
spec's agree (`hzt`). The two towers are different functions, a
Sha256-specific memo against an `H`-generic recurrence, so the agreement cannot
be free. `ShapeAgreement.lean` discharges it for both concrete hashers.

Proof-only, and re-exported from `SizzLean.lean` alongside `Proofs/Perfect` and
`Proofs/ShapeWidth`. `EthCLSpecs` imports the agreement results built on it, and
a `Proofs/` module off the root never reaches the shared object.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

open SizzLean.Hasher
open SizzLean.Spec

/-- `Node.ofLeaves` with a level offset: identical to it except the right-hand
padding is a `zeroLeaf` at `lvl + d` rather than at `d`.

Proof-local. It exists only to give the BFS induction a DFS counterpart whose
padding tracks `combineLayerAt`'s `curLvl`. `ofLeavesAt_zero` collapses it back
to `Node.ofLeaves` at the end. -/
private def ofLeavesAt (H : Type) [Hasher H] (leaves : List ByteArray)
    (depth : Nat) (lvl : Nat) : Node :=
  match depth, leaves with
  | 0,     []      => zeroLeaf H lvl
  | 0,     l :: _  => .leaf l
  | d + 1, ls      =>
      let (leftLeaves, rightLeaves) := ls.splitAt (2 ^ d)
      let leftNode := ofLeavesAt H leftLeaves d lvl
      let rightNode :=
        if rightLeaves.isEmpty then zeroLeaf H (lvl + d)
        else ofLeavesAt H rightLeaves d lvl
      .pair leftNode rightNode
        (some (Hasher.combine (H := H) (Node.rootOf H leftNode) (Node.rootOf H rightNode)))

/-- At offset 0 the builder is `Node.ofLeaves` itself. Structural induction on
`depth`, generalising the leaf list because the recursive calls change it. -/
private theorem ofLeavesAt_zero (H : Type) [Hasher H] :
    ∀ (depth : Nat) (leaves : List ByteArray),
      ofLeavesAt H leaves depth 0 = Node.ofLeaves H leaves depth := by
  intro depth
  induction depth with
  | zero => intro leaves; cases leaves <;> rfl
  | succ d ih =>
      intro leaves
      -- The rewrite needs `Nat.zero_add`. `ofLeavesAt`'s pad is
      -- `zeroLeaf H (0 + d)` where `ofLeaves`' is `zeroLeaf H d`.
      simp only [ofLeavesAt, Node.ofLeaves, List.splitAt_eq, Nat.zero_add, ih]

/-! ### Equations for the offset builder

`ofLeavesAt` matches on `depth` and `leaves` together and binds its halves with
`let`, so the raw definition does not rewrite comfortably. The three lemmas below
state its arms in the form the induction consumes. `splitAt` is already resolved
to `take`/`drop`, and the depth-`d+1` root already read out of the cache
slot. -/

private theorem ofLeavesAt_nil (H : Type) [Hasher H] (lvl : Nat) :
    ofLeavesAt H [] 0 lvl = zeroLeaf H lvl := rfl

private theorem ofLeavesAt_cons (H : Type) [Hasher H] (l : ByteArray) (ls : List ByteArray)
    (lvl : Nat) : ofLeavesAt H (l :: ls) 0 lvl = .leaf l := rfl

private theorem ofLeavesAt_succ (H : Type) [Hasher H] (ls : List ByteArray) (d lvl : Nat) :
    ofLeavesAt H ls (d + 1) lvl
      = .pair (ofLeavesAt H (ls.take (2 ^ d)) d lvl)
          (if (ls.drop (2 ^ d)).isEmpty then zeroLeaf H (lvl + d)
           else ofLeavesAt H (ls.drop (2 ^ d)) d lvl)
          (some (Hasher.combine (H := H)
            (Node.rootOf H (ofLeavesAt H (ls.take (2 ^ d)) d lvl))
            (Node.rootOf H
              (if (ls.drop (2 ^ d)).isEmpty then zeroLeaf H (lvl + d)
               else ofLeavesAt H (ls.drop (2 ^ d)) d lvl)))) := by
  simp only [ofLeavesAt, List.splitAt_eq]

/-- The workhorse. `ofLeavesAt` fills its cache slot at construction time, so
`rootOf` reads the combine straight out without descending. -/
private theorem rootOf_ofLeavesAt_succ (H : Type) [Hasher H] (ls : List ByteArray) (d lvl : Nat) :
    Node.rootOf H (ofLeavesAt H ls (d + 1) lvl)
      = Hasher.combine (H := H)
          (Node.rootOf H (ofLeavesAt H (ls.take (2 ^ d)) d lvl))
          (Node.rootOf H
            (if (ls.drop (2 ^ d)).isEmpty then zeroLeaf H (lvl + d)
             else ofLeavesAt H (ls.drop (2 ^ d)) d lvl)) := by
  rw [ofLeavesAt_succ, Node.rootOf_pair_some]

/-! ### `combineLayerAt` as a list operation

One BFS layer is a positional pairing. The DFS split needs three facts about it.
How long the result is, when it is empty, and how it commutes with `take` and
`drop` at half the index. Nothing here mentions `Node`. -/

/-- Two-at-a-time list induction. `combineLayerAt` consumes a pair per step, so
plain `List.rec` hands back an induction hypothesis about `y :: rs` where every
proof below needs one about `rs`. Stated once, over a fuel bound, and reused. -/
private theorem twoStepInduction {motive : List ByteArray → Prop}
    (hnil : motive []) (hone : ∀ x, motive [x])
    (hcons : ∀ x y rs, motive rs → motive (x :: y :: rs)) :
    ∀ ls, motive ls := by
  have key : ∀ (fuel : Nat) (ls : List ByteArray), ls.length ≤ fuel → motive ls := by
    intro fuel
    induction fuel with
    | zero =>
        intro ls h
        cases ls with
        | nil => exact hnil
        | cons a t => simp at h
    | succ m ih =>
        intro ls h
        match ls with
        | []  => exact hnil
        | [x] => exact hone x
        | x :: y :: rs =>
            exact hcons x y rs (ih rs (by simp only [List.length_cons] at h; omega))
  intro ls
  exact key ls.length ls (Nat.le_refl _)

/-- A layer is empty exactly when its input is. This is what lets the BFS and
DFS sides agree on the `isEmpty` guard that picks padding over recursion. -/
private theorem combineLayerAt_eq_nil_iff (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (ls : List ByteArray), combineLayerAt H lvl ls = [] ↔ ls = [] := by
  refine twoStepInduction ?_ ?_ ?_
  · simp [combineLayerAt_nil]
  · intro x; simp [combineLayerAt_singleton]
  · intro x y rs _; simp [combineLayerAt_cons₂]

private theorem combineLayerAt_isEmpty (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (ls : List ByteArray), (combineLayerAt H lvl ls).isEmpty = ls.isEmpty := by
  refine twoStepInduction ?_ ?_ ?_
  · simp [combineLayerAt_nil]
  · intro x; simp [combineLayerAt_singleton]
  · intro x y rs _; simp [combineLayerAt_cons₂]

/-- Pairing commutes with `take` at half the index: the first `2 * k` entries
form the first `k` pairs. -/
private theorem combineLayerAt_take (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (ls : List ByteArray) (k : Nat),
      combineLayerAt H lvl (ls.take (2 * k)) = (combineLayerAt H lvl ls).take k := by
  refine twoStepInduction ?_ ?_ ?_
  · intro k; simp [combineLayerAt_nil]
  · intro x k
    cases k with
    | zero => simp [combineLayerAt_nil]
    | succ j =>
        -- `2 * (j + 1)` is not syntactically a successor, so `take_succ_cons`
        -- fires only after the rewrite below puts it in that form.
        simp [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, combineLayerAt_singleton]
  · intro x y rs ih k
    cases k with
    | zero => simp [combineLayerAt_nil]
    | succ j =>
        simp only [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, List.take_succ_cons,
          combineLayerAt_cons₂, ih j]

/-- Pairing commutes with `drop` at half the index. -/
private theorem combineLayerAt_drop (H : Type) [Hasher H] (lvl : Nat) :
    ∀ (ls : List ByteArray) (k : Nat),
      combineLayerAt H lvl (ls.drop (2 * k)) = (combineLayerAt H lvl ls).drop k := by
  refine twoStepInduction ?_ ?_ ?_
  · intro k; simp [combineLayerAt_nil]
  · intro x k
    cases k with
    | zero => simp
    | succ j =>
        simp [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, combineLayerAt_singleton,
          combineLayerAt_nil]
  · intro x y rs ih k
    cases k with
    | zero => simp
    | succ j =>
        simp only [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, List.drop_succ_cons,
          combineLayerAt_cons₂, ih j]

/-! ### One BFS layer is one DFS level -/

/-- A non-empty list keeps a non-empty prefix. -/
private theorem take_ne_nil {ls : List ByteArray} (hls : ls ≠ []) (k : Nat) (hk : 0 < k) :
    ls.take k ≠ [] := by
  cases ls with
  | nil => exact absurd rfl hls
  | cons a t =>
      rw [show k = (k - 1) + 1 by omega, List.take_succ_cons]
      simp

/-- **The crux: one BFS layer is one DFS level.** Fold `combineLayerAt` over the
leaf list and build one level shallower at the next offset. That gives the same
root as building the original list one level deeper.

Stated for a **non-empty** list, and the empty case does not fold into it.
`Spec.merkleize` short-circuits an empty chunk list to a single tower lookup,
while `ofLeavesAt` keeps building real `pair` nodes down to its given depth.
`rootOf_ofLeavesAt_nil` below covers that case.

`hzt` enters in exactly one place, the `[x]` base case, where the BFS side pads
with `zeroHashAtDepth H lvl` and the DFS side with `Node.rootOf H (zeroLeaf H lvl)`.
Everywhere else the two pads are the same `zeroLeaf` term, because the offset was
chosen so that `lvl + (d + 1)` and `(lvl + 1) + d` coincide. -/
private theorem ofLeavesAt_layer (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d) :
    ∀ (depth : Nat) (ls : List ByteArray), ls ≠ [] → ∀ (lvl : Nat),
      Node.rootOf H (ofLeavesAt H ls (depth + 1) lvl)
        = Node.rootOf H (ofLeavesAt H (combineLayerAt H lvl ls) depth (lvl + 1)) := by
  intro depth
  induction depth with
  | zero =>
      intro ls hls lvl
      match ls with
      | []  => exact absurd rfl hls
      | [x] =>
          -- The lone leaf pairs with the level's zero pad on both sides.
          simp [rootOf_ofLeavesAt_succ, combineLayerAt_singleton, ofLeavesAt_cons,
            Node.rootOf_leaf, hzt]
      | x :: y :: rs =>
          -- Two real leaves: the DFS split puts `x` left and `y` right, which is
          -- the pair `combineLayerAt` produces. No padding, so no `hzt`.
          simp [rootOf_ofLeavesAt_succ, combineLayerAt_cons₂, ofLeavesAt_cons,
            Node.rootOf_leaf]
  | succ d ih =>
      intro ls hls lvl
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      have hpos : 0 < 2 ^ (d + 1) := Nat.two_pow_pos _
      have htake : (combineLayerAt H lvl ls).take (2 ^ d)
          = combineLayerAt H lvl (ls.take (2 ^ (d + 1))) := by
        rw [hpow, combineLayerAt_take]
      have hdrop : (combineLayerAt H lvl ls).drop (2 ^ d)
          = combineLayerAt H lvl (ls.drop (2 ^ (d + 1))) := by
        rw [hpow, combineLayerAt_drop]
      -- Both expansions take explicit arguments. A bare rewrite would fire on
      -- the freshly exposed left child instead of the right-hand side.
      rw [rootOf_ofLeavesAt_succ H ls (d + 1) lvl,
        rootOf_ofLeavesAt_succ H (combineLayerAt H lvl ls) d (lvl + 1),
        htake, hdrop,
        ih (ls.take (2 ^ (d + 1))) (take_ne_nil hls _ hpos) lvl,
        combineLayerAt_isEmpty,
        show lvl + 1 + d = lvl + (d + 1) by omega]
      -- Both `if`s now test the same condition and pad with the same term.
      by_cases hemp : ls.drop (2 ^ (d + 1)) = []
      · simp [hemp]
      · rw [if_neg (by simp [hemp]), if_neg (by simp [hemp]),
          ih (ls.drop (2 ^ (d + 1))) hemp lvl]

/-! ### `merkleizeAt`'s four arms, and the core theorem -/

-- `merkleizeAt`'s termination is structural on `remaining`, so the compiled
-- matcher splits on it first and neither of these reduces while it is a
-- variable. Casing it makes both arms fire.
private theorem merkleizeAt_nil (H : Type) [Hasher H] (lvl remaining : Nat) :
    merkleizeAt H [] lvl remaining = zeroHashAtDepth H remaining := by
  cases remaining <;> rfl

private theorem merkleizeAt_singleton (H : Type) [Hasher H] (c : ByteArray) (lvl remaining : Nat) :
    merkleizeAt H [c] lvl remaining = promoteThroughZeros H c lvl remaining := by
  cases remaining <;> rfl

/-- The defensive arm: more than one chunk with no levels left to build. The
spec's own merkleizer asserts `count <= limit` before it starts. The pyspec would
therefore refuse this state, and it has no defined answer. -/
private theorem merkleizeAt_multi_zero (H : Type) [Hasher H]
    (x y : ByteArray) (rs : List ByteArray) (lvl : Nat) :
    merkleizeAt H (x :: y :: rs) lvl 0 = x := rfl

private theorem merkleizeAt_multi_succ (H : Type) [Hasher H]
    (x y : ByteArray) (rs : List ByteArray) (lvl k : Nat) :
    merkleizeAt H (x :: y :: rs) lvl (k + 1)
      = merkleizeAt H (combineLayerAt H lvl (x :: y :: rs)) (lvl + 1) k := rfl

/-- The singleton short-circuit agrees with the builder. `merkleizeAt` sends a
one-element list straight to `promoteThroughZeros`. The builder still descends,
putting the single leaf on the far left and a `zeroLeaf` pad on every right.

This needs no depth bound. `promoteThroughZeros` pads with the zero hash *of the
level it is at*. The builder pads with that same term, so the tower recurrence
never comes up. -/
private theorem promoteThroughZeros_eq_ofLeavesAt (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d) :
    ∀ (remaining : Nat) (c : ByteArray) (lvl : Nat),
      promoteThroughZeros H c lvl remaining
        = Node.rootOf H (ofLeavesAt H [c] remaining lvl) := by
  intro remaining
  induction remaining with
  | zero =>
      intro c lvl
      rw [promoteThroughZeros_zero, ofLeavesAt_cons, Node.rootOf_leaf]
  | succ k ih =>
      intro c lvl
      rw [promoteThroughZeros_succ, ih, ← combineLayerAt_singleton H lvl c]
      exact (ofLeavesAt_layer H hzt k [c] (by simp) lvl).symm

/-- **The spec merkleizer builds the cache tree**, for a non-empty chunk list.
Induction on `remaining`, casing `cs` to match `merkleizeAt`'s three arms. The
singleton arm is the lemma above. The multi-chunk arm is one layer plus the
induction hypothesis. The defensive depth-0 arm holds because the builder also
keeps only the head at depth 0. -/
private theorem merkleizeAt_eq_ofLeavesAt (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d) :
    ∀ (remaining : Nat) (cs : List ByteArray), cs ≠ [] → ∀ (lvl : Nat),
      merkleizeAt H cs lvl remaining
        = Node.rootOf H (ofLeavesAt H cs remaining lvl) := by
  intro remaining
  induction remaining with
  | zero =>
      intro cs hcs lvl
      match cs with
      | []  => exact absurd rfl hcs
      | [c] =>
          rw [merkleizeAt_singleton, promoteThroughZeros_zero, ofLeavesAt_cons,
            Node.rootOf_leaf]
      | x :: y :: rs =>
          rw [merkleizeAt_multi_zero, ofLeavesAt_cons, Node.rootOf_leaf]
  | succ k ih =>
      intro cs hcs lvl
      match cs with
      | []  => exact absurd rfl hcs
      | [c] => rw [merkleizeAt_singleton, promoteThroughZeros_eq_ofLeavesAt H hzt]
      | x :: y :: rs =>
          have hne : combineLayerAt H lvl (x :: y :: rs) ≠ [] := by
            simp [combineLayerAt_eq_nil_iff]
          rw [merkleizeAt_multi_succ, ih _ hne (lvl + 1)]
          exact (ofLeavesAt_layer H hzt k (x :: y :: rs) (by simp) lvl).symm

/-- The empty chunk list: `merkleizeAt` returns one tower lookup, the builder
returns a genuine tower, and the two are the same value at every depth. -/
private theorem rootOf_ofLeavesAt_nil (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d) :
    ∀ (remaining lvl : Nat),
      Node.rootOf H (ofLeavesAt H [] remaining lvl) = zeroHashAtDepth H (lvl + remaining) := by
  intro remaining
  induction remaining with
  | zero => intro lvl; rw [ofLeavesAt_nil, hzt, Nat.add_zero]
  | succ k ih =>
      intro lvl
      rw [rootOf_ofLeavesAt_succ, List.take_nil, List.drop_nil,
        if_pos (by simp : ([] : List ByteArray).isEmpty = true),
        ih lvl, hzt (lvl + k),
        show lvl + (k + 1) = (lvl + k) + 1 by omega,
        zeroHashAtDepth_succ H (lvl + k)]

/-- **`merkleize` is the cache builder.** `merkleize` of a chunk list is the root
of the tree `Node.ofLeaves` builds from it, at every depth. -/
theorem merkleize_eq_ofLeaves (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d)
    (cs : List ByteArray) (depth : Nat) :
    merkleize H cs depth = Node.rootOf H (Node.ofLeaves H cs depth) := by
  rw [merkleize_eq_merkleizeAt, ← ofLeavesAt_zero]
  by_cases hcs : cs = []
  · subst hcs
    rw [merkleizeAt_nil, rootOf_ofLeavesAt_nil H hzt depth 0, Nat.zero_add]
  · exact merkleizeAt_eq_ofLeavesAt H hzt depth cs hcs 0

/-! ### The two structural helpers the shape arms need -/

theorem ofSubtrees_succ (H : Type) [Hasher H] (subs : List Node) (d : Nat) :
    Node.ofSubtrees H subs (d + 1)
      = .pair (Node.ofSubtrees H (subs.take (2 ^ d)) d)
          (if (subs.drop (2 ^ d)).isEmpty then zeroLeaf H d
           else Node.ofSubtrees H (subs.drop (2 ^ d)) d)
          (some (Hasher.combine (H := H)
            (Node.rootOf H (Node.ofSubtrees H (subs.take (2 ^ d)) d))
            (Node.rootOf H
              (if (subs.drop (2 ^ d)).isEmpty then zeroLeaf H d
               else Node.ofSubtrees H (subs.drop (2 ^ d)) d)))) := by
  simp only [Node.ofSubtrees, List.splitAt_eq]

private theorem rootOf_ofSubtrees_succ (H : Type) [Hasher H] (subs : List Node) (d : Nat) :
    Node.rootOf H (Node.ofSubtrees H subs (d + 1))
      = Hasher.combine (H := H)
          (Node.rootOf H (Node.ofSubtrees H (subs.take (2 ^ d)) d))
          (Node.rootOf H
            (if (subs.drop (2 ^ d)).isEmpty then zeroLeaf H d
             else Node.ofSubtrees H (subs.drop (2 ^ d)) d)) := by
  rw [ofSubtrees_succ, Node.rootOf_pair_some]

private theorem rootOf_ofLeaves_succ (H : Type) [Hasher H] (ls : List ByteArray) (d : Nat) :
    Node.rootOf H (Node.ofLeaves H ls (d + 1))
      = Hasher.combine (H := H)
          (Node.rootOf H (Node.ofLeaves H (ls.take (2 ^ d)) d))
          (Node.rootOf H
            (if (ls.drop (2 ^ d)).isEmpty then zeroLeaf H d
             else Node.ofLeaves H (ls.drop (2 ^ d)) d)) := by
  rw [← ofLeavesAt_zero, rootOf_ofLeavesAt_succ]
  simp only [Nat.zero_add, ofLeavesAt_zero]

/-- Composite arms merkleize a list of sub-tree *roots*, so they need the builder
over sub-trees rather than over leaves. The two builders share the split-at-`2^d`
shape, so this is `List.map` commuting with `take`, `drop` and `isEmpty`. -/
theorem rootOf_ofSubtrees_eq_ofLeaves (H : Type) [Hasher H] :
    ∀ (depth : Nat) (subs : List Node),
      Node.rootOf H (Node.ofSubtrees H subs depth)
        = Node.rootOf H (Node.ofLeaves H (subs.map (Node.rootOf H)) depth) := by
  intro depth
  induction depth with
  | zero =>
      intro subs
      cases subs with
      | nil => rfl
      | cons s tl =>
          rw [show Node.ofSubtrees H (s :: tl) 0 = s from rfl,
            show Node.ofLeaves H ((s :: tl).map (Node.rootOf H)) 0
              = .leaf (Node.rootOf H s) from rfl, Node.rootOf_leaf]
  | succ d ih =>
      intro subs
      rw [rootOf_ofSubtrees_succ, rootOf_ofLeaves_succ]
      simp only [← List.map_take, ← List.map_drop, List.isEmpty_map, ih]
      by_cases hemp : subs.drop (2 ^ d) = []
      · simp [hemp]
      · rw [if_neg (by simp [hemp]), if_neg (by simp [hemp]), ih]

end SizzLean.Cache.MerkleTree
