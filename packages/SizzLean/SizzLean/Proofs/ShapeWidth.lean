import SizzLean.Cache.MerkleTree.Build
import SizzLean.Proofs.Perfect

/-!
# `SizzLean.Proofs.ShapeWidth`: every built tree has a 32-byte root

`ofSubtrees_isOpenable` (`EthCLLib.Proofs.MerkleOpening`) asks each sub-tree for
a 32-byte root before it will hand back a path witness. For a container or a
composite list those sub-trees are `Node.ofShape` trees. The obligation is
therefore "every shape builds to a 32-byte root". The proof below runs by mutual
induction over the `ofShape` / `subtreesForFields` / `subtreesForListComposite`
block (`Cache/MerkleTree/Build.lean:116-215`).

Proof-only, and re-exported from `SizzLean.lean` alongside `Proofs/Perfect`
because `EthCLLib` imports it. A `Proofs/` module off the root never reaches the
library's shared object, and the importer then fails at load time.

Hasher-generic. The zero-padding arms need the `zeroLeaf` pad's own root width,
which enters as the `hzero32` hypothesis, the same way `ofSubtrees_isOpenable`
threads `hzero`. Its witness `rootOf_zeroLeaf_size` reaches the FFI-populated
memo through `zeroHashAt_size`, so that declaration carries
`sha256Combine_eq_spec`. The rest of the file is axiom-free.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

open SizzLean.Hasher
open SizzLean.Spec

/-- `padToChunk` widens a short buffer to exactly one chunk. Only true for
`b.size ≤ 32`: the definition returns `b` untouched when it is already at least a
chunk wide, so an over-long buffer stays over-long. Every `ofShape` basic-type arm
feeds it a serialisation of at most 32 bytes. -/
private theorem padToChunk_size (b : ByteArray) (hb : b.size ≤ 32) :
    (padToChunk b).size = 32 := by
  -- The `else` arm is a fuel loop pushing `32 - b.size` zero bytes, so the width
  -- claim is about the loop. Generalise over it before touching the `if`.
  have key : ∀ (k : Nat) (acc : ByteArray),
      (padToChunk.go k acc).size = acc.size + k := by
    intro k
    induction k with
    | zero => intro acc; rfl
    | succ n ih =>
        intro acc
        rw [show padToChunk.go (n + 1) acc = padToChunk.go n (acc.push 0) from rfl,
            ih (acc.push 0), ByteArray.size_push]
        omega
  -- `padToChunk`'s `let n := b.size` elaborates to a `have`, which `split` will
  -- not see through. The `rfl` below zeta-reduces it and exposes the `if`.
  have hbp : BYTES_PER_CHUNK = 32 := rfl
  rw [show padToChunk b
        = if b.size ≥ BYTES_PER_CHUNK then b
          else padToChunk.go (BYTES_PER_CHUNK - b.size) b from rfl]
  split
  · omega
  · rw [key]; omega

/-- Every chunk `chunkify` emits is exactly 32 bytes. Each one is `padToChunk` of
a 32-wide `extract`, and an extract is never wider than its window. Feeds the
`ofLeaves` arms of `rootOf_ofShape_size`, whose leaves are all `chunkify` output. -/
private theorem chunkify_size (b : ByteArray) : ∀ c ∈ chunkify b, c.size = 32 := by
  -- Same shape as `padToChunk_size`: the claim is about the accumulator loop, so
  -- carry "every entry so far is 32 bytes" as the invariant.
  have key : ∀ (k : Nat) (acc : List ByteArray),
      (∀ c ∈ acc, c.size = 32) → ∀ c ∈ chunkify.go b k acc, c.size = 32 := by
    intro k
    induction k with
    | zero => intro acc hacc; exact hacc
    | succ n ih =>
        intro acc hacc
        rw [show chunkify.go b (n + 1) acc
              = chunkify.go b n
                  (padToChunk (b.extract (n * BYTES_PER_CHUNK)
                    (n * BYTES_PER_CHUNK + BYTES_PER_CHUNK)) :: acc) from rfl]
        refine ih _ ?_
        intro c hc
        rcases List.mem_cons.mp hc with h | h
        · subst h
          exact padToChunk_size _ (by
            have hbp : BYTES_PER_CHUNK = 32 := rfl
            rw [ByteArray.size_extract]; omega)
        · exact hacc c h
  rw [show chunkify b
        = if (b.size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK = 0 then []
          else chunkify.go b ((b.size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK) [] from rfl]
  split
  · intro c hc; simp at hc
  · exact key _ [] (by simp)

/-- A `zeroLeaf` pad has a 32-byte root at every depth. Depth 0 is the zero
chunk. A positive depth is a pair whose cache slot holds `zeroHashAt`, 32 bytes
by `zeroHashAt_size`.

Width is strictly weaker than `IsPerfect`. That predicate also pins every cached
slot to the honest `combine`. It therefore needs a hypothesis tying the hasher
to the one that populated the zero table (`zeroLeaf_isPerfect_of_combine`).
Nothing here reads the bytes, only their length, so this statement drops that
hypothesis. -/
theorem rootOf_zeroLeaf_size (H : Type) [Hasher H] (d : Nat) :
    (Node.rootOf H (zeroLeaf H d)).size = 32 := by
  rw [rootOf_eq_merkleRoot]
  cases d with
  | zero => rw [zeroLeaf_zero, merkleRoot_leaf]; exact zeroHashAt_size H 0
  | succ k =>
      -- The seal on `merkleRoot` blocks unfolding. Enter through the
      -- populated-slot arm, since `zeroLeaf` pre-fills it at construction.
      rw [zeroLeaf_succ, Node.merkleRoot_pair_some]
      exact zeroHashAt_size H (k + 1)

/-- An `ofLeaves` tree has a 32-byte root, given its data leaves do. It needs no
depth bound and no `IsPerfect` witness. Above depth 0 the constructor emits a
pair whose cache slot already holds a `combine` output, 32 by `CombineWidth32`,
whatever sits beneath it. Depth 0 is a data leaf or a `zeroLeaf` pad.

Deliberately weaker in its hypotheses than the perfection route
(an `IsPerfect` witness + `merkleRoot_size`), which would drag in `hzero`. -/
private theorem rootOf_ofLeaves_size (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero32 : ∀ d, (Node.rootOf H (zeroLeaf H d)).size = 32)
    (leaves : List ByteArray) (hsz : ∀ l ∈ leaves, l.size = 32) (depth : Nat) :
    (Node.rootOf H (Node.ofLeaves H leaves depth)).size = 32 := by
  rw [rootOf_eq_merkleRoot]
  cases depth with
  | zero =>
      cases leaves with
      | nil =>
          rw [show Node.ofLeaves H ([] : List ByteArray) 0 = zeroLeaf H 0 from rfl,
              ← rootOf_eq_merkleRoot]
          exact hzero32 0
      | cons l tl =>
          rw [show Node.ofLeaves H (l :: tl) 0 = .leaf l from rfl, merkleRoot_leaf]
          exact hsz l (by simp)
  | succ d =>
      unfold Node.ofLeaves
      simp only [List.splitAt_eq]
      rw [merkleRoot_pair H (by
        intro root heq
        rw [Option.some.injEq] at heq
        rw [← heq]; simp only [rootOf_eq_merkleRoot])]
      exact CombineWidth32.size _ _

/-- An `ofSubtrees` tree has a 32-byte root, given its sub-trees do. The
`hzero`-free counterpart of `merkleRoot_ofSubtrees_size` in
`Proofs/Perfect.lean`, which routes the zero pad through `IsPerfect`. Here the
pad's width comes straight from `rootOf_zeroLeaf_size`. -/
private theorem rootOf_ofSubtrees_size (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero32 : ∀ d, (Node.rootOf H (zeroLeaf H d)).size = 32)
    (subs : List Node) (hsz : ∀ s ∈ subs, (Node.rootOf H s).size = 32) (depth : Nat) :
    (Node.rootOf H (Node.ofSubtrees H subs depth)).size = 32 := by
  rw [rootOf_eq_merkleRoot]
  cases depth with
  | zero =>
      cases subs with
      | nil =>
          rw [show Node.ofSubtrees H ([] : List Node) 0 = zeroLeaf H 0 from rfl,
              ← rootOf_eq_merkleRoot]
          exact hzero32 0
      | cons s tl =>
          rw [show Node.ofSubtrees H (s :: tl) 0 = s from rfl, ← rootOf_eq_merkleRoot]
          exact hsz s (by simp)
  | succ d =>
      unfold Node.ofSubtrees
      simp only [List.splitAt_eq]
      rw [merkleRoot_pair H (by
        intro root heq
        rw [Option.some.injEq] at heq
        rw [← heq]; simp only [rootOf_eq_merkleRoot])]
      exact CombineWidth32.size _ _

/-- A `mixInLength` wrapper has a 32-byte root: the constructor's cached slot holds
a `combine` output, 32 by `CombineWidth32`. Needs nothing about the body. -/
private theorem rootOf_mixInLength_size (H : Type) [Hasher H] [CombineWidth32 H]
    (n : Node) (count : Nat) :
    (Node.rootOf H (Node.mixInLength H n count)).size = 32 := by
  rw [rootOf_eq_merkleRoot, Node.mixInLength,
      merkleRoot_pair H (by
        intro root heq
        rw [Option.some.injEq] at heq
        rw [← heq]; simp only [rootOf_eq_merkleRoot])]
  exact CombineWidth32.size _ _

/-! ### Every `ofShape` tree has a 32-byte root

The three statements below are proven together because `Node.ofShape`,
`Node.subtreesForFields` and `Node.subtreesForListComposite` are one `mutual`
group (`Build.lean:116-215`). Lean 4.29.1 generates no functional-induction
principle for that block. `Node.ofShape.induct` and both spellings of the mutual
variant are unknown identifiers, checked. This proof therefore mirrors the
definition's own pattern match and carries an explicit lexicographic measure.

The measure is `(sizeOf type, phase, elements)`. The first component falls on
every descent into a field type or an element type. The `phase` component lets
`subtreesForListComposite` call `ofShape` at the *same* element type. The list
builder sits at phase 1 and the shape builder at phase 0, so that call descends
even where the type stays the same. The third component carries the list
builder's own recursion down its element list. -/

-- The dependent match on `s.interp` refines against `interp`'s per-constructor
-- recursion, the same elaborator cost that makes `Build.lean` raise this.
set_option maxHeartbeats 1000000

mutual

/-- **Every `ofShape` tree has a 32-byte root**, together with the two sub-tree
list builders that share its `mutual` block.

This is the fact `ofSubtrees_isOpenable` needs at a container or composite-list
position, and it is what makes a generalized index into such a field openable.

No `hzero` here. Every arm bottoms out in `padToChunk` (exactly a chunk), a
cached `combine` output, or a `zeroLeaf` root, and all three are 32 bytes. -/
theorem rootOf_ofShape_size (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero32 : ∀ d, (Node.rootOf H (zeroLeaf H d)).size = 32) :
    (s : SSZType) → (x : s.interp) → (Node.rootOf H (Node.ofShape H s x)).size = 32
  | .uintN 8,    _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]; exact padToChunk_size _ (by simp)
  | .uintN 16,   _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]
      exact padToChunk_size _ (by simp [SSZType.serialize, uint16LE])
  | .uintN 32,   _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]
      exact padToChunk_size _ (by simp [SSZType.serialize, uint32LE])
  | .uintN 64,   _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]
      exact padToChunk_size _ (by simp [SSZType.serialize, uint64LE])
  | .uintN 128,  _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]
      exact padToChunk_size _ (by simp [natToChunk_size])
  | .uintN 256,  _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]
      exact padToChunk_size _ (by simp [natToChunk_size])
  | .uintN _,    _ => by
      -- The builder's own catch-all (a non-spec width, one zero chunk). Its
      -- equation lemma carries the guard "the width is none of the six
      -- literals", which `simp only [Node.ofShape]` cannot discharge from a bare
      -- pattern variable. Unfold the whole match and let `split` do the case
      -- work. `split` also enumerates the non-`uintN` arms. Each of those
      -- carries a constructor-clash equation, so `simp_all` closes them.
      rw [Node.ofShape.eq_def]
      split <;>
        first
          | (rw [Node.rootOf_leaf]
             exact padToChunk_size _ (by
               simp [SSZType.serialize, uint16LE, uint32LE, uint64LE, natToChunk_size]))
          | simp_all
  | .bool,       _ => by
      simp only [Node.ofShape, Node.rootOf_leaf]; exact padToChunk_size _ (by simp)
  | .bitvector _, _ => by
      simp only [Node.ofShape]; exact rootOf_ofLeaves_size H hzero32 _ (chunkify_size _) _
  | .bitlist _,   _ => by
      simp only [Node.ofShape]; exact rootOf_mixInLength_size H _ _
  | .vector t _, _ => by
      -- Basic elements flatten to chunks. Composite elements recurse per element.
      simp only [Node.ofShape]
      split
      · exact rootOf_ofLeaves_size H hzero32 _ (chunkify_size _) _
      · exact rootOf_ofSubtrees_size H hzero32 _
          (rootOf_subtreesForListComposite_size H hzero32 t _ [] (by simp)) _
  | .list _ _,   _ => by
      -- Both branches wrap in `mixInLength`, whose root is a `combine` output,
      -- so neither needs anything about the body.
      simp only [Node.ofShape]
      split <;> exact rootOf_mixInLength_size H _ _
  | .container fs, vs => by
      simp only [Node.ofShape]
      exact rootOf_ofSubtrees_size H hzero32 _ (rootOf_subtreesForFields_size H hzero32 fs vs) _
termination_by s _ => (sizeOf s, 0, 0)

/-- The sub-tree list has one entry per field. It sits here and not with the
agreement proofs, because `ofSubtrees_isOpenable`'s capacity side condition needs
it from this module onwards. -/
theorem subtreesForFields_length (H : Type) [Hasher H] :
    ∀ (fs : List SSZType) (vs : SSZType.interpFields fs),
      (Node.subtreesForFields H fs vs).length = fs.length
  | [],      _  => by simp [Node.subtreesForFields]
  | _ :: ts, vs => by
      simp only [Node.subtreesForFields, List.length_cons,
        subtreesForFields_length H ts vs.2]

/-- Companion: every per-field sub-tree of a container has a 32-byte root. This is
the form `ofSubtrees_isOpenable` consumes directly. -/
theorem rootOf_subtreesForFields_size (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero32 : ∀ d, (Node.rootOf H (zeroLeaf H d)).size = 32) :
    (fs : List SSZType) → (vs : SSZType.interpFields fs) →
      ∀ n ∈ Node.subtreesForFields H fs vs, (Node.rootOf H n).size = 32
  | [],      _  => by intro n hn; simp [Node.subtreesForFields] at hn
  | t :: ts, vs => by
      intro n hn
      simp only [Node.subtreesForFields, List.mem_cons] at hn
      rcases hn with h | h
      · subst h; exact rootOf_ofShape_size H hzero32 t vs.1
      · exact rootOf_subtreesForFields_size H hzero32 ts vs.2 n h
termination_by fs _ => (sizeOf fs, 0, 0)

/-- Companion: every per-element sub-tree of a composite list or vector has a
32-byte root. The statement generalises over the accumulator, since
`subtreesForListComposite` recurses tail-first for stack safety. -/
theorem rootOf_subtreesForListComposite_size (H : Type) [Hasher H] [CombineWidth32 H]
    (hzero32 : ∀ d, (Node.rootOf H (zeroLeaf H d)).size = 32)
    (t : SSZType) :
    (xs : List t.interp) → (acc : List Node) →
      (∀ n ∈ acc, (Node.rootOf H n).size = 32) →
      ∀ n ∈ Node.subtreesForListComposite H t xs acc, (Node.rootOf H n).size = 32
  | [],      acc, hacc => by
      intro n hn
      simp only [Node.subtreesForListComposite, List.mem_reverse] at hn
      exact hacc n hn
  | x :: xs, acc, hacc => by
      intro n hn
      simp only [Node.subtreesForListComposite] at hn
      refine rootOf_subtreesForListComposite_size H hzero32 t xs _ ?_ n hn
      intro m hm
      rcases List.mem_cons.mp hm with h | h
      · subst h; exact rootOf_ofShape_size H hzero32 t x
      · exact hacc m h
termination_by xs _ _ => (sizeOf t, 1, xs.length)

end

end SizzLean.Cache.MerkleTree
