import SizzLean.Proofs.Merkleize
import SizzLean.Proofs.ShapeWidth
import SizzLean.Spec.GeneralizedIndex

/-!
# `SizzLean.Proofs.ShapeAgreement`: built trees carry the spec's roots

`Node.ofShape` and `SSZType.hashTreeRoot` run arm-for-arm parallel
(`Build.lean:110-114`). This file proves the root identity that parallelism
implies. `SizzLeanTests/TreeBackedCoherence.lean` checks it by `native_decide` on
concrete containers.

Every completeness theorem on the Merkle stack quantifies over
`Node.ofShape … merkleRoot`. This converts them into claims about the roots the
spec computes.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

open SizzLean.Hasher
open SizzLean.Spec

/-! ### The two zero towers

The cache layer memoises a Sha256-specific table. The spec recomputes an
`H`-generic recurrence. They agree at every depth, since both run the same
doubling recurrence and the memo only caches its first 100 entries. -/

/-- A zero subtree's root is its table entry: depth 0 is the leaf itself, and
every deeper one reads the slot `zeroLeaf` pre-filled at construction. -/
private theorem rootOf_zeroLeaf (H : Type) [Hasher H] :
    ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAt H d
  | 0     => by rw [zeroLeaf_zero, Node.rootOf_leaf]
  | _ + 1 => by rw [zeroLeaf_succ, Node.rootOf_pair_some]

/-- The memo table and the spec recurrence agree at every depth.

`hcomb` is the one hasher-specific input. The cache tower is a Sha256-specific
memo that calls the FFI `sha256Combine` directly. The spec tower goes through
`Hasher.combine (H := H)`. -/
private theorem zeroHashAt_eq_zeroHashAtDepth (H : Type) [Hasher H]
    (hcomb : ∀ a b, Hasher.combine (H := H) a b = LeanHazmat.Sha256.sha256Combine a b) :
    ∀ d, zeroHashAt H d = zeroHashAtDepth H d
  -- The two `zero32`s are separate definitions, the cache layer keeping its own
  -- copy so it can load without the spec, so the base closes by `rfl` rather
  -- than by matching syntactically.
  | 0 => by rw [zeroHashAtDepth_zero, zeroHashAt_zero]; rfl
  | d + 1 => by
      rw [zeroHashAt_succ H d, zeroHashAtDepth_succ H d, ← hcomb,
        zeroHashAt_eq_zeroHashAtDepth H hcomb d]

/-- **The two zero towers agree.** The cache layer's is the spec's, at every
depth. -/
private theorem rootOf_zeroLeaf_eq_zeroHashAtDepth (H : Type) [Hasher H]
    (hcomb : ∀ a b, Hasher.combine (H := H) a b = LeanHazmat.Sha256.sha256Combine a b)
    (d : Nat) : Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d := by
  rw [rootOf_zeroLeaf, zeroHashAt_eq_zeroHashAtDepth H hcomb]

/-- At the shipped FFI hasher, `combine` *is* `sha256Combine`, so the tower
agreement is free. -/
theorem rootOf_zeroLeaf_eq_zeroHashAtDepth_sha256 :
    ∀ d, Node.rootOf Sha256 (zeroLeaf Sha256 d) = zeroHashAtDepth Sha256 d :=
  rootOf_zeroLeaf_eq_zeroHashAtDepth Sha256 (fun _ _ => rfl)

/-- At the pure-Lean reference hasher, `combine` is `LeanSha256.combine`, a
different function from the memo's FFI call. The bridge is the named
`sha256Combine_eq_spec` axiom, which therefore appears in `#print axioms` of this
corollary and everything downstream of it. -/
theorem rootOf_zeroLeaf_eq_zeroHashAtDepth_sha256Spec :
    ∀ d, Node.rootOf Sha256Spec (zeroLeaf Sha256Spec d) = zeroHashAtDepth Sha256Spec d :=
  rootOf_zeroLeaf_eq_zeroHashAtDepth Sha256Spec
    (fun _ _ => by rw [sha256Combine_eq_spec]; rfl)

/-- The degenerate `uintN` width. The builder pads an empty buffer where the
spec returns the zero chunk bare, and padding nothing to a chunk *is* the zero
chunk. -/
private theorem padToChunk_empty : padToChunk ByteArray.empty = SizzLean.Spec.zero32 := rfl

/-- The length mix-in commutes with taking roots. `Node.mixInLength` fills its
cache slot with the combine, and `Spec.mixInLength` *is* that combine. -/
private theorem rootOf_mixInLength (H : Type) [Hasher H] (n : Node) (count : Nat) :
    Node.rootOf H (Node.mixInLength H n count)
      = Hasher.combine (H := H) (Node.rootOf H n) (natToChunk count) := by
  rw [Node.mixInLength, Node.rootOf_pair_some, Node.rootOf_leaf]

/-! ### Every built tree carries the spec's root

The three statements below are proven together because `Node.ofShape`,
`Node.subtreesForFields` and `Node.subtreesForListComposite` are one `mutual`
group (`Build.lean:116-215`). Lean 4.29.1 generates no functional-induction
principle for that block, so this mirrors the definition's own pattern match
under the explicit `(sizeOf type, phase, elements)` measure `ShapeWidth.lean`
introduced. The `phase` component is what lets `subtreesForListComposite` call
`ofShape` at an unchanged element type.

No arm closes by `rfl`. `SSZType.hashTreeRoot` and `SSZType.serialize` both come
from `mutual` blocks, so neither reduces definitionally, even on the arms whose
two sides read identically. Every arm goes through the equation lemmas
instead. -/

-- The dependent match on `s.interp` refines against `interp`'s per-constructor
-- recursion, the same elaborator cost `Build.lean` and `ShapeWidth.lean` raise
-- this for.
set_option maxHeartbeats 1000000

mutual

/-- **Every built tree carries the spec's root.** -/
theorem rootOf_ofShape_eq_hashTreeRoot (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d) :
    (s : SSZType) → (x : s.interp) →
      Node.rootOf H (Node.ofShape H s x) = SSZType.hashTreeRoot H s x
  | .uintN 8,   _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf]
  | .uintN 16,  _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf,
        SSZType.serialize, uint16LE]
  | .uintN 32,  _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf,
        SSZType.serialize, uint32LE]
  | .uintN 64,  _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf,
        SSZType.serialize, uint64LE]
  | .uintN 128, _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf]
  | .uintN 256, _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf]
  | .uintN _,   _ => by
      -- The builder's catch-all pads an empty buffer. The spec returns `zero32`
      -- bare, and `padToChunk ByteArray.empty = Spec.zero32`. The guarded
      -- equation lemma will not fire from a bare pattern variable, so unfold
      -- both matches and let `split` enumerate.
      -- `split` on two matches relates the two sides' witnesses by `HEq` across
      -- types that agree only after `subst_vars` substitutes the width
      -- equation, so `heq_eq_eq` cannot fire before then. After that
      -- `simp_all` closes both the diagonal cases and the impossible
      -- cross-cases, the latter from a `∀ x, ¬ _ ≍ x` hypothesis at `x` itself.
      rw [Node.ofShape.eq_def, SSZType.hashTreeRoot.eq_def]
      split <;> split <;> (try subst_eqs) <;>
        simp_all [Node.rootOf_leaf, SSZType.serialize, uint16LE, uint32LE, uint64LE,
          padToChunk_empty]
  | .bool, _ => by
      simp [Node.ofShape, SSZType.hashTreeRoot, Node.rootOf_leaf]
  | .bitvector _, _ => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      exact (merkleize_eq_ofLeaves H hzt _ _).symm
  | .bitlist _, _ => by
      -- `hashTreeRoot`'s body mentions `merkleize` under its own namespace, which
      -- no rewrite can match by name, so the last step goes through `exact`
      -- (defeq) rather than `rw` (syntactic).
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      rw [rootOf_mixInLength, mixInLength_eq]
      exact congrArg (fun r => Hasher.combine (H := H) r (natToChunk _))
        (merkleize_eq_ofLeaves H hzt _ _).symm
  | .vector t n, v => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      split
      · exact (merkleize_eq_ofLeaves H hzt _ _).symm
      · rw [rootOf_ofSubtrees_eq_ofLeaves,
          rootOf_subtreesForListComposite_eq H hzt t _ []]
        exact (merkleize_eq_ofLeaves H hzt _ _).symm
  | .list t cap, xs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      split
      · rw [rootOf_mixInLength, mixInLength_eq]
        exact congrArg (fun r => Hasher.combine (H := H) r (natToChunk _))
          (merkleize_eq_ofLeaves H hzt _ _).symm
      · rw [rootOf_mixInLength, mixInLength_eq, rootOf_ofSubtrees_eq_ofLeaves,
          rootOf_subtreesForListComposite_eq H hzt t _ []]
        exact congrArg (fun r => Hasher.combine (H := H) r (natToChunk _))
          (merkleize_eq_ofLeaves H hzt _ _).symm
  | .container fs, vs => by
      simp only [Node.ofShape, SSZType.hashTreeRoot]
      rw [rootOf_ofSubtrees_eq_ofLeaves, rootOf_subtreesForFields_eq H hzt fs vs]
      exact (merkleize_eq_ofLeaves H hzt _ _).symm
termination_by s _ => (sizeOf s, 0, 0)

/-- Companion: the per-field sub-tree roots are the spec's field roots. -/
theorem rootOf_subtreesForFields_eq (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d) :
    (fs : List SSZType) → (vs : SSZType.interpFields fs) →
      (Node.subtreesForFields H fs vs).map (Node.rootOf H)
        = SSZType.hashTreeRootFields H fs vs
  | [],      _  => by simp [Node.subtreesForFields, SSZType.hashTreeRootFields]
  | t :: ts, vs => by
      have ihHead := rootOf_ofShape_eq_hashTreeRoot H hzt t vs.1
      have ihTail := rootOf_subtreesForFields_eq H hzt ts vs.2
      simp [Node.subtreesForFields, SSZType.hashTreeRootFields, ihHead, ihTail]
termination_by fs _ => (sizeOf fs, 0, 0)

/-- Companion: the per-element sub-tree roots are the spec's element roots. The
statement generalises over the accumulator, since both builders recurse
tail-first and close with a `reverse`. -/
theorem rootOf_subtreesForListComposite_eq (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d)
    (t : SSZType) :
    (xs : List t.interp) → (acc : List Node) →
      (Node.subtreesForListComposite H t xs acc).map (Node.rootOf H)
        = SSZType.hashTreeRootListComposite H t xs (acc.map (Node.rootOf H))
  | [],      acc => by
      simp [Node.subtreesForListComposite, SSZType.hashTreeRootListComposite]
  | x :: xs, acc => by
      have ihHead := rootOf_ofShape_eq_hashTreeRoot H hzt t x
      have ihTail := rootOf_subtreesForListComposite_eq H hzt t xs
        (Node.ofShape H t x :: acc)
      simp [Node.subtreesForListComposite, SSZType.hashTreeRootListComposite,
        ihHead] at ihTail ⊢
      exact ihTail
termination_by xs _ => (sizeOf t, 1, xs.length)

end

/-! ### The `merkleRoot` form, and the two concrete hashers -/

/-- The `merkleRoot` form, which every completeness theorem on the stack
quantifies over. `rootOf_eq_merkleRoot` holds on every `Node` with no hypothesis,
so this is a rewrite. -/
theorem merkleRoot_ofShape_eq_hashTreeRoot (H : Type) [Hasher H]
    (hzt : ∀ d, Node.rootOf H (zeroLeaf H d) = zeroHashAtDepth H d)
    (s : SSZType) (x : s.interp) :
    Node.merkleRoot H (Node.ofShape H s x) = SSZType.hashTreeRoot H s x := by
  rw [← rootOf_eq_merkleRoot]
  exact rootOf_ofShape_eq_hashTreeRoot H hzt s x

/-- At the shipped FFI hasher, the one the fork bodies bind through
`fastHasherTag`. Carries no named FFI axiom: the zero tower is free here. -/
theorem merkleRoot_ofShape_eq_hashTreeRoot_sha256
    (s : SSZType) (x : s.interp) :
    Node.merkleRoot Sha256 (Node.ofShape Sha256 s x)
      = SSZType.hashTreeRoot Sha256 s x :=
  merkleRoot_ofShape_eq_hashTreeRoot Sha256
    rootOf_zeroLeaf_eq_zeroHashAtDepth_sha256 s x

/-- At the pure-Lean reference hasher. Carries `sha256Combine_eq_spec`, since the
memo tower reaches the reference hasher only through that bridge. -/
theorem merkleRoot_ofShape_eq_hashTreeRoot_sha256Spec
    (s : SSZType) (x : s.interp) :
    Node.merkleRoot Sha256Spec (Node.ofShape Sha256Spec s x)
      = SSZType.hashTreeRoot Sha256Spec s x :=
  merkleRoot_ofShape_eq_hashTreeRoot Sha256Spec
    rootOf_zeroLeaf_eq_zeroHashAtDepth_sha256Spec s x

end SizzLean.Cache.MerkleTree
