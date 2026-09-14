import SizzLean.Spec.HashTreeRoot
import SizzLean.Cache.MerkleTree.Zero
import SizzLean.Proofs.Merkle.Naive

/-!
# `SizzLean.Proofs.Merkle.Zero`: the zero towers agree

Three towers compute the all-zero subtree roots: the spec's
`Spec.zeroHashAt` (the reference recurrence), the cache layer's
`Cache.MerkleTree.zeroHashAt` (the memoised runtime tower, whose
kernel body is `zeroHashRec`), and the naive tree's empty tree
`naiveRoot H [] d` (padding with zero leaves). This file proves the
three agree, so every `Node.ofLeaves` padding below is the same
zero tower the spec's `merkleize` short-circuits to.

Lean idiom, annotated once: the `(H := H)` on `Hasher.combine`
names the phantom hasher tag, which instance synthesis cannot
recover from the value arguments.
-/

set_option autoImplicit false

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec
open SizzLean.Cache.MerkleTree (zero32 zeroHashAt zeroHashRec)

/-- The cache layer's `zero32` is the spec's `zero32`. -/
theorem cache_zero32_eq_spec : SizzLean.Cache.MerkleTree.zero32 = Spec.zero32 := rfl

/-- The cache-side tower is the spec-side tower, at every depth.
Both bodies are the same `Hasher.combine` recurrence over the same
`zero32` leaf (`cache_zero32_eq_spec`). The proof is an induction
on the depth: the zero case is the shared `zero32` leaf, and the
successor case rewrites with the induction hypothesis inside the
`combine`. The kernel sees the body, never the `@[implemented_by]`
substitute, so the memoisation raises no proof obligation here. -/
theorem zeroHashRec_eq_spec (H : Type) [Hasher H] :
    ∀ d : Nat, SizzLean.Cache.MerkleTree.zeroHashRec H d = Spec.zeroHashAt H d := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      show Hasher.combine (H := H)
            (SizzLean.Cache.MerkleTree.zeroHashRec H d)
            (SizzLean.Cache.MerkleTree.zeroHashRec H d) = _
      rw [ih, Spec.zeroHashAt]

/-- The cache-side memoised tower is the spec-side tower: its
kernel body is `zeroHashRec`, which `zeroHashRec_eq_spec` just
matched to the spec's recurrence. -/
theorem cache_zeroHashAt_eq_spec (H : Type) [Hasher H] :
    ∀ d : Nat, SizzLean.Cache.MerkleTree.zeroHashAt H d = Spec.zeroHashAt H d :=
  zeroHashRec_eq_spec H

/-- The empty naive tree is the spec's zero tower: padding zero
leaves and combining them pairwise computes the same tower the
spec's recurrence states. -/
theorem spec_zeroHashAt_eq_naiveRoot (H : Type) [Hasher H] :
    ∀ d : Nat, Spec.zeroHashAt H d = naiveRoot H [] d :=
  fun d => naiveRoot_nil H d |>.symm

end SizzLean.Proofs.Merkle
