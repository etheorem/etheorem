import SizzLean.Spec.HashTreeRoot
import SizzLean.Proofs.Merkle.Naive

/-!
# `SizzLean.Proofs.Merkle.Opening`: Merkle branch completeness

A Merkle *branch* (the SSZ spec's `Merkle proof`) is the list of
sibling hashes along a root-to-leaf path. This file defines the
branch a pure-path tree honestly produces and the hash fold the
spec's `is_valid_merkle_branch` performs, and proves the two meet:

* `foldOpening_naiveOpeningAt`: for every path that lands at a
  chunk, folding the tree's own opening over that chunk
  reconstructs the tree's root.
* `foldOpening_openingAt`: the same, stated on `Spec.merkleize`,
  the merkleizer `SSZType.hashTreeRoot` calls.
* `foldOpening_mixInLength` / `foldOpening_mixInLength_merkleize`:
  under a length mix-in the path gains one `false` in front and
  the length chunk is the top sibling. This is the shape a list
  element's inclusion proof takes.

## The tree the branch lives in

The pure path's tree is the chunk list plus the depth:
`Spec.merkleize H chunks depth` pads `chunks` to `2 ^ depth`
leaves and combines pairwise. `naiveOpeningAt` walks that tree top
down, and at each pair names the sibling by the sibling *subtree's
own root* (`naiveRootAt` over the other half), so the sibling value
is the tree's own output and no coherence hypothesis is needed.
`naiveLeafAt` is the chunk a path addresses; the padding leaves are
honest participants, an all-padding path addresses the zero tower's
leaf. The overflow arm of `naiveRootAt` (more chunks than the
depth holds) sits outside the hypotheses, the same way it sits
outside `merkleize_eq_naiveRoot`.

`foldOpening` combines deepest-first: the recursion sinks to the
leaf, then folds outward, so it consumes `naiveOpeningAt`'s
top-down list directly and the completeness theorem needs no
reversal. EthCLLib's `branchFold` reads its `branch` array from the
leaf up, entry `i` the level-`i` sibling, so the bridge theorem in
`EthCLLib/Proofs/MerkleBranch.lean` passes the list reversed.

Lean idiom, annotated once: every `Hasher.combine` here takes the
explicit `(H := H)`. `Hasher`'s parameter is a phantom tag the
method's types do not mention, so instance synthesis cannot recover
it from the value arguments.
-/

set_option autoImplicit false

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec

/-- The chunk a bit path addresses in the pure-path tree over
`cs` at `(lvl, rem)`: `none` when the path runs past the chunk
level or stops above it, `some c` with `c` the addressed leaf
otherwise. A path into the padding addresses the padding's own
leaf, the zero tower's base `naiveZero H lvl`, which is what the
tree roots that region with. The halves are spelled `take` /
`drop`, the form `naiveRootAt_split` states the root's own step
in. -/
def naiveLeafAt (H : Type) [Hasher H] :
    List ByteArray → (lvl rem : Nat) → List Bool → Option ByteArray
  | cs, lvl, 0, [] =>
      some (match cs with
        | [] => naiveZero H lvl
        | _  => cs.head?.getD Spec.zero32)
  | _, _, 0, _ :: _ => none
  | _, _, _ + 1, [] => none
  | cs, lvl, rem + 1, bit :: rest =>
      if bit then naiveLeafAt H (cs.drop (2 ^ rem)) lvl rem rest
             else naiveLeafAt H (cs.take (2 ^ rem)) lvl rem rest

/-- The sibling roots along a bit path in the pure-path tree over
`cs` at `(lvl, rem)`, top down: the first path bit's sibling
first, the sibling named by the sibling subtree's own root. A path
that is not exactly `rem` bits long yields a prefix list; the
completeness theorem's hypothesis excludes that case. -/
def naiveOpeningAt (H : Type) [Hasher H] :
    List ByteArray → (lvl rem : Nat) → List Bool → List ByteArray
  | _, _, _, [] => []
  | _, _, 0, _ :: _ => []
  | cs, lvl, rem + 1, bit :: rest =>
      (if bit then naiveRootAt H (cs.take (2 ^ rem)) lvl rem
              else naiveRootAt H (cs.drop (2 ^ rem)) lvl rem)
        :: (if bit then naiveOpeningAt H (cs.drop (2 ^ rem)) lvl rem rest
                   else naiveOpeningAt H (cs.take (2 ^ rem)) lvl rem rest)

/-- One depth-first split of `naiveRootAt`, with the halves named
by `take` / `drop`. The step lemma both completeness inductions
rewrite with. -/
theorem naiveRootAt_split (H : Type) [Hasher H] (cs : List ByteArray)
    (lvl rem : Nat) :
    naiveRootAt H cs lvl (rem + 1)
      = Hasher.combine (H := H)
          (naiveRootAt H (cs.take (2 ^ rem)) lvl rem)
          (naiveRootAt H (cs.drop (2 ^ rem)) lvl rem) := by
  cases cs with
  | nil =>
      have ht : [].take (2 ^ rem) = ([] : List ByteArray) := by
        cases _ : 2 ^ rem <;> rfl
      have hd : [].drop (2 ^ rem) = ([] : List ByteArray) := by
        cases _ : 2 ^ rem <;> rfl
      rw [ht, hd]
      rfl
  | cons c cs =>
      rw [naiveRootAt.eq_def]
      simp only [List.splitAt_eq]

/-- The hash fold `is_valid_merkle_branch` performs: start from the
leaf, combine with each sibling, the side picked by the path bit
(`false` keeps the current value on the left). The list is
top down, so the deepest sibling combines first. -/
def foldOpening (H : Type) [Hasher H] (leaf : ByteArray) :
    List ByteArray → List Bool → ByteArray
  | _, [] => leaf
  | [], _ :: _ => leaf
  | sib :: sibs, bit :: bits =>
      match bit with
      | false => Hasher.combine (H := H) (foldOpening H leaf sibs bits) sib
      | true => Hasher.combine (H := H) sib (foldOpening H leaf sibs bits)

/-- Branch completeness: the pure-path tree's own opening folds
back to the tree's root, for every path that lands at a chunk.
Induction on the depth with the chunk list, the level, the path,
and the leaf generalized; at each split the descent and the root
take the same half, and the sibling is the other half's root. -/
theorem foldOpening_naiveOpeningAt (H : Type) [Hasher H] :
    ∀ (rem : Nat) (cs : List ByteArray) (lvl : Nat) (bits : List Bool)
      (leaf : ByteArray),
      naiveLeafAt H cs lvl rem bits = some leaf →
        foldOpening H leaf (naiveOpeningAt H cs lvl rem bits) bits
          = naiveRootAt H cs lvl rem := by
  intro rem
  induction rem with
  | zero =>
      intro cs lvl bits leaf h
      cases bits with
      | nil =>
          simp only [naiveLeafAt, Option.some.injEq] at h
          subst h
          cases cs with
          | nil => rfl
          | cons c cs => rfl
      | cons bit rest =>
          simp only [naiveLeafAt] at h
          exact absurd h (by simp)
  | succ rem ih =>
      intro cs lvl bits leaf h
      cases bits with
      | nil =>
          simp only [naiveLeafAt] at h
          exact absurd h (by simp)
      | cons bit rest =>
          rw [naiveOpeningAt, naiveRootAt_split]
          cases bit with
          | false =>
              simp only [Bool.false_eq_true, if_false, foldOpening] at h ⊢
              rw [ih _ _ _ _ h]
          | true =>
              simp only [if_true, foldOpening] at h ⊢
              rw [ih _ _ _ _ h]

/-- Branch completeness on the merkleizer `SSZType.hashTreeRoot`
calls: the opening of `merkleize H chunks depth` folds back to the
root, for every path that lands at a chunk. `merkleize_eq_naiveRoot`
(`Proofs/Merkle/Naive.lean`) transfers the tree theorem; the
length bound is its hypothesis, and `chunkDepth` of the type's own
cap satisfies it (`Proofs/Merkle/Chunk.lean`). -/
theorem foldOpening_openingAt (H : Type) [Hasher H] (chunks : List ByteArray)
    (depth : Nat) (hlen : chunks.length ≤ 2 ^ depth)
    (bits : List Bool) (leaf : ByteArray)
    (hleaf : naiveLeafAt H chunks 0 depth bits = some leaf) :
    foldOpening H leaf (naiveOpeningAt H chunks 0 depth bits) bits
      = Spec.merkleize H chunks depth := by
  rw [merkleize_eq_naiveRoot H chunks depth hlen]
  exact foldOpening_naiveOpeningAt H depth chunks 0 bits leaf hleaf

/-- Branch completeness under a length mix-in: with the length
chunk prepended to the opening and one `false` prepended to the
path, the fold returns the mix-in pair's root. The body is the
pure-path tree over `cs` at depth `d`; the wrapped root is
`Spec.mixInLength` of the body root. This is the shape a list
element's inclusion proof takes, the corollary the sidecar proofs
compose with. -/
theorem foldOpening_mixInLength (H : Type) [Hasher H]
    (cs : List ByteArray) (d : Nat) (count : Nat)
    (bits : List Bool) (leaf : ByteArray)
    (hleaf : naiveLeafAt H cs 0 d bits = some leaf) :
    foldOpening H leaf (natToChunk count :: naiveOpeningAt H cs 0 d bits)
        (false :: bits)
      = Spec.mixInLength H (naiveRootAt H cs 0 d) count := by
  show Hasher.combine (H := H)
      (foldOpening H leaf (naiveOpeningAt H cs 0 d bits) bits)
      (natToChunk count) = _
  rw [foldOpening_naiveOpeningAt H d cs 0 bits leaf hleaf]
  rfl

/-- The merkleizer form of the mix-in corollary: the body root
spelled `Spec.merkleize H cs d`, under the same length bound as
`foldOpening_openingAt`. -/
theorem foldOpening_mixInLength_merkleize (H : Type) [Hasher H]
    (cs : List ByteArray) (d : Nat) (hlen : cs.length ≤ 2 ^ d)
    (count : Nat) (bits : List Bool) (leaf : ByteArray)
    (hleaf : naiveLeafAt H cs 0 d bits = some leaf) :
    foldOpening H leaf (natToChunk count :: naiveOpeningAt H cs 0 d bits)
        (false :: bits)
      = Spec.mixInLength H (Spec.merkleize H cs d) count := by
  rw [merkleize_eq_naiveRoot H cs d hlen]
  exact foldOpening_mixInLength H cs d count bits leaf hleaf

end SizzLean.Proofs.Merkle
