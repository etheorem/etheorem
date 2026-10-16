import SizzLean.Spec.HashTreeRoot
import SizzLean.Proofs.Merkle.Naive
import SizzLean.Hasher.Class

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

/-- The bit path of `2 ^ depth + index` addresses chunk `index`.

`naiveLeafAt` takes a bit path, and a caller has an index.
`gindexBits (2 ^ depth + index)` is `index`'s bits, most significant first
(`gindexBits_pow_add`), and each descent step halves the chunk list. Bit `d`
therefore picks the half that holds `index`, at every level.

Induction on the depth, closing with `List.getElem?_take_of_lt` on the low half
and `List.getElem?_drop` on the high half. The sub-path carries `index`'s bits
where the recursive call wants those of `index % 2 ^ d`, and
`Nat.testBit_mod_two_pow` bridges the two.

Level `0` is the chunk level. Its padding leaf is `naiveZero H 0`, which is
`zero32`. A path past the last chunk reads `zero32`, and so does the
out-of-range `getD`, so the statement needs no in-range hypothesis. -/
theorem naiveLeafAt_gindexBits (H : Type) [Hasher H] :
    ∀ (depth : Nat) (cs : List ByteArray) (index : Nat), index < 2 ^ depth →
      naiveLeafAt H cs 0 depth ((List.range depth).reverse.map (index.testBit ·))
        = some (cs[index]?.getD Spec.zero32) := by
  intro depth
  induction depth with
  | zero =>
      intro cs index hindex
      have hi : index = 0 := by simpa using hindex
      subst hi
      cases cs with
      | nil => rfl
      | cons c cs => rfl
  | succ d ih =>
      intro cs index hindex
      have hbits : (List.range (d + 1)).reverse.map (index.testBit ·)
          = index.testBit d :: (List.range d).reverse.map (index.testBit ·) := by
        simp [List.range_succ]
      -- Below `d` the two indices have the same bits, so the sub-path is shared.
      have hsub : (List.range d).reverse.map (index.testBit ·)
          = (List.range d).reverse.map ((index % 2 ^ d).testBit ·) :=
        List.map_congr_left fun i hi => by
          rw [Nat.testBit_mod_two_pow]
          simp [List.mem_range.mp (List.mem_reverse.mp hi)]
      have hmod : index % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
      -- `index` fits two levels, so `index / 2 ^ d` is `0` or `1`, and bit `d`
      -- tests which half holds it.
      have hbit : index.testBit d = decide (2 ^ d ≤ index) := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.lt_or_ge index (2 ^ d) with hlt | hge
        · rw [Nat.div_eq_of_lt hlt]
          simp [Nat.not_le.mpr hlt]
        · have hone : index / 2 ^ d = 1 := by
            have hup : index / 2 ^ d < 2 :=
              Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ, Nat.mul_two] at hindex; omega)
            have hlo := (Nat.one_le_div_iff (Nat.two_pow_pos d)).mpr hge
            omega
          rw [hone]
          simp [hge]
      rw [hbits, hbit]
      rcases Nat.lt_or_ge index (2 ^ d) with hlow | hhigh
      · -- low half: `take` keeps `index` where it is
        have hmodeq : index % 2 ^ d = index := Nat.mod_eq_of_lt hlow
        simp only [Nat.not_le.mpr hlow, decide_false, Bool.false_eq_true,
          naiveLeafAt, if_false]
        rw [hsub, ih (cs.take (2 ^ d)) (index % 2 ^ d) hmod, hmodeq,
          List.getElem?_take_of_lt hlow]
      · -- high half: `drop` shifts `index` down by the halfway mark
        have hfit : index - 2 ^ d < 2 ^ d := by
          rw [Nat.pow_succ, Nat.mul_two] at hindex
          omega
        have hmodeq : index % 2 ^ d = index - 2 ^ d := by
          rw [Nat.mod_eq_sub_mod hhigh, Nat.mod_eq_of_lt hfit]
        simp only [decide_true, naiveLeafAt, if_true, hhigh]
        rw [hsub, ih (cs.drop (2 ^ d)) (index % 2 ^ d) hmod, hmodeq,
          List.getElem?_drop, Nat.add_sub_cancel' hhigh]

/-! ### Widths and lengths along an opening

`isValidMerkleBranch` takes its leaf and siblings as `Vector UInt8 32`, and its
guard checks the branch length. The theorems above state neither, so these do:
the leaf and every sibling are 32 bytes, and the opening has one entry per path
bit. The width lemmas take `[CombineWidth32 H]`, since every interior node is a
`combine`. The length lemma takes no instance. -/

/-- The zero tower is 32 bytes at every level: `zero32` at the base, a `combine`
above it. -/
theorem naiveZero_size (H : Type) [Hasher H] [CombineWidth32 H] (lvl : Nat) :
    (naiveZero H lvl).size = 32 := by
  cases lvl with
  | zero => rfl
  | succ l => exact CombineWidth32.size (H := H) _ _

/-- Every root the pure-path tree computes is 32 bytes, given 32-byte chunks.

No induction. Above the chunk level the root is a `combine` (`naiveRootAt_split`),
whose width `CombineWidth32` gives. At the chunk level it is the padding's leaf
or a chunk, and `hcs` covers the chunk. The overflow arm reads the head, so
`hcs` covers that too. -/
theorem naiveRootAt_size (H : Type) [Hasher H] [CombineWidth32 H]
    (cs : List ByteArray) (lvl rem : Nat) (hcs : ∀ c ∈ cs, c.size = 32) :
    (naiveRootAt H cs lvl rem).size = 32 := by
  cases rem with
  | zero =>
      cases cs with
      | nil => exact naiveZero_size H lvl
      | cons c cs =>
          show (List.head? (c :: cs) |>.getD Spec.zero32).size = 32
          exact hcs c (List.mem_cons_self ..)
  | succ r =>
      rw [naiveRootAt_split]
      exact CombineWidth32.size (H := H) _ _

/-- The merkleizer returns 32 bytes, given 32-byte chunks that fit the depth.
`merkleize_eq_naiveRoot` moves the goal to the reference tree and
`naiveRootAt_size` closes it. -/
theorem merkleize_size (H : Type) [Hasher H] [CombineWidth32 H]
    (chunks : List ByteArray) (depth : Nat) (hlen : chunks.length ≤ 2 ^ depth)
    (hcs : ∀ c ∈ chunks, c.size = 32) :
    (Spec.merkleize H chunks depth).size = 32 := by
  rw [merkleize_eq_naiveRoot H chunks depth hlen]
  exact naiveRootAt_size H chunks 0 depth hcs

/-- A chunk a path addresses is 32 bytes. Each descent step is a `take` or a
`drop`, and both keep membership, so `hcs` holds again at the next step. -/
theorem naiveLeafAt_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ (rem : Nat) (cs : List ByteArray) (lvl : Nat) (bits : List Bool)
      (leaf : ByteArray),
      (∀ c ∈ cs, c.size = 32) →
      naiveLeafAt H cs lvl rem bits = some leaf → leaf.size = 32 := by
  intro rem
  induction rem with
  | zero =>
      intro cs lvl bits leaf hcs h
      cases bits with
      | nil =>
          simp only [naiveLeafAt, Option.some.injEq] at h
          subst h
          cases cs with
          | nil => exact naiveZero_size H lvl
          | cons c cs => exact hcs c (List.mem_cons_self ..)
      | cons bit rest =>
          simp only [naiveLeafAt] at h
          exact absurd h (by simp)
  | succ rem ih =>
      intro cs lvl bits leaf hcs h
      cases bits with
      | nil =>
          simp only [naiveLeafAt] at h
          exact absurd h (by simp)
      | cons bit rest =>
          cases bit with
          | false =>
              simp only [naiveLeafAt, Bool.false_eq_true, if_false] at h
              exact ih _ lvl rest leaf
                (fun c hc => hcs c (List.mem_of_mem_take hc)) h
          | true =>
              simp only [naiveLeafAt, if_true] at h
              exact ih _ lvl rest leaf
                (fun c hc => hcs c (List.mem_of_mem_drop hc)) h

/-- The opening has one entry per path bit. `naiveOpeningAt` adds one sibling per
bit and stops when the bits or the levels run out. -/
theorem naiveOpeningAt_length (H : Type) [Hasher H] :
    ∀ (rem : Nat) (cs : List ByteArray) (lvl : Nat) (bits : List Bool),
      bits.length = rem → (naiveOpeningAt H cs lvl rem bits).length = rem := by
  intro rem
  induction rem with
  | zero =>
      intro cs lvl bits hbits
      cases bits with
      | nil => rfl
      | cons _ _ => simp at hbits
  | succ rem ih =>
      intro cs lvl bits hbits
      cases bits with
      | nil => simp at hbits
      | cons bit rest =>
          have hrest : rest.length = rem := by
            rw [List.length_cons] at hbits; omega
          cases bit with
          | false =>
              simp only [naiveOpeningAt, Bool.false_eq_true, if_false,
                List.length_cons]
              rw [ih _ lvl rest hrest]
          | true =>
              simp only [naiveOpeningAt, if_true, List.length_cons]
              rw [ih _ lvl rest hrest]

/-- Every sibling in an opening is 32 bytes. Each entry is the other half's own
`naiveRootAt`, sized by `naiveRootAt_size`. -/
theorem naiveOpeningAt_size (H : Type) [Hasher H] [CombineWidth32 H] :
    ∀ (rem : Nat) (cs : List ByteArray) (lvl : Nat) (bits : List Bool)
      (s : ByteArray),
      (∀ c ∈ cs, c.size = 32) →
      s ∈ naiveOpeningAt H cs lvl rem bits → s.size = 32 := by
  intro rem
  induction rem with
  | zero =>
      intro cs lvl bits s _ hs
      cases bits with
      | nil => simp [naiveOpeningAt] at hs
      | cons _ _ => simp [naiveOpeningAt] at hs
  | succ rem ih =>
      intro cs lvl bits s hcs hs
      cases bits with
      | nil => simp [naiveOpeningAt] at hs
      | cons bit rest =>
          have htake : ∀ c ∈ cs.take (2 ^ rem), c.size = 32 :=
            fun c hc => hcs c (List.mem_of_mem_take hc)
          have hdrop : ∀ c ∈ cs.drop (2 ^ rem), c.size = 32 :=
            fun c hc => hcs c (List.mem_of_mem_drop hc)
          cases bit with
          | false =>
              simp only [naiveOpeningAt, Bool.false_eq_true, if_false,
                List.mem_cons] at hs
              rcases hs with hs | hs
              · subst hs; exact naiveRootAt_size H _ lvl rem hdrop
              · exact ih _ lvl rest s htake hs
          | true =>
              simp only [naiveOpeningAt, if_true, List.mem_cons] at hs
              rcases hs with hs | hs
              · subst hs; exact naiveRootAt_size H _ lvl rem htake
              · exact ih _ lvl rest s hdrop hs

end SizzLean.Proofs.Merkle
