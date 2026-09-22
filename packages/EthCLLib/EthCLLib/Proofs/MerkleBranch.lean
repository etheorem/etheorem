import EthCLLib.Spec.SigningRoot
import SizzLean.Proofs.Merkle.Gindex
import SizzLean.Proofs.Merkle.Opening

/-!
# `EthCLLib.Proofs.MerkleBranch`: what `isValidMerkleBranch` accepts

`EthCLLib.Spec.isValidMerkleBranch` is `is_valid_merkle_branch`
(`phase0/beacon-chain.md:800-812`).

Past the length guard, the check reduces to a plain fold of `branch` over `leaf`,
compared to `root`.

Bit ordering: `branch` runs bottom-to-top and entry `i` is the level-`i` sibling.
The routing convention lives in `EthCLLib.Spec.MerklePath`. The check and
this fold both call `routeRight`, so the two agree by definition.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean
open EthCLLib.Spec

/-! ### The proof-side fold

`computeMerkleBranchRoot` runs its fold in `Except` and wraps the result, neither
of which an induction can peel. `branchFold` is the same walk as a plain
`ByteArray` function. It models nothing the spec declares, and
`computeMerkleBranchRoot_eq_branchFold` is the only bridge to it. The definition
is public: `isValidMerkleBranch_iff` names it on its right-hand side, and an
outside module (the fork-ledger rows, the SizzLean opening bridge) has to be
able to state a goal against it. -/

/-- The branch walk as a bare fold, reading siblings straight out of `branch`:
entry `i` of `branch` is the level-`i` sibling, level `0` at the leaf, so the
array runs bottom-to-top. -/
def branchFold [HasherTag] (leaf : ByteArray)
    (branch : Array (Vector UInt8 32)) (depth index : Nat) : ByteArray :=
  (List.range depth).foldl (init := leaf) fun value i =>
    if routeRight index i
    then Hasher.combine (H := HasherTag.H) (vecToBytes branch[i]!) value
    else Hasher.combine (H := HasherTag.H) value (vecToBytes branch[i]!)

/-- One level off the top: the `d+1` walk is the `d` walk followed by level `d`. -/
private theorem branchFold_succ [HasherTag] (leaf : ByteArray)
    (branch : Array (Vector UInt8 32)) (d index : Nat) :
    branchFold leaf branch (d + 1) index
      = (let value := branchFold leaf branch d index
         if routeRight index d
         then Hasher.combine (H := HasherTag.H) (vecToBytes branch[d]!) value
         else Hasher.combine (H := HasherTag.H) value (vecToBytes branch[d]!)) := by
  unfold branchFold
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The checked fold itself, in range: every `branch[i]` read hits, so the
`IndexError` arm never fires. The statement sits on the inner `foldlM`, since the
induction has to step the fold without `computeMerkleBranchRoot`'s closing wrap
in the way. It generalises over the accumulator for the same reason. -/
private theorem branchFoldM_ok [HasherTag] (branch : Array (Vector UInt8 32)) (index : Nat) :
    ∀ (depth : Nat), depth ≤ branch.size → ∀ (leaf : ByteArray),
      (List.range depth).foldlM (m := Except Cache.IndexError) (init := leaf)
          (fun value i => do
            let sibling ←
              if h : i < branch.size then pure (vecToBytes branch[i])
              else throw (.indexError i branch.size)
            return if routeRight index i
              then Hasher.combine (H := HasherTag.H) sibling value
              else Hasher.combine (H := HasherTag.H) value sibling)
        = .ok (branchFold leaf branch depth index) := by
  intro depth
  induction depth with
  | zero => intro _ leaf; rfl
  | succ d ih =>
      intro hb leaf
      rw [List.range_succ, List.foldlM_append, ih (by omega) leaf, branchFold_succ]
      simp [dif_pos (show d < branch.size by omega),
        getElem!_pos branch d (show d < branch.size by omega)]
      rfl

/-- In range, the checked walk is the plain one. -/
private theorem computeMerkleBranchRoot_eq_branchFold [HasherTag]
    (leaf : Vector UInt8 32) (branch : Array (Vector UInt8 32)) (depth index : Nat)
    (hb : depth ≤ branch.size) :
    computeMerkleBranchRoot leaf branch depth index
      = .ok (bytesToRoot (branchFold (vecToBytes leaf) branch depth index)) := by
  unfold computeMerkleBranchRoot
  rw [branchFoldM_ok branch index depth hb (vecToBytes leaf)]
  rfl

/-! ### Past the guard

Both theorems below state their right-hand side with `branchFold`. They serve
the theorems in this module that state the check's contract over
`computeMerkleBranchRoot` and `isValidMerkleBranch` alone;
`isValidMerkleBranch_iff` is public, and `branchFold` is
public with it, so the fork-ledger rows can cite the iff directly. -/

/-- A well-formed branch has `branch.size = depth`, which the honest opening
satisfies. The length guard then passes, and `isValidMerkleBranch` is the
byte-root of the branch walk compared to `root`. -/
private theorem isValidMerkleBranch_eq_beq [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth index : Nat) (root : Vector UInt8 32)
    (hsize : branch.size = depth) :
    isValidMerkleBranch leaf branch depth index root
      = (bytesToRoot (branchFold (vecToBytes leaf) branch depth index) == root) := by
  unfold isValidMerkleBranch
  rw [if_pos hsize,
    computeMerkleBranchRoot_eq_branchFold leaf branch depth index (Nat.le_of_eq hsize.symm)]

/-- **Reconstruction (acceptance #1).** The check's contract, public
for the fork-ledger rows that cite it: given
`hsize : branch.size = depth`, the check accepts iff the left/right
fold of `branch` over `leaf` reconstructs `root`. The fold reads
`index`'s bits to pick each side, one `testBit` per level
(`routeRight_eq_testBit`).

`hsize` is what the length guard enforces. Without it the statement
fails on a length mismatch, where the check returns `false` whatever
the fold produces.

The proof closes symbolically, so no compiler axiom enters. -/
theorem isValidMerkleBranch_iff [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth index : Nat) (root : Vector UInt8 32)
    (hsize : branch.size = depth) :
    isValidMerkleBranch leaf branch depth index root = true
      ↔ bytesToRoot (branchFold (vecToBytes leaf) branch depth index) = root := by
  rw [isValidMerkleBranch_eq_beq _ _ _ _ _ hsize]
  exact beq_iff_eq

/-- `routeRight` is `Nat.testBit`: the level-`i` routing bit is bit
`i` of the index. This lines the check's fold up with
`SizzLean.Cache.MerkleTree.gindexBits`, whose bits are the index's
`testBit`s, so a path addressed top-down by a generalized index
routes level for level with `branchFold` bottom-up. -/
theorem routeRight_eq_testBit (index i : Nat) :
    routeRight index i = index.testBit i := by
  simp [routeRight, Nat.and_one_is_mod, Nat.testBit,
    Nat.shiftRight_eq_div_pow]

/-- Root-typing a sibling array preserves its length. Named so the statement
below can cite it, rather than carrying `(by rw [Array.size_map]; exact hsize)`
inline where a reader expects a term. -/
theorem size_map_bytesToRoot {sibs : Array ByteArray} {depth : Nat}
    (hsize : sibs.size = depth) : (sibs.map bytesToRoot).size = depth := by
  rw [Array.size_map]; exact hsize

/-! ### The SizzLean opening bridge

A SizzLean tree's honest opening satisfies the check. The
two folds walk the same levels in opposite orders: `branchFold`
reads `branch` from the leaf up, `foldOpening` consumes the opening
from the root down, so the bridge passes the sibling list reversed
into the array. The bits agree level for level through
`routeRight_eq_testBit` and
`SizzLean.Proofs.Merkle.gindexBits_pow_add`. -/

/-- `branchFold` reads only the first `depth` entries, so two
sibling arrays that agree there fold to the same value. -/
private theorem branchFold_congr_entries [HasherTag] (leaf : ByteArray) :
    ∀ (depth index : Nat) (B1 B2 : Array (Vector UInt8 32)),
      (∀ i, i < depth → B1[i]! = B2[i]!) →
      branchFold leaf B1 depth index = branchFold leaf B2 depth index := by
  intro depth
  induction depth with
  | zero => intro index B1 B2 _; rfl
  | succ d ih =>
      intro index B1 B2 hagree
      rw [branchFold_succ, branchFold_succ,
        ih index B1 B2 (fun i hi => hagree i (by omega)),
        hagree d (by omega)]

/-- Array element access is list element access on the data. -/
private theorem getElem!_to_list (a : Array (Vector UInt8 32)) (i : Nat) :
    a[i]! = a.toList[i]! := by
  simp [Array.getElem!_eq_getD]

/-- Appending past the read window changes no earlier entry. -/
private theorem getElem!_append_left (xs ys : List (Vector UInt8 32)) (i : Nat)
    (h : i < xs.length) : (xs ++ ys)[i]! = xs[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append, List.getElem?_eq_getElem h]
  simp [h]

/-- The two folds agree: `branchFold` over the sibling array (its
bottom-up order) is `foldOpening` over the sibling list mapped to
bytes (its top-down order), the path bits read off `index` one
`testBit` per level. Induction on the depth with the leaf, the
siblings, and the index generalized; the last fold step is the
head sibling. -/
theorem branchFold_eq_foldOpening [HasherTag] (leaf : ByteArray)
    (sibs : List (Vector UInt8 32)) (depth index : Nat) (hsize : sibs.length = depth) :
    branchFold leaf sibs.toArray.reverse depth index
      = SizzLean.Proofs.Merkle.foldOpening (H := HasherTag.H) leaf (sibs.map vecToBytes)
          ((List.range depth).reverse.map (index.testBit ·)) := by
  induction depth generalizing leaf sibs index with
  | zero =>
      have h0 : sibs = [] := List.length_eq_zero_iff.mp hsize
      subst h0
      rfl
  | succ d ih =>
      cases sibs with
      | nil => simp at hsize
      | cons s0 s' =>
      rw [List.length_cons] at hsize
      have hs' : s'.length = d := by omega
      have hih := ih leaf s' index hs'
      -- Array data through `toList`: the reversed cons array holds
      -- the reversed cons, the reversed tail array the reversed tail.
      have htoList1 : ((s0 :: s' : List (Vector UInt8 32)).toArray.reverse).toList
          = (s0 :: s' : List (Vector UInt8 32)).reverse := by simp
      have htoList2 : (s'.toArray.reverse).toList
          = (s' : List (Vector UInt8 32)).reverse := by simp
      -- The first `d` entries of both arrays are the tail's reverse.
      have hagree : ∀ i, i < d →
          ((s0 :: s').toArray.reverse)[i]! = (s'.toArray.reverse)[i]! := by
        intro i hi
        rw [getElem!_to_list, getElem!_to_list, htoList1, htoList2, List.reverse_cons]
        exact getElem!_append_left _ _ _ (by rwa [List.length_reverse, hs'])
      have hval := branchFold_congr_entries leaf d index
        ((s0 :: s').toArray.reverse) (s'.toArray.reverse) hagree
      -- The top entry of the reversed cons array is the head `s0`.
      have hd : ((s0 :: s').toArray.reverse)[d]! = s0 := by
        rw [getElem!_to_list, htoList1, List.reverse_cons,
          List.getElem!_eq_getElem?_getD, List.getElem?_append]
        simp [hs']
      -- The bits: one cons, most significant first.
      have hbits : (List.range (d + 1)).reverse.map (index.testBit ·)
          = index.testBit d :: (List.range d).reverse.map (index.testBit ·) := by
        simp [List.range_succ]
      rw [branchFold_succ, hval, hbits, routeRight_eq_testBit]
      cases hb : index.testBit d with
      | false =>
          simp only [List.map_cons, Bool.false_eq_true, if_false,
            SizzLean.Proofs.Merkle.foldOpening, hd]
          rw [← hih]
      | true =>
          simp only [List.map_cons, if_true, SizzLean.Proofs.Merkle.foldOpening, hd]
          rw [← hih]

/-- **Branch completeness.** An honest opening passes the check:
for `index < 2 ^ depth`, if folding the byte-level opening
over the leaf reconstructs the root, then
`isValidMerkleBranch leaf branch depth index root` is `true`. The
siblings are 32-byte roots, `branch` runs bottom-up, and the
reconstruction hypothesis is stated on `gindexBits (2 ^ depth +
index)`, the bit path the generalized index produces. This is the
theorem the fork ledger's `processDeposit` rows wait on. -/
theorem isValidMerkleBranch_of_foldOpening [HasherTag]
    (leaf root : Vector UInt8 32) (sibs : List (Vector UInt8 32)) (depth index : Nat)
    (hsize : sibs.length = depth) (hindex : index < 2 ^ depth)
    (hrec : SizzLean.Proofs.Merkle.foldOpening (H := HasherTag.H) (vecToBytes leaf)
        (sibs.map vecToBytes)
        (SizzLean.Cache.MerkleTree.gindexBits (2 ^ depth + index))
      = vecToBytes root) :
    isValidMerkleBranch leaf sibs.toArray.reverse depth index root = true := by
  have hbs : sibs.toArray.reverse.size = depth := by simp [hsize]
  rw [isValidMerkleBranch_iff leaf sibs.toArray.reverse depth index root hbs,
    branchFold_eq_foldOpening (vecToBytes leaf) sibs depth index hsize]
  rw [SizzLean.Proofs.Merkle.gindexBits_pow_add depth index hindex] at hrec
  rw [hrec]
  -- `bytesToRoot` inverts `vecToBytes` on a 32-byte vector.
  ext i h
  simp only [bytesToRoot, bytesToVec, vecToBytes, Vector.getElem_ofFn, ByteArray.get!]
  have hlt : i < root.toArray.size := by
    have hsz : root.toArray.size = 32 := by simp
    omega
  show root.toArray[i]! = root.toArray[i]'hlt
  exact getElem!_pos root.toArray i hlt

/-! ### Completeness stated on `Spec.merkleize`

`isValidMerkleBranch_of_foldOpening` takes the reconstruction as a hypothesis,
and `SizzLean.Proofs.Merkle.foldOpening_openingAt` proves it for
`Spec.merkleize`. Composing the two leaves a statement with no fold in it: a
chunk list, a depth, an index, and the check accepts.

The composition costs the widths. `isValidMerkleBranch` takes root-typed
siblings, so `bytesToRoot` must not drop bytes. `[CombineWidth32 HasherTag.H]`
and the 32-byte chunks guarantee that. -/

/-- `bytesToRoot` drops nothing from a 32-byte buffer: root-typing and
converting back returns the same bytes. The width hypotheses below discharge
this lemma's `hsz`. -/
theorem vecToBytes_bytesToRoot (b : ByteArray) (hsz : b.size = 32) :
    vecToBytes (bytesToRoot b) = b := by
  apply ByteArray.ext
  apply Array.ext
  · simp [vecToBytes, bytesToRoot, bytesToVec, hsz]
  · intro i h1 h2
    simp only [vecToBytes, bytesToRoot, bytesToVec, Vector.toArray_ofFn,
      Array.getElem_ofFn, ByteArray.get!]
    exact getElem!_pos b.data i (by omega)

open SizzLean.Proofs.Merkle in
/-- **Completeness on the merkleizer.** Open `Spec.merkleize H chunks depth` at
`index` and `isValidMerkleBranch` accepts.

The check reads its siblings root-typed and bottom-up, so the statement reverses
`naiveOpeningAt`'s top-down list, and `hleaf` supplies the leaf.
`isValidMerkleBranch_of_merkleize_idx` below reads it as chunk `index` instead.

`foldOpening_openingAt` discharges `isValidMerkleBranch_of_foldOpening`'s
reconstruction hypothesis. The leaf, every sibling, and the merkleizer's output
are 32 bytes, so `bytesToRoot` drops nothing.

**Axiom use**: at `Sha256`, `CombineWidth32` carries `sha256Combine_eq_spec`. At
`Sha256Spec`, the theorem uses no axiom. -/
theorem isValidMerkleBranch_of_merkleize [HasherTag] [CombineWidth32 HasherTag.H]
    (chunks : List ByteArray) (depth index : Nat)
    (hlen : chunks.length ≤ 2 ^ depth) (hindex : index < 2 ^ depth)
    (hchunks : ∀ c ∈ chunks, c.size = 32) (leaf : ByteArray)
    (hleaf : naiveLeafAt HasherTag.H chunks 0 depth
        (SizzLean.Cache.MerkleTree.gindexBits (2 ^ depth + index)) = some leaf) :
    isValidMerkleBranch (bytesToRoot leaf)
        ((naiveOpeningAt HasherTag.H chunks 0 depth
            (SizzLean.Cache.MerkleTree.gindexBits
              (2 ^ depth + index))).map bytesToRoot).toArray.reverse
        depth index
        (bytesToRoot (SizzLean.Spec.merkleize HasherTag.H chunks depth))
      = true := by
  -- The `gindexBits` term is written in full each time: `set` is a mathlib
  -- tactic, and this package builds without mathlib.
  have hblen :
      (SizzLean.Cache.MerkleTree.gindexBits (2 ^ depth + index)).length = depth := by
    rw [gindexBits_pow_add depth index hindex]; simp
  -- the path is `depth` bits long, so the opening is `depth` siblings long
  have hslen :
      ((naiveOpeningAt HasherTag.H chunks 0 depth
          (SizzLean.Cache.MerkleTree.gindexBits
            (2 ^ depth + index))).map bytesToRoot).length = depth := by
    rw [List.length_map, naiveOpeningAt_length HasherTag.H depth chunks 0 _ hblen]
  apply isValidMerkleBranch_of_foldOpening (bytesToRoot leaf) _ _ depth index
    hslen hindex
  -- root-typing the siblings loses nothing, so the fold sees the opening itself
  have hmapback :
      ((naiveOpeningAt HasherTag.H chunks 0 depth
            (SizzLean.Cache.MerkleTree.gindexBits
              (2 ^ depth + index))).map bytesToRoot).map vecToBytes
        = naiveOpeningAt HasherTag.H chunks 0 depth
            (SizzLean.Cache.MerkleTree.gindexBits (2 ^ depth + index)) := by
    rw [List.map_map]
    have hid :
        (naiveOpeningAt HasherTag.H chunks 0 depth
            (SizzLean.Cache.MerkleTree.gindexBits (2 ^ depth + index))).map
              (vecToBytes ∘ bytesToRoot)
          = (naiveOpeningAt HasherTag.H chunks 0 depth
              (SizzLean.Cache.MerkleTree.gindexBits (2 ^ depth + index))).map id :=
      List.map_congr_left fun s hs =>
        vecToBytes_bytesToRoot s
          (naiveOpeningAt_size HasherTag.H depth chunks 0 _ s hchunks hs)
    rw [hid, List.map_id]
  have hleafsz : leaf.size = 32 :=
    naiveLeafAt_size HasherTag.H depth chunks 0 _ leaf hchunks hleaf
  rw [hmapback, vecToBytes_bytesToRoot leaf hleafsz,
    foldOpening_openingAt HasherTag.H chunks depth hlen _ leaf hleaf]
  exact (vecToBytes_bytesToRoot _
    (merkleize_size HasherTag.H chunks depth hlen hchunks)).symm

open SizzLean.Proofs.Merkle in
/-- **Completeness at an index.** The same result with the leaf read as
`chunks[index]?`, or as the padding where `index` runs past the last chunk.
`naiveLeafAt_gindexBits` names the leaf. -/
theorem isValidMerkleBranch_of_merkleize_idx [HasherTag] [CombineWidth32 HasherTag.H]
    (chunks : List ByteArray) (depth index : Nat)
    (hlen : chunks.length ≤ 2 ^ depth) (hindex : index < 2 ^ depth)
    (hchunks : ∀ c ∈ chunks, c.size = 32) :
    isValidMerkleBranch (bytesToRoot (chunks[index]?.getD SizzLean.Spec.zero32))
        ((naiveOpeningAt HasherTag.H chunks 0 depth
            (SizzLean.Cache.MerkleTree.gindexBits
              (2 ^ depth + index))).map bytesToRoot).toArray.reverse
        depth index
        (bytesToRoot (SizzLean.Spec.merkleize HasherTag.H chunks depth))
      = true := by
  refine isValidMerkleBranch_of_merkleize chunks depth index hlen hindex hchunks _ ?_
  rw [gindexBits_pow_add depth index hindex]
  exact naiveLeafAt_gindexBits HasherTag.H depth chunks index hindex

end EthCLLib.Proofs
