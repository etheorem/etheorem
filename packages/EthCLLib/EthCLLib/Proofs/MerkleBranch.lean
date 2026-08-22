import EthCLLib.Spec.SigningRoot

/-!
# `EthCLLib.Proofs.MerkleBranch`: what `isValidMerkleBranch` accepts

`EthCLLib.Spec.isValidMerkleBranch` is `is_valid_merkle_branch`
(`specs/phase0/beacon-chain.md:800-812`).

Past the length guard, the check reduces to a plain fold of `branch` over `leaf`,
compared to `root`.

Bit ordering: `branch` runs bottom-to-top and entry `i` is the level-`i` sibling.
The routing convention lives in `EthCLLib.Spec.MerklePath`. The shipped check and
this fold both call `routeRight`, so the two agree by definition.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean
open SizzLean.Hasher
open EthCLLib.Spec

/-! ### The proof-side fold

`computeMerkleBranchRoot` runs its fold in `Except` and wraps the result, neither
of which an induction can peel. `branchFold` is the same walk as a plain
`ByteArray` function, `private` and proof-local. It models nothing the spec
declares, and `computeMerkleBranchRoot_eq_branchFold` is the only way in. -/

/-- The branch walk as a bare fold, reading siblings straight out of `branch`. -/
private def branchFold [HasherTag] (leaf : ByteArray)
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
      (List.range depth).foldlM (m := Except SizzLean.Cache.IndexError) (init := leaf)
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

/-! ### Past the guard -/

/-- A well-formed branch has `branch.size = depth`, which the honest opening
satisfies. The length guard then passes, and `isValidMerkleBranch` is the
byte-root of the branch walk compared to `root`. -/
theorem isValidMerkleBranch_eq_beq [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth index : Nat) (root : Vector UInt8 32)
    (hsize : branch.size = depth) :
    isValidMerkleBranch leaf branch depth index root
      = (bytesToRoot (branchFold (vecToBytes leaf) branch depth index) == root) := by
  unfold isValidMerkleBranch
  rw [if_pos hsize,
    computeMerkleBranchRoot_eq_branchFold leaf branch depth index (Nat.le_of_eq hsize.symm)]

/-- **Reconstruction (acceptance #1).** Given `hsize : branch.size = depth`, the
check accepts iff the left/right fold of `branch` over `leaf` reconstructs
`root`. The fold reads `index`'s bits to pick each side.

`hsize` is what the length guard enforces. Without it the statement fails on a
length mismatch, where the check returns `false` whatever the fold produces.

The proof closes symbolically, so no compiler axiom enters. -/
theorem isValidMerkleBranch_iff [HasherTag] (leaf : Vector UInt8 32)
    (branch : Array (Vector UInt8 32)) (depth index : Nat) (root : Vector UInt8 32)
    (hsize : branch.size = depth) :
    isValidMerkleBranch leaf branch depth index root = true
      ↔ bytesToRoot (branchFold (vecToBytes leaf) branch depth index) = root := by
  rw [isValidMerkleBranch_eq_beq _ _ _ _ _ hsize]
  exact beq_iff_eq

/-- Root-typing a sibling array preserves its length. Named so the statement
below can cite it, rather than carrying `(by rw [Array.size_map]; exact hsize)`
inline where a reader expects a term. -/
theorem size_map_bytesToRoot {sibs : Array ByteArray} {depth : Nat}
    (hsize : sibs.size = depth) : (sibs.map bytesToRoot).size = depth := by
  rw [Array.size_map]; exact hsize

end EthCLLib.Proofs
