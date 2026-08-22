import EthCLLib.Spec.SigningRoot
import EthCLLib.Proofs.MerkleOpening
import SizzLean.Proofs.Perfect
import SizzLean.Hasher.CombineWidth
import SizzLean.Proofs.Util

/-!
# `EthCLLib.Proofs.MerkleBranch`: what `isValidMerkleBranch` accepts

`EthCLLib.Spec.isValidMerkleBranch` is `is_valid_merkle_branch`
(`specs/phase0/beacon-chain.md:800-812`).

Past the length guard, the check reduces to a plain fold of `branch` over `leaf`,
compared to `root`.

Open a tree at `index` with `honestLeaf` / `honestBranch`, and the check returns
`true`. `IsOpenable` (`EthCLLib/Proofs/MerkleOpening.lean`) is the path-shaped
hypothesis, and every `IsPerfect` tree satisfies it at every index
(`isOpenable_of_isPerfect`).

The theorems quantify over `Node.merkleRoot`, the tree's own root. The spec's
callers pass a root from elsewhere: `process_deposit` reads
`state.eth1_data.deposit_root`, and hands the check a wire-deserialised `Array`
rather than a `Node`.

Bit ordering: `branch` runs bottom-to-top and entry `i` is the level-`i` sibling.
The routing convention lives in `EthCLLib.Spec.MerklePath`. The shipped check and
this fold both call `routeRight`, so the two agree by definition.

Under an abstract `[HasherTag]`, `isValidMerkleBranch_complete` and the two guard
bridges apply as they stand. The results carrying `[CombineWidth32 HasherTag.H]`
need `pureHasherTag` or `fastHasherTag`, since `HasherTag.H` is otherwise a stuck
projection matching no instance.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache.MerkleTree
open SizzLean.Proofs
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

/-- **Reads at or above `depth` cannot matter.** Two branches agreeing below
`depth` drive the same walk. The induction step can therefore ignore the sibling
`siblingPath` pushes on at the top. -/
private theorem branchFold_congr [HasherTag] (leaf : ByteArray)
    (b b' : Array (Vector UInt8 32)) (depth index : Nat)
    (hagree : ∀ i, i < depth → b[i]! = b'[i]!) :
    branchFold leaf b depth index = branchFold leaf b' depth index := by
  induction depth with
  | zero => rfl
  | succ d ih =>
      rw [branchFold_succ, branchFold_succ, ih (fun i hi => hagree i (by omega)),
          hagree d (by omega)]

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

/-- **Core completeness.** Along an openable path into `n`, folding the extracted
leaf and sibling path reconstructs the tree's root.

The proof inducts on `IsOpenable`. Each pair case peels the top level with
`branchFold_succ`. It then rewrites the lower `d` steps to ignore the pushed top
sibling, through `branchFold_congr` against `getElem!_push_lt`, in range by
`siblingPath_size`. It applies the sub-path IH, rewrites the cached sibling read
back to `merkleRoot` (`rootOf_eq_merkleRoot`, which needs no hypothesis), and
closes with `merkleRoot_pair`. Each constructor fixes its own bit, so neither
case has to split.

The base case is the `rootOf`/`merkleRoot` bridge: a zero-step fold returns the
stop node's root unchanged.

The siblings arrive root-typed, as `isValidMerkleBranch` takes them, and each
`vecToBytes (bytesToRoot ·)` round-trips on the 32-byte widths `IsOpenable`
carries. -/
private theorem branchFold_eq_merkleRoot [HasherTag] :
    ∀ {n : Node} {depth index : Nat}, IsOpenable HasherTag.H n depth index →
      branchFold (leafAt HasherTag.H n depth index)
          ((siblingPath HasherTag.H n depth index).map bytesToRoot) depth index
        = Node.merkleRoot HasherTag.H n := by
  intro n depth index ho
  induction ho with
  | stop m hsz index =>
      simpa [branchFold, leafAt_zero] using rootOf_eq_merkleRoot HasherTag.H m
  | @left l r d index c hbit hl hr32 hc ihl =>
      -- bit clear: our leaf sits in the LEFT subtree. The level-`d` sibling is
      -- `r`'s root, mixed on the right (`combine acc sibling`).
      -- The constructor and the fold both test `routeRight index d`, so `hbit`
      -- discharges the openers and the fold together.
      rw [branchFold_succ]
      simp only [leafAt, siblingPath, hbit, Bool.false_eq_true, if_false]
      have hsz : (siblingPath HasherTag.H l d index).size = d := siblingPath_size HasherTag.H hl
      rw [branchFold_congr _ _ ((siblingPath HasherTag.H l d index).map bytesToRoot) d index
            (fun i hi => by
              rw [Array.map_push, getElem!_push_lt _ _ _
                (by rw [Array.size_map, hsz]; exact hi)]),
          ihl]
      have htop := getElem!_push_size ((siblingPath HasherTag.H l d index).map bytesToRoot)
        (bytesToRoot (Node.rootOf HasherTag.H r))
      rw [Array.size_map, hsz] at htop
      rw [Array.map_push, htop,
        vecToBytes_bytesToRoot _ (by rw [rootOf_eq_merkleRoot]; exact hr32),
        rootOf_eq_merkleRoot HasherTag.H r, merkleRoot_pair HasherTag.H hc]
  | @right l r d index c hbit hr hl32 hc ihr =>
      -- bit set: our leaf sits in the RIGHT subtree. The level-`d` sibling is
      -- `l`'s root, mixed on the left (`combine sibling acc`).
      rw [branchFold_succ]
      simp only [leafAt, siblingPath, hbit, if_true]
      have hsz : (siblingPath HasherTag.H r d index).size = d := siblingPath_size HasherTag.H hr
      rw [branchFold_congr _ _ ((siblingPath HasherTag.H r d index).map bytesToRoot) d index
            (fun i hi => by
              rw [Array.map_push, getElem!_push_lt _ _ _
                (by rw [Array.size_map, hsz]; exact hi)]),
          ihr]
      have htop := getElem!_push_size ((siblingPath HasherTag.H r d index).map bytesToRoot)
        (bytesToRoot (Node.rootOf HasherTag.H l))
      rw [Array.size_map, hsz] at htop
      rw [Array.map_push, htop,
        vecToBytes_bytesToRoot _ (by rw [rootOf_eq_merkleRoot]; exact hl32),
        rootOf_eq_merkleRoot HasherTag.H l, merkleRoot_pair HasherTag.H hc]

/-- Sanity: at depth 1, the honest leaf of the left branch (bit 0 clear) is the
left leaf's bytes, root-typed. The path stops on a leaf, so `leafAt` reads its
bytes back without hashing.

`Node.rootOf` is `@[irreducible]`, so this enters its leaf arm by the named
equation lemma rather than by `rfl`. -/
example :
    let z : ByteArray := (ByteArray.mk (Array.replicate 32 0))
    let o : ByteArray := (ByteArray.mk (Array.replicate 32 1))
    honestLeaf Sha256Spec (.pair (.leaf z) (.leaf o) none) 1 0 = bytesToRoot z := by
  simp [honestLeaf, leafAt, Node.rootOf_leaf, routeRight]

/-- Root-typing a sibling array preserves its length. Named so the statement
below can cite it, rather than carrying `(by rw [Array.size_map]; exact hsize)`
inline where a reader expects a term. -/
theorem size_map_bytesToRoot {sibs : Array ByteArray} {depth : Nat}
    (hsize : sibs.size = depth) : (sibs.map bytesToRoot).size = depth := by
  rw [Array.size_map]; exact hsize

/-- **Completeness (acceptance #2).** Any openable path makes
`isValidMerkleBranch` accept its honest opening at `index` (`honestLeaf` and
`honestBranch`).

`IsOpenable` records the sibling widths itself, so this statement needs no
`CombineWidth32` instance. The check runs under the ambient `[HasherTag]`, and
the walk uses the same `HasherTag.H`, so both sides hash identically. -/
theorem isValidMerkleBranch_complete [HasherTag]
    {n : Node} {depth index : Nat} (ho : IsOpenable HasherTag.H n depth index) :
    isValidMerkleBranch (honestLeaf HasherTag.H n depth index)
        (honestBranch HasherTag.H n depth index)
        depth index (bytesToRoot (Node.merkleRoot HasherTag.H n))
      = true := by
  simp only [honestLeaf, honestBranch]
  have hleaf : (leafAt HasherTag.H n depth index).size = 32 := leafAt_size HasherTag.H ho
  -- the honest branch has size `depth`, so the shipped check's length guard passes
  have hsize :
      ((siblingPath HasherTag.H n depth index).map bytesToRoot).size = depth :=
    size_map_bytesToRoot (siblingPath_size HasherTag.H ho)
  rw [isValidMerkleBranch_iff _ _ _ _ _ hsize,
    vecToBytes_bytesToRoot _ hleaf, branchFold_eq_merkleRoot ho]

/-- Completeness on a perfect tree at any index, through `isOpenable_of_isPerfect`. The
`[CombineWidth32]` instance carries the 32-byte `combine` contract. The whole-tree
hypothesis needs that contract to know the width of every sibling root.

**Axiom use**: resolution at `Sha256` picks the instance proved from
`sha256Combine_eq_spec`, so an FFI instantiation inherits that axiom silently.
`Sha256Spec` resolves axiom-free. -/
theorem isValidMerkleBranch_complete_perfect [HasherTag] [CombineWidth32 HasherTag.H]
    {n : Node} {depth : Nat} (hp : IsPerfect HasherTag.H n depth) (index : Nat) :
    isValidMerkleBranch (honestLeaf HasherTag.H n depth index)
        (honestBranch HasherTag.H n depth index)
        depth index (bytesToRoot (Node.merkleRoot HasherTag.H n))
      = true :=
  isValidMerkleBranch_complete (isOpenable_of_isPerfect hp index)

/-- Completeness specialised to the pure-Lean `Sha256Spec` hasher, whose
`CombineWidth32` instance (built from `sha256Spec_combine_size`,
`SizzLean/Hasher/CombineWidth.lean`) supplies the size fact. -/
theorem isValidMerkleBranch_complete_sha256Spec
    {n : Node} {depth : Nat} (hp : IsPerfect Sha256Spec n depth) (index : Nat) :
    @isValidMerkleBranch pureHasherTag (honestLeaf Sha256Spec n depth index)
        (honestBranch Sha256Spec n depth index)
        depth index (bytesToRoot (Node.merkleRoot Sha256Spec n))
      = true := by
  haveI : CombineWidth32 pureHasherTag.H := inferInstanceAs (CombineWidth32 Sha256Spec)
  exact @isValidMerkleBranch_complete_perfect pureHasherTag _ n depth hp index

/-- Worked completeness: a concrete depth-1 `combine`-tree of two 32-byte leaves.
Feeding the honest opening of the left leaf makes the pure-`Sha256Spec` check
accept, discharged straight from `isValidMerkleBranch_complete_sha256Spec`. -/
example :
    let z : ByteArray := (ByteArray.mk (Array.replicate 32 0))
    let o : ByteArray := (ByteArray.mk (Array.replicate 32 1))
    @isValidMerkleBranch pureHasherTag
        (honestLeaf Sha256Spec (.pair (.leaf z) (.leaf o) none) 1 0)
        (honestBranch Sha256Spec (.pair (.leaf z) (.leaf o) none) 1 0)
        1 0
        (bytesToRoot (Node.merkleRoot Sha256Spec (.pair (.leaf z) (.leaf o) none)))
      = true := by
  exact isValidMerkleBranch_complete_sha256Spec
    (.pair (.leaf _ (by rfl)) (.leaf _ (by rfl)) (by simp)) 0

end EthCLLib.Proofs
