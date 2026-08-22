import EthCLLib.Proofs.MerkleBranch
import EthCLLib.Proofs.MerkleShape
import SizzLean.Spec.GeneralizedIndex
import SizzLean.Proofs.ShapeWidth
import SizzLean.Proofs.ShapeAgreement

/-!
# `EthCLLib.Proofs.GeneralizedIndexBranch`: completeness at a generalized index

`isValidMerkleBranch` takes a `(depth, index)` pair. The spec's call sites carry
a *generalized index* and split it with `floorlog2` / `get_subtree_index`. This
module runs that split (`SizzLean.Spec.GeneralizedIndex`) and lands in the
completeness kit. It then instantiates the result at the shape the spec
addresses, a container field.

## What is proved

Completeness only: the check accepts every honest opening. Rejecting a forged
branch is binding, which has no sound statement under a real 64-to-32 `combine`.

Statements come in two spellings: over `Node.merkleRoot` of the built tree, and
over `SSZType.hashTreeRoot`. `merkleRoot_ofShape_eq_hashTreeRoot`
(`SizzLean/Proofs/ShapeAgreement.lean`) is the step between them.

## The zero-table hypothesis

`hzero` (pad perfection) arrives as a hypothesis, the way `ofSubtrees_isOpenable`
takes it. Reading the memo's bytes goes through `sha256Combine_eq_spec`. Keeping
`hzero` a parameter therefore leaves every theorem below axiom-free, and puts the
commitment at the instantiating call site (`zeroLeaf_isPerfect_sha256`).

The pad's root width follows from `hzero` through
`rootOf_zeroLeaf_size_of_isPerfect`, so it needs no second hypothesis.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open SizzLean
open SizzLean.Hasher
open SizzLean.Spec
open SizzLean.Cache.MerkleTree
open EthCLLib.Spec

/-- **Completeness at a generalized index.** Take a path witness at the
`(depth, index)` a gindex decomposes to. The check then accepts the honest
opening run at that same pair. This restates `isValidMerkleBranch_complete` in
the vocabulary call sites use, so no caller re-derives the split.

Nothing consumes `1 ≤ g`, since the check takes any index. It stays in the
statement to record the valid-gindex range. -/
theorem isValidMerkleBranch_complete_gindex [HasherTag]
    {n : Node} {g : GeneralizedIndex} (_hg : 1 ≤ g)
    (ho : IsOpenable HasherTag.H n (floorLog2 g) (getSubtreeIndex g)) :
    isValidMerkleBranch
        (honestLeaf HasherTag.H n (floorLog2 g) (getSubtreeIndex g))
        (honestBranch HasherTag.H n (floorLog2 g) (getSubtreeIndex g))
        (floorLog2 g) (getSubtreeIndex g)
        (bytesToRoot (Node.merkleRoot HasherTag.H n))
      = true :=
  isValidMerkleBranch_complete ho

/-- **A container's tree is openable at every field slot**, stated at the raw
`(depth, index)` pair rather than at a gindex. `Node.ofShape` builds
`.container fs` as `ofSubtrees` over the field sub-trees at depth
`chunkDepth fs.length` (`Build.lean:186-188`), and `ofSubtrees_isOpenable` opens
that at any position. `rootOf_subtreesForFields_size` is the sub-tree width side
condition.

The single witness: the gindex spelling below rewrites into it and the two-step
theorem composes two copies of it.

No bound on `k`: `ofSubtrees` pads, so a position past the field count is still
openable and opens onto padding. The in-range hypothesis appears only where the
*gindex* arithmetic needs it. -/
theorem ofShape_container_isOpenable' [HasherTag] [CombineWidth32 HasherTag.H]
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat) :
    IsOpenable HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
      (chunkDepth fs.length) k := by
  -- `brecOn` compiles `ofShape`, so it does not reduce by `rfl`. The equation
  -- lemma exposes the `ofSubtrees` form underneath.
  simp only [Node.ofShape]
  -- The capacity side condition: a container places one sub-tree per field, and
  -- `chunkDepth` is chosen to hold that many leaves.
  exact ofSubtrees_isOpenable HasherTag.H hzero (chunkDepth fs.length) _
    (by rw [subtreesForFields_length]; exact le_two_pow_chunkDepth fs.length)
    (rootOf_subtreesForFields_size HasherTag.H
      (rootOf_zeroLeaf_size_of_isPerfect HasherTag.H hzero) fs vs) k

/-- **A container field's gindex decomposes to its `(depth, index)` pair.** The
gindex arrives as `hg`, the success case of `get_generalized_index`. The
statements below therefore quantify over the `g` it produced, and not over the
`Except` that produced it.

`k < fs.length` puts the field inside the tree's capacity through
`le_two_pow_chunkDepth`, which is what the converse-decomposition lemmas need. -/
theorem gindexSplit_container_field {fs : List SSZType} {k : Nat}
    {g : GeneralizedIndex} (hk : k < fs.length)
    (hg : getGeneralizedIndex (.container fs) [.field k] = .ok g) :
    floorLog2 g = chunkDepth fs.length ∧ getSubtreeIndex g = k := by
  have hrange : k < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk (le_two_pow_chunkDepth fs.length)
  rw [getGeneralizedIndex_container_field hk] at hg
  -- `hg` is now `.ok (2 ^ d + k) = .ok g`. Strip the constructor to name `g`.
  have hgv : g = 2 ^ chunkDepth fs.length + k := by injection hg with h; exact h.symm
  subst hgv
  exact ⟨floorLog2_two_pow_add hrange, getSubtreeIndex_two_pow_add hrange⟩

/-- **A container field's gindex position is openable.** The same witness, read
at the `(depth, index)` pair `get_generalized_index` produces for field `k`. -/
theorem ofShape_container_isOpenable [HasherTag] [CombineWidth32 HasherTag.H]
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat)
    (g : GeneralizedIndex)
    (hg : getGeneralizedIndex (.container fs) [.field k] = .ok g)
    (hk : k < fs.length) :
    IsOpenable HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
      (floorLog2 g) (getSubtreeIndex g) := by
  obtain ⟨hdep, hidx⟩ := gindexSplit_container_field hk hg
  rw [hdep, hidx]
  exact ofShape_container_isOpenable' hzero fs vs k

/-- **Completeness at a container field's generalized index.** Opening
`Node.ofShape` for a container at the gindex `get_generalized_index` assigns
field `k`, and the check accepts.

This theorem states the leaf with `honestLeaf`, a tree-vocabulary opener.
`isValidMerkleBranch_complete_containerField_specLeaf` below restates that leaf
as field `k`'s `hash_tree_root`. A spec call site holds it in that second
form. -/
theorem isValidMerkleBranch_complete_containerField
    [HasherTag] [CombineWidth32 HasherTag.H]
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat)
    (g : GeneralizedIndex)
    (hg : getGeneralizedIndex (.container fs) [.field k] = .ok g)
    (hk : k < fs.length) :
    isValidMerkleBranch
        (honestLeaf HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (honestBranch HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (floorLog2 g) (getSubtreeIndex g)
        (bytesToRoot (Node.merkleRoot HasherTag.H
          (Node.ofShape HasherTag.H (.container fs) vs)))
      = true :=
  isValidMerkleBranch_complete
    (ofShape_container_isOpenable hzero fs vs k g hg hk)

/-- A two-step container path composes the two field gindices. The builder
threads its accumulator, so the outer gindex multiplies through the inner
container's width, which is the `2 ^ d₁ * 2 ^ d₂` split `IsOpenable.trans`
consumes.

`hfield` tells the builder the second step lands in a container. Without it
`elemType` cannot reduce. Both steps land on containers, the one shape whose
`itemPosition` is the plain index, so no packing correction survives into the
statement.

`hk₁` and `hk₂` discharge the two range checks. `hk₁` also lets `hfield` name the
field with `fs[k₁]`, the spelling the openability theorems below use, instead of
the `getD` default this proof needs internally. -/
theorem getGeneralizedIndex_container_field₂
    {fs : List SSZType} {k₁ : Nat} {gs : List SSZType} {k₂ : Nat}
    (hk₁ : k₁ < fs.length) (hk₂ : k₂ < gs.length)
    (hfield : fs[k₁] = .container gs) :
    getGeneralizedIndex (.container fs) [.field k₁, .field k₂]
      = .ok ((2 ^ chunkDepth fs.length + k₁) * 2 ^ chunkDepth gs.length + k₂) := by
  -- `elemType` reads the field with `getD`, and `simp` normalises that to the
  -- `getElem?` spelling. Restate `hfield` in that form or it stops matching the
  -- rewritten goal. `hk₁` is what turns the `getElem?` back into `hfield`'s
  -- total `getElem`.
  have hfield' : (fs[k₁]?).getD .bool = .container gs := by
    rw [List.getElem?_eq_getElem hk₁]; exact hfield
  simp [getGeneralizedIndex, getGeneralizedIndex.go, getPowerOfTwoCeil, chunkCount,
    itemPosition, elemType, hfield', stepCapacity, SSZType.isBasicType,
    Nat.not_le.mpr hk₁, Nat.not_le.mpr hk₂]

/-- **A two-step container path is openable.** The outer container's field `k₁`
holds a container sub-tree. Opening that sub-tree at its own field `k₂` composes
with the outer path by `IsOpenable.trans`, at the concatenated index
`k₁ * 2 ^ d₂ + k₂` the gindex builder produces.

`nodeAt_ofShape_container` supplies the tree step. The outer tree's field-`k₁`
sub-tree *is* the field value's own `ofShape` tree.

The caller owes two facts about the schema, and none about the tree. Field
`k₁`'s type is the container `gs` (`hfield`), and its value is `ws` (`hval`).
Both are `rfl` / `HEq.refl` at any concrete container, and neither mentions
`nodeAt`.

`hval` is a `HEq` because `SSZType.fieldAt fs vs k₁ hk₁` has type
`(fs[k₁]).interp`. That becomes `interpFields gs` only once `hfield` applies, so
`congr` on `Node.ofShape` relates the two, and `Eq` does not.

`hk₁ : k₁ < fs.length` is what lets the statement name field `k₁` at all. The
one-step witness needs no such bound, since `ofSubtrees` pads every position. -/
theorem ofShape_container_isOpenable₂ [HasherTag] [CombineWidth32 HasherTag.H]
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs)
    (k₁ : Nat) (hk₁ : k₁ < fs.length)
    (gs : List SSZType) (ws : SSZType.interpFields gs) (k₂ : Nat)
    (hk₂ : k₂ < gs.length)
    (hfield : fs[k₁] = .container gs)
    (hval : HEq (SSZType.fieldAt fs vs k₁ hk₁) ws) :
    IsOpenable HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
      (chunkDepth fs.length + chunkDepth gs.length)
      (k₁ * 2 ^ chunkDepth gs.length + k₂) := by
  refine IsOpenable.trans
    (ofShape_container_isOpenable' hzero fs vs k₁) ?_
    (Nat.lt_of_lt_of_le hk₂ (le_two_pow_chunkDepth gs.length))
  have hsub : nodeAt (Node.ofShape HasherTag.H (.container fs) vs)
        (chunkDepth fs.length) k₁
      = Node.ofShape HasherTag.H (.container gs) ws := by
    rw [nodeAt_ofShape_container HasherTag.H fs vs k₁ hk₁]
    congr 1
  rw [hsub]
  exact ofShape_container_isOpenable' hzero gs ws k₂

/-- **A two-step container gindex decomposes to its `(depth, index)` pair.** The
composed gindex is `2 ^ (d₁ + d₂) + (k₁ * 2 ^ d₂ + k₂)`. The one-step converse
lemmas take that form, once the proof bounds the index by `2 ^ (d₁ + d₂)`. -/
theorem gindexSplit_container_field₂ {fs gs : List SSZType} {k₁ k₂ : Nat}
    {g : GeneralizedIndex} (hk₁ : k₁ < fs.length) (hk₂ : k₂ < gs.length)
    (hfield : fs[k₁] = .container gs)
    (hg : getGeneralizedIndex (.container fs) [.field k₁, .field k₂] = .ok g) :
    floorLog2 g = chunkDepth fs.length + chunkDepth gs.length
      ∧ getSubtreeIndex g = k₁ * 2 ^ chunkDepth gs.length + k₂ := by
  have h1 : k₁ < 2 ^ chunkDepth fs.length :=
    Nat.lt_of_lt_of_le hk₁ (le_two_pow_chunkDepth fs.length)
  have h2 : k₂ < 2 ^ chunkDepth gs.length :=
    Nat.lt_of_lt_of_le hk₂ (le_two_pow_chunkDepth gs.length)
  -- The composed index fits the composed depth. `k₁` contributes at most
  -- `2 ^ d₁ - 1` blocks of `2 ^ d₂`, and `k₂` stays inside one block.
  have hidx : k₁ * 2 ^ chunkDepth gs.length + k₂
      < 2 ^ (chunkDepth fs.length + chunkDepth gs.length) := by
    have hstep : k₁ * 2 ^ chunkDepth gs.length + k₂
        < (k₁ + 1) * 2 ^ chunkDepth gs.length := by
      rw [Nat.succ_mul]; omega
    have hle : (k₁ + 1) * 2 ^ chunkDepth gs.length
        ≤ 2 ^ chunkDepth fs.length * 2 ^ chunkDepth gs.length :=
      Nat.mul_le_mul_right _ h1
    rw [← Nat.pow_add] at hle
    omega
  -- Rewrite the builder's `(2 ^ d₁ + k₁) * 2 ^ d₂ + k₂` into the `2 ^ d + i` form
  -- the converse lemmas take.
  have hshape : (2 ^ chunkDepth fs.length + k₁) * 2 ^ chunkDepth gs.length + k₂
      = 2 ^ (chunkDepth fs.length + chunkDepth gs.length)
        + (k₁ * 2 ^ chunkDepth gs.length + k₂) := by
    rw [Nat.add_mul, Nat.pow_add, Nat.add_assoc]
  rw [getGeneralizedIndex_container_field₂ hk₁ hk₂ hfield] at hg
  have hgv : g = 2 ^ (chunkDepth fs.length + chunkDepth gs.length)
      + (k₁ * 2 ^ chunkDepth gs.length + k₂) := by
    injection hg with h; rw [← h, hshape]
  subst hgv
  exact ⟨floorLog2_two_pow_add hidx, getSubtreeIndex_two_pow_add hidx⟩

/-- **Completeness at a two-step container gindex.** The shape behind
`FINALIZED_ROOT_GINDEX` (`BeaconState.finalized_checkpoint.root`) and
`EXECUTION_BLOCK_HASH_GINDEX`
(`BeaconBlockBody.execution_payload.block_hash`).

Stated at the raw `(depth, index)` pair. `getGeneralizedIndex_container_field₂`
above is the arithmetic half. It shows the gindex those constants carry composes
to exactly this depth and index. Neither constant appears here, and the concrete
field lists never appear either, so the `#guard`ed arithmetic below is what ties
the two together. Inherits the two schema facts from the witness. -/
theorem isValidMerkleBranch_complete_containerField₂
    [HasherTag] [CombineWidth32 HasherTag.H]
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs)
    (k₁ : Nat) (hk₁ : k₁ < fs.length)
    (gs : List SSZType) (ws : SSZType.interpFields gs) (k₂ : Nat)
    (hk₂ : k₂ < gs.length)
    (hfield : fs[k₁] = .container gs)
    (hval : HEq (SSZType.fieldAt fs vs k₁ hk₁) ws) :
    isValidMerkleBranch
        (honestLeaf HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (chunkDepth fs.length + chunkDepth gs.length)
          (k₁ * 2 ^ chunkDepth gs.length + k₂))
        (honestBranch HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (chunkDepth fs.length + chunkDepth gs.length)
          (k₁ * 2 ^ chunkDepth gs.length + k₂))
        (chunkDepth fs.length + chunkDepth gs.length)
        (k₁ * 2 ^ chunkDepth gs.length + k₂)
        (bytesToRoot (Node.merkleRoot HasherTag.H
          (Node.ofShape HasherTag.H (.container fs) vs)))
      = true :=
  isValidMerkleBranch_complete
    (ofShape_container_isOpenable₂ hzero fs vs k₁ hk₁ gs ws k₂ hk₂
      hfield hval)

/-- **The same, at the gindex a caller holds.** The statement quantifies over the
`g` that `get_generalized_index` produced. `gindexSplit_container_field₂` supplies
the depth and the index.

`isValidMerkleBranch_complete_containerField` is the one-step form. -/
theorem isValidMerkleBranch_complete_containerField₂_gindex
    [HasherTag] [CombineWidth32 HasherTag.H]
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs)
    (k₁ : Nat) (hk₁ : k₁ < fs.length)
    (gs : List SSZType) (ws : SSZType.interpFields gs) (k₂ : Nat)
    (hk₂ : k₂ < gs.length)
    (hfield : fs[k₁] = .container gs)
    (hval : HEq (SSZType.fieldAt fs vs k₁ hk₁) ws)
    (g : GeneralizedIndex)
    (hg : getGeneralizedIndex (.container fs) [.field k₁, .field k₂] = .ok g) :
    isValidMerkleBranch
        (honestLeaf HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (honestBranch HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (floorLog2 g) (getSubtreeIndex g)
        (bytesToRoot (Node.merkleRoot HasherTag.H
          (Node.ofShape HasherTag.H (.container fs) vs)))
      = true := by
  obtain ⟨hdep, hidx⟩ := gindexSplit_container_field₂ hk₁ hk₂ hfield hg
  rw [hdep, hidx]
  exact isValidMerkleBranch_complete_containerField₂ hzero fs vs k₁ hk₁ gs ws k₂ hk₂
    hfield hval

/-! ### Restated over the spec's roots

Everything above concludes about `Node.merkleRoot` of a built tree, which is our
construction rather than the spec's. `merkleRoot_ofShape_eq_hashTreeRoot` says
that root *is* the container's `hash_tree_root`, so the same theorems restate
against the spec function, which is what a client computes. -/

/-- **The verified root is the container's own `hash_tree_root`.** -/
theorem isValidMerkleBranch_complete_containerField_specRoot
    [HasherTag] [CombineWidth32 HasherTag.H]
    (hzt : ∀ d, Node.rootOf HasherTag.H (zeroLeaf HasherTag.H d)
            = zeroHashAtDepth HasherTag.H d)
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat)
    (g : GeneralizedIndex)
    (hg : getGeneralizedIndex (.container fs) [.field k] = .ok g)
    (hk : k < fs.length) :
    isValidMerkleBranch
        (honestLeaf HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (honestBranch HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (floorLog2 g) (getSubtreeIndex g)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container fs) vs))
      = true := by
  rw [← merkleRoot_ofShape_eq_hashTreeRoot HasherTag.H hzt (.container fs) vs]
  exact isValidMerkleBranch_complete_containerField hzero fs vs k g hg hk

/-- **The opened leaf is the field's own `hash_tree_root`.**

* `leafAt_eq_rootOf_nodeAt` moves from the leaf opener to the node opener.
* `nodeAt_ofShape_container` identifies that node as field `k`'s tree.
* `rootOf_ofShape_eq_hashTreeRoot` turns its root into the spec function. -/
theorem honestLeaf_ofShape_container [HasherTag]
    (hzt : ∀ d, Node.rootOf HasherTag.H (zeroLeaf HasherTag.H d)
            = zeroHashAtDepth HasherTag.H d)
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat) (hk : k < fs.length) :
    honestLeaf HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
        (chunkDepth fs.length) k
      = bytesToRoot (SSZType.hashTreeRoot HasherTag.H fs[k] (SSZType.fieldAt fs vs k hk)) := by
  unfold honestLeaf
  rw [leafAt_eq_rootOf_nodeAt, nodeAt_ofShape_container HasherTag.H fs vs k hk,
    rootOf_ofShape_eq_hashTreeRoot HasherTag.H hzt]

/-- **Completeness with both sides in the spec's vocabulary.** The leaf is field
`k`'s `hash_tree_root`. The root is the container's `hash_tree_root`.

Spec call sites carry this shape. `verify_data_column_sidecar_inclusion_proof`
passes `hash_tree_root(sidecar.kzg_commitments)` against `body_root`. The
light-client `EXECUTION_PAYLOAD` and sync-committee proofs pass a field root
against the body or state root. -/
theorem isValidMerkleBranch_complete_containerField_specLeaf
    [HasherTag] [CombineWidth32 HasherTag.H]
    (hzt : ∀ d, Node.rootOf HasherTag.H (zeroLeaf HasherTag.H d)
            = zeroHashAtDepth HasherTag.H d)
    (hzero : ∀ d, IsPerfect HasherTag.H (zeroLeaf HasherTag.H d) d)
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat)
    (g : GeneralizedIndex)
    (hg : getGeneralizedIndex (.container fs) [.field k] = .ok g)
    (hk : k < fs.length) :
    isValidMerkleBranch
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H fs[k] (SSZType.fieldAt fs vs k hk)))
        (honestBranch HasherTag.H (Node.ofShape HasherTag.H (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (floorLog2 g) (getSubtreeIndex g)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container fs) vs))
      = true := by
  obtain ⟨hdep, hidx⟩ := gindexSplit_container_field hk hg
  rw [← honestLeaf_ofShape_container hzt fs vs k hk, ← hdep, ← hidx]
  exact isValidMerkleBranch_complete_containerField_specRoot hzt hzero fs vs k g hg hk

/-- **The same statement at the shipped hasher, with no hypotheses left.**
`rootOf_zeroLeaf_eq_zeroHashAtDepth_sha256` closes `hzt`, and
`zeroLeaf_isPerfect_sha256` closes `hzero`.

**Axiom use**: `sha256Combine_eq_spec` (`Hasher/Sha256Equiv.lean`), through both
dischargers. The zero tower is memoised from the FFI `sha256Combine`. -/
theorem isValidMerkleBranch_complete_containerField_specRoot_sha256
    (fs : List SSZType) (vs : SSZType.interpFields fs) (k : Nat)
    (g : GeneralizedIndex)
    (hg : getGeneralizedIndex (.container fs) [.field k] = .ok g)
    (hk : k < fs.length) :
    @isValidMerkleBranch fastHasherTag
        (honestLeaf Sha256 (Node.ofShape Sha256 (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (honestBranch Sha256 (Node.ofShape Sha256 (.container fs) vs)
          (floorLog2 g) (getSubtreeIndex g))
        (floorLog2 g) (getSubtreeIndex g)
        (bytesToRoot (SSZType.hashTreeRoot Sha256 (.container fs) vs))
      = true := by
  haveI : CombineWidth32 fastHasherTag.H := inferInstanceAs (CombineWidth32 Sha256)
  exact @isValidMerkleBranch_complete_containerField_specRoot fastHasherTag _
    rootOf_zeroLeaf_eq_zeroHashAtDepth_sha256 zeroLeaf_isPerfect_sha256
    fs vs k g hg hk

/-! **Pin: the light-client gindices decompose as the spec says.** Values from
`consensus-specs` (`altair/`, `capella/` and `electra/light-client/sync-protocol.md`).
Each is a one-step container field, so `isValidMerkleBranch_complete_containerField`
covers it. Kept as a regression on the `floorLog2` / `getSubtreeIndex` pair every
call site above passes to the check. -/
-- capella `EXECUTION_PAYLOAD_GINDEX`: `BeaconBlockBody` field 9 of 11.
#guard floorLog2 25 == 4 && getSubtreeIndex 25 == 9
-- altair `CURRENT_` / `NEXT_SYNC_COMMITTEE_GINDEX`: `BeaconState` fields 22, 23
-- of 24.
#guard floorLog2 54 == 5 && getSubtreeIndex 54 == 22
#guard floorLog2 55 == 5 && getSubtreeIndex 55 == 23
-- The `_ELECTRA` respellings of the same two fields, which is what Fulu and
-- Gloas carry: Electra's `BeaconState` grew to 37 fields, and Fulu (38) and
-- Gloas (46) grew it again, all inside `(32, 64]`, so the depth is 6, not 5.
#guard floorLog2 86 == 6 && getSubtreeIndex 86 == 22
#guard floorLog2 87 == 6 && getSubtreeIndex 87 == 23

/-! **Pin: gindex composition is `trans`'s index concatenation.**
`EXECUTION_BLOCK_HASH_GINDEX = 412` walks capella `BeaconBlockBody` field 9 of
11 at depth 4. It then walks capella `ExecutionPayload` field 12 of 15, also at
depth 4. That is `25 * 2 ^ 4 + 12 = 412`. Decomposed it is depth `4 + 4` and index
`9 * 2 ^ 4 + 12 = 156`, which is exactly `IsOpenable.trans`'s
`i₁ * 2 ^ d₂ + i₂`.

`FINALIZED_ROOT_GINDEX = 105` follows the same law at `52 * 2 + 1`, depth
`5 + 1`, index `20 * 2 + 1 = 41`. Its `_ELECTRA` respelling `169` is
`84 * 2 + 1` over the 37-field Electra `BeaconState`.

`EXECUTION_BLOCK_HASH_GINDEX_GLOAS = 832` (`gloas/light-client/sync-protocol.md:55`)
is a three-step path, `signed_execution_payload_bid` then `message` then
`parent_block_hash`. The two-step composition does not reach it, so only its
`(depth, index)` split appears below. -/
#guard floorLog2 412 == 4 + 4 && getSubtreeIndex 412 == 9 * 2 ^ 4 + 12
#guard floorLog2 105 == 5 + 1 && getSubtreeIndex 105 == 20 * 2 + 1
#guard floorLog2 169 == 6 + 1 && getSubtreeIndex 169 == 20 * 2 + 1
#guard floorLog2 832 == 9 && getSubtreeIndex 832 == 320

end EthCLLib.Proofs
