import EthCLSpecs.Proofs.Heze.ShouldExtendPayload

/-!
# `EthCLSpecs.Proofs.Heze.PayloadTiebreak`: a failed inclusion list loses the payload tiebreak

At a block from the previous slot, fork choice decides between the EMPTY node and the
FULL node of the block. `getWeight` gives weight `0` to both nodes
(`consensus-specs/specs/gloas/fork-choice.md:516-519`). The two nodes have the same root.
So `betterOf` in `getHead` decides by `getPayloadStatusTiebreaker` alone. EMPTY scores
`1`. FULL scores `2` when `shouldExtendPayload` is `true`, and `0` when it is `false`.
Heze's `shouldExtendPayload` is `false` for an unverified payload, and for a verified
payload with a recorded `false` inclusion-list answer (`ShouldExtendPayload.lean`).

This module proves that the `getHead` walk goes from the pending node of the block to
its EMPTY node. The step needs a block from the previous slot, and a recorded `false`
answer when the payload is verified. At a block that is not from the previous slot, the
attestation weights decide, and the tiebreaker is the payload status itself. On a weight
tie there, FULL (`1`) wins against EMPTY (`0`). Without a verified payload, the pending
node has only its EMPTY child.

`headLoopBody` names the loop body of `getHead` (`Gloas/ForkChoice.lean:534-569`), and
`getHead_eq_fuelLoop_headLoopBody` shows by `rfl` that `getHead` runs `fuelLoop` over it.
An edit to the loop breaks the build here. `getHeadStep_run_eq_empty_of_recorded_unsatisfied`
states that the body at the pending node returns `.next` of the EMPTY node.
`getHead_walk_pending_to_empty` then states it for the walk: whenever the `getHead` loop
reaches the pending node with fuel left, it continues from the EMPTY node. The module
does not prove that the walk reaches the pending node.

Every theorem about the loop body, the weights, and the tiebreakers takes the three
hypotheses that make the block a block from the previous slot: the block lookup
succeeds, the current slot is the slot after the block, and the slot increment does not
overflow. The theorems about FULL and the loop body also take `hfull`: when the payload
is verified, the recorded answer is `false`. `getNodeChildren_run_pending_unverified`
takes only an unverified payload. `betterOf_run_of_tie` takes none of these hypotheses:
it holds for any two nodes with the same root and the same weight. The default `[ExecutionEngine]` instance answers
`true` for every payload. So only a non-default engine records `false`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok
  fuelLoop_run_of_next)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd Step fuelLoop)
open EthCLSpecs.Heze (Preset Config Store Root ForkChoiceNode BeaconBlock Gwei getCurrentSlot
  isPayloadVerified isPreviousSlotPayloadDecision getPayloadStatusTiebreaker getWeight
  getNodeChildren getHead shouldExtendPayload)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- A pending node whose payload is not verified has one child, its EMPTY node. -/
theorem getNodeChildren_run_pending_unverified (store : Store map) (blocks : Array Root)
    (root : Root) (hunverified : isPayloadVerified store root = false) :
    (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
        store blocks (ForkChoiceNode.pending root)).run store
      = .ok (#[ForkChoiceNode.empty root], store) := by
  simp [getNodeChildren, ForkChoiceNode.pending, hunverified]
  rfl

variable [Config]

/-- The `betterOf` fold of the `getHead` loop over the children of one node, from
`children[0]!`. `headLoopBody` runs it. -/
def headFold (store : Store map) (children : Array ForkChoiceNode) :
    ForkChoiceStoreRun (Store map) ForkChoiceNode :=
  children.foldlM (init := children[0]!)
    (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store)

/-- The loop body of `getHead` at `head`: the children of `head`. With no children, the
walk stops at `head`. Otherwise it continues from the result of `headFold`. -/
def headLoopBody (store : Store map) (blocks : Array Root) (head : ForkChoiceNode) :
    ForkChoiceStoreRun (Store map) (Step ForkChoiceNode ForkChoiceNode) := do
  let children ← getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
    store blocks head
  if children.isEmpty then pure (.done head)
  else
    let best ← headFold store children
    pure (.next best)

/-- The fuel of the `getHead` loop. -/
def headFuel (store : Store map) : Nat := 2 * (FcMap.keys store.blocks).length + 2

/-- `getHead` runs `fuelLoop` over `headLoopBody`, from the pending node of the justified
root. The proof is `rfl`, so an edit to the `getHead` loop breaks this theorem. -/
theorem getHead_eq_fuelLoop_headLoopBody (store : Store map) :
    getHead (StoreTransition := ForkChoiceStoreRun (Store map)) store = (do
      let blocks ← EthCLSpecs.Heze.getFilteredBlockTree
        (StoreTransition := ForkChoiceStoreRun (Store map)) store
      let head : ForkChoiceNode := .pending store.justifiedCheckpoint.root
      fuelLoop (headFuel store) head head (headLoopBody store blocks)) :=
  rfl

/-- At a block from the previous slot, the tiebreaker of the EMPTY node is `1`. This
fact has no condition on the payload. -/
theorem getPayloadStatusTiebreaker_run_empty :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      (getPayloadStatusTiebreaker (StoreTransition := ForkChoiceStoreRun (Store map))
          store (ForkChoiceNode.empty root)).run store
        = .ok (1, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow
  simp [getPayloadStatusTiebreaker, isPreviousSlotPayloadDecision, ForkChoiceNode.empty,
    FcMap.getOrThrow, FcMap.getOrThrowKey, hblock, checkedAdd, hnooverflow, hcurrentslot,
    except_bind_ok]
  rfl

/-- At a block from the previous slot, the tiebreaker of the FULL node is `0` when a
verified payload has the recorded inclusion-list answer `false`. An unverified payload
also scores `0`: `shouldExtendPayload` rejects it before the FOCIL gate. -/
theorem getPayloadStatusTiebreaker_run_full_of_recorded_unsatisfied :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      (isPayloadVerified store root = true →
        FcMap.lookup store.payloadInclusionListSatisfaction root = some false) →
      (getPayloadStatusTiebreaker (StoreTransition := ForkChoiceStoreRun (Store map))
          store (ForkChoiceNode.full root)).run store
        = .ok (0, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow hfull
  have hextend :
      (shouldExtendPayload (StoreTransition := ForkChoiceStoreRun (Store map)) store root).run
          store
        = .ok (false, store) := by
    cases hverified : isPayloadVerified store root
    · exact shouldExtendPayload_run_eq_false_of_unverified store store store root rootBlock
        (rootBlock.slot + 1) hblock hcurrentslot hnooverflow rfl hverified
    · exact shouldExtendPayload_run_eq_false_of_recorded_unsatisfied
        store root rootBlock hblock hcurrentslot hnooverflow hverified (hfull hverified)
  simp [getPayloadStatusTiebreaker, isPreviousSlotPayloadDecision, ForkChoiceNode.full,
    FcMap.getOrThrow, FcMap.getOrThrowKey, hblock, checkedAdd, hnooverflow, hcurrentslot,
    except_bind_ok, hextend,
    EthCLSpecs.Heze.Const.payloadStatusEmpty, EthCLSpecs.Heze.Const.payloadStatusFull]
  rfl

/-- At a block from the previous slot, the EMPTY node and the FULL node both have
weight `0`. `getWeight` returns early when `isPreviousSlotPayloadDecision` is `true`. -/
theorem getWeight_run_of_previous_slot_decision :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock) (node : ForkChoiceNode),
      node.root = root →
      (node.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusEmpty ∨
        node.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusFull) →
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store node).run store
        = .ok (0, store) := by
  intro store root rootBlock node hroot hstatus hblock hcurrentslot hnooverflow
  subst hroot
  rcases hstatus with hs | hs <;>
    simp [getWeight, isPreviousSlotPayloadDecision, FcMap.getOrThrow, FcMap.getOrThrowKey,
      hblock, checkedAdd,
      hnooverflow, hcurrentslot, hs, except_bind_ok] <;>
    rfl

/-- `betterOf` on two nodes with the same root and the same weight picks by the
tiebreaker: `a` when its tiebreaker is greater, `b` otherwise. The roots compare equal
because the byte-vector order is reflexive (`Std.ReflOrd.compare_self`, through the
`LawfulEqOrd` instance of `EthCLLib/Spec/FiniteMap.lean`). -/
theorem betterOf_run_of_tie (store : Store map) (a b : ForkChoiceNode) (w : Gwei)
    (ta tb : UInt8) (hroot : a.root = b.root)
    (hwA : (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store a).run store
      = .ok (w, store))
    (hwB : (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run store
      = .ok (w, store))
    (htA : (getPayloadStatusTiebreaker (StoreTransition := ForkChoiceStoreRun (Store map))
        store a).run store = .ok (ta, store))
    (htB : (getPayloadStatusTiebreaker (StoreTransition := ForkChoiceStoreRun (Store map))
        store b).run store = .ok (tb, store)) :
    (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store a b).run store
      = .ok (if ta > tb then a else b, store) := by
  have hcmp : compare a.root b.root = Ordering.eq := by
    rw [hroot]
    exact Std.ReflOrd.compare_self
  have hww : ¬ (w < w) := UInt64.lt_irrefl w
  simp only [getHead.betterOf, run_bind, hwA, hwB, htA, htB, except_bind_ok, hcmp,
    gt_iff_lt, hww, if_false]
  rfl

/-- At a block from the previous slot, `betterOf` keeps the EMPTY node against itself.
The `getHead` fold starts from the EMPTY node, so it always makes this comparison. The
tiebreakers are equal, and `betterOf` returns its second argument on a tie. This fact has
no condition on the payload. -/
theorem betterOf_run_empty_self :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map))
          store (ForkChoiceNode.empty root) (ForkChoiceNode.empty root)).run store
        = .ok (ForkChoiceNode.empty root, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow
  have hwE := getWeight_run_of_previous_slot_decision store root rootBlock
    (ForkChoiceNode.empty root) rfl (Or.inl rfl) hblock hcurrentslot hnooverflow
  have htE := getPayloadStatusTiebreaker_run_empty store root rootBlock
    hblock hcurrentslot hnooverflow
  rw [betterOf_run_of_tie store _ _ 0 1 1 rfl hwE hwE htE htE, if_neg (by decide)]

/-- At a block from the previous slot, `betterOf` keeps the EMPTY node against the FULL
node under `hfull`. The two weights are `0`. The EMPTY tiebreaker `1` is greater than
the FULL tiebreaker `0`. -/
theorem betterOf_run_eq_empty_of_recorded_unsatisfied :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      (isPayloadVerified store root = true →
        FcMap.lookup store.payloadInclusionListSatisfaction root = some false) →
      (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map))
          store (ForkChoiceNode.empty root) (ForkChoiceNode.full root)).run store
        = .ok (ForkChoiceNode.empty root, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow hfull
  have hwE := getWeight_run_of_previous_slot_decision store root rootBlock
    (ForkChoiceNode.empty root) rfl (Or.inl rfl) hblock hcurrentslot hnooverflow
  have hwF := getWeight_run_of_previous_slot_decision store root rootBlock
    (ForkChoiceNode.full root) rfl (Or.inr rfl) hblock hcurrentslot hnooverflow
  have htE := getPayloadStatusTiebreaker_run_empty store root rootBlock
    hblock hcurrentslot hnooverflow
  have htF := getPayloadStatusTiebreaker_run_full_of_recorded_unsatisfied store root
    rootBlock hblock hcurrentslot hnooverflow hfull
  have hroot : (ForkChoiceNode.empty root).root = (ForkChoiceNode.full root).root := rfl
  have hgt : (1 : UInt8) > 0 := by decide
  rw [betterOf_run_of_tie store _ _ 0 1 0 hroot hwE hwF htE htF, if_pos hgt]

/-- Take a block from the previous slot. When its payload is verified, the recorded
inclusion-list answer is `false` (`hfull`). Then the `getHead` loop body at the pending
node of this block returns `.next` of its EMPTY node.

With a verified payload, the pending node has two children, and EMPTY wins the tiebreak
against FULL. Without one, EMPTY is the only child, and `hfull` holds trivially. In both
cases the children are not empty, so the loop does not stop at the pending node. -/
theorem getHeadStep_run_eq_empty_of_recorded_unsatisfied :
    ∀ (store : Store map) (blocks : Array Root) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      (isPayloadVerified store root = true →
        FcMap.lookup store.payloadInclusionListSatisfaction root = some false) →
      (headLoopBody store blocks (ForkChoiceNode.pending root)).run store
        = .ok (.next (ForkChoiceNode.empty root), store) := by
  intro store blocks root rootBlock hblock hcurrentslot hnooverflow hfull
  have hEE := betterOf_run_empty_self store root rootBlock hblock hcurrentslot hnooverflow
  unfold headLoopBody headFold
  cases hverified : isPayloadVerified store root
  · -- Not verified: one child, and the fold runs over the EMPTY node alone.
    rw [run_bind, getNodeChildren_run_pending_unverified store blocks root hverified,
      except_bind_ok]
    have hne : (#[ForkChoiceNode.empty root]).isEmpty = false := rfl
    have hfirst : #[ForkChoiceNode.empty root][0]! = ForkChoiceNode.empty root := rfl
    rw [hne, if_neg Bool.false_ne_true, hfirst, ← Array.foldlM_toList]
    simp only [List.foldlM_cons, List.foldlM_nil, run_bind, run_pure, hEE, except_bind_ok]
  · -- Verified: the pending node has two children, EMPTY, then FULL.
    have hEF := betterOf_run_eq_empty_of_recorded_unsatisfied store root rootBlock
      hblock hcurrentslot hnooverflow hfull
    have hchildren :
        (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
            store blocks (ForkChoiceNode.pending root)).run store
          = .ok (#[ForkChoiceNode.empty root, ForkChoiceNode.full root], store) := by
      simp [getNodeChildren, ForkChoiceNode.pending, hverified]
      rfl
    rw [run_bind, hchildren, except_bind_ok]
    have hne : (#[ForkChoiceNode.empty root, ForkChoiceNode.full root]).isEmpty = false :=
      rfl
    -- Fold over the two-element array as a list, one `betterOf` step at a time.
    have hfirst :
        #[ForkChoiceNode.empty root, ForkChoiceNode.full root][0]!
          = ForkChoiceNode.empty root :=
      rfl
    rw [hne, if_neg Bool.false_ne_true, hfirst, ← Array.foldlM_toList]
    simp only [List.foldlM_cons, List.foldlM_nil, run_bind, run_pure, hEE, hEF,
      except_bind_ok]

/-- The `getHead` walk under the hypotheses of
`getHeadStep_run_eq_empty_of_recorded_unsatisfied`. Take the loop that `getHead` runs
(`getHead_eq_fuelLoop_headLoopBody`), at the pending node of the block, with `fuel + 1`
units of fuel. The loop continues from the EMPTY node of the block, with `fuel` units,
and the store does not change. So the head that `getHead` returns from there is the
head of a walk from the EMPTY node. -/
theorem getHead_walk_pending_to_empty (store : Store map) (blocks : Array Root)
    (root : Root) (rootBlock : BeaconBlock) (fuel : Nat) (exhausted : ForkChoiceNode)
    (hblock : FcMap.lookup store.blocks root = some rootBlock)
    (hcurrentslot : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run store = .ok (rootBlock.slot + 1, store))
    (hnooverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot))
    (hfull : isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false) :
    (fuelLoop (fuel + 1) (ForkChoiceNode.pending root) exhausted
        (headLoopBody store blocks)).run store
      = (fuelLoop fuel (ForkChoiceNode.empty root) exhausted
          (headLoopBody store blocks)).run store :=
  fuelLoop_run_of_next fuel _ exhausted _ _ store store
    (getHeadStep_run_eq_empty_of_recorded_unsatisfied store blocks root rootBlock hblock
      hcurrentslot hnooverflow hfull)

end

end EthCLSpecs.Proofs.Heze
