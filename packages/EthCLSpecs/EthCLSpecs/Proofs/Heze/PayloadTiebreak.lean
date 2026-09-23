import EthCLSpecs.Proofs.Heze.ShouldExtendPayload
import EthCLSpecs.Proofs.OrdVector

/-!
# `EthCLSpecs.Proofs.Heze.PayloadTiebreak`: a failed inclusion list loses the payload tiebreak

At a block from the previous slot, fork choice decides between the EMPTY node and the
FULL node of the block. `getWeight` gives weight `0` to both nodes
(`consensus-specs/specs/gloas/fork-choice.md:518`). The two nodes have the same root.
So `betterOf` in `getHead` decides by `getPayloadStatusTiebreaker` alone. EMPTY scores
`1`. FULL scores `2` when `shouldExtendPayload` is `true`, and `0` when it is `false`.
Heze's `shouldExtendPayload` is `false` for a verified payload with a recorded `false`
inclusion-list answer (`ShouldExtendPayload.lean`).

This module proves that, under these conditions, one step of the `getHead` walk goes
from the pending node of the block to its EMPTY node. At a block that is not from the
previous slot, the attestation weights decide, and the tiebreaker is the payload status
itself. On a weight tie there, FULL (`1`) wins against EMPTY (`0`). The module does not
prove a fact about the full walk.

The step theorem restates the body of the `getHead` loop
(`Gloas/ForkChoice.lean:534-569`) as a `do` block. The restatement leaves out the
`children.isEmpty` guard and the `.next` wrapper. It does not refer to `getHead`
itself. So an edit to that loop body outside `betterOf` does not break the theorem.
Check the restatement against the loop when `getHead` changes.

All theorems use the first three hypotheses of
`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`: the block lookup
succeeds, the current slot is the slot after the block, and the slot increment does
not overflow. Together, these make the block a block from the previous slot. The
theorems about the FULL tiebreaker, `betterOf`, and the head step also use the last two
hypotheses: the payload is verified, and the recorded answer is `false`. The default
`[ExecutionEngine]` instance answers `true` for every payload. So only a non-default
engine records `false`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun compare_vectorUInt8_self run_bind run_pure
  except_bind_ok)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd)
open EthCLSpecs.Heze (Preset Config Store Root ForkChoiceNode BeaconBlock getCurrentSlot
  isPayloadVerified isPreviousSlotPayloadDecision getPayloadStatusTiebreaker getWeight
  getNodeChildren getHead)

section
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

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

/-- At a block from the previous slot, the tiebreaker of the FULL node is `0` when the
payload is verified and its recorded inclusion-list answer is `false`. -/
theorem getPayloadStatusTiebreaker_run_full_of_recorded_unsatisfied :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (getPayloadStatusTiebreaker (StoreTransition := ForkChoiceStoreRun (Store map))
          store (ForkChoiceNode.full root)).run store
        = .ok (0, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow hverified hunsatisfied
  have hextend := shouldExtendPayload_run_eq_false_of_recorded_unsatisfied
    store root rootBlock hblock hcurrentslot hnooverflow hverified hunsatisfied
  simp [getPayloadStatusTiebreaker, isPreviousSlotPayloadDecision, ForkChoiceNode.full,
    FcMap.getOrThrow, FcMap.getOrThrowKey, hblock, checkedAdd, hnooverflow, hcurrentslot,
    except_bind_ok, hextend,
    EthCLSpecs.Heze.Const.payloadStatusEmpty, EthCLSpecs.Heze.Const.payloadStatusFull]
  rfl

/-- At a block from the previous slot, the EMPTY node and the FULL node both have
weight `0`. `getWeight` returns early when `isPreviousSlotPayloadDecision` is `true`.
The theorem applies to a node of either decided status. -/
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

/-- `betterOf` keeps the EMPTY node against itself and against the FULL node. These are
the two comparisons that the `getHead` fold makes, because the fold starts from the
EMPTY node. The two weights are `0`. The two roots are equal
(`compare_vectorUInt8_self`). The EMPTY tiebreaker `1` is greater than the FULL
tiebreaker `0`. -/
theorem betterOf_run_eq_empty_of_recorded_unsatisfied :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      ∀ other ∈ [ForkChoiceNode.empty root, ForkChoiceNode.full root],
        (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map))
            store (ForkChoiceNode.empty root) other).run store
          = .ok (ForkChoiceNode.empty root, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow hverified hunsatisfied other hother
  have hwE := getWeight_run_of_previous_slot_decision store root rootBlock
    (ForkChoiceNode.empty root) rfl (Or.inl rfl) hblock hcurrentslot hnooverflow
  have hwF := getWeight_run_of_previous_slot_decision store root rootBlock
    (ForkChoiceNode.full root) rfl (Or.inr rfl) hblock hcurrentslot hnooverflow
  have htE := getPayloadStatusTiebreaker_run_empty store root rootBlock
    hblock hcurrentslot hnooverflow
  have htF := getPayloadStatusTiebreaker_run_full_of_recorded_unsatisfied store root rootBlock
    hblock hcurrentslot hnooverflow hverified hunsatisfied
  -- Both nodes project to `root`. Stated as rewrites so that `simp` keeps the node
  -- constructors folded, and `hwE` / `htE` / `hwF` / `htF` still match.
  have hrootE : (ForkChoiceNode.empty root).root = root := rfl
  have hrootF : (ForkChoiceNode.full root).root = root := rfl
  have hcmp : compare root root = Ordering.eq := compare_vectorUInt8_self root
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hother
  rcases hother with rfl | rfl <;>
    simp only [getHead.betterOf, run_bind, hwE, hwF, htE, htF,
      except_bind_ok, hrootE, hrootF, hcmp] <;>
    simp <;>
    rfl

/-- Take a block from the previous slot with a verified payload whose recorded
inclusion-list answer is `false`. One step of the `getHead` walk at the pending node of
this block goes to its EMPTY node. The statement restates the body of the `getHead`
loop: first the children of the pending node, then the `betterOf` fold that starts from
`children[0]!`. The module docstring lists what the restatement leaves out. -/
theorem getHeadStep_run_eq_empty_of_recorded_unsatisfied :
    ∀ (store : Store map) (blocks : Array Root) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (do
          let children ← getNodeChildren
            (StoreTransition := ForkChoiceStoreRun (Store map))
            store blocks (ForkChoiceNode.pending root)
          children.foldlM (init := children[0]!)
            (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store)
        : ForkChoiceStoreRun (Store map) ForkChoiceNode).run store
        = .ok (ForkChoiceNode.empty root, store) := by
  intro store blocks root rootBlock hblock hcurrentslot hnooverflow hverified hunsatisfied
  have hbetter := betterOf_run_eq_empty_of_recorded_unsatisfied store root rootBlock
    hblock hcurrentslot hnooverflow hverified hunsatisfied
  have hEE := hbetter (ForkChoiceNode.empty root) (by simp)
  have hEF := hbetter (ForkChoiceNode.full root) (by simp)
  -- The pending node has a verified payload, so it has two children: EMPTY, then FULL.
  have hchildren :
      (getNodeChildren (StoreTransition := ForkChoiceStoreRun (Store map))
          store blocks (ForkChoiceNode.pending root)).run store
        = .ok (#[ForkChoiceNode.empty root, ForkChoiceNode.full root], store) := by
    simp [getNodeChildren, ForkChoiceNode.pending, hverified]
    rfl
  rw [run_bind, hchildren, except_bind_ok]
  -- Fold over the two-element array as a list, one `betterOf` step at a time.
  have hfirst :
      #[ForkChoiceNode.empty root, ForkChoiceNode.full root][0]! = ForkChoiceNode.empty root :=
    rfl
  rw [hfirst, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil, run_bind, run_pure, hEE, hEF,
    except_bind_ok]

end

end EthCLSpecs.Proofs.Heze
