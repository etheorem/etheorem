import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty

/-!
# `EthCLSpecs.Proofs.Heze.CensorshipCost`: a failed inclusion list costs the payload

This module states two facts about one block side by side. It uses
`PayloadTiebreak.lean` and `ParentPayloadEmpty.lean`. Take a block from the previous
slot with a verified payload whose recorded inclusion-list answer is `false`. Then:

1. one step of the `getHead` walk at the pending node of the block goes to its EMPTY
   node; and
2. take any child of the block that fork choice puts under the EMPTY node, with the
   empty parent requests. Process it on a state that caches the bid of the block. Then
   `processParentExecutionPayload` does not change the state, and it does not settle
   the bid of the block.

The two facts are independent. Fact 2 holds for every child on the EMPTY edge, and it
uses only the block lookup. No theorem here connects the child to the head step. A
proposer that follows fork choice builds on EMPTY, but the model does not include the
proposer. A child built on the FULL edge settles the bid through
`applyParentExecutionPayload`.

The theorem also does not cover the full `getHead` walk or later blocks. After a child
on the EMPTY edge, the epoch substep `processBuilderPendingPayments` is the remaining
path for the bid (`BuilderPendingPayments.lean`). This module does not use that
theorem. A proof that no other path pays the bid needs an invariant over whole traces.
`processProposerSlashing` can also clear the pending payment.

The answer comes from the `[ExecutionEngine]` seam. The default instance answers `true`
for every payload, so only a non-default engine gives the recorded `false`. No theorem
in this module names a transaction.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State Root ForkChoiceNode BeaconBlock
  ExecutionRequests getCurrentSlot isPayloadVerified getNodeChildren getHead
  getParentPayloadStatus processParentExecutionPayload)

/-- The conditions under which fork choice sees a payload that fails the inclusion
list. `root` names the block `rootBlock` from the previous slot. The payload of the
block is verified. The recorded inclusion-list answer for the payload is `false`. -/
structure UnsatisfiedPayload {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
    (store : Store map) (root : Root) (rootBlock : BeaconBlock) : Prop where
  /-- The store holds the block at `root`. -/
  block : FcMap.lookup store.blocks root = some rootBlock
  /-- The current slot is the slot after the block. -/
  currentSlot :
    (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
      = .ok (rootBlock.slot + 1, store)
  /-- The slot increment does not overflow. -/
  noOverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot)
  /-- The payload of the block is verified. -/
  verified : isPayloadVerified store root = true
  /-- The recorded inclusion-list answer for the payload is `false`. -/
  unsatisfied : FcMap.lookup store.payloadInclusionListSatisfaction root = some false

/-- Two facts under `UnsatisfiedPayload`. First, the head step at the pending node of
the block selects the EMPTY node. Second, take any child of the block that fork choice
puts under EMPTY, with the empty parent requests. Run `processParentExecutionPayload`
for the child on a state that caches the bid of the block. The run does not change the
state. The module docstring explains why the two facts are independent. -/
theorem unsatisfiedPayload_headEmpty_and_emptyChild_unsettled
    {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
    (store : Store map) (root : Root) (rootBlock : BeaconBlock) (blocks : Array Root)
    (h : UnsatisfiedPayload store root rootBlock) :
    (do
        let children ← getNodeChildren
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store blocks (ForkChoiceNode.pending root)
        children.foldlM (init := children[0]!)
          (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store)
      : ForkChoiceStoreRun (Store map) ForkChoiceNode).run store
      = .ok (ForkChoiceNode.empty root, store) ∧
    ∀ (child : BeaconBlock) (state : State),
      child.parentRoot = root →
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store child).run store
        = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, store) →
      sszGet state latestExecutionPayloadBid
        = rootBlock.body.signedExecutionPayloadBid.message →
      htr child.body.parentExecutionRequests = htr (default : ExecutionRequests) →
      (processParentExecutionPayload (StateTransition := HezeRun) child).run state
        = .ok ((), state) := by
  refine ⟨getHeadStep_run_eq_empty_of_recorded_unsatisfied store blocks root rootBlock
    h.block h.currentSlot h.noOverflow h.verified h.unsatisfied, ?_⟩
  intro child state hparent hstatus hcached hreq
  have hlookup : FcMap.lookup store.blocks child.parentRoot = some rootBlock := by
    rw [hparent]; exact h.block
  have hne := (getParentPayloadStatus_run_eq_empty_iff store child rootBlock hlookup).mp hstatus
  exact processParentExecutionPayload_run_of_empty_parent state child
    (by rw [hcached]; exact hne) hreq

end EthCLSpecs.Proofs.Heze
