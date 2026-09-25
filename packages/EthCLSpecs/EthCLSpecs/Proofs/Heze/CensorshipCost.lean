import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments

/-!
# `EthCLSpecs.Proofs.Heze.CensorshipCost`: what a failed inclusion list costs

`unsatisfiedPayload_cost` states three facts about one block. It uses
`PayloadTiebreak.lean`, `ParentPayloadEmpty.lean`, and `BuilderPendingPayments.lean`.
Take a block from the previous slot with a verified payload whose recorded
inclusion-list answer is `false`. Then:

1. one step of the `getHead` walk at the pending node of the block goes to its EMPTY
   node. The theorem does not cover the full walk;
2. take any child of the block that fork choice puts under the EMPTY node, with the
   empty parent requests. Process it on a state that caches the bid of the block. Then
   `processParentExecutionPayload` does not change the state, and it does not settle
   the bid of the block;
3. at the epoch substep that judges the payment of the bid, the withdrawal of the bid
   is queued if and only if its entry reaches the quorum.

Facts 1 and 2 are independent. Fact 2 holds for every child on the EMPTY edge, and it
uses only the block lookup. A proposer that follows fork choice builds on EMPTY, but the
model does not include the proposer. A child built on the FULL edge settles the bid
through `applyParentExecutionPayload`.

Fact 3 takes one hypothesis about the blocks between the bid and the epoch substep,
`BidPaymentCarried`: the entry for the slot of the bid still carries the withdrawal of
the bid when the substep reads it. The hypothesis excludes a proposer slashing of the
block's proposer, which clears the entry, and a child on the FULL edge, which settles
it. No theorem here proves the hypothesis from the block transitions.

The answer comes from the `[ExecutionEngine]` seam. The default instance answers `true`
for every payload, so only a non-default engine gives the recorded `false`. No theorem
in this module names a transaction.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun compare_vectorUInt8_self)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State Root ForkChoiceNode BeaconBlock
  ExecutionRequests getCurrentSlot isPayloadVerified getNodeChildren getHead
  getParentPayloadStatus processParentExecutionPayload processBuilderPendingPayments)

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

/-- `UnsatisfiedPayload` has a witness, so the theorem below is not vacuous. The store
uses the minimal preset and `treeMap`. It holds the default block at the zero root,
sits in slot `1`, holds a payload for the block, and records the answer `false`. The
store sets the answer directly, so the witness holds under any `[ExecutionEngine]`
instance. `pinRecordRefuted` in `Tests/HezeForkChoicePins.lean` reaches a recorded
`false` through the record path, under an engine that answers `false`. -/
example :
    letI : Preset := EthCLSpecs.Heze.minimal
    letI : HasherTag := fastHasherTag
    letI : Config := EthCLSpecs.Heze.minimalConfig
    ∃ (store : Store treeMap) (root : Root) (rootBlock : BeaconBlock),
      UnsatisfiedPayload store root rootBlock := by
  letI : Preset := EthCLSpecs.Heze.minimal
  letI : HasherTag := fastHasherTag
  letI : Config := EthCLSpecs.Heze.minimalConfig
  let root : Root := Vector.replicate 32 0
  -- Minimal slots last 6000 ms, so `time := 6` with `genesisTime := 0` is slot `1`, the
  -- slot after the default block's slot `0`.
  refine ⟨{ time := 6, genesisTime := 0
            justifiedCheckpoint := default, finalizedCheckpoint := default
            unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
            proposerBoostRoot := root
            equivocatingIndices := #[]
            blocks := FcMap.insert FcMap.empty root default
            blockStates := FcMap.empty
            blockTimeliness := FcMap.empty
            checkpointStates := FcMap.empty
            latestMessages := FcMap.empty
            unrealizedJustifications := FcMap.empty
            payloads := FcMap.insert FcMap.empty root default
            payloadTimelinessVote := FcMap.empty
            payloadDataAvailabilityVote := FcMap.empty
            payloadInclusionListSatisfaction := FcMap.insert FcMap.empty root false
            inclusionListStore := EthCLSpecs.Heze.InclusionListStore.empty },
    root, default, ⟨?_, ?_, by decide, by decide +kernel, by decide +kernel⟩⟩
  · have hcmp : compare root root = .eq := compare_vectorUInt8_self root
    simp only [FcMap.lookup, FcMap.insert, FcMap.empty]
    unfold Std.TreeMap.get? Std.TreeMap.insert Std.DTreeMap.Const.get? Std.DTreeMap.insert
    simp [EmptyCollection.emptyCollection, Std.TreeMap.empty, Std.DTreeMap.empty,
      Std.DTreeMap.Internal.Impl.empty, Std.DTreeMap.Internal.Impl.Const.get?,
      Std.DTreeMap.Internal.Impl.insert, hcmp]
  · simp +zetaDelta [getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis, checkedSub,
      checkedMul, EthCLSpecs.Heze.Const.slotDurationMs]
    -- The two sides differ only in the slot: `6000 / Config.slotDurationMs` against
    -- `default.slot + 1`. The kernel evaluates both to `1`.
    exact congrArg (fun slot => (.ok (slot, _) : Except _ _)) (by decide +kernel)

/-- The cost of an unsatisfied payload, in three facts. Let `bid` be the bid of the block.

1. Fork choice drops the payload. One step of the `getHead` walk at the pending node of
   the block selects the EMPTY node.
2. A child on the EMPTY edge does not pay the bid. Take any child of the block that fork
   choice puts under EMPTY, with the empty parent requests. Run
   `processParentExecutionPayload` for the child on a state that caches `bid`. The run does
   not change the state, so it settles no payment.
3. The builder still pays if the block reached the quorum. Take the state at the epoch
   substep that judges the payment of `bid`, where the payment is carried
   (`BidPaymentCarried`) and the qualifying withdrawals fit under the list limit. Then
   `processBuilderPendingPayments` succeeds and queues the withdrawal of `bid` if and only
   if the entry reaches the quorum (`EpochPaysBidIffQuorum`).

The weight of the entry counts same-slot attestations for the beacon block
(`process_attestation`). The theorem takes the weight as it finds it, and it does not
relate the weight to the inclusion-list answer. `BidPaymentCarried` is the assumption
about the blocks between the child and the epoch substep. -/
theorem unsatisfiedPayload_cost
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
    (∀ (child : BeaconBlock) (state : State),
      child.parentRoot = root →
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store child).run store
        = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, store) →
      sszGet state latestExecutionPayloadBid
        = rootBlock.body.signedExecutionPayloadBid.message →
      htr child.body.parentExecutionRequests = htr (default : ExecutionRequests) →
      (processParentExecutionPayload (StateTransition := HezeRun) child).run state
        = .ok ((), state)) ∧
    (∀ epochState : State,
      BidPaymentCarried epochState rootBlock.body.signedExecutionPayloadBid.message →
      (sszGet epochState builderPendingWithdrawals).val.size +
          (qualifyingBuilderWithdrawals epochState).length
        ≤ EthCLSpecs.Heze.Const.builderPendingWithdrawalsLimit →
      ∃ after : State,
        (processBuilderPendingPayments : HezeRun Unit).run epochState = .ok ((), after) ∧
        EpochPaysBidIffQuorum epochState after
          rootBlock.body.signedExecutionPayloadBid.message) := by
  refine ⟨getHeadStep_run_eq_empty_of_recorded_unsatisfied store blocks root rootBlock
    h.block h.currentSlot h.noOverflow h.verified h.unsatisfied, ?_,
    fun epochState hcarried hfits =>
      processBuilderPendingPayments_run_bid epochState _ hcarried hfits⟩
  intro child state hparent hstatus hcached hreq
  have hlookup : FcMap.lookup store.blocks child.parentRoot = some rootBlock := by
    rw [hparent]; exact h.block
  have hne := (getParentPayloadStatus_run_eq_empty_iff store child rootBlock hlookup).mp hstatus
  exact processParentExecutionPayload_run_of_empty_parent state child
    (by rw [hcached]; exact hne) hreq

end EthCLSpecs.Proofs.Heze
