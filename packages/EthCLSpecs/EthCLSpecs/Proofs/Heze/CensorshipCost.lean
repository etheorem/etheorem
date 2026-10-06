import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.PaymentCarried

/-!
# `EthCLSpecs.Proofs.Heze.CensorshipCost`: what a failed inclusion list costs

`unsatisfiedPayload_cost` states three facts about one block. It uses
`PayloadTiebreak.lean`, `ParentPayloadEmpty.lean`, and `BuilderPendingPayments.lean`.
Take a block from the previous slot whose recorded inclusion-list answer is `false`.
Then:

1. Whenever the `getHead` loop reaches the pending node of the block with fuel left, it
   continues from the EMPTY node (`getHead_walk_pending_to_empty`). The theorem does
   not prove that the walk reaches the pending node.
2. Take any child of the block that fork choice puts under the EMPTY node, with the
   empty parent requests. Process it on a state that caches the bid of the block. Then
   `processParentExecutionPayload` does not change the state, and it does not settle
   the bid of the block.
3. At the epoch substep that judges the payment of the bid, the substep appends the
   entry of the bid if and only if the entry reaches the quorum.

Facts 1 and 2 are independent. Fact 2 holds for every child on the EMPTY edge, and it
uses only the block lookup. A proposer that follows fork choice builds on EMPTY, but the
model does not include the proposer. A child built on the FULL edge settles the bid
through `applyParentExecutionPayload`.

Fact 3 takes one hypothesis about the blocks between the bid and the epoch substep,
`BidPaymentCarried`: the entry for the slot of the bid still carries the withdrawal of
the bid when the substep reads it. `unsatisfiedPayload_cost_of_run` derives it from the
chain (`PaymentCarried.lean`) and states the three facts with it. It takes two chain
hypotheses. The first block after the bid takes the EMPTY edge. No block carries a
proposer slashing at the slot of the bid whose proposer is the proposer of the bid's block.

The answer comes from the `[ExecutionEngine]` seam. The default instance answers `true`
for every payload, so only a non-default engine gives the recorded `false`.
`InclusionDichotomy.lean` derives `UnsatisfiedPayload` from an honest inclusion list and
a missing transaction. No theorem in this module names a specific transaction.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root ForkChoiceNode BeaconBlock
  ExecutionRequests getCurrentSlot getParentPayloadStatus processParentExecutionPayload
  processBuilderPendingPayments)

/-- The conditions under which fork choice sees a payload that fails the inclusion
list. `root` names the block `rootBlock` from the previous slot. The recorded
inclusion-list answer for the payload is `false`. The payload need not be verified:
the `getHead` loop goes to EMPTY either way. -/
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
  /-- The recorded inclusion-list answer for the payload is `false`. -/
  unsatisfied : FcMap.lookup store.payloadInclusionListSatisfaction root = some false

/-- `UnsatisfiedPayload` has a witness, so the theorem below is not vacuous. The store
uses the minimal preset and `treeMap`. It holds the default block at the zero root,
sits in slot `1`, and records the answer `false` for the block. The
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
            payloads := FcMap.empty
            payloadTimelinessVote := FcMap.empty
            payloadDataAvailabilityVote := FcMap.empty
            payloadInclusionListSatisfaction := FcMap.insert FcMap.empty root false
            inclusionListStore := EthCLSpecs.Heze.InclusionListStore.empty },
    root, default, ⟨?_, ?_, by decide, by decide +kernel⟩⟩
  · simp only [FcMap.lookup, FcMap.insert, FcMap.empty]
    unfold Std.TreeMap.get? Std.TreeMap.insert Std.DTreeMap.Const.get? Std.DTreeMap.insert
    simp [EmptyCollection.emptyCollection, Std.TreeMap.empty, Std.DTreeMap.empty,
      Std.DTreeMap.Internal.Impl.empty, Std.DTreeMap.Internal.Impl.Const.get?,
      Std.DTreeMap.Internal.Impl.insert]
  · simp +zetaDelta [getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis, checkedSub,
      checkedMul, EthCLSpecs.Heze.Const.slotDurationMs]
    -- The two sides differ only in the slot: `6000 / Config.slotDurationMs` against
    -- `default.slot + 1`. The kernel evaluates both to `1`.
    exact congrArg (fun slot => (.ok (slot, _) : Except _ _)) (by decide +kernel)

/-- The cost of an unsatisfied payload, in three facts. Let `bid` be the bid of the block.

1. Fork choice drops the payload. Whenever the `getHead` loop reaches the pending node of
   the block with fuel left, it continues from the EMPTY node.
2. A child on the EMPTY edge does not pay the bid. Take any child of the block that fork
   choice puts under EMPTY, with the empty parent requests. Run
   `processParentExecutionPayload` for the child on a state that caches `bid`. The run does
   not change the state, so it settles no payment.
3. The builder still pays if the block reached the quorum. Take the state at the epoch
   substep that judges the payment of `bid`, where the payment is carried
   (`BidPaymentCarried`), the total active balance reads as `total`, the quorum product fits
   (`QuorumFits`), and the qualifying withdrawals fit under the list limit. Then
   `processBuilderPendingPayments` succeeds and appends the entry of `bid` if and only if
   the entry reaches the quorum (`EpochPaysBidIffQuorum`).

The weight of the entry counts same-slot attestations for the beacon block
(`process_attestation`). The theorem makes no assumption about the weight, and it does
not relate the weight to the inclusion-list answer. `BidPaymentCarried` is the assumption
about the blocks between the child and the epoch substep. -/
theorem unsatisfiedPayload_cost
    {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
    (store : Store map) (root : Root) (rootBlock : BeaconBlock) (blocks : Array Root)
    (h : UnsatisfiedPayload store root rootBlock) :
    (∀ (fuel : Nat) (exhausted : ForkChoiceNode),
      (fuelLoop (fuel + 1) (ForkChoiceNode.pending root) exhausted
          (headLoopBody store blocks)).run store
        = (fuelLoop fuel (ForkChoiceNode.empty root) exhausted
            (headLoopBody store blocks)).run store) ∧
    (∀ (child : BeaconBlock) (preState : BeaconState),
      child.parentRoot = root →
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store child).run store
        = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, store) →
      preState.latestExecutionPayloadBid = rootBlock.body.signedExecutionPayloadBid.message →
      htr child.body.parentExecutionRequests = htr (default : ExecutionRequests) →
      (processParentExecutionPayload (StateTransition := HezeRun) child).run
          (pureState preState)
        = .ok ((), pureState preState)) ∧
    (∀ (epochState : BeaconState) (total : EthCLSpecs.Heze.Gwei),
      BidPaymentCarried epochState rootBlock.body.signedExecutionPayloadBid.message →
      EthCLSpecs.Heze.getTotalActiveBalance (pureState epochState) = .ok total →
      QuorumFits total →
      epochState.builderPendingWithdrawals.val.size +
          (qualifyingBuilderWithdrawals epochState total).length
        ≤ EthCLSpecs.Heze.Const.builderPendingWithdrawalsLimit →
      ∃ postState : BeaconState,
        runPure (processBuilderPendingPayments (StateTransition := HezeRun)) epochState
          = .ok ((), postState) ∧
        EpochPaysBidIffQuorum epochState postState total
          rootBlock.body.signedExecutionPayloadBid.message) := by
  refine ⟨fun fuel exhausted => getHead_walk_pending_to_empty store blocks root rootBlock
    fuel exhausted h.block h.currentSlot h.noOverflow (fun _ => h.unsatisfied), ?_,
    fun epochState total hcarried htotal hquorum hfits =>
      processBuilderPendingPayments_run_bid epochState _ hcarried total htotal hquorum hfits⟩
  intro child preState hparent hstatus hcached hreq
  have hlookup : FcMap.lookup store.blocks child.parentRoot = some rootBlock := by
    rw [hparent]; exact h.block
  have hne := (getParentPayloadStatus_run_eq_empty_iff store child rootBlock hlookup).mp hstatus
  exact processParentExecutionPayload_run_of_empty_parent preState child
    (by rw [hcached]; exact hne) hreq

/-- `unsatisfiedPayload_cost` with fact 3 stated over the chain. Let `sbR` be the signed
block at `root`, with a bid of value `> 0`. Run `sbR`, then `steps` to the last slot of
the next epoch, then `processSlot` and the first eight epoch substeps. The first block
after `sbR` takes the EMPTY edge. No block has a proposer slashing at the slot of the bid
by the proposer of `sbR`. When the total active balance of the judging state reads as
`total`, the quorum product fits (`QuorumFits`), and the qualifying withdrawals fit,
`processBuilderPendingPayments` appends the entry of the bid if and only if it reaches the
quorum.

Facts 1 and 2 are those of `unsatisfiedPayload_cost`, and they use `h`. Fact 3 uses only
the chain hypotheses. The theorem does not derive `hempty` from fact 2. `hempty` constrains
the parent block hash in the bid of the first block. Fact 2 reads the payload status from
the fork-choice store. -/
theorem unsatisfiedPayload_cost_of_run
    {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
    (store : Store map) (root : Root) (sbR : EthCLSpecs.Heze.SignedBeaconBlock)
    (blocks : Array Root) (h : UnsatisfiedPayload store root sbR.message)
    (v : Bool) (steps : List ChainStep) (st0 st1 stEnd stA stJudge : BeaconState)
    (hpos : 0 < sbR.message.body.signedExecutionPayloadBid.message.value)
    (hwin : windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot < 2 ^ 64)
    (hr : BlockStep sbR v st0 st1)
    (hrun : ChainRun (windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot)
      steps st1 stEnd)
    (hend : stEnd.slot.toNat = windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot)
    (hempty : EmptyChild sbR.message.body.signedExecutionPayloadBid.message steps)
    (hslashR : NoSlashingAt sbR.message.body.signedExecutionPayloadBid.message.slot
      sbR.message.proposerIndex sbR)
    (hslash : NoSlashingSteps sbR.message.body.signedExecutionPayloadBid.message.slot
      sbR.message.proposerIndex steps)
    (hslot : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState stEnd)
      = .ok ((), pureState stA))
    (hprefix : processEpochPrefix.run (pureState stA) = .ok ((), pureState stJudge))
    (total : EthCLSpecs.Heze.Gwei)
    (htotal : EthCLSpecs.Heze.getTotalActiveBalance (pureState stJudge) = .ok total)
    (hquorum : QuorumFits total)
    (hfits : stJudge.builderPendingWithdrawals.val.size +
        (qualifyingBuilderWithdrawals stJudge total).length
      ≤ EthCLSpecs.Heze.Const.builderPendingWithdrawalsLimit) :
    (∀ (fuel : Nat) (exhausted : ForkChoiceNode),
      (fuelLoop (fuel + 1) (ForkChoiceNode.pending root) exhausted
          (headLoopBody store blocks)).run store
        = (fuelLoop fuel (ForkChoiceNode.empty root) exhausted
            (headLoopBody store blocks)).run store) ∧
    (∀ (child : BeaconBlock) (preState : BeaconState),
      child.parentRoot = root →
      (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
          store child).run store
        = .ok (EthCLSpecs.Heze.Const.payloadStatusEmpty, store) →
      preState.latestExecutionPayloadBid = sbR.message.body.signedExecutionPayloadBid.message →
      htr child.body.parentExecutionRequests = htr (default : ExecutionRequests) →
      (processParentExecutionPayload (StateTransition := HezeRun) child).run
          (pureState preState)
        = .ok ((), pureState preState)) ∧
    ∃ after : BeaconState,
      runPure (processBuilderPendingPayments (StateTransition := HezeRun)) stJudge
        = .ok ((), after) ∧
      EpochPaysBidIffQuorum stJudge after total
        sbR.message.body.signedExecutionPayloadBid.message :=
  have hcost := unsatisfiedPayload_cost store root sbR.message blocks h
  ⟨hcost.1, hcost.2.1, hcost.2.2 stJudge total
    (bidPaymentCarried_of_run sbR v steps st0 st1 stEnd stA stJudge hpos hwin hr hrun hend
      hempty hslashR hslash hslot hprefix).1 htotal hquorum hfits⟩

end EthCLSpecs.Proofs.Heze
