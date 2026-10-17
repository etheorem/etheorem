import EthCLSpecs.Proofs.Heze.BlockRoot
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.CheckpointOrd
import EthCLSpecs.Proofs.Heze.Churn
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLSpecs.Proofs.Heze.HandlerFrames
import EthCLSpecs.Proofs.Heze.HeadAvoidsFull
import EthCLSpecs.Proofs.Heze.InclusionDichotomy
import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLSpecs.Proofs.Heze.KeepsUncached
import EthCLSpecs.Proofs.Heze.KeepsUncached.Block
import EthCLSpecs.Proofs.Heze.KeepsUncached.Epoch
import EthCLSpecs.Proofs.Heze.KeepsUncached.Payload
import EthCLSpecs.Proofs.Heze.KeepsUncached.Slots
import EthCLSpecs.Proofs.Heze.KeepsUncached.Withdrawals
import EthCLSpecs.Proofs.Heze.StorePure
import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope
import EthCLSpecs.Proofs.Heze.OnInclusionList
import EthCLSpecs.Proofs.Heze.OnTickPerSlot
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty
import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.Heze.RootFrames
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Proofs.Heze.ShouldExtendPayload
import EthCLSpecs.Proofs.Heze.SlotsIncrease
import EthCLSpecs.Proofs.Heze.Time

/-!
# `EthCLSpecs.Proofs.Heze`: the Heze fork's theorems (index)

Every theorem about an `EthCLSpecs.Heze` declaration, one module per subject.
The directory mirrors `EthCLSpecs/Heze/`, for the reason `Proofs/Gloas.lean`
states: a fork elaborates its own constant for every declaration, inherited ones
included, so a theorem here is about the Heze constant and about no other fork's.
`shouldExtendPayload` is the case that shows it. Gloas declares it and Heze
overrides it with the FOCIL gate, so the Gloas theorems say nothing about the
Heze constant.

Every declaration here sits in the `EthCLSpecs.Proofs.Heze` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Heze.BlockRoot`: a block root is the root of its header
  (`htr_eq_htr_headerOf`), under the hypothesis that every `combine` returns 32 bytes.
  The root of a 32-byte vector is its bytes (`hashTreeRoot_bytes32`).
* `EthCLSpecs.Proofs.Heze.BuilderPendingPayments`: the Heze port of the epoch
  substep for builder payments (`processBuilderPendingPayments_run`), and the
  per-entry quorum condition (`mem_qualifyingPaymentIndices_iff`), proved with
  `HezeRun`. When the payment of a bid is carried to the substep
  (`BidPaymentCarried`), the substep appends the entry of the bid if and only if the
  entry reaches the quorum (`processBuilderPendingPayments_run_bid`).
* `EthCLSpecs.Proofs.Heze.CensorshipCost`: three facts about a block with a recorded
  `false` inclusion-list answer (`unsatisfiedPayload_cost`). The `getHead` loop
  continues from EMPTY at the block. A child on EMPTY, with the empty parent requests,
  does not settle the bid. At the epoch substep, the entry of the bid is appended if and
  only if it reaches the quorum.
* `EthCLSpecs.Proofs.Heze.CheckpointOrd`: the derived order on `Checkpoint` is transitive
  and returns `.eq` only on equal checkpoints (`instTransOrdCheckpoint`,
  `instLawfulEqOrdCheckpoint`), so `treeMap` meets the map laws at `Checkpoint`.
* `EthCLSpecs.Proofs.Heze.Churn`: the inherited `reserveChurn`, which takes the Gloas proof
  terms, and run theorems for the two inherited churn callers.
* `EthCLSpecs.Proofs.Heze.GetInclusionListTransactions`: collector run
  equations for `getInclusionListCommittee` and
  `getInclusionListTransactions`
  (`getInclusionListCommittee_run_eq`, `getInclusionListTransactions_run_eq`),
  plus the missing-timeliness predicate on the `FcMap.fold` entries array. Under
  `LawfulFcMap`, a successful collection keeps each transaction of an honest list
  (`collectInclusionListTransactions_ok_mem`, `mem_getInclusionListTransactions`).
* `EthCLSpecs.Proofs.Heze.HandlerFrames`: the six handlers other than `onInclusionList`
  keep the IL store (`onBlock_keeps_ilStore` and the rest), with the `keeps_solve`
  tactic that walks a handler body.
* `EthCLSpecs.Proofs.Heze.HeadAvoidsFull`: the node tree (`NodeEdge`, `NodeBelow`).
  Take a block from the previous slot with an unverified payload or a recorded `false`
  answer. The head that `getHead` returns is not the FULL node of the block and not
  below it (`getHead_run_avoids_full`). For a missing transaction under
  `DichotomyHypotheses`, the same holds at every `LaterStore`
  (`inclusionList_missing_tx_head_avoids_full`).
* `EthCLSpecs.Proofs.Heze.InclusionDichotomy`: for one honest inclusion-list
  transaction, the envelope handler records one of two answers
  (`inclusionList_dichotomy`). With `true`, the payload includes the transaction or the
  EL omits it under `LawfulInclusionList`. With `false`, `UnsatisfiedPayload` holds at
  a later store (`LaterStore`). That store holds the block and the answer at its root.
  Its current slot is the slot after the block, and its slot increment does not overflow.
  `inclusionList_missing_tx` states the direction for one missing transaction, and
  `inclusionList_missing_tx_cost` takes it to the three facts of `unsatisfiedPayload_cost`.
* `EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied`: the complete
  `.run` equation of `isPayloadInclusionListSatisfied`
  (`isPayloadInclusionListSatisfied_run`), and the four read corollaries
  for a missing record, an unverified recorded value, a recorded `false`,
  and a recorded `true` with a verified payload.
* `EthCLSpecs.Proofs.Heze.KeepsUncached`: a run of each Heze operation handler, and of
  `processOperations`, that starts on an uncached box ends on an uncached box
  (`keepsUncached_processOperations` and the handler lemmas). `increaseBalance` and
  `decreaseBalance` also return an uncached box (`returnsUncached_increaseBalance`).
* `EthCLSpecs.Proofs.Heze.KeepsUncached.Block`, `….Payload`, `….Withdrawals`,
  `….Epoch`, `….Slots`: the same fact for every substep of `processBlock` and
  `processEpoch`, and for `processSlots` and `stateTransition`
  (`keepsUncached_stateTransition`). A run of the state transition that starts on an
  uncached box ends on an uncached box.
* `EthCLSpecs.Proofs.Heze.NodeTrace`: the successful handler runs of one node
  (`NodeTrace`). From a seed with the empty IL store, such as the anchor store of
  `getForkchoiceStore`, the IL store is `ilStoreOfArrivals` of the arrivals of the trace
  (`NodeTrace.ilStore`).
* `EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope`: the complete
  compositional `.run` equation of `onExecutionPayloadEnvelope`
  (`onExecutionPayloadEnvelope_run`), tagged
  `@[characterizes EthCLSpecs.Heze.onExecutionPayloadEnvelope]`, plus
  the four direct error corollaries and the successful-path corollary
  `onExecutionPayloadEnvelope_run_eq_of_successful_checks`, proved with
  `ForkChoiceStoreRun`. Under `LawfulFcMap`, the envelope and its
  inclusion-list answer are at the same root
  (`onExecutionPayloadEnvelope_run_pairing`).
* `EthCLSpecs.Proofs.Heze.OnInclusionList`: the run of `onInclusionList`
  (`onInclusionList_run_eq`), the three branches of `processInclusionList`
  (`processInclusionList_cases`), and the arrival model. An honest list stays in the
  IL store with the timeliness of its first arrival (`honestStored_of_arrivals`).
* `EthCLSpecs.Proofs.Heze.OnTickPerSlot`: a per-slot tick keeps the `blocks` and
  `payloadInclusionListSatisfaction` maps (`onTickPerSlot_run_keeps`).
* `EthCLSpecs.Proofs.Heze.ParentPayloadEmpty`: `processParentExecutionPayload` on
  the EMPTY edge, with the empty parent requests, does not change the state
  (`processParentExecutionPayload_run_of_empty_parent`). Fork choice calls an edge
  EMPTY exactly when the two block hashes differ
  (`getParentPayloadStatus_run_eq_empty_iff`).
* `EthCLSpecs.Proofs.Heze.PayloadTiebreak`: the payload tiebreak at a block from
  the previous slot, the zero weights, `betterOf`, and the `getHead` loop body
  `headLoopBody` to EMPTY (`getHeadStep_run_eq_empty_of_recorded_unsatisfied`), proved
  with `ForkChoiceStoreRun`. `getHead_eq_fuelLoop_headLoopBody` ties the body to
  `getHead` by `rfl`, and `getHead_walk_pending_to_empty` takes the walk from the
  pending node to the EMPTY node. The step lemmas hold at any runner state
  (`getCurrentSlot_run_state`).
* `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: the
  complete run of `recordPayloadInclusionListSatisfaction`
  (`recordPayloadInclusionListSatisfaction_run`), proved with
  `ForkChoiceStoreRun`.
* `EthCLSpecs.Proofs.Heze.RootFrames`: each handler keeps the block, the envelope, and
  the answer at a root `r`, unless it writes another value there
  (`HandlerEvent.run_keeps_rootView`). A trace after the envelope handler, with no second
  envelope for `r`, gives `LaterStore` (`NodeTrace.laterStore`). Traces split and join
  (`NodeTrace.split`, `NodeTrace.append`). `inclusionList_missing_tx_trace` states the
  missing-transaction result over such a trace.
* `EthCLSpecs.Proofs.Heze.Run`: `HezeRun`, the runner for Heze state transitions.
* `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: the complete `.run`
  equation of `shouldExtendPayload` (`shouldExtendPayload_run`), the
  existing recorded-unsatisfied FOCIL rejection
  (`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`), and the
  named prefix, FOCIL, vote, and inherited-Gloas-tail corollaries.
* `EthCLSpecs.Proofs.Heze.SlotsIncrease`: block slots increase along parent links at the
  end of a trace from the anchor store, or two distinct headers or blocks share a root
  (`NodeTrace.slotInv`). The argument uses the header check of `processBlockHeader` and
  the block-root lemma, and needs no frame over the state transition.
  `inclusionList_missing_tx_anchored` states the missing-transaction result on such a
  trace, with the justified-root hypothesis reduced to a slot comparison.
* `EthCLSpecs.Proofs.Heze.StorePure`: every state that the store holds is the uncached box
  of a plain value, at the end of a trace from the anchor store of `getForkchoiceStore`
  over an uncached anchor (`StorePure.anchor`, `NodeTrace.storePure`). The `blockStates`
  half needs only the law of the root map (`NodeTrace.blockStatesPure`). The run
  inversions of `onBlock` and the envelope handler return the stored states as plain
  values (`onBlock_run_ok`, `onExecutionPayloadEnvelope_run_ok`). The predicates are in
  `….StorePure.Basic`.
* `EthCLSpecs.Proofs.Heze.Time`: the inherited `computeEpochAtSlot`,
  `computeStartSlotAtEpoch`, and `computeActivationExitEpoch` at Heze. The `Downgrade`
  bridge reaches one fork up, so each theorem takes the Gloas proof term.
-/
