import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLSpecs.Proofs.Heze.InclusionDichotomy
import EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope
import EthCLSpecs.Proofs.Heze.OnInclusionList
import EthCLSpecs.Proofs.Heze.OnTickPerSlot
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty
import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Proofs.Heze.ShouldExtendPayload

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

* `EthCLSpecs.Proofs.Heze.BuilderPendingPayments`: the Heze port of the epoch
  substep for builder payments (`processBuilderPendingPayments_run`), and the
  per-entry quorum condition (`mem_qualifyingPaymentIndices_iff`), proved with
  `HezeRun`. When the payment of a bid is carried to the substep
  (`BidPaymentCarried`), the substep queues the bid if and only if its entry reaches
  the quorum (`processBuilderPendingPayments_run_bid`).
* `EthCLSpecs.Proofs.Heze.CensorshipCost`: three facts about a block with a recorded
  `false` inclusion-list answer (`unsatisfiedPayload_cost`). The `getHead` loop
  continues from EMPTY at the block. A child on EMPTY, with the empty parent requests,
  does not settle the bid. At the epoch substep, the bid is paid if and only if its
  entry reaches the quorum.
* `EthCLSpecs.Proofs.Heze.GetInclusionListTransactions`: collector run
  equations for `getInclusionListCommittee` and
  `getInclusionListTransactions`
  (`getInclusionListCommittee_run_eq`, `getInclusionListTransactions_run_eq`),
  plus the missing-timeliness predicate on the `FcMap.fold` entries array. Under
  `LawfulFcMap`, a successful collection keeps each transaction of an honest list
  (`collectInclusionListTransactions_ok_mem`, `mem_getInclusionListTransactions`).
* `EthCLSpecs.Proofs.Heze.InclusionDichotomy`: for one honest inclusion-list
  transaction, the envelope handler records one of two answers
  (`inclusionList_dichotomy`). With `true`, the payload includes the transaction or the
  EL omits it under `LawfulInclusionList`. With `false`, `UnsatisfiedPayload` holds at
  a later store (`LaterStore`) that holds the block and the answer at its root, whose current slot is
  the slot after the block, and whose slot increment does not overflow.
  `inclusionList_missing_tx` states the direction for one missing transaction, and
  `inclusionList_missing_tx_cost` takes it to the three facts of `unsatisfiedPayload_cost`.
* `EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope`: the store after a successful
  `onExecutionPayloadEnvelope` (`onExecutionPayloadEnvelope_run_eq`). The envelope and
  its inclusion-list answer are at the same root
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
  pending node to the EMPTY node.
* `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: the
  complete run of `recordPayloadInclusionListSatisfaction`
  (`recordPayloadInclusionListSatisfaction_run`), proved with
  `ForkChoiceStoreRun`.
* `EthCLSpecs.Proofs.Heze.Run`: `HezeRun`, the runner for Heze state transitions.
* `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's verified,
  recorded-unsatisfied FOCIL rejection theorem
  (`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`), proved with
  `ForkChoiceStoreRun`.
-/
