import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
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
  `HezeRun`.
* `EthCLSpecs.Proofs.Heze.CensorshipCost`: two independent facts about a block with
  a recorded `false` inclusion-list answer
  (`unsatisfiedPayload_headEmpty_and_emptyChild_unsettled`). The head step goes to
  EMPTY. A child on EMPTY, with the empty parent requests, does not settle the bid.
* `EthCLSpecs.Proofs.Heze.GetInclusionListTransactions`: collector run
  equations for `getInclusionListCommittee` and
  `getInclusionListTransactions`
  (`getInclusionListCommittee_run_eq`, `getInclusionListTransactions_run_eq`),
  plus the missing-timeliness predicate on the `FcMap.fold` entries array.
* `EthCLSpecs.Proofs.Heze.ParentPayloadEmpty`: `processParentExecutionPayload` on
  the EMPTY edge, with the empty parent requests, does not change the state
  (`processParentExecutionPayload_run_of_empty_parent`). Fork choice calls an edge
  EMPTY exactly when the two block hashes differ
  (`getParentPayloadStatus_run_eq_empty_iff`).
* `EthCLSpecs.Proofs.Heze.PayloadTiebreak`: the payload tiebreak at a block from
  the previous slot, the zero weights, `betterOf`, and the head step to EMPTY
  (`getHeadStep_run_eq_empty_of_recorded_unsatisfied`), proved with
  `ForkChoiceStoreRun`.
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
