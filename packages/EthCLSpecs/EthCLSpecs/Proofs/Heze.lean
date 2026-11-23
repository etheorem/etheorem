import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope
import EthCLSpecs.Proofs.Heze.ShouldExtendPayload
-- Detached while Heze runs on the plain `State` (WS-126 task 3.1). Task 3.2 reattaches
-- them. `OnExecutionPayloadEnvelope` imports both through
-- `RecordPayloadInclusionListSatisfaction`, so it builds after task 3.2 lands.
-- import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
-- import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction

/-!
# `EthCLSpecs.Proofs.Heze`: the Heze fork's theorems (index)

Every theorem about an `EthCLSpecs.Heze` declaration, one module per subject.
The directory mirrors `EthCLSpecs/Heze/`, for the reason `Proofs/Gloas.lean`
states: a fork elaborates its own constant for every declaration, inherited ones
included, so a theorem here is about the Heze constant and about no other fork's.
`shouldExtendPayload` is the case that shows it. Gloas declares it and Heze
overrides it with the FOCIL gate, so a theorem about the Gloas constant says
nothing about the Heze constant.

Every declaration here sits in the `EthCLSpecs.Proofs.Heze` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Heze.GetInclusionListTransactions`: the `.run` equation
  of `getInclusionListCommittee` (`getInclusionListCommittee_run_eq`) and its
  zero-divisor reject on an empty committee
  (`getInclusionListCommittee_run_error_of_empty`), plus the transactions
  contract of the pure `getInclusionListTransactions` over the counted items
  (`mem_getInclusionListTransactions_iff`, `getInclusionListTransactions_nodup`).
* `EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied`: the complete
  `.run` equation of `isPayloadInclusionListSatisfied`
  (`isPayloadInclusionListSatisfied_run`), and the four read corollaries
  for a missing record, an unverified recorded value, a recorded `false`,
  and a recorded `true` with a verified payload.
* `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: the
  complete run of `recordPayloadInclusionListSatisfaction`
  (`recordPayloadInclusionListSatisfaction_run`), proved with
  `ForkChoiceStoreRun`.
* `EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope`: the complete
  compositional `.run` equation of `onExecutionPayloadEnvelope`
  (`onExecutionPayloadEnvelope_run`), tagged
  `@[characterizes EthCLSpecs.Heze.onExecutionPayloadEnvelope]`, plus
  the four direct error corollaries and the successful-path corollary
  `onExecutionPayloadEnvelope_run_eq_of_successful_checks`, proved with
  `ForkChoiceStoreRun`.
* `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: the complete `.run`
  equation of `shouldExtendPayload` (`shouldExtendPayload_run`), the
  existing recorded-unsatisfied FOCIL rejection
  (`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`), and the
  named prefix, FOCIL, vote, and inherited-Gloas-tail corollaries.
-/
