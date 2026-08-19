import EthCLSpecs.Proofs.BuilderIndex
import EthCLSpecs.Proofs.BuilderPendingPayments
import EthCLSpecs.Proofs.CanBuilderCoverBid
import EthCLSpecs.Proofs.ForkChoiceRun
import EthCLSpecs.Proofs.GetPtc
import EthCLSpecs.Proofs.InitializePtcWindow
import EthCLSpecs.Proofs.InitiateBuilderExit
import EthCLSpecs.Proofs.IsValidIndexedPayloadAttestation
import EthCLSpecs.Proofs.ProcessOperations
import EthCLSpecs.Proofs.Run
import EthCLSpecs.Proofs.UpdateCheckpoints

/-!
# `EthCLSpecs.Proofs`: consensus-spec theorems (index)

Mathlib-free proofs about `EthCLSpecs` declarations, colocated with the specs
the way `SizzLean.Proofs` is colocated with `SizzLean`: same package, same
build. Each theorem is closed by whichever tactic its goal needs, `bv_decide`,
`decide`, `native_decide`, or plain case analysis. Always over the spec's own
types, never mathlib. A theorem that turns out to need mathlib moves to the standalone
`EthCLProofs` package instead (`docs/SPECS_ARCHITECTURE.md` §11), following the
`LeanPoseidonProofs` containment pattern. Mathlib never reaches this library,
the framework, the runner, or the conformance path.

A theorem that states its subject's main contract carries
`@[characterizes <function>]` (`EthCLLib.Internal.ProofLedger`). The tag is a
claim, so the attribute rejects a target no `forkdef` declared and a target the
statement never mentions. `just proof-coverage` counts the tags, audits every
theorem's axioms, and its committed baseline fails the build when a claim
disappears. Supporting lemmas stay untagged and count as touched.

Re-exports:

* `EthCLSpecs.Proofs.BuilderIndex`: the builder-index flag round-trip
  (`isBuilderIndex`, `toBuilderIndex`, `convertBuilderIndexToValidatorIndex`).
* `EthCLSpecs.Proofs.BuilderPendingPayments`: `processBuilderPendingPayments`'s
  withdrawal-queuing and payment-window-shift postcondition
  (`processBuilderPendingPayments_run`, plus
  `processBuilderPendingPayments_run_of_fits`).
* `EthCLSpecs.Proofs.CanBuilderCoverBid`: the exact `Bool`-vs-`UInt64`-inequality
  characterization of `canBuilderCoverBid`.
* `EthCLSpecs.Proofs.GetPtc`: `getPtc`'s else-branch `ptcWindow` offset bound,
  for the `data.slot + 1 == state.slot` caller (`getPtcElseOffset`,
  `getPtcElseOffset_lt_next_slot`) and the `slot == curSlot` fork-choice replay callers
  (`getPtcElseOffset_lt_same_slot`).
* `EthCLSpecs.Proofs.InitializePtcWindow`: the seeded `ptcWindow`'s two
  regions (`initializePtcWindow`).
* `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit_run_eq`, its
  builder-registry `SSZList.set!` projection, and the in-range / out-of-range
  reads of that projection, with conditional and shipped-configuration no-wrap
  corollaries for the written `withdrawableEpoch`.
* `EthCLSpecs.Proofs.IsValidIndexedPayloadAttestation`: literal and semantic
  characterizations of `isValidIndexedPayloadAttestation`, including its adjacent
  nondecreasing and validator-range checks. The semantic layer indexes the
  validator registry in bounds rather than through `!`.
* `EthCLSpecs.Proofs.ProcessOperations`: Gloas `processOperations` structural
  coordinator equation (`processOperations_eq_seq`), deposit-gate failure, and
  exact success sequencing under `EthCLSpecs.Proofs.Gloas`; handlers remain
  opaque and may modify state.
* `EthCLSpecs.Proofs.Run`: `GloasRun`, the state-transition monad every Gloas
  proof in this directory pins its theorems to.
* `EthCLSpecs.Proofs.UpdateCheckpoints`: `Gloas.updateCheckpoints` checkpoint
  monotonicity, the justified/finalized epoch never decreases. Its theorems sit
  in `EthCLSpecs.Proofs.Gloas`, since `updateCheckpoints` exists in both forks.
-/
