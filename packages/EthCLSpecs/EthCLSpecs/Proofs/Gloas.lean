import EthCLSpecs.Proofs.Gloas.BuilderIndex
import EthCLSpecs.Proofs.Gloas.BuilderPendingPayments
import EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid
import EthCLSpecs.Proofs.Gloas.ForkChoiceRun
import EthCLSpecs.Proofs.Gloas.GetPtc
import EthCLSpecs.Proofs.Gloas.InitializePtcWindow
import EthCLSpecs.Proofs.Gloas.InitiateBuilderExit
import EthCLSpecs.Proofs.Gloas.IsValidIndexedPayloadAttestation
import EthCLSpecs.Proofs.Gloas.ProcessOperations
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.Gloas.UpdateCheckpoints

/-!
# `EthCLSpecs.Proofs.Gloas`: the Gloas fork's theorems (index)

Every theorem about an `EthCLSpecs.Gloas` declaration, one module per subject.
The directory mirrors `EthCLSpecs/Gloas/`, the rule `SPECS_ARCHITECTURE.md` §3.4
sets for the fork bodies, and for the same reason: a fork elaborates its own
constant for every declaration, inherited ones included, so a theorem is about
one fork's constant and about no other fork's. `updateCheckpoints` is the case
that shows it. Fulu and Gloas each declare it, each elaboration is a separate
constant, and this directory proves the Gloas one.

Every declaration here sits in the `EthCLSpecs.Proofs.Gloas` namespace, so a
Fulu companion theorem of the same name would land in `EthCLSpecs.Proofs.Fulu`
and collide with nothing.

Re-exports:

* `EthCLSpecs.Proofs.Gloas.BuilderIndex`: the builder-index flag round-trip
  (`isBuilderIndex`, `toBuilderIndex`, `convertBuilderIndexToValidatorIndex`).
* `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: `processBuilderPendingPayments`'s
  withdrawal-queuing and payment-window-shift postcondition
  (`processBuilderPendingPayments_run`, plus
  `processBuilderPendingPayments_run_of_fits`).
* `EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid`: the exact `Bool`-vs-`UInt64`-inequality
  characterization of `canBuilderCoverBid`.
* `EthCLSpecs.Proofs.Gloas.GetPtc`: `getPtc`'s else-branch `ptcWindow` offset bound,
  for the `data.slot + 1 == state.slot` caller (`getPtcElseOffset`,
  `getPtcElseOffset_lt_next_slot`) and the `slot == curSlot` fork-choice replay callers
  (`getPtcElseOffset_lt_same_slot`).
* `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded `ptcWindow`'s two
  regions (`initializePtcWindow`).
* `EthCLSpecs.Proofs.Gloas.InitiateBuilderExit`: `initiateBuilderExit_run_eq`, its
  builder-registry `SSZList.set!` projection, and the in-range / out-of-range
  reads of that projection, with conditional and shipped-configuration no-wrap
  corollaries for the written `withdrawableEpoch`.
* `EthCLSpecs.Proofs.Gloas.IsValidIndexedPayloadAttestation`: literal and semantic
  characterizations of `isValidIndexedPayloadAttestation`, including its adjacent
  nondecreasing and validator-range checks. The semantic layer indexes the
  validator registry in bounds rather than through `!`.
* `EthCLSpecs.Proofs.Gloas.ProcessOperations`: Gloas `processOperations` structural
  coordinator equation (`processOperations_eq_seq`), deposit-gate failure, and
  exact success sequencing; handlers remain
  opaque and may modify state.
* `EthCLSpecs.Proofs.Gloas.Run`: `GloasRun`, the state-transition monad every Gloas
  proof in this directory pins its theorems to.
* `EthCLSpecs.Proofs.Gloas.UpdateCheckpoints`: `Gloas.updateCheckpoints` checkpoint
  monotonicity, the justified/finalized epoch never decreases. Its theorems sit
  in `EthCLSpecs.Proofs.Gloas`, since `updateCheckpoints` exists in both forks.
-/
