import EthCLSpecs.Proofs.Gloas.BuilderIndex
import EthCLSpecs.Proofs.Gloas.GetPtc
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.Gloas.UpdateCheckpoints
-- Detached while Gloas runs on the plain `State` (WS-126 task 4.1).
-- The modules below state their runs through the box vocabulary (`pureState`, `runPure`,
-- `view_uncachedBox`), so they fail on the plain state. `ForkChoiceRun` imports
-- `InitiateBuilderExit` and `BuilderPendingPayments`. `ProcessOperations` imported the
-- deleted `Proofs/Gloas/KeepsUncached.lean`. Task 4.3 reattaches `CanBuilderCoverBid`,
-- `InitializePtcWindow`, `IsValidIndexedPayloadAttestation` and `ProcessDepositRequest`;
-- task 4.4 `InitiateBuilderExit`; task 4.5 `BuilderPendingPayments`; task 4.6
-- `ProcessOperations`; task 4.7 `ForkChoiceRun`.
-- import EthCLSpecs.Proofs.Gloas.BuilderPendingPayments
-- import EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid
-- import EthCLSpecs.Proofs.Gloas.ForkChoiceRun
-- import EthCLSpecs.Proofs.Gloas.InitializePtcWindow
-- import EthCLSpecs.Proofs.Gloas.InitiateBuilderExit
-- import EthCLSpecs.Proofs.Gloas.IsValidIndexedPayloadAttestation
-- import EthCLSpecs.Proofs.Gloas.ProcessDepositRequest
-- import EthCLSpecs.Proofs.Gloas.ProcessOperations

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
  run equation (`processBuilderPendingPayments_run`): a quorum error propagates, and
  a successful quorum computation gives the withdrawal-queuing and
  payment-window-shift postcondition (`processBuilderPendingPayments_run_appended`).
* `EthCLSpecs.Proofs.Gloas.CanBuilderCoverBid`: the run equation of `canBuilderCoverBid`
  over the checked `Gwei` chain, and its reading as one `Nat` inequality on the plain values.
* `EthCLSpecs.Proofs.Gloas.ForkChoiceRun`: `GloasStoreRun`, the Gloas store monad, with the
  `getSlotsSinceGenesis` and `getCurrentSlot` run equations at genesis time and the
  `.zeroDivision` reject of a zero `SLOT_DURATION_MS`.
* `EthCLSpecs.Proofs.Gloas.GetPtc`: `getPtc`'s else-branch `ptcWindow` offset bound,
  for the `data.slot + 1 == state.slot` caller (`getPtcElseOffset`,
  `getPtcElseOffset_lt_next_slot`) and the `slot == curSlot` fork-choice replay callers
  (`getPtcElseOffset_lt_same_slot`).
* `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded `ptcWindow`'s two
  regions (`initializePtcWindow`).
* `EthCLSpecs.Proofs.Gloas.InitiateBuilderExit`: `initiateBuilderExit_run_eq`, the
  whole-transition equation over the plain `BeaconState`, with the in-range /
  out-of-range reads of that equation and conditional and shipped-configuration sum-bound
  corollaries for the written `withdrawableEpoch`.
* `EthCLSpecs.Proofs.Gloas.IsValidIndexedPayloadAttestation`: literal and semantic
  characterizations of `isValidIndexedPayloadAttestation`, including its adjacent
  nondecreasing and validator-range checks. The semantic layer reads the
  validator registry with in-bounds proofs, so its statement has no `!` read.
* `EthCLSpecs.Proofs.Gloas.ProcessDepositRequest`: `processDepositRequest_run`, the
  whole-transition equation (the run appends one pending deposit and writes nothing
  else), and
  `processDepositRequest_keeps_startIndex`.
* `EthCLSpecs.Proofs.Gloas.ProcessOperations`: Gloas `processOperations` structural
  coordinator equation (`processOperations_eq_seq`), deposit-gate failure, and
  exact success sequencing; handlers remain
  opaque and may modify state.
* `EthCLSpecs.Proofs.Gloas.Run`: `GloasRun`, the state-transition monad every Gloas
  proof in this directory pins its theorems to. The generic `StateT`-over-`Except`
  bind and `Except` facts live in `EthCLLib.Proofs.Run`; both fork directories
  import that module and name the facts directly.
* `EthCLSpecs.Proofs.Gloas.UpdateCheckpoints`: `Gloas.updateCheckpoints` checkpoint
  monotonicity, the justified/finalized epoch never decreases. Its theorems sit
  in `EthCLSpecs.Proofs.Gloas`, since `updateCheckpoints` exists in both forks.
-/
