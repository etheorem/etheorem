# Consensus Proof Candidates

## Purpose

A shortlist of Lean theorem candidates in `EthCLSpecs`. This is not a classification of
the fork's surface area, just the functions with a clear invariant, safety property, algebraic property (such as an inverse), monotonicity property, or other proof-worthy correctness property.

## Overview

Gloas introduces 62 new functions and overrides 46 inherited ones. The candidates below were identified by reading across the Gloas specification and supporting libraries, focusing on functions with clear correctness properties, safety invariants, algebraic laws, monotonicity properties, and other proof-worthy invariants. The list is not exhaustive.

The sections below group candidates by the kind of theorem they naturally suggest.

---

## Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Gloas
function, applying one after the other returns the original value, at least
under a stated precondition.

| Function                              | Location                    | Rationale                                                                                                                                                                                                                                                                                  |
| ------------------------------------- | --------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:415` | **In review**, see `EthCLSpecs/Proofs/BuilderIndex.lean`. Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit, since `toBuilderIndex` always clears that bit, the round trip holds only under that precondition, not as a free identity |

---

## Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never
exceeding a spec constant, or a termination bound, a fuel parameter large enough for a
bounded walk to finish.

| Function                         | Location                            | Rationale                                                                                                                                         |
| -------------------------------- | ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| `computeExitEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:90-100` | The churn arithmetic this call site performs through `reserveChurn` must not underflow                                                            |
| `reserveChurn`                   | `Fulu/RegistryUpdates.lean:69-74`   | Arithmetic never underflows                                                                                                                       |
| `getExpectedWithdrawals`         | `Gloas/Withdrawals.lean:160-168`    | The withdrawals returned by its four phases combined never exceed `MAX_WITHDRAWALS_PER_PAYLOAD`                                                   |
| `initiateBuilderExit`            | `Gloas/Operations.lean:90-93`       | Whether `epoch + minBuilderWithdrawabilityDelay` can overflow `UInt64` given `epoch`'s realistic range is the no-overflow bound to establish here |
| `getPtc`                         | `Gloas/Operations.lean:368-376`     | Under the caller's guarantee that `data.slot + 1 == state.slot`, its computed offset into `ptcWindow` stays in range                              |
| `canBuilderCoverBid`             | `Gloas/Operations.lean:419-422`     | Primary builder-solvency predicate; the natural theorem is that accepting a bid never leaves the builder insolvent                                |
| `applyWithdrawals`               | `Gloas/Withdrawals.lean:173-184`    | A builder-flagged withdrawal decreases the builder's balance by at most its own balance, so the balance never goes negative                       |
| `getAncestor`                    | `Gloas/ForkChoice.lean:156-163`     | The fuel supplied to its `fuelIterate` DAG walk is sufficient for the walk to terminate before running out                                        |
| `getHead`                        | `Gloas/ForkChoice.lean:446-465`     | The fuel `2 * blocks.length + 2` supplied to its LMD-GHOST walk is sufficient for the walk to reach a decided head before running out             |

---

## Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function                           | Location                             | Rationale                                                                                                                          |
| ---------------------------------- | ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------- |
| `processProposerSlashing`          | `Gloas/Operations.lean:213-243`      | Payment-voiding must never touch another proposer's `BuilderPendingPayment`                                                        |
| `processAttestation`               | `Gloas/Operations.lean:289-360`      | Committee-index safety together with builder-payment weight accounting                                                             |
| `processBuilderPendingPayments`    | `Gloas/EpochProcessing.lean:229-248` | **In review**, see `EthCLSpecs/Proofs/BuilderPendingPayments.lean`. Under an explicit capacity hypothesis, every qualifying previous-epoch payment's withdrawal is appended to `builderPendingWithdrawals` in slot order, and the payment window shifts down by `SLOTS_PER_EPOCH`; this does not establish protocol-wide exactly-once settlement |
| `processPtcWindow`                 | `Gloas/EpochProcessing.lean:267-277` | Each newly populated `ptcWindow` entry equals `computePtc` evaluated for its corresponding slot                                    |
| `applyDepositForBuilder`           | `Gloas/Operations.lean:120-128`      | A deposit with an invalid signature is neither applied to a builder's balance nor requeued                                         |
| `processBuilderDepositRequest`     | `Gloas/Operations.lean:174-190`      | A new builder is onboarded only when its deposit signature is valid                                                                |
| `isValidIndexedPayloadAttestation` | `Gloas/Operations.lean:389-400`      | Returns true only when the attesting indices are non-empty, sorted, within the validator set, and the aggregate signature verifies |
| `processExecutionPayloadBid`       | `Gloas/Operations.lean:451-484`      | The self-build and builder-bid paths it chooses between are mutually exclusive and jointly exhaustive                              |
| `applyParentExecutionPayload`      | `Gloas/Operations.lean:489-513`      | Exactly one of settle-current, settle-previous, or evict fires, so a payment is never settled twice                                |

---

## Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates:
never decreasing, never shrinking, never losing a previously-added element.

| Function             | Location                        | Rationale                                                    |
| -------------------- | ------------------------------- | ------------------------------------------------------------ |
| `getWeight`          | `Gloas/ForkChoice.lean:359-369` | Weight only grows as more attestations accumulate for a node |
| `onAttesterSlashing` | `Gloas/ForkChoice.lean:791-801` | The set of equivocating indices only grows, never shrinks    |
| `updateCheckpoints`  | `Gloas/ForkChoice.lean:470-472` | Justified/finalized epochs never decrease                    |

---

## State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual
processing steps into the top-level state transition, and the properties that hold as a
direct consequence of running through it.

| Function            | Location                        | Rationale                                                                                                                                                                                          |
| ------------------- | ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `processSlot`       | `Gloas/Transition.lean:33-53`   | After `processSlot`, the `executionPayloadAvailability` bit at index `(slot + 1) mod SLOTS_PER_HISTORICAL_ROOT` reads `false`, matching the documented invariant that a payload starts unavailable |
| `processOperations` | `Gloas/Transition.lean:88-95`   | Captures a documented precondition (`body.deposits.size == 0`) that should hold whenever the function is entered                                                                                   |
| `stateTransition`   | `Gloas/Transition.lean:109-120` | Top-level state-transition correctness; composes `processSlots`, `processBlock`, and the root check into the canonical transition                                                                  |

---

## Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function                         | Location                        | Rationale                                                                                                                                          |
| -------------------------------- | ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------- |
| `onBlock`                        | `Gloas/ForkChoice.lean:594-625` | Accepts a block only if a full parent implies a verified payload, and the block's ancestry agrees with the currently finalized checkpoint          |
| `validateOnAttestation`          | `Gloas/ForkChoice.lean:737-756` | Validates that the attestation's index is 0 or 1, that a same-slot attestation has index 0, and that a full-vote attestation's payload is verified |
| `getForkchoiceStore`             | `Gloas/ForkChoice.lean:808-827` | Every root-keyed map in a freshly built store agrees on the anchor entry                                                                           |
| `isAncestor`                     | `Gloas/ForkChoice.lean:168-175` | Agrees with the ancestor relation that `getAncestor` computes iteratively                                                                          |
| `verifyExecutionPayloadEnvelope` | `Gloas/ForkChoice.lean:652-678` | Acceptance requires every validation check performed by `verifyExecutionPayloadEnvelope` to succeed                                                |

---

## Upgrade-boundary properties

Functions whose entire purpose is the Fulu-to-Gloas upgrade itself: preserving state
across the boundary or seeding Gloas-only state from it. The fork comparison here is not
incidental, it's what the function does.

| Function              | Location                     | Rationale                                                                                                                                                            |
| --------------------- | ---------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `upgradeToGloas`      | `Gloas/Upgrade.lean:101-156` | Preserves inherited state while correctly initializing the new ePBS state                                                                                            |
| `computePtcFromFulu`  | `Gloas/Upgrade.lean:35-43`   | Agrees with `Gloas.computePtc` once the state is upgraded                                                                                                            |
| `initializePtcWindow` | `Gloas/Upgrade.lean:50-60`   | **In review**, see `EthCLSpecs/Proofs/InitializePtcWindow.lean`. The first `SLOTS_PER_EPOCH` entries are the empty committee, and every remaining entry equals `computePtcFromFulu` at the slot computed by `initializePtcWindow` |

---

## Candidates needing a sharper statement

Functions where the useful theorem hasn't been identified yet, either because the
obvious candidate property doesn't hold up, or because none has been proposed. Once
identified, the candidate belongs in one of the sections above.

| Function     | Location                             | Rationale                                                                                                                                     |
| ------------ | ------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------- |
| `computePtc` | `Gloas/EpochProcessing.lean:254-261` | No standalone theorem has been identified yet. The strongest current candidate is its agreement with `computePtcFromFulu` after state upgrade |

---

## Related work

- [`FUTURE_WORK.md`](FUTURE_WORK.md) — the in-range index invariants a few candidates
  above depend on, and the two-approach design discussion for provable indexing.
- [`SPECS_ARCHITECTURE.md`](SPECS_ARCHITECTURE.md) §11 — candidate theorems from the
  framework's own design docs, and the inheritance-replay proof-transfer question the
  `inherit`-adjacent entries above assume.
