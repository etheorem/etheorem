# Consensus Proof Candidates

## Purpose

A shortlist of Lean theorem candidates in `EthCLSpecs`. This is not a classification of
the fork's surface area, just the functions with a clear invariant, safety property, algebraic property (such as an inverse), monotonicity property, or other proof-worthy correctness property.

## Overview

Gloas introduces 62 new functions and overrides 46 inherited ones. The candidates below were identified by reading across the Gloas specification and supporting libraries, focusing on functions with clear correctness properties, safety invariants, algebraic laws, monotonicity properties, and other proof-worthy invariants. The list is not exhaustive.

The sections below group candidates by the kind of theorem they naturally suggest.
A candidate carries no marker until it is discharged, at which point its row reads
**Proved** and names the module holding the theorems. There is no intermediate state:
a proof in flight is tracked by its pull request, and the row flips when that merges.

## The Location column

Each row cites a line span into the spec body: start at the declaration's own line
(`forkdef` / `def` / `abbrev` / `inherit`), end at the last non-blank line before the
next top-level construct. These spans rot on their own, since any edit above a
declaration moves it, so `just check-citations` resolves every one of them against the
declaration its row names and fails on a mismatch. It covers the module docstrings
under `EthCLSpecs/Proofs/`, which cite in the same format, and it runs in CI next to
`just lint`. `just check-citations --fix` rewrites the stale spans.

Do not refresh a span by hand. The rows are only worth trusting if they are all
checked at once, and a hand edit that skips the checker is how the table ends up
mixing fresh rows with stale ones again.

---

## Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Gloas
function, applying one after the other returns the original value, at least
under a stated precondition.

| Function                              | Location                    | Rationale                                                                                                                                                                                                                                                                                  |
| ------------------------------------- | --------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:456` | **Proved**, see `EthCLSpecs/Proofs/BuilderIndex.lean`. Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit, since `toBuilderIndex` always clears that bit, the round trip holds only under that precondition, not as a free identity. |

---

## Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never
exceeding a spec constant, or a termination bound, a fuel parameter large enough for a
bounded walk to finish.

| Function                                | Location                            | Rationale                                                                                                                                          |
| --------------------------------------- | ----------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------- |
| `computeExitEpochAndUpdateChurn`        | `Gloas/EpochProcessing.lean:93-103` | The churn arithmetic this call site performs through `reserveChurn` must not underflow                                                             |
| `reserveChurn`                          | `Fulu/RegistryUpdates.lean:69-74`   | Arithmetic never underflows                                                                                                                        |
| `getExpectedWithdrawals`                | `Gloas/Withdrawals.lean:171-179`    | The withdrawals returned by its four phases combined never exceed `MAX_WITHDRAWALS_PER_PAYLOAD`                                                    |
| `initiateBuilderExit`                   | `Gloas/Operations.lean:88-91`       | **Proved**, see `EthCLSpecs/Proofs/InitiateBuilderExit.lean`. `initiateBuilderExit_run_eq` is the whole-transition equation; its exact in-range/out-of-range effect on the builder registry is characterized; no-wrap is conditional for an arbitrary `Config` and proved unconditionally for both shipped Gloas preset/config pairs |
| `processBuilderExitRequest`             | `Gloas/Operations.lean:194-204`     | On its successful builder-exit branch, the index supplied to `initiateBuilderExit` is in range; under either shipped Gloas preset/config pair, the selected builder receives the intended non-wrapping future `withdrawableEpoch`. All non-matching or ineligible branches leave the builder registry unchanged |
| `getPtc`                                | `Gloas/Operations.lean:389-406`     | **Proved**, see `EthCLSpecs/Proofs/GetPtc.lean`. Its computed offset into `ptcWindow` stays in range under the two guarded call patterns covered here: `data.slot + 1 == state.slot` and the fork-choice replay callers' `slot == curSlot` |
| `getPendingBalanceToWithdrawForBuilder` | `Gloas/Operations.lean:61-65`       | Under an explicit bound preventing overflow across both sequential `UInt64` folds, its result agrees with the unbounded `Nat` sum of the matching pending-withdrawal and pending-payment amounts |
| `canBuilderCoverBid`                    | `Gloas/Operations.lean:460-463`     | **Proved**, see `EthCLSpecs/Proofs/CanBuilderCoverBid.lean`. Its `Bool` result is characterized exactly against the implementation's computed `minBalance`. Proving that queuing an accepted bid preserves `MIN_DEPOSIT_AMOUNT` + pending obligations ≤ builder balance is the caller-level follow-up, and needs pending-total no-overflow and ring-cell freshness hypotheses |
| `applyWithdrawals`                      | `Gloas/Withdrawals.lean:184-194`    | A builder-flagged withdrawal decreases the builder's balance by at most its own balance, so the balance never goes negative                        |
| `getAncestor`                           | `Gloas/ForkChoice.lean:177-184`     | The fuel supplied to its `fuelLoop` DAG walk is sufficient for the walk to terminate before running out                                            |
| `getHead`                               | `Gloas/ForkChoice.lean:534-569`     | The fuel `2 * blocks.length + 2` supplied to its LMD-GHOST walk is sufficient for the walk to reach a decided head before running out              |

---

## Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function                           | Location                             | Rationale                                                                                                                          |
| ---------------------------------- | ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------- |
| `processProposerSlashing`          | `Gloas/Operations.lean:211-241`      | Payment-voiding must never touch another proposer's `BuilderPendingPayment`                                                        |
| `processAttestation`               | `Gloas/Operations.lean:291-369`      | Committee-index safety together with builder-payment weight accounting                                                             |
| `processBuilderPendingPayments`    | `Gloas/EpochProcessing.lean:234-253` | **Proved**, see `EthCLSpecs/Proofs/BuilderPendingPayments.lean`. Under an explicit capacity hypothesis, every qualifying previous-epoch payment's withdrawal is appended to `builderPendingWithdrawals` in slot order, and the payment window shifts down by `SLOTS_PER_EPOCH`; this does not establish protocol-wide exactly-once settlement |
| `processPtcWindow`                 | `Gloas/EpochProcessing.lean:272-282` | Each newly populated `ptcWindow` entry equals `computePtc` evaluated for its corresponding slot                                    |
| `applyDepositForBuilder`           | `Gloas/Operations.lean:118-126`      | A deposit with an invalid signature is neither applied to a builder's balance nor requeued                                         |
| `processBuilderDepositRequest`     | `Gloas/Operations.lean:172-188`      | A new builder is onboarded only when its deposit signature is valid                                                                |
| `getIndexedPayloadAttestation`     | `Gloas/Operations.lean:411-417`      | Preserves `pa.data` and `pa.signature`, and produces the sorted multiset of PTC seats selected by `pa.aggregationBits`. The proof requires `Array.qsort` sortedness and permutation lemmas not currently available in core/Std |
| `isValidIndexedPayloadAttestation` | `Gloas/Operations.lean:422-433`      | **Proved**, see `EthCLSpecs/Proofs/IsValidIndexedPayloadAttestation.lean`. Returns true exactly when the attesting indices are non-empty, adjacent-nondecreasing (duplicates permitted), all within the validator registry, and the configured `[CryptoBackend]` accepts the exact aggregate-verification call |
| `processPayloadAttestation`        | `Gloas/Operations.lean:438-451`      | Running `processPayloadAttestation` does not modify `State`: it only reads the input state and evaluates three assertions. A concrete run-level theorem should show that both success and rejection preserve the state component |
| `processExecutionPayloadBid`       | `Gloas/Operations.lean:492-526`      | The self-build and builder-bid paths it chooses between are mutually exclusive and jointly exhaustive                              |
| `applyParentExecutionPayload`      | `Gloas/Operations.lean:531-555`      | Exactly one of settle-current, settle-previous, or evict fires, so a payment is never settled twice                                |

---

## Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates:
never decreasing, never shrinking, never losing a previously-added element.

| Function             | Location                        | Rationale                                                    |
| -------------------- | ------------------------------- | ------------------------------------------------------------ |
| `getWeight`          | `Gloas/ForkChoice.lean:422-434` | Weight only grows as more attestations accumulate for a node |
| `onAttesterSlashing` | `Gloas/ForkChoice.lean:1023-1033` | The set of equivocating indices only grows, never shrinks    |
| `updateCheckpoints`  | `Gloas/ForkChoice.lean:574-576` | **Proved**, see `EthCLSpecs/Proofs/UpdateCheckpoints.lean`. Each justified/finalized checkpoint either remains unchanged or advances to its candidate, so its epoch never decreases, and no other Store field moves. |

---

## State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual
processing steps into the top-level state transition, and the properties that hold as a
direct consequence of running through it.

| Function            | Location                        | Rationale                                                                                                                                                                                          |
| ------------------- | ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `processSlot`       | `Gloas/Transition.lean:32-52`   | After `processSlot`, the `executionPayloadAvailability` bit at index `(slot + 1) mod SLOTS_PER_HISTORICAL_ROOT` reads `false`, matching the documented invariant that a payload starts unavailable |
| `processOperations` | `Gloas/Transition.lean:87-94`   | **Proved**, see `EthCLSpecs/Proofs/ProcessOperations.lean`; public declarations live in `EthCLSpecs.Proofs.Gloas`. Non-empty in-block deposits fail immediately with `StateTransitionError.assert` and the pre-state preserved; success is equivalent to empty deposits plus the six operation-family loops succeeding sequentially. Handlers remain opaque; no per-operation correctness or rollback guarantee for later failures is claimed |
| `stateTransition`   | `Gloas/Transition.lean:108-118` | Top-level state-transition correctness; composes `processSlots`, `processBlock`, and the root check into the canonical transition                                                                  |

---

## Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function                         | Location                         | Rationale                                                                                                                                          |
| ---------------------------------- | ---------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------- |
| `onBlock`                        | `Gloas/ForkChoice.lean:759-808`  | Accepts a block only if a full parent implies a verified payload, and the block's ancestry agrees with the currently finalized checkpoint          |
| `validateOnAttestation`          | `Gloas/ForkChoice.lean:954-984`  | Validates that the attestation's index is 0 or 1, that a same-slot attestation has index 0, and that a full-vote attestation's payload is verified |
| `getForkchoiceStore`             | `Gloas/ForkChoice.lean:1044-1076` | Every root-keyed map in a freshly built store agrees on the anchor entry                                                                           |
| `isAncestor`                     | `Gloas/ForkChoice.lean:189-194`  | Agrees with the ancestor relation that `getAncestor` computes iteratively                                                                          |
| `verifyExecutionPayloadEnvelope` | `Gloas/ForkChoice.lean:873-908`  | Acceptance requires every validation check performed by `verifyExecutionPayloadEnvelope` to succeed                                                |

---

## Upgrade-boundary properties

Functions whose entire purpose is the Fulu-to-Gloas upgrade itself: preserving state
across the boundary or seeding Gloas-only state from it. The fork comparison here is not
incidental, it's what the function does.

| Function              | Location                     | Rationale                                                                                                                                                            |
| --------------------- | ---------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `upgradeToGloas`      | `Gloas/Upgrade.lean:109-164` | Preserves inherited state while correctly initializing the new ePBS state                                                                                            |
| `computePtcFromFulu`  | `Gloas/Upgrade.lean:43-51`   | Agrees with `Gloas.computePtc` once the state is upgraded                                                                                                            |
| `initializePtcWindow` | `Gloas/Upgrade.lean:58-68`   | **Proved**, see `EthCLSpecs/Proofs/InitializePtcWindow.lean`. The first `SLOTS_PER_EPOCH` entries are the empty committee, and every remaining entry equals `computePtcFromFulu` at the slot computed by `initializePtcWindow`. |

---

## Candidates needing a sharper statement

Functions where the useful theorem hasn't been identified yet, either because the
obvious candidate property doesn't hold up, or because none has been proposed. Once
identified, the candidate belongs in one of the sections above.

| Function     | Location                             | Rationale                                                                                                                                     |
| ------------ | ------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------- |
| `computePtc` | `Gloas/EpochProcessing.lean:259-266` | No standalone theorem has been identified yet. The strongest current candidate is its agreement with `computePtcFromFulu` after state upgrade |

---

## Related work

- [`FUTURE_WORK.md`](FUTURE_WORK.md) — the in-range index invariants a few candidates
  above depend on, and the two-approach design discussion for provable indexing.
- [`SPECS_ARCHITECTURE.md`](SPECS_ARCHITECTURE.md) §11 — candidate theorems from the
  framework's own design docs, and the inheritance-replay proof-transfer question the
  `inherit`-adjacent entries above assume.
