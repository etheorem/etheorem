# Consensus Proof Candidates

## Purpose

A shortlist of Lean theorem candidates in `EthCLSpecs`, so contributors have a curated
starting point. This is not a classification of
the fork's surface area, just the functions with a clear invariant, safety property,
determinism guarantee, or algebraic property (like an inverse) worth proving.

## Overview

Gloas introduces 62 new functions and overrides 46 inherited ones. The candidates below
were identified by reading across `EthCLSpecs` and `EthCLLib`, focusing on functions with
clear correctness properties, safety invariants, determinism guarantees, or useful
algebraic laws. The list is intentionally curated rather than exhaustive.

---

## Gloas overrides

Functions Gloas redeclares under a name that also exists in Fulu, so a Fulu-vs-Gloas diff
is often the cleanest way to state the theorem.

| Function                         | Location                            | Rationale                                                                                                                      |
| -------------------------------- | ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| `processSlot`                    | `Gloas/Transition.lean:33-53`       | Identical to Fulu's `processSlot` except one new bit-clear; the small diff makes this a natural preservation theorem           |
| `processOperations`              | `Gloas/Transition.lean:88-95`       | `assert (body.deposits.size == 0)` — a "should never happen" precondition, cheap to state                                      |
| `computeExitEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:90-100` | Shares `reserveChurn` with Fulu; one proof of no-underflow covers 4 call sites across both forks                               |
| `getAncestor`                    | `Gloas/ForkChoice.lean:156-163`     | `fuelIterate` DAG walk — `Loop.lean`'s own docstring names this exact fuel-bound pattern as a deferred lemma, never discharged |
| `getHead`                        | `Gloas/ForkChoice.lean:446-465`     | Determinism of the LMD-GHOST head as a pure function of the store                                                              |
| `stateTransition`                | `Gloas/Transition.lean:109-120`     | Top-level happy-path correctness, glues `processSlots` + `processBlock` + root check                                           |
| `getExpectedWithdrawals`         | `Gloas/Withdrawals.lean:160-168`    | 4-phase composition must never exceed `MAX_WITHDRAWALS_PER_PAYLOAD`, a bound invariant feeding builder solvency                |
| `processAttestation`             | `Gloas/Operations.lean:289-360`     | `data.index < 2` safety check plus builder-payment weight monotonicity                                                         |
| `processProposerSlashing`        | `Gloas/Operations.lean:213-243`     | Payment-voiding must never touch another proposer's `BuilderPendingPayment`                                                    |
| `getWeight`                      | `Gloas/ForkChoice.lean:359-369`     | Determinism plus monotonicity — weight only grows with more attestations                                                       |
| `onBlock`                        | `Gloas/ForkChoice.lean:594-625`     | Parent-full-implies-verified, finality-conflict rejection                                                                      |
| `validateOnAttestation`          | `Gloas/ForkChoice.lean:737-756`     | Precondition bundle: index ∈ {0,1}, same-slot ⇒ index 0, full vote ⇒ payload verified                                          |
| `onAttesterSlashing`             | `Gloas/ForkChoice.lean:791-801`     | Equivocating-index set must only grow, never shrink                                                                            |
| `getForkchoiceStore`             | `Gloas/ForkChoice.lean:808-827`     | Freshly-built store's root-keyed maps agree on one anchor entry, the base case on which other invariants can be built          |
| `updateCheckpoints`              | `Gloas/ForkChoice.lean:470-472`     | Justified/finalized epochs never decrease                                                                                      |

---

## New Gloas functionality

Functions with no Fulu counterpart (EIP-7732 ePBS: builder registry, execution payload
bids/envelopes, PTC voting). No Fulu diff is possible; the theorem has to stand on its
own.

| Function                              | Location                             | Rationale                                                                                                                                                                                                              |
| ------------------------------------- | ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `initiateBuilderExit`                 | `Gloas/Operations.lean:90-93`        | Sets `withdrawableEpoch := epoch + delay`; unlike Fulu's `initiateValidatorExit`, which guards the identical arithmetic with an overflow assertion, this path lacks one, making it a useful candidate for confirmation |
| `getPtc`                              | `Gloas/Operations.lean:368-376`      | The source comment explicitly notes an unchecked precondition                                                                                                                                                          |
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:415`          | **In review**, see `EthCLSpecs/Proofs/BuilderIndex.lean`. Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit, `toBuilderIndex` always clears it, so the round trip needs that precondition, not a free identity            |
| `processBuilderPendingPayments`       | `Gloas/EpochProcessing.lean:229-248` | Exactly-once payout via `shiftWindow`                                                                                                                                                                                  |
| `processPtcWindow`                    | `Gloas/EpochProcessing.lean:267-277` | Maintains the window-consistency invariant `getPtc`'s docstring depends on                                                                                                                                             |
| `applyDepositForBuilder`              | `Gloas/Operations.lean:120-128`      | On an invalid signature the deposit is neither applied nor requeued; this forfeiture behavior is a useful candidate for confirmation against the spec                                                                  |
| `processBuilderDepositRequest`        | `Gloas/Operations.lean:174-190`      | New builder onboarded only with a valid signature                                                                                                                                                                      |
| `isValidIndexedPayloadAttestation`    | `Gloas/Operations.lean:389-400`      | Precondition bundle: non-empty, sorted, in-range, valid aggregate signature                                                                                                                                            |
| `canBuilderCoverBid`                  | `Gloas/Operations.lean:419-422`      | Core solvency check used by the builder-payment flow                                                                                                                                                                   |
| `processExecutionPayloadBid`          | `Gloas/Operations.lean:451-484`      | Self-build vs builder path must be mutually exclusive and jointly exhaustive                                                                                                                                           |
| `applyParentExecutionPayload`         | `Gloas/Operations.lean:489-513`      | Exactly one of {settle-current, settle-previous, evict} fires, guarding against double-settling a payment                                                                                                              |
| `applyWithdrawals`                    | `Gloas/Withdrawals.lean:173-184`     | The builder-solvency safety net (`umin` floor) applied during every withdrawal                                                                                                                                         |
| `isAncestor`                          | `Gloas/ForkChoice.lean:168-175`      | Must agree with a direct DAG walk from `node`, the same relation `getAncestor` computes iteratively                                                                                                                    |
| `verifyExecutionPayloadEnvelope`      | `Gloas/ForkChoice.lean:652-678`      | One of the densest precondition bundles in the new-Gloas surface (9 asserts); gates block acceptance                                                                                                                   |
| `computePtc`                          | `Gloas/EpochProcessing.lean:254-261` | Deterministic given `(state, slot)`; feeds the cross-fork consistency theorem with `computePtcFromFulu`                                                                                                                |

---

## Standalone helpers

Plain `def`s, not `forkdef`s, so they fall outside the override/new-Gloas split above but
are worth proving.

| Function              | Location                          | Rationale                                                                                                                                                                               |
| --------------------- | --------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `upgradeToGloas`      | `Gloas/Upgrade.lean:101-156`      | Field-by-field preservation across the fork boundary: ~20 fields copied verbatim, 6 list fields converted via `mapCap`, ePBS-fresh fields get a "day-one" spec worth stating on its own |
| `computePtcFromFulu`  | `Gloas/Upgrade.lean:35-43`        | Should agree with `Gloas.computePtc` once the state is actually upgraded — a cross-fork consistency theorem                                                                             |
| `initializePtcWindow` | `Gloas/Upgrade.lean:50-60`        | Seeds the window `upgradeToGloas` installs; same window-consistency class as `processPtcWindow`/`getPtc`, at the fork boundary instead of steady-state                                  |
| `reserveChurn`        | `Fulu/RegistryUpdates.lean:69-74` | Shared by both forks' exit/consolidation churn; one no-underflow proof covers all four call sites                                                                                       |

---

## Related work

- [`FUTURE_WORK.md`](FUTURE_WORK.md) — the in-range index invariants a few candidates
  above depend on, and the two-approach design discussion for provable indexing.
- [`SPECS_ARCHITECTURE.md`](SPECS_ARCHITECTURE.md) §11 — candidate theorems from the
  framework's own design docs, and the inheritance-replay proof-transfer question the
  `inherit`-adjacent entries above assume.
