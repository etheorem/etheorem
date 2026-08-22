# Proof ledger

## Purpose

The forward half of proof coverage. `proof-coverage.baseline` records what is
proved; this file records what we intend to prove, one row per candidate spec
function. A candidate is a function with a clear invariant, safety property,
algebraic law, monotonicity property, or other proof-worthy claim. The list is a
shortlist, not a classification of the fork's surface: Gloas introduces 62 new
functions and overrides 46 inherited ones, and the rows below were found by
reading across the Gloas specification and its supporting libraries.

## The columns

| Column | What it holds |
| --- | --- |
| Function | The spec function, by its Lean name. |
| Location | A line span into the fork body that declares it, `Fork/File.lean:start-end`. |
| Property | The theorem the row asks for, and what a landed theorem does and does not establish. |
| Status | `proposed`, `in progress`, `proved`, or `out of scope`. |
| Tracking | The pull request that landed or is landing the proof, and the module holding it. |

A row stays here for its whole life. It opens as `proposed`, and the pull
request that discharges it flips the status and bumps the baseline in the same
diff, so the ledger reads as the full list of candidates and the baseline reads
as the subset that is done.

`in progress` covers a theorem being written and one that is partly landed
alike. A theorem lands partly when it states one branch, one call pattern, or a
restatement of a helper rather than the whole claim the row asks for. It then
carries no `@[characterizes]` tag, and the Property cell says what is landed and
what is open. `getPtc` and `shouldExtendPayload` are the two cases that show it.

`out of scope` carries its reason in the Property cell, cryptographic
assumptions being the standing case.

## The Location column

Each row cites a line span into the spec body: start at the declaration's own
line (`forkdef` / `def` / `abbrev` / `inherit`), end at the last non-blank line
before the next top-level construct. These spans rot on their own, since any edit
above a declaration moves it, so `just check-citations` resolves every one of
them against the declaration its row names and fails on a mismatch. It covers the
module docstrings under `EthCLSpecs/Proofs/`, which cite in the same format, and
it runs in CI next to `just lint`. `just check-citations --fix` rewrites the stale
spans.

Do not refresh a span by hand. The rows are only worth trusting if they are all
checked at once, and a hand edit that skips the checker is how the table ends up
mixing fresh rows with stale ones again.

## What the coverage report reads

`just proof-coverage` reads this file. A row counts as proved when its Status
cell reads `proved`, and the Location column's leading path component names the
fork, so `` `getPtc` `` in a `Gloas/…` row resolves to `EthCLSpecs.Gloas.getPtc`.
The report warns when a proved row carries no `@[characterizes …]` tag on any
theorem, and when a tagged function has no proved row here. Both warnings are
advisory. The report never fails on this file, since the rows are prose and a
table the script cannot parse is still a table a person can read.

## One section per fork

A fork elaborates its own constant for every declaration, inherited ones
included, so a proof about `EthCLSpecs.Gloas.f` says nothing about
`EthCLSpecs.Heze.f`. The rows are grouped by fork for that reason, and by the
kind of theorem they ask for within a fork, since the kind is what tells an
author how to state it. `EthCLSpecs/Proofs/` splits per fork the same way.

## Dependencies between rows

Three claims rest on another row:

- The committee partition rests on the shuffle bijection.
- Plausible liveness rests on accountable safety.
- Both `processDeposit` rows rest on the Merkle branch check that
  [`../../SizzLean/docs/PLAN.md`](../../SizzLean/docs/PLAN.md) Phase 5 tracks.

---

## Gloas

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Gloas function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:456` | Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit, since `toBuilderIndex` always clears that bit, the round trip holds only under that precondition, not as a free identity | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |
| `toBuilderIndex` | `Gloas/Operations.lean:54` | Clears the `BUILDER_INDEX_FLAG` bit, so it inverts `convertBuilderIndexToValidatorIndex` on any index that already carries the flag; the companion direction is the row above | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeExitEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:93-103` | The churn arithmetic this call site performs through `reserveChurn` must not underflow | proposed |  |
| `getExpectedWithdrawals` | `Gloas/Withdrawals.lean:171-179` | The withdrawals returned by its four phases combined never exceed `MAX_WITHDRAWALS_PER_PAYLOAD` | proposed |  |
| `initiateBuilderExit` | `Gloas/Operations.lean:88-91` | `initiateBuilderExit_run_eq` is the whole-transition equation; its exact in-range/out-of-range effect on the builder registry is characterized; no-wrap is conditional for an arbitrary `Config` and proved unconditionally for both shipped Gloas preset/config pairs | proved | #39, `Proofs/Gloas/InitiateBuilderExit.lean` |
| `processBuilderExitRequest` | `Gloas/Operations.lean:194-204` | On its successful builder-exit branch, the index supplied to `initiateBuilderExit` is in range; under either shipped Gloas preset/config pair, the selected builder receives the intended non-wrapping future `withdrawableEpoch`. All non-matching or ineligible branches leave the builder registry unchanged | proposed |  |
| `getPtc` | `Gloas/Operations.lean:389-406` | Its computed offset into `ptcWindow` stays in range under the two guarded call patterns: `data.slot + 1 == state.slot` and the fork-choice replay callers' `slot == curSlot`. Landed so far: both bounds, stated over `getPtcElseOffset`, a restatement of the else-branch arithmetic. Open: a statement about `getPtc` itself, which is what would carry a `characterizes` tag and move the function past the touched tier | in progress | `4b4b78a`, `Proofs/Gloas/GetPtc.lean` |
| `getPendingBalanceToWithdrawForBuilder` | `Gloas/Operations.lean:61-65` | Under an explicit bound preventing overflow across both sequential `UInt64` folds, its result agrees with the unbounded `Nat` sum of the matching pending-withdrawal and pending-payment amounts | proposed |  |
| `canBuilderCoverBid` | `Gloas/Operations.lean:460-463` | Its `Bool` result is characterized exactly against the implementation's computed `minBalance`. Proving that queuing an accepted bid preserves `MIN_DEPOSIT_AMOUNT` + pending obligations ≤ builder balance is the caller-level follow-up, and needs pending-total no-overflow and ring-cell freshness hypotheses | proved | #36, `Proofs/Gloas/CanBuilderCoverBid.lean` |
| `applyWithdrawals` | `Gloas/Withdrawals.lean:184-194` | A builder-flagged withdrawal decreases the builder's balance by at most its own balance, so the balance never goes negative | proposed |  |
| `getAncestor` | `Gloas/ForkChoice.lean:177-184` | The fuel supplied to its `fuelLoop` DAG walk is sufficient for the walk to terminate before running out | proposed |  |
| `getHead` | `Gloas/ForkChoice.lean:534-569` | The fuel `2 * blocks.length + 2` supplied to its LMD-GHOST walk is sufficient for the walk to reach a decided head before running out | proposed |  |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processProposerSlashing` | `Gloas/Operations.lean:211-241` | Payment-voiding must never touch another proposer's `BuilderPendingPayment` | proposed |  |
| `processAttestation` | `Gloas/Operations.lean:291-369` | Committee-index safety together with builder-payment weight accounting | proposed |  |
| `processBuilderPendingPayments` | `Gloas/EpochProcessing.lean:234-253` | Under an explicit capacity hypothesis, every qualifying previous-epoch payment's withdrawal is appended to `builderPendingWithdrawals` in slot order, and the payment window shifts down by `SLOTS_PER_EPOCH`; this does not establish protocol-wide exactly-once settlement | proved | #25, `Proofs/Gloas/BuilderPendingPayments.lean` |
| `processPtcWindow` | `Gloas/EpochProcessing.lean:272-282` | Each newly populated `ptcWindow` entry equals `computePtc` evaluated for its corresponding slot | proposed |  |
| `applyDepositForBuilder` | `Gloas/Operations.lean:118-126` | A deposit with an invalid signature is neither applied to a builder's balance nor requeued | proposed |  |
| `processBuilderDepositRequest` | `Gloas/Operations.lean:172-188` | A new builder is onboarded only when its deposit signature is valid | proposed |  |
| `getIndexedPayloadAttestation` | `Gloas/Operations.lean:411-417` | Preserves `pa.data` and `pa.signature`, and produces the sorted multiset of PTC seats selected by `pa.aggregationBits`. The proof requires `Array.qsort` sortedness and permutation lemmas not currently available in core/Std | proposed |  |
| `isValidIndexedPayloadAttestation` | `Gloas/Operations.lean:422-433` | Returns true exactly when the attesting indices are non-empty, adjacent-nondecreasing (duplicates permitted), all within the validator registry, and the configured `[CryptoBackend]` accepts the exact aggregate-verification call | proved | #38, `Proofs/Gloas/IsValidIndexedPayloadAttestation.lean` |
| `processPayloadAttestation` | `Gloas/Operations.lean:438-451` | Running `processPayloadAttestation` does not modify `State`: it only reads the input state and evaluates three assertions. A concrete run-level theorem should show that both success and rejection preserve the state component | proposed |  |
| `processExecutionPayloadBid` | `Gloas/Operations.lean:492-526` | The self-build and builder-bid paths it chooses between are mutually exclusive and jointly exhaustive | proposed |  |
| `applyParentExecutionPayload` | `Gloas/Operations.lean:531-555` | Exactly one of settle-current, settle-previous, or evict fires, so a payment is never settled twice | proposed |  |

### Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates: never decreasing, never shrinking, never losing a previously-added element.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getWeight` | `Gloas/ForkChoice.lean:422-434` | Weight only grows as more attestations accumulate for a node | proposed |  |
| `onAttesterSlashing` | `Gloas/ForkChoice.lean:1023-1033` | The set of equivocating indices only grows, never shrinks | proposed |  |
| `updateCheckpoints` | `Gloas/ForkChoice.lean:574-576` | Each justified/finalized checkpoint either remains unchanged or advances to its candidate, so its epoch never decreases, and no other Store field moves | proved | #30, `Proofs/Gloas/UpdateCheckpoints.lean` |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processSlot` | `Gloas/Transition.lean:32-52` | After `processSlot`, the `executionPayloadAvailability` bit at index `(slot + 1) mod SLOTS_PER_HISTORICAL_ROOT` reads `false`, matching the documented invariant that a payload starts unavailable | proposed |  |
| `processOperations` | `Gloas/Transition.lean:87-94` | public declarations live in `EthCLSpecs.Proofs.Gloas`. Non-empty in-block deposits fail immediately with `StateTransitionError.assert` and the pre-state preserved; success is equivalent to empty deposits plus the six operation-family loops succeeding sequentially. Handlers remain opaque; no per-operation correctness or rollback guarantee for later failures is claimed | proved | #57, `Proofs/Gloas/ProcessOperations.lean` |
| `stateTransition` | `Gloas/Transition.lean:108-118` | Top-level state-transition correctness; composes `processSlots`, `processBlock`, and the root check into the canonical transition | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `onBlock` | `Gloas/ForkChoice.lean:759-808` | Accepts a block only if a full parent implies a verified payload, and the block's ancestry agrees with the currently finalized checkpoint | proposed |  |
| `validateOnAttestation` | `Gloas/ForkChoice.lean:954-984` | Validates that the attestation's index is 0 or 1, that a same-slot attestation has index 0, and that a full-vote attestation's payload is verified | proposed |  |
| `getForkchoiceStore` | `Gloas/ForkChoice.lean:1044-1076` | Every root-keyed map in a freshly built store agrees on the anchor entry | proposed |  |
| `isAncestor` | `Gloas/ForkChoice.lean:189-194` | Agrees with the ancestor relation that `getAncestor` computes iteratively | proposed |  |
| `verifyExecutionPayloadEnvelope` | `Gloas/ForkChoice.lean:873-908` | Acceptance requires every validation check performed by `verifyExecutionPayloadEnvelope` to succeed | proposed |  |

### Upgrade-boundary properties

Functions whose entire purpose is the Fulu-to-Gloas upgrade itself: preserving state across the boundary or seeding Gloas-only state from it. The fork comparison here is not incidental, it's what the function does.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `upgradeToGloas` | `Gloas/Upgrade.lean:109-164` | Preserves inherited state while correctly initializing the new ePBS state | proposed |  |
| `computePtcFromFulu` | `Gloas/Upgrade.lean:43-51` | Agrees with `Gloas.computePtc` once the state is upgraded | proposed |  |
| `initializePtcWindow` | `Gloas/Upgrade.lean:58-68` | The first `SLOTS_PER_EPOCH` entries are the empty committee, and every remaining entry equals `computePtcFromFulu` at the slot computed by `initializePtcWindow` . A plain `def` inside the fork body rather than a `forkdef`, so it is no spec function and the coverage report's denominator never holds it | proved | #26, `Proofs/Gloas/InitializePtcWindow.lean` |

### Candidates needing a sharper statement

Functions where the useful theorem hasn't been identified yet, either because the obvious candidate property doesn't hold up, or because none has been proposed. Once identified, the candidate belongs in one of the sections above.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computePtc` | `Gloas/EpochProcessing.lean:259-266` | No standalone theorem has been identified yet. The strongest current candidate is its agreement with `computePtcFromFulu` after state upgrade | proposed |  |


---

## Fulu

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Fulu function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeEpochAtSlot` | `Fulu/Time.lean:29` | `computeEpochAtSlot (computeStartSlotAtEpoch e) = e`, for `e < 2^59`. The raw `UInt64` multiply wraps above `2^59`, so the identity needs that bound | proposed |  |
| `computeStartSlotAtEpoch` | `Fulu/Time.lean:32` | The same identity, seen from this side. The round trip is the row above | proposed |  |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `reserveChurn` | `Fulu/RegistryUpdates.lean:69-74` | Arithmetic never underflows | proposed |  |
| `increaseBalance` | `Fulu/Balances.lean:29` | The balance addition never wraps | proposed |  |
| `processDeposit` | `Fulu/Operations.lean:223` | Neither the incremented deposit index nor the running total balance exceeds `2^64`. Dafny stated both bounds and assumed them through `{:axiom}` lemmas, so Dafny's statements are reusable as a template. Its proofs are not. A sharper bound is open as well. The branch check needs `eth1DepositIndex < 2^32`, which follows from `eth1DepositIndex <= eth1Data.depositCount` together with a bound on `depositCount`. The consensus spec does not bound `depositCount`, since that count arrives from the execution layer. Any statement here is therefore conditional on the deposit contract's depth-32 capacity | proposed |  |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:174` | The registry never exceeds `VALIDATOR_REGISTRY_LIMIT` | proposed |  |
| `getBeaconCommittee` | `Fulu/Committees.lean:83` | An active-validator count in `[32, 2^22]` implies every committee size is in `(0, MAX_VALIDATORS_PER_COMMITTEE]`. Dafny proves the same bound in `ActiveValidatorBounds` | proposed |  |
| `computeBalanceWeightedSelection` | `Fulu/Committees.lean:118` | Its `cbwsAux` sampler loop takes `10000000` fuel, which always suffices for the walk to finish | proposed |  |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeShuffledPermutation` | `Fulu/Committees.lean:32` | A bijection on `[0, indexCount)`. No prior art: Dafny stubbed shuffling to the identity, and Runtime Verification did not prove it either | proposed |  |
| `getBeaconCommittee` | `Fulu/Committees.lean:83` | The committees for a slot partition the active set: their union is the active validator set and they are pairwise disjoint. This follows from the shuffle bijection. The committee-size bound is the separate row under Bounds and termination properties | proposed |  |
| `processDeposit` | `Fulu/Operations.lean:223` | `validators.size = balances.size` holds at the append site, and then holds across the transition. The two overflow bounds are the separate row under Bounds and termination properties | proposed |  |
| `isSlashableAttestationData` | `Fulu/Operations.lean:38` | Agrees with the spec's slashability condition, a double vote or a surround vote, given the `strictlySorted` well-formedness the caller establishes | proposed |  |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:174` | One third of a joint claim with `initiateValidatorExit` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `initiateValidatorExit` | `Fulu/RegistryUpdates.lean:112` | One third of a joint claim with `processRegistryUpdates` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `computeExitEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:78` | One third of a joint claim with `processRegistryUpdates` and `initiateValidatorExit`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processJustificationAndFinalization` | `Fulu/EpochProcessing.lean:78` | Casper FFG accountable safety: conflicting finalized and justified checkpoints imply that at least `1/3` of the stake is slashable. Needs an abstract FFG layer over the epoch-processing functions and a refinement back to them. Plausible liveness, that finalization stays possible with `>= 2/3` honest, comes after accountable safety and reuses that model. Apalache bounded-model-checked the 3SF form of the property (Konnov et al. 2025), so the result is checked up to a bound and remains unproved | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getAncestor` | `Fulu/ForkChoice.lean:136` | One third of a joint claim with `getHead` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `getHead` | `Fulu/ForkChoice.lean:261` | One third of a joint claim with `getAncestor` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `onBlock` | `Fulu/ForkChoice.lean:526` | One third of a joint claim with `getAncestor` and `getHead`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |


---

## Heze

Heze is a twelve-declaration diff over Gloas, and only its FOCIL gate has been
read for proof candidates so far. Every Gloas row above applies to Heze's
re-elaboration of that declaration as a separate claim about a separate
constant.

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `shouldExtendPayload` | `Heze/ForkChoice.lean:320-342` | Under successful preliminary lookup and slot checks, a verified payload with a recorded `false` inclusion-list satisfaction verdict is rejected by the FOCIL gate, with the pure runner state unchanged. This is not complete correctness of `shouldExtendPayload`: the later Gloas accept and reject paths and the missing-record `assert` branch stay out of scope, and the two write-path rows below stay open | in progress | #63, `Proofs/Heze/ShouldExtendPayload.lean` |
| `recordPayloadInclusionListSatisfaction` | `Heze/ForkChoice.lean:406-418` | The value inserted at `root` equals `isInclusionListSatisfied payload ilTxs`. Its `false` corollary discharges the recorded-unsatisfaction hypothesis of `shouldExtendPayload_run_eq_false_of_recorded_unsatisfied` | proposed |  |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:426-448` | After a successful envelope acceptance, `payloads[root]` and `payloadInclusionListSatisfaction[root]` are written together for the same `root`, so a verified payload is paired with some recorded satisfaction verdict | proposed |  |
| `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean:305` | EIP-7805 FOCIL: a payload is accepted only when it carries every transaction that a timely inclusion list requires | proposed |  |
| `processInclusionList` | `Heze/ForkChoice.lean:170` | At most one stored list per validator per committee, asserted in its docstring and not proved. A conflicting second list leaves the stored list untouched and records the sender as an equivocator for that committee. The handler then ignores later lists from that validator on entry | proposed |  |

---

## Related work

- [`FUTURE_WORK.md`](FUTURE_WORK.md) — the in-range index invariants a few candidates
  above depend on, and the two-approach design discussion for provable indexing.
- [`SPECS_ARCHITECTURE.md`](SPECS_ARCHITECTURE.md) §11 — candidate theorems from the
  framework's own design docs, and the inheritance-replay proof-transfer question the
  `inherit`-adjacent entries above assume.
- [`../../SizzLean/docs/PLAN.md`](../../SizzLean/docs/PLAN.md) Phase 5 — the SSZ-side
  targets, which include the merkleization agreement. Any Merkle-proof consumer here
  needs that agreement before a theorem about the cached tree says anything about a
  spec root.
- ConsenSys `eth2.0-dafny` (Phase 0, archived) — proved the state transition as
  refinement, plus committee-size bounds and fork-choice store invariants. It stubbed
  shuffling to the identity. It assumed the overflow bounds through `{:axiom}` lemmas
  instead of proving them. Its Casper FFG accountable-safety result reached only an
  unmerged branch, under a fixed validator set.
- Runtime Verification — an executable K model of the Phase 0 transition,
  conformance-tested rather than proved. A separate Coq development closed Gasper
  accountable safety and plausible liveness, over an abstract model with dynamic
  validator sets. It also proved the deposit contract's incremental Merkle root equal
  to the naive full-tree root. It refined the KEVM bytecode against an untrusted
  compiler, which found bugs. That incremental-tree result is the closest prior art to
  the deposit branch check the `processDeposit` rows name.
- Nyx Foundation `formal-leanSpec` — a parallel Lean 4 formalization of the
  post-quantum leanSpec, with its own SSZ layer.
