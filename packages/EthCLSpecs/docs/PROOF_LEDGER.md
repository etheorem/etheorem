# Proof ledger

## Purpose

The forward half of proof coverage. `proof-coverage.baseline` records what is
proved; this file records what we intend to prove, one row per candidate spec
function. A candidate is a function with a clear invariant, safety property,
algebraic law, monotonicity property, or other proof-worthy claim. The list is a
shortlist, not a classification of the fork's surface: Gloas introduces 62 new
functions and overrides 46 inherited ones, and the rows below were found by
reading across the Gloas specification and its supporting libraries. A Property
cell describes a claim over plain values, so a whole-state claim is the default
(`SPECS_ARCHITECTURE.md` §11.1).

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
carries no `@[characterizes]` tag, and its Property cell carries the fixed
shape `Landed: … Open: …`: what the landed theorem establishes, then the
remainder a `characterizes` theorem would have to cover. `getPtc` is
the case that shows it.

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

These claims rest on another row:

- The committee partition rests on the shuffle bijection.
- Plausible liveness rests on accountable safety.
- Both `processDeposit` rows rest on the Merkle branch check. Its proof module is
  [`EthCLLib/Proofs/MerkleBranch.lean`](../../EthCLLib/EthCLLib/Proofs/MerkleBranch.lean),
  which reduces `isValidMerkleBranch` past its length guard to a fold of `branch`
  over `leaf`. The theorem to cite is
  `isValidMerkleBranch_of_foldOpening`: for `index < 2 ^ depth` it accepts the
  check whenever `branchFold_eq_foldOpening` ties the branch fold to a SizzLean
  tree's own opening, and `Proofs/Merkle/Opening.lean` proves that opening
  folds back to the tree's root (`foldOpening_openingAt`, with the
  mix-in-length variant for list elements). The remaining gap is the tree the
  deposit branch is checked against: the deposit contract's incremental tree is
  not an `ofShape` tree, the case the SizzLean ledger's `branch × deposit-tree`
  row holds out of scope.
- `VerifiedImpliesRecorded` is a joint claim of `getForkchoiceStore` and
  `onExecutionPayloadEnvelope`. The local postcondition at the written root
  cites `FcMap.lookup_insert_self` and `FcMap.contains_insert_self` in
  [`EthCLLib/Proofs/LawfulFcMap.lean`](../../EthCLLib/EthCLLib/Proofs/LawfulFcMap.lean).
  `instLawfulFcMapTreeMap` needs `[Std.TransOrd K]`. `instLawfulFcMapHashMap`
  needs `[EquivBEq K]` and `[LawfulHashable K]`. `instTransOrdVectorUInt8`
  supplies transitivity for `Root` (`Vector UInt8 32`), so both families
  synthesize at those keys. The empty-anchor half also needs lookup and
  `contains` of `FcMap.empty`. Preservation at roots other than the written
  one needs the fact that insert at one key leaves every other key unchanged.
  `LawfulFcMap` does not state those two laws. A source audit identifies
  `getForkchoiceStore` and `onExecutionPayloadEnvelope` as the committed
  writers of `payloads` and `payloadInclusionListSatisfaction`. Global
  preservation still requires frame lemmas for the remaining committed
  handlers. The reverse implication is not the invariant.
  `recordPayloadInclusionListSatisfaction` returns a store with the new bit
  and the old `payloads`.
- `getPayloadStatusTiebreaker` rests on `shouldExtendPayload` returning
  `false`, as in `shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`.
  The envelope postcondition is one way to establish that hypothesis from a
  successful writer. The tiebreaker theorem does not rest on it. The full
  `getHead` walk is not a row here.
- The transport from `Heze.shouldExtendPayload` to `Gloas.shouldExtendPayload`
  rests on `SharesEpbsView` and one lemma per inherited callee that does not
  call the override. It does not rest on `VerifiedImpliesRecorded`.
- The transactions contract for `getInclusionListTransactions` is stated over
  `inclusionListItems`, the map fold. Restating it over `FcMap.lookup` rests on a
  fold law the generic `FcMap` interface does not give. At v1.7.0-beta.4 the
  function cannot raise, so the alpha.12 `.missingKey` arm and its dependence on
  the timeliness row of `processInclusionList` are gone.

---

## Gloas

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Gloas function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:508` | Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit, since `toBuilderIndex` always clears that bit, the round trip holds only under that precondition, not as a free identity | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |
| `toBuilderIndex` | `Gloas/Operations.lean:75` | Clears the `BUILDER_INDEX_FLAG` bit, so it inverts `convertBuilderIndexToValidatorIndex` on any index that already carries the flag; the companion direction is the row above | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeExitEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:96-106` | The churn arithmetic this call site performs through `reserveChurn` must not underflow | proposed |  |
| `getExpectedWithdrawals` | `Gloas/Withdrawals.lean:194-202` | The withdrawals returned by its four phases combined never exceed `MAX_WITHDRAWALS_PER_PAYLOAD` | proposed |  |
| `initiateBuilderExit` | `Gloas/Operations.lean:119-122` | `initiateBuilderExit_run_eq` is the whole-transition equation; its exact in-range/out-of-range effect on the builder registry is characterized; no-wrap is conditional for an arbitrary `Config` and proved unconditionally for both shipped Gloas preset/config pairs | proved | #39, `Proofs/Gloas/InitiateBuilderExit.lean` |
| `processBuilderExitRequest` | `Gloas/Operations.lean:265-275` | On its successful builder-exit branch, the index supplied to `initiateBuilderExit` is in range; under either shipped Gloas preset/config pair, the selected builder receives the intended non-wrapping future `withdrawableEpoch`. All non-matching or ineligible branches leave the builder registry unchanged | proposed |  |
| `getPtc` | `Gloas/Operations.lean:440-458` | Its computed offset into `ptcWindow` stays in range under the two guarded call patterns: `data.slot + 1 == state.slot` and the fork-choice replay callers' `slot == curSlot`. Landed: both bounds, stated over `getPtcElseOffset`, a restatement of the else-branch arithmetic. Open: a statement about `getPtc` itself, which is what would carry a `characterizes` tag and move the function past the touched tier | in progress | `4b4b78a`, `Proofs/Gloas/GetPtc.lean` |
| `getPendingBalanceToWithdrawForBuilder` | `Gloas/Operations.lean:92-96` | Under an explicit bound preventing overflow across both sequential `UInt64` folds, its result agrees with the unbounded `Nat` sum of the matching pending-withdrawal and pending-payment amounts | proposed |  |
| `canBuilderCoverBid` | `Gloas/Operations.lean:512-515` | Its `Bool` result is characterized exactly against the implementation's computed `minBalance`. Proving that queuing an accepted bid preserves `MIN_DEPOSIT_AMOUNT` + pending obligations ≤ builder balance is the caller-level follow-up, and needs pending-total no-overflow and ring-cell freshness hypotheses | proved | #36, `Proofs/Gloas/CanBuilderCoverBid.lean` |
| `applyWithdrawals` | `Gloas/Withdrawals.lean:207-217` | A builder-flagged withdrawal decreases the builder's balance by at most its own balance, so the balance never goes negative | proposed |  |
| `getAncestor` | `Gloas/ForkChoice.lean:184-191` | The fuel supplied to its `fuelLoop` DAG walk is sufficient for the walk to terminate before running out | proposed |  |
| `getHead` | `Gloas/ForkChoice.lean:536-573` | The fuel `2 * blocks.length + 2` supplied to its LMD-GHOST walk is sufficient for the walk to reach a decided head before running out | proposed |  |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processProposerSlashing` | `Gloas/Operations.lean:57` | Out of scope here: at v1.7.0-beta.4 Gloas inherits the Fulu body, and the payment voiding this row asked about moved into `slashValidator` (the next row). Its old claim, that payment-voiding never touches another proposer's `BuilderPendingPayment`, is that row's | out of scope |  |
| `slashValidator` | `Gloas/EpochProcessing.lean:118-151` | The closing EIP-7732 loop resets to the empty payment exactly the `builderPendingPayments` entries whose `proposerIndex` is the slashed validator, and leaves every other proposer's entry untouched. New at v1.7.0-beta.4, where the voiding moved here from `processProposerSlashing` and widened to both payment epochs and to the attester-slashing path | proposed |  |
| `processAttestation` | `Gloas/Operations.lean:336-420` | Committee-index safety together with builder-payment weight accounting: a validator's effective balance adds to the slot's payment weight at most once, and only when it set a new flag and held no flag before the attestation (the `had_no_participation` gate, new at v1.7.0-beta.4) | proposed |  |
| `processBuilderPendingPayments` | `Gloas/EpochProcessing.lean:303-322` | Whole-transition equation over a plain `BeaconState`: the run returns `preState` with only `builderPendingWithdrawals` (the qualifying withdrawals, folded through `ProgressiveList.push` in slot order; every one is appended) and `builderPendingPayments` (the window shifted down by `SLOTS_PER_EPOCH` and padded with empties) written. This does not establish protocol-wide exactly-once settlement | proved | #25, `Proofs/Gloas/BuilderPendingPayments.lean` |
| `processPtcWindow` | `Gloas/EpochProcessing.lean:345-355` | Each newly populated `ptcWindow` entry equals `computePtc` evaluated for its corresponding slot | proposed |  |
| `applyDepositForBuilder` | `Gloas/Operations.lean:145-153` | A deposit with an invalid signature is neither applied to a builder's balance nor requeued | proposed |  |
| `processBuilderDepositRequest` | `Gloas/Operations.lean:243-259` | A new builder is onboarded only when its deposit signature is valid | proposed |  |
| `getIndexedPayloadAttestation` | `Gloas/Operations.lean:463-469` | Preserves `pa.data` and `pa.signature`, and produces the sorted multiset of PTC seats selected by `pa.aggregationBits`. The proof requires `Array.qsort` sortedness and permutation lemmas not currently available in core/Std | proposed |  |
| `isValidIndexedPayloadAttestation` | `Gloas/Operations.lean:474-485` | Returns true exactly when the attesting indices are non-empty, adjacent-nondecreasing (duplicates permitted), all within the validator registry, and the configured `[CryptoBackend]` accepts the exact aggregate-verification call | proved | #38, `Proofs/Gloas/IsValidIndexedPayloadAttestation.lean` |
| `processPayloadAttestation` | `Gloas/Operations.lean:490-503` | Running `processPayloadAttestation` does not modify `State`: it only reads the input state and evaluates three assertions. A concrete run-level theorem should show that both success and rejection preserve the state component | proposed |  |
| `processExecutionPayloadBid` | `Gloas/Operations.lean:571-607` | The self-build and builder-bid paths it chooses between are mutually exclusive and jointly exhaustive | proposed |  |
| `applyParentExecutionPayload` | `Gloas/Operations.lean:618-647` | Exactly one of settle-current, settle-previous, or evict fires, so a payment is never settled twice | proposed |  |

### Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates: never decreasing, never shrinking, never losing a previously-added element.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getWeight` | `Gloas/ForkChoice.lean:426-438` | Weight only grows as more attestations accumulate for a node | proposed |  |
| `onAttesterSlashing` | `Gloas/ForkChoice.lean:1026-1036` | The set of equivocating indices only grows, never shrinks | proposed |  |
| `updateCheckpoints` | `Gloas/ForkChoice.lean:588-590` | Each justified/finalized checkpoint either remains unchanged or advances to its candidate, so its epoch never decreases, and no other Store field moves | proved | #30, `Proofs/Gloas/UpdateCheckpoints.lean` |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processSlot` | `Gloas/Transition.lean:32-52` | After `processSlot`, the `executionPayloadAvailability` bit at index `(slot + 1) mod SLOTS_PER_HISTORICAL_ROOT` reads `false`, matching the documented invariant that a payload starts unavailable | proposed |  |
| `processOperations` | `Gloas/Transition.lean:88-102` | public declarations live in `EthCLSpecs.Proofs.Gloas`. Non-empty in-block deposits fail immediately with `StateTransitionError.assert`, and a reject at this monad carries no state; success on the uncached box of a plain value is equivalent to empty deposits plus the six operation-family loops succeeding in order over five plain intermediate values, one `runPure` fact per loop. The attestation loop passes the parent block's slot (`parent_slot`, new at v1.7.0-beta.4) to each `processAttestation`. `KeepsUncached` is the fact behind the split: every handler keeps the flavour, so `runPure_bind_of_keepsUncached` names each fold's post-state as a plain value. No per-operation correctness or rollback guarantee for later failures is claimed | proved | #57, `Proofs/Gloas/ProcessOperations.lean` |
| `processDepositRequest` | `Fulu/Operations.lean:281` | The run appends one `PendingDeposit` stamped with the current slot to `pendingDeposits` and writes no other field, so `depositRequestsStartIndex` keeps its value. Gloas and Heze inherit it | proved | `Proofs/Gloas/ProcessDepositRequest.lean` |
| `stateTransition` | `Gloas/Transition.lean:119-129` | Top-level state-transition correctness; composes `processSlots`, `processBlock`, and the root check into the canonical transition | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `onBlock` | `Gloas/ForkChoice.lean:775-826` | Accepts a block only if a full parent implies a verified payload, and the block's ancestry agrees with the currently finalized checkpoint | proposed |  |
| `validateOnAttestation` | `Gloas/ForkChoice.lean:952-985` | Validates that the attestation's index is 0 or 1, that a same-slot attestation has index 0, and that a full-vote attestation's payload is verified | proposed |  |
| `getForkchoiceStore` | `Gloas/ForkChoice.lean:1051-1077` | Every root-keyed map in a freshly built store agrees on the anchor entry | proposed |  |
| `isAncestor` | `Gloas/ForkChoice.lean:196-201` | Agrees with the ancestor relation that `getAncestor` computes iteratively | proposed |  |
| `verifyExecutionPayloadEnvelope` | `Gloas/ForkChoice.lean:869-906` | Acceptance requires every validation check performed by `verifyExecutionPayloadEnvelope` to succeed | proposed |  |

### Upgrade-boundary properties

Functions whose entire purpose is the Fulu-to-Gloas upgrade itself: preserving state across the boundary or seeding Gloas-only state from it. The fork comparison here is not incidental, it's what the function does.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `upgradeToGloas` | `Gloas/Upgrade.lean:83-149` | Preserves inherited state while correctly initializing the new ePBS state | proposed |  |
| `computePtcFromFulu` | removed | Out of scope: removed at v1.7.0-beta.4. `upgrade_to_gloas` now builds the window over the Gloas post-state with Gloas's own `compute_ptc`, so no Fulu-side twin is left to agree with it | out of scope |  |
| `initializePtcWindow` | `Gloas/Operations.lean:198-210` | Each entry is an `Except` carrying its own two faults: the entry's checked add `current_epoch + e` rejects with the `.arithmetic` fault exactly at `current_epoch = UINT64_MAX`, and the `compute_ptc` read rejects a slot with no committee members; `completeUpgradeToGloas` maps the entries in index order, so the first rejecting slot surfaces. `initializePtcWindow_eq` states the whole vector equation and carries the `@[characterizes]` tag; `initializePtcWindow_getElem` joins the two regions at the element level. A `forkdef` over the Gloas state since v1.7.0-beta.4, so it is a spec function in the coverage report's denominator; alpha.12 kept it a plain `def` over the Fulu pre-state. The window's slots are exact below the same `2 ^ 59` epoch bound the `computeEpochAtSlot` row records, because the slots come from `computeStartSlotAtEpoch`'s bare multiply; at the bound the multiply wraps where the spec raises | proved | #26, `Proofs/Gloas/InitializePtcWindow.lean` |

### Candidates needing a sharper statement

Functions where the useful theorem hasn't been identified yet, either because the obvious candidate property doesn't hold up, or because none has been proposed. Once identified, the candidate belongs in one of the sections above.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computePtc` | `Gloas/EpochProcessing.lean:330-338` | No standalone theorem has been identified yet. `initializePtcWindow_eq` states the seeded window in terms of it and says nothing about `computePtc` itself. The former candidate, agreement with `computePtcFromFulu`, went with that function at v1.7.0-beta.4 | proposed |  |


---

## Fulu

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Fulu function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeEpochAtSlot` | `Fulu/Time.lean:33` | `computeEpochAtSlot (computeStartSlotAtEpoch e) = e`, for `e < 2^59`. The raw `UInt64` multiply wraps above `2^59`, so the identity needs that bound | proposed |  |
| `computeStartSlotAtEpoch` | `Fulu/Time.lean:36` | The same identity, seen from this side. The round trip is the row above | proposed |  |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `reserveChurn` | `Fulu/RegistryUpdates.lean:69-74` | Arithmetic never underflows | proposed |  |
| `modBalance` | `Fulu/Balances.lean:29` | On the pure box, the write through the infallible `[i]!` index is one plain record update: `modBalance (pureState state) i f = pureState { state with balances := state.balances.set! i.toNat (f state.balances[i.toNat]!) }`. This is the whole contract; the two mutators below build on it | proved | follow-up to #80, `Proofs/Fulu/Balances.lean` |
| `increaseBalance` | `Fulu/Balances.lean:43` | The run rejects an index past the end of `balances` with `.outOfBounds`, and an addition that leaves the `uint64` range with `.arithmetic`. In range and below that bound it returns the input value with exactly that one balance written, and that balance is the exact natural-number sum | proved | #80, `Proofs/Fulu/Balances.lean` |
| `decreaseBalance` | `Fulu/Balances.lean:54` | The run rejects an index past the end of `balances` with `.outOfBounds`. In range it returns the input value with exactly `saturatingSub balance delta` written, the spec's `saturating_sub` (v1.7.0-beta.4); that value reads back as the truncating `Nat` difference, so the `uint64` subtraction never wraps | proved | #80, `Proofs/Fulu/Balances.lean` |
| `processDeposit` | `Fulu/Operations.lean:225` | Neither the incremented deposit index nor the running total balance exceeds `2^64`. Dafny stated both bounds and assumed them through `{:axiom}` lemmas, so Dafny's statements are reusable as a template. Its proofs are not. A sharper bound is open as well. The branch check needs `eth1DepositIndex < 2^32`, which follows from `eth1DepositIndex <= eth1Data.depositCount` together with a bound on `depositCount`. The consensus spec does not bound `depositCount`, since that count arrives from the execution layer. Any statement here is therefore conditional on the deposit contract's depth-32 capacity | proposed |  |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:179` | The registry never exceeds `VALIDATOR_REGISTRY_LIMIT` | proposed |  |
| `getBeaconCommittee` | `Fulu/Committees.lean:83` | An active-validator count in `[32, 2^22]` implies every committee size is in `(0, MAX_VALIDATORS_PER_COMMITTEE]`. Dafny proves the same bound in `ActiveValidatorBounds` | proposed |  |
| `computeBalanceWeightedSelection` | `Fulu/Committees.lean:120` | An `.ok` result holds exactly `size` indices, and the run rejects with `.arithmetic` at the `2**64` counter bound. `cbwsAux` is well-founded, so `rfl` and `decide` do not unfold it, and the proof goes through `cbwsAux.induct` and its equation lemmas | proposed |  |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeShuffledPermutation` | `Fulu/Committees.lean:31` | A bijection on `[0, indexCount)`. No prior art: Dafny stubbed shuffling to the identity, and Runtime Verification did not prove it either | proposed |  |
| `getBeaconCommittee` | `Fulu/Committees.lean:82` | The committees for a slot partition the active set: their union is the active validator set and they are pairwise disjoint. This follows from the shuffle bijection. The committee-size bound is the separate row under Bounds and termination properties | proposed |  |
| `processDeposit` | `Fulu/Operations.lean:225` | `validators.size = balances.size` holds at the append site, and then holds across the transition. The two overflow bounds are the separate row under Bounds and termination properties | proposed |  |
| `isSlashableAttestationData` | `Fulu/Operations.lean:38` | Agrees with the spec's slashability condition, a double vote or a surround vote, given the `strictlySorted` well-formedness the caller establishes | proposed |  |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:179` | One third of a joint claim with `initiateValidatorExit` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `initiateValidatorExit` | `Fulu/RegistryUpdates.lean:114` | One third of a joint claim with `processRegistryUpdates` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
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
| `getAncestor` | `Fulu/ForkChoice.lean:134` | One third of a joint claim with `getHead` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `getHead` | `Fulu/ForkChoice.lean:296` | One third of a joint claim with `getAncestor` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `onBlock` | `Fulu/ForkChoice.lean:628` | One third of a joint claim with `getAncestor` and `getHead`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |


---

## Heze

Heze is a twelve-declaration diff over Gloas. A proof about a Gloas declaration
remains a separate claim about Heze's re-elaboration of that declaration.
This matters here because Heze keeps Gloas's ePBS fork-choice machinery while
adding FOCIL state and decision logic that the inherited machinery can consume.
The goal of this workstream is therefore not only to characterize individual
Heze functions, but to prove that the ePBS and FOCIL pieces compose correctly
across state writes, later reads, inherited calls, and fork-choice decisions.

The recurring proof shape is:

`writer → state fact / invariant → reader → fork-choice consequence`

The steps are kept as separate, reusable theorems rather than collapsed into
one end-to-end proof. A writer first establishes a precise fact about the state
it returns. Invariants then describe which of those facts must continue to hold
across later committed transitions. Reader theorems consume those facts without
having to reopen the writer's implementation, and fork-choice theorems turn the
reader result into an observable protocol consequence. This separation also
keeps the dependencies minimal: a downstream theorem depends on the property it
actually needs, while an earlier handler is only one way of establishing that
property.

The work is reasoned about in three complementary layers:

| Conceptual layer | Purpose | In this workstream |
| --- | --- | --- |
| **Cross-fork refinement** | State precisely what Heze preserves from Gloas ePBS and what FOCIL deliberately changes. The comparison relates only the ePBS-observable projections of a Heze and Gloas store rather than requiring equality of the fork-specific store types. | Under `SharesEpbsView`, the inherited ePBS reads agree. A recorded FOCIL `true` continues through behavior equivalent to the Gloas ePBS tail; `false` terminates the Heze extension decision early; a missing FOCIL record is a Heze-specific error case. |
| **State safety and invariants** | Connect state written by one component to assumptions made later by another, and distinguish a local postcondition from a property of all relevant committed states. | A successful payload reveal records both the payload and its FOCIL satisfaction result at the written root. The later `VerifiedImpliesRecorded` invariant strengthens this into the one-way property needed by the reader: a verified payload has a recorded satisfaction result. Initialization and frame/preservation lemmas are what make that a global store property. |
| **Protocol consequences** | Compose the lower-level facts into the fork-choice behavior that gives the proof protocol-level meaning. | A recorded `false` makes `shouldExtendPayload` return `false`; for the previous-slot FULL candidate this gives tiebreaker `0`, while EMPTY has tiebreaker `1`, so one `betterOf` comparison selects EMPTY. This does not yet claim that the full `getHead` walk reaches that node. |

These are conceptual reasoning layers, not new proof-ledger categories, so the
rows below remain organized under the ledger's existing taxonomy. They are also
not a single strict pipeline. The cross-fork refinement can be proved
independently of the global store invariant; the invariant makes the production
read path safe, while the protocol-consequence proofs consume whichever local or
global hypotheses their statements actually require.

A Heze row is added for an inherited declaration only when the FOCIL diff gives
that Heze constant a distinct proof obligation.

### First composition story

The first proof story follows one FOCIL result from the handler that records it
to the fork-choice decision that consumes it:

`onExecutionPayloadEnvelope`
→ payload + FOCIL satisfaction result
→ `isPayloadInclusionListSatisfied`
→ `shouldExtendPayload`
→ `getPayloadStatusTiebreaker`
→ one `betterOf` EMPTY/FULL comparison

**1. Writer — establish the local store facts.**

A successful `onExecutionPayloadEnvelope` commits two facts at the same root:
the execution payload is present in `payloads`, and
`payloadInclusionListSatisfaction` contains the FOCIL result computed for that
payload. The first proofs establish those facts locally on the handler's returned
store using the same-key `FcMap` laws.

**2. Reader — consume the recorded result.**

`shouldExtendPayload` first checks that the payload is verified, then reads the
FOCIL result through `isPayloadInclusionListSatisfied`.

- A recorded `false` makes the extension decision `false`.
- A recorded `true` continues into the inherited ePBS tail.
- A missing record can still occur on an arbitrary hand-built store.

The separate `VerifiedImpliesRecorded` invariant is what will later rule out
that missing-record case for verified roots along the committed store path.
Keeping that invariant separate from the local writer theorem avoids requiring
global reachability or frame proofs before the local composition can be used.

**3. Fork-choice consequence — expose the protocol effect.**

In this previous-slot EMPTY/FULL comparison, weight and root do not distinguish
the candidates, so the payload-status tiebreaker becomes the deciding key.

For a previous-slot FULL candidate, `shouldExtendPayload = false` gives FULL
tiebreaker `0`, while EMPTY has tiebreaker `1`. With equal weight and root, one
`betterOf` step therefore selects EMPTY.

The reusable tiebreaker theorem depends on the `false` extension result, not on
`onExecutionPayloadEnvelope` itself. The envelope theorem is one way to establish
that premise from a successful reveal. This keeps the writer and fork-choice
facts independently reusable.

**4. Cross-fork interpretation — relate the result back to Gloas.**

In parallel, the cross-fork refinement track explains what the same result means
relative to Gloas. Under `SharesEpbsView`, a recorded FOCIL `true` continues
through the same ePBS decision observed in Gloas, while a recorded `false` adds
the Heze restriction.

This is where the local writer/read facts become a compositional statement about
how Heze adds FOCIL to inherited ePBS behavior.

This story stops at one EMPTY/FULL comparison. It does not claim that the full
`getHead` walk reaches that node.

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getForkchoiceStore` | `Heze/ForkChoice.lean:480-510` | One half of a joint claim with `onExecutionPayloadEnvelope`. This is the initialization, the base case, of `VerifiedImpliesRecorded`. The `Prop` holds vacuously because `payloads` is empty, so `isPayloadVerified` is false at every root. The satisfaction map is empty with it. Stating the empty lookups needs laws `LawfulFcMap` does not yet give | proposed |  |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:439-461` | The other half of the joint claim with `getForkchoiceStore`. `VerifiedImpliesRecorded` says `isPayloadVerified store root = true` implies `FcMap.lookup store.payloadInclusionListSatisfaction root` is `some`. A successful `onExecutionPayloadEnvelope_run_eq_of_successful_checks` establishes it at the written root, because that equation inserts `payloads` and the satisfaction key there. Preservation at other roots waits on the missing other-key insert law. A rejected run has no post-state on `ForkChoiceStoreRun`. The store `recordPayloadInclusionListSatisfaction` returns inserts the bit and leaves `payloads` unchanged, and is outside this claim. A source audit identifies this function and `getForkchoiceStore` as the committed writers of the two maps. Global preservation still requires frame lemmas for the remaining committed handlers | proposed |  |
| `processInclusionList` | `Heze/ForkChoice.lean:140-156` | A list is stored only on the no-entry branch, and that branch inserts one `InclusionListEntry`, the signed list and its timeliness together, under `(slot, dependent_root)` and the sender. The stored-entry branch never changes `inclusionLists`, and it changes `equivocators` only by adding the sender, once, when the new list differs. At v1.7.0-beta.4 the timeliness lives in the entry, so the alpha.12 claim that every stored list root is a key of a separate timeliness map has no subject | proposed |  |
| `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean:316-324` | Under `VerifiedImpliesRecorded`, a verified root cannot take the missing-record assert. The helper can still assert on an unverified root with no record. Establishing `VerifiedImpliesRecorded` on committed stores is the separate joint invariant claim—requiring initialization, envelope preservation, and frame preservation—not this reader row | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `shouldExtendPayload` | `Heze/ForkChoice.lean:331-353` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`: block lookup, `getCurrentSlot`, the slot increment and assertion, `isPayloadVerified`, `isPayloadInclusionListSatisfied`, then the inherited Gloas tail. Named corollaries cover the prefix rejects, the FOCIL gate (unverified, missing record, recorded `false`, recorded `true`), the vote membership asserts, and the inherited Gloas accept and reject arms. Successful binds keep the intermediate runner states. A reject returns the error alone. The local envelope postconditions and the recorded-false composition are the first `onExecutionPayloadEnvelope` postcondition row. The branch where the recorded bit is `true` is the second. `VerifiedImpliesRecorded` is the joint claim with `getForkchoiceStore`. Transport to `Gloas.shouldExtendPayload` is the later row for this function | proved | `Proofs/Heze/ShouldExtendPayload.lean` |
| `getInclusionListCommittee` | `Heze/ForkChoice.lean:232-240` | Complete `.run` equation at `ForkChoiceStoreRun σ`: empty concatenated indices throw the arithmetic error; a nonempty array returns `cyclicSample` of those indices and leaves the runner state unchanged | proved | follow-up to #82, `Proofs/Heze/GetInclusionListTransactions.lean` |
| `getInclusionListTransactions` | `Heze/ForkChoice.lean:191-195` | Pure at v1.7.0-beta.4. `mem_getInclusionListTransactions_iff`: a transaction is in the result exactly when the list of some item for `(slot, dependent_root)` carries it, where the item's sender is not an equivocator for the key and, at `onlyTimely = true`, its entry is timely. `getInclusionListTransactions_nodup`: the result holds no duplicate. The items are `inclusionListItems`, the map fold the spec's loop iterates. `FcMap` has no fold law, so relating the items to `FcMap.lookup` stays open at an arbitrary `map` | proved | `Proofs/Heze/GetInclusionListTransactions.lean` |
| `collectInclusionListTransactions` | removed | Out of scope: removed at v1.7.0-beta.4. Each stored entry carries its own timeliness, so no lookup can miss and `getInclusionListTransactions` filters and deduplicates in one pure step. This row's claim (equivocator exclusion, the timeliness filter, no duplicates) is now the proved `getInclusionListTransactions` row | out of scope |  |
| `recordPayloadInclusionListSatisfaction` | `Heze/ForkChoice.lean:423-431` | Complete `.run` equation at `ForkChoiceStoreRun (Store map)`: a block missing from `store.blocks` is `missingKey root`; a slot-zero block is the checked-sub arithmetic error; a dependent-root walk error propagates; a successful walk records `isInclusionListSatisfied payload ilTxs` at `root`, for the timely transactions `ilTxs` stored under `(block.slot - 1, dependent_root)`, and keeps the walk's runner state. At v1.7.0-beta.4 the function takes no state and collects without throwing | proved | follow-up to #82, `Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`, `Proofs/Heze/GetInclusionListTransactions.lean` (successful-path origin #82) |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:439-461` | `onExecutionPayloadEnvelope_run` is the complete compositional `.run` equation at `ForkChoiceStoreRun (Store map)`: missing `blockStates` is `.assert "envelope.beacon_block_root in store.block_states"`; failed data availability is `.assert "(isDataAvailable envelope.beaconBlockRoot)"`; verification and recorder errors propagate unchanged; success is the handler's final `set` of `blockStates` and `payloads` on the recorder's explicitly returned store, discarding the recorder-produced runner state. `onExecutionPayloadEnvelope_run_of_pureState` restates the whole equation over a plain block state `state`, stored as `pureState state`, and `onExecutionPayloadEnvelope_run_eq_of_successful_checks` restates the successful branch as the original store updated by three same-root `FcMap.insert` expressions. `verifyExecutionPayloadEnvelope_pureState` proves that a successful verification on `pureState state` returns `pureState state`, so the corollaries ask only that the verification succeeds. Same-key `FcMap` insertion is available in `EthCLLib.Proofs.LawfulFcMap`, with `treeMap` and `hashMap` instances at `Root` | proved | #92, `Proofs/Heze/OnExecutionPayloadEnvelope.lean` (successful-path origin #84) |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:439-461` | On the store `onExecutionPayloadEnvelope_run_eq_of_successful_checks` returns, under `[LawfulFcMap map Root]`: `FcMap.lookup` of `payloadInclusionListSatisfaction` at `signedEnv.message.beaconBlockRoot` is `some (isInclusionListSatisfied signedEnv.message.payload ilTxs)`, where `ilTxs` is `getInclusionListTransactions` at the block's `(slot - 1, dependent_root)` key, `FcMap.contains` of `payloads` at that root is `true`, and `isPayloadVerified` is `true`. The bit is that engine result. When the bit is `false` and the slot-prefix hypotheses of `shouldExtendPayload_run_eq_false_of_recorded_unsatisfied` hold, `shouldExtendPayload` returns `false`. Cite `FcMap.lookup_insert_self` and `FcMap.contains_insert_self`. Other roots, `VerifiedImpliesRecorded` for the whole store, and the `true` bit are separate rows | proposed |  |
| `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean:316` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`: a missing satisfaction key is the membership assert; a recorded value is returned only when the payload is verified, otherwise `false`. Corollaries name the missing-record reject, an unverified recorded value, a recorded `false`, and a recorded `true` with a verified payload. Success leaves `runnerStore` unchanged. Under `VerifiedImpliesRecorded`, the missing-record arm on a verified root is the later row for this function | proved | `Proofs/Heze/IsPayloadInclusionListSatisfied.lean` |
| `processInclusionList` | `Heze/ForkChoice.lean:140` | At most one stored list per validator per `(slot, dependent_root)` key, asserted in its docstring and not proved. A second list from the same validator leaves the stored entry untouched; when it differs, the sender joins the key's equivocators. Every later list from that validator for the key takes the stored-entry branch and is ignored | proposed |  |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:439-461` | On that same post-state, when `isInclusionListSatisfied signedEnv.message.payload ilTxs = true`, `isPayloadInclusionListSatisfied` returns `true` and `shouldExtendPayload` returns the inherited tail. The tail hypotheses stay in the statement: both PTC vote arrays, proposer boost, and parent fullness. The statement takes the stored bit. It does not assume the optimistic `ExecutionEngine` instance | proposed |  |
| `shouldExtendPayload` | `Heze/ForkChoice.lean:331-353` | Under `SharesEpbsView`, a shared prefix failure, an unverified root, and a verified root with a recorded `true` satisfaction bit give the same extension result as `Gloas.shouldExtendPayload`. Recorded `false` returns `false`. A missing satisfaction key asserts on the Heze side. `getPayloadStatusTiebreaker` is a separate row | proposed |  |
| `getPayloadStatusTiebreaker` | `Heze/ForkChoice.lean:355` | For a previous-slot EMPTY/FULL pair at the same root, if `shouldExtendPayload = false`, EMPTY's tiebreaker is `1` and FULL's is `0`. Since `getWeight` is `0` for both in that previous-slot decision and the roots are equal, a `betterOf` corollary selects EMPTY. The reusable theorem depends on the `false` extension result; a successful envelope is one way to establish that premise | proposed |  |

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
