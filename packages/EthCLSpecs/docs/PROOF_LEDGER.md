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

Seven claims rest on another row:

- The Heze theorem `unsatisfiedPayload_cost` rests on the Heze `shouldExtendPayload`,
  `getPayloadStatusTiebreaker`, `getParentPayloadStatus`,
  `processParentExecutionPayload`, and `processBuilderPendingPayments` rows. Its form
  over the chain, `unsatisfiedPayload_cost_of_run`, also rests on the
  `processBlockHeader` row. It takes the chain as `BlockStep` and `ChainRun`
  hypotheses. `stateTransition_chainRun` from the `stateTransition` row gives these
  hypotheses for a run of `stateTransition`, but the theorem does not use it.
- The Heze `getPayloadStatusTiebreaker` row rests on the Heze `shouldExtendPayload`
  row.
- The `onExecutionPayloadEnvelope` row rests on the
  `recordPayloadInclusionListSatisfaction` row.
- The Heze theorem `inclusionList_dichotomy` rests on the `processInclusionList`,
  `collectInclusionListTransactions`, and `onExecutionPayloadEnvelope` rows. Its
  corollary `inclusionList_missing_tx_cost` also rests on `unsatisfiedPayload_cost`.
- The committee partition rests on the shuffle bijection.
- Plausible liveness rests on accountable safety.
- The postconditions of the Heze FOCIL handlers rest on the laws of `FcMap`.
  [`EthCLLib/Proofs/LawfulFcMap.lean`](../../EthCLLib/EthCLLib/Proofs/LawfulFcMap.lean)
  states six of them: lookup after an insert at the same key and at a different
  key, lookup in the empty map, `contains` against lookup, the fold of pushes,
  and `keys`. `instLawfulFcMapTreeMap` needs `[Std.TransOrd K]` and
  `[Std.LawfulEqOrd K]`. `instTransOrdVectorUInt8` and
  `instLawfulEqOrdVectorUInt8` supply the order laws for `Root`
  (`Vector UInt8 32`) along the existing `instOrdVectorUInt8` comparator, so
  the instance synthesizes at those keys.
  `onExecutionPayloadEnvelope_run_pairing` is the first handler postcondition
  built on them.

---

## Gloas

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Gloas function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:484` | Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit. `toBuilderIndex` always clears that bit, so the round trip holds only under that precondition | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |
| `toBuilderIndex` | `Gloas/Operations.lean:55` | Clears the `BUILDER_INDEX_FLAG` bit, so it inverts `convertBuilderIndexToValidatorIndex` on any index that already carries the flag; the companion direction is the row above | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeExitEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:96-109` | The Gloas override reads `get_exit_churn_limit`. When the activation-exit epoch, the churn limit and the reservation succeed, the run succeeds, and its `balance_to_consume - exit_balance` subtraction cannot fault. Each activation-epoch, churn-limit or reservation fault passes through unchanged | proved | `Proofs/Gloas/Churn.lean` |
| `reserveChurn` | `Gloas/EpochProcessing.lean:78` | The Fulu claims. The body reads no preset or config value, so each theorem takes the Fulu proof term | proved | `Proofs/Gloas/Churn.lean` |
| `computeConsolidationEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:123` | The Fulu claims, at the Gloas consolidation limit. That limit has no `MIN` floor and can be zero, and `reserveChurn` rejects a zero limit | proved | `Proofs/Gloas/Churn.lean` |
| `getExpectedWithdrawals` | `Gloas/Withdrawals.lean:172-180` | The withdrawals returned by its four phases combined never exceed `MAX_WITHDRAWALS_PER_PAYLOAD` | proposed |  |
| `initiateBuilderExit` | `Gloas/Operations.lean:105-108` | `initiateBuilderExit_run_eq` is the whole-transition equation; its exact in-range/out-of-range effect on the builder registry is characterized; no-wrap is conditional for an arbitrary `Config` and proved unconditionally for both shipped Gloas preset/config pairs | proved | #39, `Proofs/Gloas/InitiateBuilderExit.lean` |
| `processBuilderExitRequest` | `Gloas/Operations.lean:221-232` | On its successful builder-exit branch, the index supplied to `initiateBuilderExit` is in range. Under either shipped Gloas preset/config pair, the selected builder receives the intended non-wrapping future `withdrawableEpoch`. All non-matching or ineligible branches leave the builder registry unchanged | proposed |  |
| `getPtc` | `Gloas/Operations.lean:413-430` | Its computed offset into `ptcWindow` stays in range under the two guarded call patterns: `data.slot + 1 == state.slot` and the fork-choice replay callers' `slot == curSlot`. Landed: both bounds, stated over `getPtcElseOffset`, a restatement of the else-branch arithmetic. Open: a statement about `getPtc` itself, which is what would carry a `characterizes` tag and move the function past the touched tier | in progress | `4b4b78a`, `Proofs/Gloas/GetPtc.lean` |
| `getPendingBalanceToWithdrawForBuilder` | `Gloas/Operations.lean:71-82` | When the `Nat` sums of the matching pending-withdrawal and pending-payment amounts add to less than `2^64`, the result is that exact total. At `2^64` or more it rejects with `.arithmetic`, the point where the pyspec's `uint64` sums raise `ValueError` | proved | `Proofs/Gloas/PendingBalanceForBuilder.lean` |
| `canBuilderCoverBid` | `Gloas/Operations.lean:492-498` | With a successful pending balance and a `MIN_DEPOSIT_AMOUNT` addition below `2^64`, its `Bool` result is characterized exactly against the computed `minBalance`. A pending-balance fault passes through, and the addition rejects with `.arithmetic` at `2^64`. Proving that queuing an accepted bid preserves `MIN_DEPOSIT_AMOUNT` + pending obligations ≤ builder balance is the caller-level follow-up, and needs ring-cell freshness hypotheses | proved | #36, `Proofs/Gloas/CanBuilderCoverBid.lean` |
| `applyWithdrawals` | `Gloas/Withdrawals.lean:185-195` | A builder-flagged withdrawal decreases the builder's balance by at most its own balance, so the balance never goes negative | proposed |  |
| `getAncestor` | `Gloas/ForkChoice.lean:177-184` | The fuel supplied to its `fuelLoop` DAG walk is sufficient for the walk to terminate before running out | proposed |  |
| `getHead` | `Gloas/ForkChoice.lean:578-613` | The fuel `2 * blocks.length + 2` supplied to its LMD-GHOST walk is sufficient for the walk to reach a decided head before running out | proposed |  |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processProposerSlashing` | `Gloas/Operations.lean:239-269` | Payment-voiding must never touch another proposer's `BuilderPendingPayment` | proposed |  |
| `processAttestation` | `Gloas/Operations.lean:322-393` | Committee-index safety together with builder-payment weight accounting | proposed |  |
| `processBuilderPendingPayments` | `Gloas/EpochProcessing.lean:264-287` | The total-active-balance read for the quorum faults first, on a `uint64` overflow of the sum, and that fault passes through. The quorum product `per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR` faults next, with `.arithmetic`, when it reaches `2 ^ 64` (`processBuilderPendingPayments_run_quorum_error`). Given the total and a quorum product that fits (`QuorumFits`), both outcomes over a plain `BeaconState`. When the qualifying previous-epoch withdrawals fit under the list limit, the run returns `preState` with only two fields written. `builderPendingWithdrawals` holds the old list followed by the qualifying withdrawals in slot order. `builderPendingPayments` holds the window shifted down by `SLOTS_PER_EPOCH` and padded with empties. When the withdrawals do not fit, the run raises `.listFull`. This does not establish protocol-wide exactly-once settlement | proved | #25, `Proofs/Gloas/BuilderPendingPayments.lean` |
| `processPtcWindow` | `Gloas/EpochProcessing.lean:307-327` | Each newly populated `ptcWindow` entry equals `computePtc` evaluated for its corresponding slot | proposed |  |
| `applyDepositForBuilder` | `Gloas/Operations.lean:131-143` | A deposit with an invalid signature is neither applied to a builder's balance nor requeued | proposed |  |
| `processBuilderDepositRequest` | `Gloas/Operations.lean:191-210` | A new builder is onboarded only when its deposit signature is valid | proposed |  |
| `getIndexedPayloadAttestation` | `Gloas/Operations.lean:435-441` | Preserves `pa.data` and `pa.signature`, and produces the sorted multiset of PTC seats selected by `pa.aggregationBits`. The proof requires `Array.qsort` sortedness and permutation lemmas not currently available in core/Std | proposed |  |
| `isValidIndexedPayloadAttestation` | `Gloas/Operations.lean:449-461` | Returns `.ok true` exactly when the attesting indices are non-empty, adjacent-nondecreasing (duplicates permitted), all within the validator registry, and the configured `[CryptoBackend]` accepts the exact aggregate-verification call. An index past the registry raises `.outOfBounds` | proved | #38, `Proofs/Gloas/IsValidIndexedPayloadAttestation.lean` |
| `processPayloadAttestation` | `Gloas/Operations.lean:466-479` | Running `processPayloadAttestation` does not modify `State`: it only reads the input state and evaluates three assertions. A concrete run-level theorem should show that both success and rejection preserve the state component | proposed |  |
| `processExecutionPayloadBid` | `Gloas/Operations.lean:527-562` | The self-build and builder-bid paths it chooses between are mutually exclusive and jointly exhaustive | proposed |  |
| `applyParentExecutionPayload` | `Gloas/Operations.lean:567-591` | Exactly one of settle-current, settle-previous, or evict fires, so a payment is never settled twice | proposed |  |
| `computeShuffledPermutation` | `Gloas/EpochProcessing.lean:134` | Inherited from Fulu. The same bijection on `[0, indexCount)` for the Gloas constant | proved | TBD-PR, `Proofs/Gloas/Shuffle.lean` |
| `computeCommittee` | `Gloas/EpochProcessing.lean:137` | Inherited from Fulu. The same slice partition for the Gloas constant | proved | TBD-PR, `Proofs/Gloas/Committees.lean` |
| `getBeaconCommittee` | `Gloas/EpochProcessing.lean:138` | Inherited from Fulu. The same per-epoch partition of the active set for the Gloas constant | proved | TBD-PR, `Proofs/Gloas/Committees.lean` |
| `isSlashableAttestationData` | `Gloas/Operations.lean:28` | Inherited from Fulu. The same double-vote-or-surround test for the Gloas constant, and the same root-collision reading of two different data with one target epoch | proved | `Proofs/Gloas/AttesterSlashing.lean` |

### Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates: never decreasing, never shrinking, never losing a previously-added element.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getWeight` | `Gloas/ForkChoice.lean:466-478` | Weight only grows as more attestations accumulate for a node | proposed |  |
| `onAttesterSlashing` | `Gloas/ForkChoice.lean:1086-1096` | The set of equivocating indices only grows | proposed |  |
| `updateCheckpoints` | `Gloas/ForkChoice.lean:618-620` | Each justified/finalized checkpoint either remains unchanged or advances to its candidate, so its epoch never decreases, and no other Store field moves | proved | #30, `Proofs/Gloas/UpdateCheckpoints.lean` |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processSlot` | `Gloas/Transition.lean:32-52` | After `processSlot`, the `executionPayloadAvailability` bit at index `(slot + 1) mod SLOTS_PER_HISTORICAL_ROOT` reads `false`, matching the documented invariant that a payload starts unavailable | proposed |  |
| `processOperations` | `Gloas/Transition.lean:87-94` | public declarations live in `EthCLSpecs.Proofs.Gloas`. Non-empty in-block deposits fail immediately with `StateTransitionError.assert`, and a reject at this monad carries no state; success on the uncached box of a plain value is equivalent to empty deposits plus the six operation-family loops succeeding in order over five plain intermediate values, one `runPure` fact per loop. `KeepsUncached` is the fact behind the split: every handler keeps the flavour, so `runPure_bind_of_keepsUncached` names each fold's post-state as a plain value. No per-operation correctness or rollback guarantee for later failures is claimed | proved | #57, `Proofs/Gloas/ProcessOperations.lean` |
| `stateTransition` | `Gloas/Transition.lean:108-118` | Top-level state-transition correctness; composes `processSlots`, `processBlock`, and the root check into the canonical transition | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `onBlock` | `Gloas/ForkChoice.lean:811-860` | Accepts a block only if a full parent implies a verified payload, and the block's ancestry agrees with the currently finalized checkpoint | proposed |  |
| `validateOnAttestation` | `Gloas/ForkChoice.lean:1010-1045` | Validates that the attestation's index is 0 or 1, that a same-slot attestation has index 0, and that a full-vote attestation's payload is verified | proposed |  |
| `getForkchoiceStore` | `Gloas/ForkChoice.lean:1107-1139` | Every root-keyed map in a freshly built store agrees on the anchor entry | proposed |  |
| `isAncestor` | `Gloas/ForkChoice.lean:189-194` | Agrees with the ancestor relation that `getAncestor` computes iteratively | proposed |  |
| `verifyExecutionPayloadEnvelope` | `Gloas/ForkChoice.lean:925-960` | Acceptance requires every validation check performed by `verifyExecutionPayloadEnvelope` to succeed | proposed |  |

### Upgrade-boundary properties

Functions whose entire purpose is the Fulu-to-Gloas upgrade itself: preserving state across the boundary or seeding Gloas-only state from it. The fork comparison here is not incidental, it's what the function does.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `upgradeToGloas` | `Gloas/Upgrade.lean:111-168` | Preserves inherited state while correctly initializing the new ePBS state | proposed |  |
| `computePtcFromFulu` | `Gloas/Upgrade.lean:43-51` | Agrees with `Gloas.computePtc` once the state is upgraded | proposed |  |
| `initializePtcWindow` | `Gloas/Upgrade.lean:58-70` | The first `SLOTS_PER_EPOCH` entries are the empty committee. Every remaining entry equals `computePtcFromFulu` at the slot the definition computes. Both claims hold under a bound on the window's largest epoch. The function is a plain `def` in the fork body, not a `forkdef`. It is not a spec function, so the coverage report's denominator never holds it | proved | #26, `Proofs/Gloas/InitializePtcWindow.lean` |

### Candidates needing a sharper statement

Functions where the useful theorem hasn't been identified yet, either because the obvious candidate property doesn't hold up, or because none has been proposed. Once identified, the candidate belongs in one of the sections above.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computePtc` | `Gloas/EpochProcessing.lean:293-301` | No standalone theorem has been identified yet. The strongest current candidate is its agreement with `computePtcFromFulu` after state upgrade | proposed |  |


---

## Fulu

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Fulu function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeEpochAtSlot` | `Fulu/Time.lean:30` | `computeEpochAtSlot (computeStartSlotAtEpoch e) = e`, conditional on `e * SLOTS_PER_EPOCH < 2^64` at a symbolic preset. Closed unconditionally at both shipped presets, for `e < 2^61` at minimal and `e < 2^59` at mainnet | proved | `Proofs/Fulu/Time.lean` |
| `computeStartSlotAtEpoch` | `Fulu/Time.lean:42-44` | The same identity, seen from this side. The round trip is the row above | proved | `Proofs/Fulu/Time.lean` |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `reserveChurn` | `Fulu/RegistryUpdates.lean:86` | It rejects with `.arithmetic` on a zero limit, the pyspec's `ZeroDivisionError`. It rejects with `.arithmetic` when the epoch add, the multiply, or the consumed add reaches `2^64`. Below every bound it returns the exact epoch and consumed total. A successful reservation returns a consumed total at least as large as the balance | proved | `Proofs/Fulu/Churn.lean` |
| `computeExitEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:103` | When the activation-exit epoch, the churn limit and the reservation succeed, the run succeeds, and its `balance_to_consume - exit_balance` subtraction cannot fault. Each activation-epoch, churn-limit or reservation fault passes through unchanged | proved | `Proofs/Fulu/Churn.lean` |
| `computeConsolidationEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:120` | The same claims over the consolidation fields and the consolidation limit | proved | `Proofs/Fulu/Churn.lean` |
| `modBalance` | `Fulu/Balances.lean:29` | On the pure box, the write through the infallible `[i]!` index is one plain record update: `modBalance (pureState state) i f = pureState { state with balances := state.balances.set! i.toNat (f state.balances[i.toNat]!) }`. This is the whole contract; the two mutators below build on it | proved | follow-up to #80, `Proofs/Fulu/Balances.lean` |
| `increaseBalance` | `Fulu/Balances.lean:43` | The run rejects an index past the end of `balances` with `.outOfBounds`, and an addition that leaves the `uint64` range with `.arithmetic`. In range and below that bound it returns the input value with exactly that one balance written, and that balance is the exact natural-number sum | proved | #80, `Proofs/Fulu/Balances.lean` |
| `decreaseBalance` | `Fulu/Balances.lean:53` | The run rejects an index past the end of `balances` with `.outOfBounds`. In range it returns the input value with exactly the clamped difference written; the `Nat` difference truncates at zero, so the clamp matches the spec and the `uint64` subtraction never wraps | proved | #80, `Proofs/Fulu/Balances.lean` |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:242` | The registry never exceeds `VALIDATOR_REGISTRY_LIMIT` | proposed |  |
| `getBeaconCommittee` | `Fulu/Committees.lean:147` | An active-validator count in `[32, 2^22]` implies every committee size is in `(0, MAX_VALIDATORS_PER_COMMITTEE]`. Dafny proves the same bound in `ActiveValidatorBounds` | proposed |  |
| `computeStartSlotAtEpoch` | `Fulu/Time.lean:42-44` | The function multiplies an epoch back to a slot. It faults with `.arithmetic` above `2^64`. It never faults on an epoch derived from a slot. The claim is open where the caller supplies the epoch | proved | `Proofs/Fulu/Time.lean` |
| `computeStartSlotAtEpoch` | `Gloas/EpochProcessing.lean:34` | The Fulu claims, restated at Gloas's own constant. Each theorem takes the Fulu proof term through the `Downgrade` bridge | proved | `Proofs/Gloas/Time.lean` |
| `computeStartSlotAtEpoch` | `Heze/EpochProcessing.lean:24` | The same claims at Heze's constant. The bridge reaches one fork up, so the proof terms come from Gloas | proved | `Proofs/Heze/Time.lean` |
| `computeActivationExitEpoch` | `Fulu/Time.lean:54-57` | The function adds `1 + MAX_SEED_LOOKAHEAD` to an epoch. It faults with `.arithmetic` when the sum reaches `2^64`. Below that bound it returns the exact sum. It never faults on an epoch derived from a slot, under a preset bound that both shipped presets satisfy | proved | `Proofs/Fulu/Time.lean` |
| `computeActivationExitEpoch` | `Gloas/EpochProcessing.lean:47` | The Fulu claims, restated at Gloas's own constants through the `Downgrade` bridge | proved | `Proofs/Gloas/Time.lean` |
| `computeActivationExitEpoch` | `Heze/EpochProcessing.lean:35` | The same claims at Heze's constants. The proof terms come from Gloas | proved | `Proofs/Heze/Time.lean` |
| `reserveChurn` | `Heze/EpochProcessing.lean:23` | The Fulu claims at Heze. The proof terms come from Gloas | proved | `Proofs/Heze/Churn.lean` |
| `computeExitEpochAndUpdateChurn` | `Heze/EpochProcessing.lean:66` | The Gloas claims at Heze, proved again over the Heze `State` | proved | `Proofs/Heze/Churn.lean` |
| `computeConsolidationEpochAndUpdateChurn` | `Heze/EpochProcessing.lean:72` | The Gloas claims at Heze, proved again over the Heze `State` | proved | `Proofs/Heze/Churn.lean` |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeShuffledPermutation` | `Fulu/Committees.lean:55` | The body raises where the pyspec raises: at `indexCount = 0`, above `2^40`, and at round 256. A run succeeds exactly when the pyspec does not raise (`computeShuffledPermutation_eq_ok_iff`). It then returns a bijection on `[0, indexCount)`, stated as a `List.Perm` of `List.range` (`computeShuffledPermutation_perm`). The proof never reads the hash, so it holds for every hasher and cites no hash axiom. No prior art: Dafny stubbed shuffling to the identity, and Runtime Verification did not prove it either | proved | TBD-PR, `Proofs/Fulu/Shuffle.lean` |
| `getBeaconCommittee` | `Fulu/Committees.lean:147` | Over one epoch, every committee run succeeds and returns its slice of the shuffled active set (`getBeaconCommittee_ok`). The committees for every slot and committee index are a permutation of the active set (`getBeaconCommittee_partition`). No validator sits in two committees of the epoch (`getBeaconCommittee_nodup`). The slots are the spec's `compute_start_slot_at_epoch(e) + j`. The theorems do not establish a per-slot partition, since one slot's committees hold only that slot's share. The theorems assume three preset facts, which both shipped presets satisfy: `VALIDATOR_REGISTRY_LIMIT ≤ 2^40`, `SHUFFLE_ROUND_COUNT ≤ 256`, and `(MAX_COMMITTEES_PER_SLOT + 1) * SLOTS_PER_EPOCH ≤ 2^23`. They also assume that the epoch's last slot fits in `uint64`. The committee-size bound is the separate row under Bounds and termination properties | proved | TBD-PR, `Proofs/Fulu/Committees.lean` |
| `computeCommittee` | `Fulu/Committees.lean:123` | When the `uint64` products fit, `index < count`, and the shuffle's bounds hold, the run succeeds. Committee `index` of `count` is then the slice `[len * index / count, len * (index + 1) / count)` of `indices`, read through the shuffled permutation (`computeCommittee_ok`). For `0 < count`, committees `0 … count-1` laid end to end are a permutation of `indices` (`computeCommittee_partition`) | proved | TBD-PR, `Proofs/Fulu/Committees.lean` |
| `isSlashableAttestationData` | `Fulu/Operations.lean:38` | The test is true exactly for a double vote (different roots, one target epoch) or a surround vote (`isSlashableAttestationData_iff`). The statement needs no precondition on the index lists. Two different data with one target epoch are a double vote, or two different data share one root (`isSlashableAttestationData_of_ne`) | proved | `Proofs/Fulu/AttesterSlashing.lean` |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:242` | One third of a joint claim with `initiateValidatorExit` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `initiateValidatorExit` | `Fulu/RegistryUpdates.lean:144` | One third of a joint claim with `processRegistryUpdates` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `computeExitEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:103` | One third of a joint claim with `processRegistryUpdates` and `initiateValidatorExit`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |

### Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates: never decreasing, never shrinking, never losing a previously-added element.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeEpochAtSlot` | `Fulu/Time.lean:30` | The epoch never decreases as the slot grows. A `uint64` division by a positive constant, so the proof needs no preset bound | proved | `Proofs/Fulu/Time.lean` |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processJustificationAndFinalization` | `Fulu/EpochProcessing.lean:102` | Casper FFG accountable safety: conflicting finalized and justified checkpoints imply that at least `1/3` of the stake is slashable. Needs an abstract FFG layer over the epoch-processing functions and a refinement back to them. Plausible liveness, that finalization stays possible with `>= 2/3` honest, comes after accountable safety and reuses that model. Apalache bounded-model-checked the 3SF form of the property (Konnov et al. 2025), so the result is checked up to a bound and remains unproved | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getAncestor` | `Fulu/ForkChoice.lean:137` | One third of a joint claim with `getHead` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `getHead` | `Fulu/ForkChoice.lean:265` | One third of a joint claim with `getAncestor` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `onBlock` | `Fulu/ForkChoice.lean:549` | One third of a joint claim with `getAncestor` and `getHead`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |


---

## Heze

Heze is a twelve-declaration diff over Gloas. The ledger lists proof candidates for its
FOCIL gate and for the inherited ePBS declarations that the gate reaches. Every Gloas
row above applies to Heze's re-elaboration of that declaration as a separate claim
about a separate constant.

`Proofs/Heze/CensorshipCost.lean` states the cost for a block from the previous slot
whose recorded inclusion-list answer is `false`, in three facts
(`unsatisfiedPayload_cost`):

- when the `getHead` loop reaches the pending node of the block with fuel left, it
  continues from the EMPTY node (`getHead_walk_pending_to_empty`);
- any child on the EMPTY edge, with the empty parent requests, leaves the bid
  unsettled in `processParentExecutionPayload`;
- at the epoch substep, where the entry for the slot of the bid still carries its
  withdrawal (`BidPaymentCarried`), the substep appends that entry if and only if it
  reaches the quorum (`processBuilderPendingPayments_run_bid`).

No theorem connects the child to the loop, because the model does not include the
proposer. The default `[ExecutionEngine]` answers `true` for every payload, so a
recorded `false` needs a non-default engine. `BidPaymentCarried` is a hypothesis about
the blocks between the bid and the epoch substep. A proposer slashing of the block's
proposer clears the entry, and a child on the FULL edge settles it.
`unsatisfiedPayload_cost_of_run` derives the hypothesis from the chain and states the
three facts with it. The first block after the bid takes the EMPTY edge. No block carries
a proposer slashing at the slot of the bid whose proposer is the proposer of the bid's
block.

`Proofs/Heze/PaymentFrame.lean` proves that the spec functions between the bid and the
epoch substep keep the state slot, the slot of the latest block header, the cached bid,
and the payment window (`windowView`), or the first three for a function that writes the
window (`spineView`). Each lemma takes a run between two plain states, and the tactic
`frame_invert` (`Proofs/Heze/FrameInvert.lean`) inverts the run one action at a time.

`Proofs/Heze/PaymentWriters.lean` states four writers of the window at one index:
`processExecutionPayloadBid`, `processAttestation`, `processProposerSlashing`, and
`settleBuilderPayment` with `applyParentExecutionPayload`. Each lemma gives the
withdrawal and the recorded proposer at every index. The fifth writer, the epoch
substep, has its lemmas in `Proofs/Heze/BuilderPendingPayments.lean`. Those lemmas state
the substep on `pureState` of a value. Every spec function of the run keeps the uncached
box (`Proofs/Heze/KeepsUncached/`), so the states of the run are plain values and the chain
applies those lemmas directly. The index facts say when two slots share an index
(`builderPaymentIndex_inj`).

`Proofs/Heze/PaymentCarried.lean` decomposes `stateTransition` into slot steps and a
block step (`stateTransition_chainRun`) and proves the invariant `PaymentTracked` along
such a run. `bidPaymentCarried_of_run` concludes `BidPaymentCarried` at the state that
`processBuilderPendingPayments` reads. The witness `paymentWitness`
(`Tests/HezePaymentWitness.lean`) checks every hypothesis on a concrete chain at the
minimal preset.

`Proofs/Heze/InclusionDichotomy.lean` connects one honest inclusion-list transaction to
these facts (`inclusionList_dichotomy`). The envelope handler succeeds, and one of two
cases holds:

- the EL answer is `true`, and the transaction is in the payload or the EL omits it
  validly;
- the EL answer is `false`, and `UnsatisfiedPayload` holds at every later store
  (`LaterStore`) that holds the block at its root, keeps the answer at that root, whose current slot is the
  slot after the block, and whose slot increment does not overflow.

A `false` answer can come from another list's transaction.
`unsatisfiedPayload_of_recorded_false` gives `UnsatisfiedPayload` from a `LaterStore`
and a recorded `false`, without the arrival model. `inclusionList_missing_tx` states the direction for one transaction: a missing
transaction with no valid omission gives the answer `false`.
`inclusionList_missing_tx_cost` takes that answer to the three facts of
`unsatisfiedPayload_cost`. The block and answer conditions on the later store are per key, so a handler run
that writes only other roots keeps them. `onTickPerSlot_run_keeps` shows that a
per-slot tick keeps the `blocks` and `payloadInclusionListSatisfaction` maps. The clock
condition holds only in the slot after the block. A second envelope for the same root
records the answer again.

`Proofs/Heze/HeadAvoidsFull.lean` takes the one-step fact to the whole walk.
`inclusionList_missing_tx_head_avoids_full` covers every such later store whose
justified root is not below the FULL node of the block. There the head that `getHead`
returns is not below that FULL node. So the head does not extend the payload, and a
block on the FULL edge is never the head.

`Proofs/Heze/PayloadRace.lean` covers the slots after the decision slot on an abstract
model. From slot `N + 2` on, attestation weight decides between the EMPTY and the FULL
node of the block. The model has validators with balances and vote slots, a view per
honest node, and a proposer boost of at most `boost` on FULL. `race_empty_persists`
proves that every allowed view puts EMPTY strictly ahead in each slot of the window. The
hypothesis is a counting inequality: the honest balance that has voted since `N + 1` is
more than the adversarial balance that has voted, plus `boost`.
`Proofs/Heze/PayloadRaceBounds.lean` derives the inequality from uniform committees and
from honest proposers. With `PROPOSER_SCORE_BOOST = 40`, the first slot needs more than
70 % honest balance in the committee of `N + 1`.

`Proofs/Heze/PayloadRaceRefines.lean` ties the race model to the executable score. A
successful run of `getAttestationScore` at `full r` or `empty r` returns `sideWeight` of
that side, over the active unslashed validators of the state and the side the store gives
each one. The equations rest on the score characterization of
`Proofs/Heze/AttestationScore.lean` (and its Gloas copy), and on exclusivity: one supported
node is never under both children of `pending r`. `Proofs/Heze/Equivocators.lean`
characterizes `onAttesterSlashing`. Along a trace from the anchor, an index enters
`equivocatingIndices` only through an attester slashing that carries it in two slashable
attestations that pass their checks. An index that no such slashing marks is never in the
set, so `storeSide` does not drop it as an equivocator. `honest_not_equivocating` takes
"no such slashing marks the index" as the hypothesis `HonestSigner`, and no theorem derives
it.

`Proofs/Heze/PayloadRaceWalk.lean` ties the race to the `getHead` walk. Off the decision
slot, a weight run returns the score, or the score plus one proposer score. When the EMPTY
score beats the FULL score plus a bound on every proposer score, the loop body at
`pending r` steps to `empty r`. A head strictly below `pending r` then lies below `empty r`.
`Proofs/Heze/HonestVoteSide.lean` shows that an honest vote on a head below `empty r` puts
its validator on `empty`. The `get_ancestor` walk climbs the parent chain of the head, and
its fuel is enough, because the roots of the chain are distinct keys of the block map.

`Proofs/Heze/LatestMessages.lean` traces each latest message to the attestation event that
wrote it, and that event checked the block and the slot of the vote.
`Proofs/Heze/FullSupport.lean` shows that a validator on `full` has a latest message from a
slot after the slot of `r`. `Proofs/Heze/PayloadRaceExec.lean` composes the pieces into
`race_empty_persists_exec`. `RaceSetting` puts every honest head of the window strictly below
`pending r`. Every proposer score is the proposer score of the justified state
(`Proofs/Heze/ProposerScore.lean`). Under the setting and the counting inequality of
`race_empty_persists`, each of these heads lies below `empty r` and not below `full r`, or a
root collision exists. The sort in `on_attestation` is the hypothesis `QsortMem`, because
core Lean states no lemma about `Array.qsort`.

`Proofs/Heze/PayloadRaceDecision.lean` replaces two premises of `race_empty_persists_exec`
with other premises. Under the premises of tier T1 (`DecisionSetting`), the honest heads of
slot `N + 1` avoid `full r`, or a root collision exists (`RaceSetting.Core.first_of_decision`).
`Proofs/Heze/PayloadRaceCount.lean` derives the counting inequality from the committees of
the vote slots (`RaceCommittees`). Each validator votes in at most one of these slots. The
first committee beats the proposer score, and each later committee has at least as much
honest as adversarial balance. `race_empty_persists_composed` states tier T2 under
`RaceSetting.Core`, `DecisionSetting`, and `RaceCommittees`. For a window inside one epoch
whose committees are the `.ok` committees of one state (`EpochCommittees`), the committee
partition of `getBeaconCommittee` gives "at most one slot" (`EpochCommittees.oneVoteIn`).
`EpochCommittees` carries the three preset facts of the partition as fields.
`RaceCommittees.of_epoch` keeps only the two balance conditions as premises.

`Tests/HezeRaceWitness.lean` shows that the premises of `race_empty_persists_composed` can
hold together. Two honest nodes at the minimal preset run a window of slots 2 to 4 after a
block of slot 1. One node holds the payload and receives one adversarial vote for `full r`.
`raceWitness` checks every premise except `QsortMem` with one `native_decide`.

The theorem has these hypotheses, bundled as `DichotomyHypotheses`:

- the envelope handler succeeds: the block state is present, the data is available, the
  envelope verification succeeds, and the state slot is not zero;
- the committee lookup succeeds, and the list carries the key of that committee;
- the IL store is the result of the arrival list, from the seed of `getForkchoiceStore`;
- at the committee key of the list, the first arrival from its validator is the list,
  and it is timely;
- at that key, the validator signs no second list;
- no later arriving list has the same root, which the collision resistance of the hash
  gives;
- the EL satisfies `LawfulInclusionList` for an omission predicate that the reader
  supplies.

`arrivalHypotheses_two_keys` shows that the arrival hypotheses hold for a validator that
sits on two committees with different keys. The key carries no slot, so on a small
validator set it can repeat across epochs, and a second honest list under it fails the
hypotheses.

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processBuilderPendingPayments` | `Heze/EpochProcessing.lean:112` | The Heze port of the Gloas row, including the total-read fault and the quorum-product fault. The function shifts the payment window down by `SLOTS_PER_EPOCH`. Under an explicit capacity hypothesis, it appends the withdrawal of every qualifying payment from the previous epoch to `builderPendingWithdrawals`, in slot order. An entry is qualifying if and only if its weight reaches the quorum (`mem_qualifyingPaymentIndices_iff`). When the qualifying withdrawals do not fit under the list limit, the run raises `.listFull`. For one bid whose entry still carries its withdrawal, the substep appends that entry if and only if it reaches the quorum (`processBuilderPendingPayments_run_bid`). This row does not prove that each payment settles exactly once across the protocol | proved | #113, `Proofs/Heze/BuilderPendingPayments.lean` |
| `computeShuffledPermutation` | `Heze/EpochProcessing.lean:79` | Inherited from Fulu through Gloas. The same bijection on `[0, indexCount)` for the Heze constant | proved | TBD-PR, `Proofs/Heze/Shuffle.lean` |
| `computeCommittee` | `Heze/EpochProcessing.lean:82` | Inherited from Fulu through Gloas. The same slice partition for the Heze constant | proved | TBD-PR, `Proofs/Heze/Committees.lean` |
| `getBeaconCommittee` | `Heze/EpochProcessing.lean:83` | Inherited from Fulu through Gloas. The same per-epoch partition of the active set for the Heze constant | proved | TBD-PR, `Proofs/Heze/Committees.lean` |
| `isSlashableAttestationData` | `Heze/Operations.lean:24` | Inherited from Fulu through Gloas. The same double-vote-or-surround test for the Heze constant. Two different data with one target epoch are a double vote, or an `HtrCollision` | proved | `Proofs/Heze/AttesterSlashing.lean` |
| `processAttesterSlashing` | `Heze/Operations.lean:29` | Inherited from Fulu through Gloas. When the data are slashable, both validity reads return `true` on the state, and a validator of both index lists is slashable there, the run does not reject with an assert (`processAttesterSlashing_run_not_assert`, under `QsortMem`). Each of the first three asserts rejects when its test returns `false`. Arithmetic and index faults in `slashValidator` stay possible, so the row does not claim that the run succeeds | proved | `Proofs/Heze/AttesterSlashing.lean` |

### State-transition correctness

The block/slot/epoch-processing spine and the properties that follow directly from running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `weighJustificationAndFinalization` | `Heze/EpochProcessing.lean:90` | Inherited from Fulu through Gloas. The field lemmas on a plain value. After a successful run, the previous justified checkpoint is the old current one. The current one is the checkpoint of the current epoch when its target balance reaches two thirds, else the checkpoint of the previous epoch when its target balance does, else it stays. The bits shift by one and get the bit of each epoch that reaches two thirds. The finalized checkpoint follows the four finalization tests on the new bits (`finalizeRules`, `finalizeRules_cases`). The step reads a root only for an epoch that reaches two thirds (`weighJustificationAndFinalization_run_ok`). Every other field keeps its value (`weighJustificationAndFinalization_run_keeps`). A failed run fails in a `getBlockRoot` read for an epoch that reaches two thirds, with the error of that read, or in an overflow of a checked product or sum (`weighJustificationAndFinalization_run_error`) | proved | `Proofs/Heze/JustificationAndFinalization.lean` |
| `processJustificationAndFinalization` | `Heze/EpochProcessing.lean:91` | Inherited from Fulu through Gloas. In the first two epochs the run returns the state unchanged. After them it runs five reads in `Except`: the two participant sets, the total active balance, and the two target balances. A failed read ends the run with its error. Then it is the run of `weighJustificationAndFinalization` on the three balances (`processJustificationAndFinalization_run_eq`, `processJustificationAndFinalization_run_ok`) | proved | `Proofs/Heze/JustificationAndFinalization.lean` |
| `processJustificationAndFinalization` | `Heze/EpochProcessing.lean:91` | Landed: Casper FFG accountable safety on an abstract model of two chains, each with its own votes and stake (`ffg_accountable_safety`). Chain 1 finalizes `b`, chain 2 justifies a later checkpoint, and `b` is not on chain 2. Then validators with at least one third of the reference stake, less `5/3` of the two stake drifts, cast slashable votes. The model weighs a link at the epoch of its target or the next epoch, as the weigh step does. It assumes that the chains share their start checkpoints and agree below a common checkpoint (`CommonBase`, `Agree`). Open: the refinement of the model to this function, and a bound on the drift | in progress | `EthCLLib/Proofs/FFG/Safety.lean` |
| `processBlockHeader` | `Heze/Operations.lean:30` | Landed: a successful run checked the header of the state it read. The block has a greater slot, and the parent root of the block is the root of that header (`processBlockHeader_run_ok`). The block is for the state slot and by the proposer of the state, the new header has the block's slot, and the slot, the cached bid, and the payment window stay (`processBlockHeader_run_spine`). Open: the reject paths | in progress | `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/PaymentWriters.lean` |
| `stateTransition` | `Heze/Transition.lean:30` | Landed: a successful run passes through a successful `processBlockHeader` run, so some state on the way has a header with a smaller slot than the block, and the parent root of the block is the root of that header (`stateTransition_run_header`). A successful run is a run of `processSlots` to the block's slot, then the block step: the signature check, `processBlock`, and the root check (`stateTransition_split`). `processSlots` is one slot step per slot (`processSlots_chainRun`). Open: the reject paths | in progress | `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/PaymentCarried.lean` |
| `processParentExecutionPayload` | `Heze/Operations.lean:66` | Landed: on the EMPTY edge (the child bid does not extend the cached parent block hash) with the empty parent requests, the run succeeds and returns the input state, so it settles no builder payment. On either edge, a successful run keeps the slot, the header slot, and the cached bid. It keeps the withdrawal and the recorded proposer of every window entry but the entry at the index of the cached bid's slot in the half its epoch picks (`processParentExecutionPayload_run_withdrawal`). The row says nothing about the weights. Open: the request loops beyond the window, and the two `assert` rejects | in progress | #113, `Proofs/Heze/ParentPayloadEmpty.lean`, `Proofs/Heze/PaymentWriters.lean` |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `shouldExtendPayload` | `Heze/ForkChoice.lean:322-345` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`: block lookup, the slot increment, `getCurrentSlot`, the slot assertion, `isPayloadVerified`, `isPayloadInclusionListSatisfied`, then the inherited Gloas tail. Named corollaries cover the prefix rejects, the FOCIL gate (unverified, missing record, recorded `false`, recorded `true`), the vote membership asserts, and the inherited Gloas accept and reject arms. Successful binds keep the intermediate runner states. A reject returns the error alone. `onExecutionPayloadEnvelope_run_pairing` exposes the inserted payload and inclusion-list answer after one envelope run. Three obligations remain open. One composes those writes with this read-side equation. One carries a successful envelope run to the extension decision. One is the store invariant that every root in `payloads` has a recorded answer. See the second `onExecutionPayloadEnvelope` row for those obligations | proved | `Proofs/Heze/ShouldExtendPayload.lean` |
| `getInclusionListCommittee` | `Heze/ForkChoice.lean:204-213` | Complete `.run` equation at `ForkChoiceStoreRun σ`: empty concatenated indices throw the arithmetic error; a nonempty array returns `cyclicSample` of those indices and leaves the runner state unchanged | proved | follow-up to #82, `Proofs/Heze/GetInclusionListTransactions.lean` |
| `getInclusionListTransactions` | `Heze/ForkChoice.lean:223-231` | Whole-operation `.run` equation at `ForkChoiceStoreRun (Store map)`: the committee run bound to collection at the committee's stored lists. Empty-committee and missing-timeliness errors follow as untagged corollaries | proved | follow-up to #82, `Proofs/Heze/GetInclusionListTransactions.lean` |
| `collectInclusionListTransactions` | `Heze/ForkChoice.lean:135-152` | Landed: at `onlyTimely = true`, when every stored list has a timeliness entry, the collection succeeds without a change to the runner state, and each transaction of a stored list with timeliness `true` from a non-equivocator is in the result (`collectInclusionListTransactions_ok_mem`). `mem_getInclusionListTransactions` states the same through the committee lookup. Open: the converse (each result transaction comes from such a list), an equivocator's entry contributing nothing, the `onlyTimely = false` call, and the absence of duplicates from `arrayUnion` | in progress | #115, `Proofs/Heze/GetInclusionListTransactions.lean` |
| `recordPayloadInclusionListSatisfaction` | `Heze/ForkChoice.lean:409-421` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`. Slot zero gives the checked-sub arithmetic error. An empty committee and a missing timeliness key give collector errors. Any collector error propagates. A successful collection records `isInclusionListSatisfied payload ilTxs` at `root` and keeps the collector's runner state | proved | follow-up to #82, `Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`, `Proofs/Heze/GetInclusionListTransactions.lean` (successful-path origin #82) |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:429-451` | `onExecutionPayloadEnvelope_run` is the complete compositional `.run` equation at `ForkChoiceStoreRun (Store map)`. Missing `blockStates` is `.assert "envelope.beacon_block_root in store.block_states"`. Failed data availability is `.assert "(isDataAvailable envelope.beaconBlockRoot)"`. Verification and recorder errors propagate unchanged. Success is the handler's final `set` of `blockStates` and `payloads` on the recorder's explicitly returned store, which discards the recorder-produced runner state. `onExecutionPayloadEnvelope_run_of_pureState` restates the whole equation over a plain block state `state`, stored as `pureState state`. `onExecutionPayloadEnvelope_run_eq_of_successful_checks` restates the successful branch as the original store updated by three same-root `FcMap.insert` expressions. `verifyExecutionPayloadEnvelope_pureState` proves that a successful verification on `pureState state` returns `pureState state`, so the corollaries ask only that the verification succeeds | proved | #92, `Proofs/Heze/OnExecutionPayloadEnvelope.lean` (successful-path origin #84) |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:429-451` | Postconditions on the final store of `onExecutionPayloadEnvelope_run_eq_of_successful_checks`. Landed: under `LawfulFcMap`, a lookup at the block root `r` of the envelope returns the envelope and the EL answer for its payload (`onExecutionPayloadEnvelope_run_pairing`). With the answer `false`, `inclusionList_dichotomy` gives `UnsatisfiedPayload` at any later store that holds the block and the answer at `r` (`LaterStore`). `unsatisfiedPayload_of_recorded_false` makes that step without the arrival model. The laws hold for `treeMap` at `Root` keys (`EthCLLib/Proofs/LawfulFcMap.lean`, with the order laws in `EthCLLib/Spec/FiniteMap.lean`). A successful run keeps the IL store (`onExecutionPayloadEnvelope_keeps_ilStore`) and the block lookup at any root (`onExecutionPayloadEnvelope_keeps_block`). For an envelope at another root, it keeps the lookups at `r` of `payloads` and of the answer map (`onExecutionPayloadEnvelope_keeps_payload`, `onExecutionPayloadEnvelope_keeps_answer`). So a trace after the envelope handler with no second envelope for `r` gives `LaterStore` (`NodeTrace.laterStore`), and the missing-transaction result holds at the end of such a trace (`inclusionList_missing_tx_trace`). Open: the composition with the read-side characterizations `isPayloadInclusionListSatisfied_run` and `shouldExtendPayload_run`. Also open: the end-to-end corollary from a successful envelope run to the extension decision | in progress | `Proofs/Heze/OnExecutionPayloadEnvelope.lean`, `Proofs/Heze/InclusionDichotomy.lean`, `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |
| `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean:307` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`: a missing satisfaction key is the membership assert. A recorded value is returned only when the payload is verified, otherwise `false`. Corollaries name the missing-record reject, an unverified recorded value, a recorded `false`, and a recorded `true` with a verified payload. Success leaves `runnerStore` unchanged. `onExecutionPayloadEnvelope_run_pairing` pairs the recorded answer with the payload after one envelope run | proved | `Proofs/Heze/IsPayloadInclusionListSatisfied.lean` |
| `getPayloadStatusTiebreaker` | `Heze/ForkChoice.lean:346` | Landed: at a block from the previous slot, the EMPTY node scores `1`. The FULL node scores `0` when the payload is unverified, or verified with the recorded inclusion-list answer `false`. Both nodes have weight `0`, so `betterOf` keeps EMPTY. The body of the `getHead` loop (`headLoopBody`, tied to `getHead` by `rfl` in `getHead_eq_fuelLoop_headLoopBody`) then returns `.next` of the EMPTY node, so the walk continues from EMPTY when it reaches the pending node (`getHead_walk_pending_to_empty`). Open: the FULL score `2` path. The other FULL score `0` path: an answer `true` for a payload that is not both timely and available, with a proposer-boost block that is a child of the block on its EMPTY edge. Blocks that are not from the previous slot. The reachable rejects | in progress | #113, `Proofs/Heze/PayloadTiebreak.lean` |
| `getHead` | `Heze/ForkChoice.lean:359` | Landed: take a block from the previous slot with an unverified payload or a recorded `false` inclusion-list answer. A successful `getHead` run returns a head that is not the FULL node of the block and not below it in the node tree (`getHead_run_avoids_full`). The node tree (`NodeEdge`) has the three cases of `get_node_children`, without the filter and the verification. Each node has at most one parent (`NodeEdge.parent_unique`). The theorem assumes that the pending node of the justified root is not below the FULL node. `not_nodeBelow_full_of_slot_le` gives that from slots when block slots increase along parent links (`SlotsIncrease`). `SlotsIncrease` holds at the end of every trace from the anchor store with no block at the anchor's parent root, or two distinct headers or blocks share a root (`NodeTrace.slotInv`). That proof assumes every `combine` returns 32 bytes. With no block at `r`, the head avoids the FULL node of `r` with no condition on the payload (`getHead_run_avoids_full_of_no_block`). The head has one of the three payload statuses (`getHead_run_status`). At an honest node in the slot after `r`, whose envelopes for `r` all omit a transaction of the honest inclusion list, the head avoids the FULL node of `r`, or a root collision exists (`honestNode_head_avoids_full`). That theorem assumes a justified block with a slot no greater than the slot of `r`. The head lies below the pending node of the justified root (`getHead_run_below_justified`). Open: the fuel bound of the Gloas row | in progress | `Proofs/Heze/HeadAvoidsFull.lean`, `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/HonestHead.lean`, `Proofs/Heze/HeadBelowJustified.lean` |
| `shouldBuildOnFull` | `Heze/ForkChoice.lean:297` | Landed: a successful run rejects a pending head (`shouldBuildOnFull_run_ne_pending`) and answers `false` at an EMPTY head (`shouldBuildOnFull_run_empty`). An honest proposer on a head at `r` that avoids the FULL node of `r` builds on the EMPTY node of `r`, and `processParentExecutionPayload` leaves its state unchanged, so the block settles no builder payment. In a store whose block at `r` carries the latest bid of that state, fork choice puts the block on the EMPTY edge of `r` (`honestProposal_empty_of_root`). Open: the FULL head from the previous slot, where the PTC votes decide. A proposer that builds on `get_proposer_head` after a re-org (`validator.md:186-188`) | in progress | `Proofs/Heze/HonestDuties.lean` |
| `getParentPayloadStatus` | `Heze/ForkChoice.lean:285` | Landed: when the parent block is in the store, the status is EMPTY exactly when the child bid's `parentBlockHash` differs from the parent bid's `blockHash`. Open: a theorem that equal hashes give `.ok payloadStatusFull` (the landed `iff` only excludes EMPTY), and the missing-parent reject | in progress | #113, `Proofs/Heze/ParentPayloadEmpty.lean` |
| `processInclusionList` | `Heze/ForkChoice.lean:170` | Landed: the function has three results (`processInclusionList_cases`). It returns the store unchanged, or it adds the sender to the equivocators at the committee key, or it stores the list at its root with the given timeliness. Under `ArrivalHypotheses` (no earlier list from the validator at the committee key, only the one list from it after, no root collision), a fold over an arrival list keeps its list stored with the timeliness of the first arrival, and keeps the validator out of the equivocators (`honestStored_of_arrivals`). Open: which inputs select each branch. A conflicting second list from a validator leaves the stored list in place and adds the validator to the equivocators, and a list from a known equivocator leaves the store unchanged. The invariant for every validator at once, that at most one stored list per validator per committee exists. The docstring asserts it, and no theorem proves it | in progress | #115, `Proofs/Heze/OnInclusionList.lean` |
| `onInclusionList` | `Heze/ForkChoice.lean:523` | Landed: when the time into the slot is `t` and the deadline `getInclusionListDueMs` does not raise, the handler replaces the IL store with `processInclusionList` on the list, with timeliness `t < ilDueMs`, the deadline value (`onInclusionList_run_eq`). With the frames of the other handlers, the IL store after a trace of successful handler runs from a seed with the empty IL store is `ilStoreOfArrivals` of the arrivals of the trace (`NodeTrace.ilStore`). The anchor store of `getForkchoiceStore` is such a seed (`getForkchoiceStore_ilStore`). Open: the two reject paths, where `timeIntoSlotMs` fails because `store.time` is before `store.genesisTime`, and where the deadline product `INCLUSION_LIST_DUE_BPS * SLOT_DURATION_MS` overflows | in progress | #115, `Proofs/Heze/OnInclusionList.lean`, `Proofs/Heze/NodeTrace.lean` |
| `onTick` | `Heze/ForkChoice.lean:364` | Landed: a successful run keeps the IL store (`onTick_keeps_ilStore`), and the lookups at any root of `blocks`, `payloads`, and `payloadInclusionListSatisfaction` (`onTick_keeps_rootView`). A successful run keeps the unrealized pair and raises no checkpoint epoch. Each realized checkpoint stays or takes the unrealized checkpoint of its kind, and the finalized epoch stays at most the justified epoch when both pairs are ordered (`onTick_growsAt`, `TickRel`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean`, `Proofs/Heze/CheckpointInvariants.lean` |
| `onBlock` | `Heze/ForkChoice.lean:370` | Landed: a successful run keeps the IL store (`onBlock_keeps_ilStore`), through the PTC replay and the pull-up. It keeps the lookups at any root of `payloads` and `payloadInclusionListSatisfaction` (`onBlock_keeps_payloadAnswer`). It keeps the block lookup at a root `r` when its block has another root, or when the lookup already returns its block (`onBlock_keeps_block`). A successful run read the parent state, ran the state transition from it, and inserted the block and the post-state at the block root (`onBlock_run_ok`). It keeps the slot invariant, or two distinct headers or blocks share a root (`SlotInv.onBlock`). A successful run passed the two acceptance asserts: a full parent has a verified payload, and the checkpoint block of the parent at the finalized epoch is the finalized root (`onBlock_run_ok_asserts`). It writes the checkpoint pair of the post-state, then the pair that `processJustificationAndFinalization` writes on the post-state, each through `ckptPick` (`onBlock_run_ckpt`, `computePulledUpTip_run_ok`). It keeps the checkpoint invariant, or two distinct headers or blocks share a root (`CkptInv.onBlock`). Along a trace from the anchor store, each stored state ends a chain run from the anchor state over the blocks on the parent links of its root, the run ends at the block of the state, and each of the four store checkpoints comes from such a state (`NodeTrace.ckptInv`). In both pairs, the finalized epoch is at most the justified epoch. No checkpoint epoch goes down along a trace (`NodeTrace.ckptGrows`). Open: the ancestry claim of the Gloas row, between the block and the finalized checkpoint. `onBlock_run_ok_asserts` states only the assert | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean`, `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/CheckpointInvariants.lean`, `Proofs/Heze/BlockChain.lean` |
| `updateCheckpoints` | `Heze/ForkChoice.lean:360` | Inherited from Gloas. A record update of the two realized checkpoints. Each one takes its candidate when the candidate has a greater epoch, else it stays (`updateCheckpoints_eq_pick`, `ckptPick`). The two writes are separate, so the new justified checkpoint need not descend from the new finalized one. The order of their epochs holds when the store pair and the candidate pair are ordered (`ckptPick_ord`) | proved | `Proofs/Heze/CheckpointInvariants.lean` |
| `getCheckpointBlock` | `Heze/ForkChoice.lean:289` | Inherited from Gloas. A block is on the EMPTY side of `r` when its pending node is below `empty r`. Take a successful run from a root `j` that returns the root of such a block. Then `j` is on the EMPTY side too (`emptySide_of_checkpointBlock`). The proof uses `getAncestor_run_above` and needs no fuel bound. Under `SlotsIncrease`, no node below `empty r` is below `full r` (`below_emptySide_not_full`). The finality lock takes an honest node whose finalized block is on the EMPTY side of `r`. After a later trace, the head is not below `full r`, or two distinct headers or blocks share a root, or the justified checkpoint conflicts with that finalized checkpoint (`honestNode_finality_lock`, `Conflicting`). The store updates its justified and finalized checkpoints separately, so the theorem keeps the conflict case | proved | `Proofs/Heze/FinalityLock.lean` |
| `onPayloadAttestationMessage` | `Heze/ForkChoice.lean:368` | Landed: a successful run keeps the IL store (`onPayloadAttestationMessage_keeps_ilStore`), and the lookups at any root of the three maps (`onPayloadAttestationMessage_keeps_rootView`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |
| `onAttestation` | `Heze/ForkChoice.lean:457` | Landed: a successful run keeps the IL store (`onAttestation_keeps_ilStore`), and the lookups at any root of the three maps (`onAttestation_keeps_rootView`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |
| `onAttesterSlashing` | `Heze/ForkChoice.lean:458` | Landed: a successful run keeps the IL store (`onAttesterSlashing_keeps_ilStore`), and the lookups at any root of the three maps (`onAttesterSlashing_keeps_rootView`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |

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
  compiler, which found bugs. That incremental-tree result is prior art for the
  Electra deposit branch check, which Fulu removes.
- Nyx Foundation `formal-leanSpec` — a parallel Lean 4 formalization of the
  post-quantum leanSpec, with its own SSZ layer.
