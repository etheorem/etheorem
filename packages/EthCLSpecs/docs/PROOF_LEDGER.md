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
  `onInclusionList`, `getInclusionListTransactions`, and `onExecutionPayloadEnvelope`
  rows. Its corollary `inclusionList_missing_tx_cost` also rests on
  `unsatisfiedPayload_cost`.
- The committee partition rests on the shuffle bijection.
- Plausible liveness rests on accountable safety.
- `VerifiedImpliesRecorded` is a joint claim of `getForkchoiceStore` and
  `onExecutionPayloadEnvelope`. The local postcondition at the written root
  cites `FcMap.lookup_insert_self` and `FcMap.contains_insert_self`. The
  empty-anchor half needs lookup in `FcMap.empty`, and preservation at roots
  other than the written one needs lookup after an insert at a different key.
  `LawfulFcMap` states both (next item). A source audit identifies
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
| `convertBuilderIndexToValidatorIndex` | `Gloas/Operations.lean:555` | Round-trips with `toBuilderIndex` on any `bi` that does not already carry the `BUILDER_INDEX_FLAG` bit. `toBuilderIndex` always clears that bit, so the round trip holds only under that precondition | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |
| `toBuilderIndex` | `Gloas/Operations.lean:80` | Clears the `BUILDER_INDEX_FLAG` bit, so it inverts `convertBuilderIndexToValidatorIndex` on any index that already carries the flag; the companion direction is the row above | proved | #16, `Proofs/Gloas/BuilderIndex.lean` |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeExitEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:101-114` | The Gloas override reads `get_exit_churn_limit`. When the activation-exit epoch, the churn limit and the reservation succeed, the run succeeds, and its `balance_to_consume - exit_balance` subtraction cannot fault. Each activation-epoch, churn-limit or reservation fault passes through unchanged | proved | `Proofs/Gloas/Churn.lean` |
| `reserveChurn` | `Gloas/EpochProcessing.lean:83` | The Fulu claims. The body reads no preset or config value, so each theorem takes the Fulu proof term | proved | `Proofs/Gloas/Churn.lean` |
| `computeConsolidationEpochAndUpdateChurn` | `Gloas/EpochProcessing.lean:180` | The Fulu claims, at the Gloas consolidation limit. That limit has no `MIN` floor and can be zero, and `reserveChurn` rejects a zero limit | proved | `Proofs/Gloas/Churn.lean` |
| `getExpectedWithdrawals` | `Gloas/Withdrawals.lean:195-203` | The withdrawals returned by its four phases combined never exceed `MAX_WITHDRAWALS_PER_PAYLOAD` | proposed |  |
| `initiateBuilderExit` | `Gloas/Operations.lean:140-143` | `initiateBuilderExit_run_eq` is the whole-transition equation; its exact in-range/out-of-range effect on the builder registry is characterized; no-wrap is conditional for an arbitrary `Config` and proved unconditionally for both shipped Gloas preset/config pairs | proved | #39, `Proofs/Gloas/InitiateBuilderExit.lean` |
| `processBuilderExitRequest` | `Gloas/Operations.lean:308-320` | On its successful builder-exit branch, the index supplied to `initiateBuilderExit` is in range. Under either shipped Gloas preset/config pair, the selected builder receives the intended non-wrapping future `withdrawableEpoch`. All non-matching or ineligible branches leave the builder registry unchanged | proposed |  |
| `getPtc` | `Gloas/Operations.lean:483-501` | Its computed offset into `ptcWindow` stays in range under the two guarded call patterns: `data.slot + 1 == state.slot` and the fork-choice replay callers' `slot == curSlot`. Landed: both bounds, stated over `getPtcElseOffset`, a restatement of the else-branch arithmetic. Open: a statement about `getPtc` itself, which is what would carry a `characterizes` tag and move the function past the touched tier | in progress | `4b4b78a`, `Proofs/Gloas/GetPtc.lean` |
| `getPendingBalanceToWithdrawForBuilder` | `Gloas/Operations.lean:106-117` | When the `Nat` sums of the matching pending-withdrawal and pending-payment amounts add to less than `2^64`, the result is that exact total. At `2^64` or more it rejects with `.arithmetic`, the point where the pyspec's running `uint64` balance raises `ValueError` | proved | `Proofs/Gloas/PendingBalanceForBuilder.lean` |
| `canBuilderCoverBid` | `Gloas/Operations.lean:563-569` | With a successful pending balance and a `MIN_DEPOSIT_AMOUNT` addition below `2^64`, its `Bool` result is characterized exactly against the computed `minBalance`. A pending-balance fault passes through, and the addition rejects with `.arithmetic` at `2^64`. Proving that queuing an accepted bid preserves `MIN_DEPOSIT_AMOUNT` + pending obligations ≤ builder balance is the caller-level follow-up, and needs ring-cell freshness hypotheses | proved | #36, `Proofs/Gloas/CanBuilderCoverBid.lean` |
| `applyWithdrawals` | `Gloas/Withdrawals.lean:208-218` | A builder-flagged withdrawal decreases the builder's balance by at most its own balance, so the balance never goes negative | proposed |  |
| `getAncestor` | `Gloas/ForkChoice.lean:184-191` | The fuel supplied to its `fuelLoop` DAG walk is sufficient for the walk to terminate before running out | proposed |  |
| `getHead` | `Gloas/ForkChoice.lean:575-612` | The fuel `2 * blocks.length + 2` supplied to its LMD-GHOST walk is sufficient for the walk to reach a decided head before running out | proposed |  |
| `computeBalanceWeightedSelection` | `Gloas/EpochProcessing.lean:239` | An `.ok` result holds exactly `size` indices, and the run rejects with `.arithmetic` at the `2**64` counter bound or at either `uint64` product, and with `.outOfBounds` on a candidate past the registry. `cbwsAux` is well-founded, so `rfl` and `decide` do not unfold it, and the proof goes through `cbwsAux.induct` and its equation lemmas | proposed |  |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processProposerSlashing` | `Gloas/Operations.lean:62` | Out of scope here: at v1.7.0-beta.4 Gloas inherits the Fulu body, and the payment voiding this row asked about moved into `slashValidator` (the next row). Its old claim, that payment-voiding never touches another proposer's `BuilderPendingPayment`, is that row's | out of scope |  |
| `slashValidator` | `Gloas/EpochProcessing.lean:126-169` | The closing EIP-7732 loop resets to the empty payment exactly the `builderPendingPayments` entries whose `proposerIndex` is the slashed validator, and leaves every other proposer's entry untouched. New at v1.7.0-beta.4, where the voiding moved here from `processProposerSlashing` and widened to both payment epochs and to the attester-slashing path | proposed |  |
| `processAttestation` | `Gloas/Operations.lean:384-463` | Committee-index safety together with builder-payment weight accounting: a validator's effective balance adds to the slot's payment weight at most once, and only when it set a new flag and held no flag before the attestation (the `had_no_participation` gate, new at v1.7.0-beta.4) | proposed |  |
| `processBuilderPendingPayments` | `Gloas/EpochProcessing.lean:410-433` | The total-active-balance read for the quorum faults first, on a `uint64` overflow of the sum, and that fault passes through (`processBuilderPendingPayments_run_total_error`). The quorum product `per_slot_balance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR` faults next, with `.arithmetic`, when it reaches `2 ^ 64` (`processBuilderPendingPayments_run_quorum_error`). Given the total and a quorum product that fits (`QuorumFits`), the whole-transition equation over a plain `BeaconState`: the run returns `preState` with only `builderPendingWithdrawals` (the qualifying withdrawals, folded through `ProgressiveList.push` in slot order; every one is appended) and `builderPendingPayments` (the window shifted down by `SLOTS_PER_EPOCH` and padded with empties) written. This does not establish protocol-wide exactly-once settlement | proved | #25, `Proofs/Gloas/BuilderPendingPayments.lean` |
| `processPtcWindow` | `Gloas/EpochProcessing.lean:461-480` | Each newly populated `ptcWindow` entry equals `computePtc` evaluated for its corresponding slot | proposed |  |
| `applyDepositForBuilder` | `Gloas/Operations.lean:168-183` | A deposit with an invalid signature is neither applied to a builder's balance nor requeued | proposed |  |
| `processBuilderDepositRequest` | `Gloas/Operations.lean:275-297` | A new builder is onboarded only when its deposit signature is valid | proposed |  |
| `getIndexedPayloadAttestation` | `Gloas/Operations.lean:506-512` | Preserves `pa.data` and `pa.signature`, and produces the sorted multiset of PTC seats selected by `pa.aggregationBits`. The proof requires `Array.qsort` sortedness and permutation lemmas not currently available in core/Std | proposed |  |
| `isValidIndexedPayloadAttestation` | `Gloas/Operations.lean:520-532` | Returns `.ok true` exactly when the attesting indices are non-empty, adjacent-nondecreasing (duplicates permitted), all within the validator registry, and the configured `[CryptoBackend]` accepts the exact aggregate-verification call. An index past the registry raises `.outOfBounds` | proved | #38, `Proofs/Gloas/IsValidIndexedPayloadAttestation.lean` |
| `processPayloadAttestation` | `Gloas/Operations.lean:537-550` | Running `processPayloadAttestation` does not modify `State`: it only reads the input state and evaluates three assertions. A concrete run-level theorem should show that both success and rejection preserve the state component | proposed |  |
| `processExecutionPayloadBid` | `Gloas/Operations.lean:625-661` | The self-build and builder-bid paths it chooses between are mutually exclusive and jointly exhaustive | proposed |  |
| `applyParentExecutionPayload` | `Gloas/Operations.lean:672-701` | Exactly one of settle-current, settle-previous, or evict fires, so a payment is never settled twice | proposed |  |
| `computeShuffledPermutation` | `Gloas/EpochProcessing.lean:193` | Inherited from Fulu. The same bijection on `[0, indexCount)` for the Gloas constant | proved | TBD-PR, `Proofs/Gloas/Shuffle.lean` |
| `computeCommittee` | `Gloas/EpochProcessing.lean:198` | Inherited from Fulu. The same slice partition for the Gloas constant | proved | TBD-PR, `Proofs/Gloas/Committees.lean` |
| `getBeaconCommittee` | `Gloas/EpochProcessing.lean:199` | Inherited from Fulu. The same per-epoch partition of the active set for the Gloas constant, with the same seed premises. At v1.7.0-beta.4 the registry is a progressive list with no limit, so the theorems take the bounds that the spec itself needs in place of `VALIDATOR_REGISTRY_LIMIT ≤ 2^40`. The active set of the epoch has at most `2^40` indices: above that, `compute_shuffled_permutation` overflows `Uint32(position_bucket)` and raises. The nodup result also takes a registry of at most `2^64` entries, so that its indices are distinct `uint64` values | proved | TBD-PR, `Proofs/Gloas/Committees.lean` |
| `isSlashableAttestationData` | `Gloas/Operations.lean:30` | Inherited from Fulu. The same double-vote-or-surround test for the Gloas constant, and the same root-collision reading of two different data with one target epoch | proved | `Proofs/Gloas/AttesterSlashing.lean` |

### Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates: never decreasing, never shrinking, never losing a previously-added element.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getWeight` | `Gloas/ForkChoice.lean:465-477` | Weight only grows as more attestations accumulate for a node | proposed |  |
| `onAttesterSlashing` | `Gloas/ForkChoice.lean:1073-1083` | The set of equivocating indices only grows | proposed |  |
| `updateCheckpoints` | `Gloas/ForkChoice.lean:627-629` | Each justified/finalized checkpoint either remains unchanged or advances to its candidate, so its epoch never decreases, and no other Store field moves | proved | #30, `Proofs/Gloas/UpdateCheckpoints.lean` |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processSlot` | `Gloas/Transition.lean:32-52` | After `processSlot`, the `executionPayloadAvailability` bit at index `(slot + 1) mod SLOTS_PER_HISTORICAL_ROOT` reads `false`, matching the documented invariant that a payload starts unavailable | proposed |  |
| `processOperations` | `Gloas/Transition.lean:88-102` | public declarations live in `EthCLSpecs.Proofs.Gloas`. Non-empty in-block deposits fail immediately with `StateTransitionError.assert`, and a reject at this monad carries no state; success on the uncached box of a plain value is equivalent to empty deposits plus the six operation-family loops succeeding in order over five plain intermediate values, one `runPure` fact per loop. The attestation loop passes the parent block's slot (`parent_slot`, new at v1.7.0-beta.4) to each `processAttestation`. `KeepsUncached` is the fact behind the split: every handler keeps the flavour, so `runPure_bind_of_keepsUncached` names each fold's post-state as a plain value. No per-operation correctness or rollback guarantee for later failures is claimed | proved | #57, `Proofs/Gloas/ProcessOperations.lean` |
| `processDepositRequest` | `Fulu/Operations.lean:282` | The run appends one `PendingDeposit` stamped with the current slot to `pendingDeposits` and writes no other field, so `depositRequestsStartIndex` keeps its value. Gloas and Heze inherit it | proved | `Proofs/Gloas/ProcessDepositRequest.lean` |
| `stateTransition` | `Gloas/Transition.lean:119-129` | Top-level state-transition correctness; composes `processSlots`, `processBlock`, and the root check into the canonical transition | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `onBlock` | `Gloas/ForkChoice.lean:822-873` | Accepts a block only if a full parent implies a verified payload, and the block's ancestry agrees with the currently finalized checkpoint | proposed |  |
| `validateOnAttestation` | `Gloas/ForkChoice.lean:999-1032` | Validates that the attestation's index is 0 or 1, that a same-slot attestation has index 0, and that a full-vote attestation's payload is verified | proposed |  |
| `getForkchoiceStore` | `Gloas/ForkChoice.lean:1098-1124` | Every root-keyed map in a freshly built store agrees on the anchor entry | proposed |  |
| `isAncestor` | `Gloas/ForkChoice.lean:196-201` | Agrees with the ancestor relation that `getAncestor` computes iteratively | proposed |  |
| `verifyExecutionPayloadEnvelope` | `Gloas/ForkChoice.lean:916-953` | Acceptance requires every validation check performed by `verifyExecutionPayloadEnvelope` to succeed | proposed |  |

### Upgrade-boundary properties

Functions whose entire purpose is the Fulu-to-Gloas upgrade itself: preserving state across the boundary or seeding Gloas-only state from it. The fork comparison here is not incidental, it's what the function does.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `upgradeToGloas` | `Gloas/Upgrade.lean:83-149` | Preserves inherited state while correctly initializing the new ePBS state | proposed |  |
| `computePtcFromFulu` | removed | Out of scope: removed at v1.7.0-beta.4. `upgrade_to_gloas` now builds the window over the Gloas post-state with Gloas's own `compute_ptc`, so no Fulu-side twin is left to agree with it | out of scope |  |
| `initializePtcWindow` | `Gloas/Operations.lean:228-240` | Each entry is an `Except` carrying its own three faults: the entry's checked add `current_epoch + e` rejects with the `.arithmetic` fault exactly at `current_epoch = UINT64_MAX`, the start slot's checked multiply rejects with `.arithmetic` where the spec raises, and the `compute_ptc` read rejects a slot with no committee members; `completeUpgradeToGloas` maps the entries in index order, so the first rejecting slot surfaces. `initializePtcWindow_eq` states the whole vector equation and carries the `@[characterizes]` tag; `initializePtcWindow_getElem` joins the two regions at the element level. A `forkdef` over the Gloas state since v1.7.0-beta.4, so it is a spec function in the coverage report's denominator; alpha.12 kept it a plain `def` over the Fulu pre-state | proved | #26, `Proofs/Gloas/InitializePtcWindow.lean` |

### Candidates needing a sharper statement

Functions where the useful theorem hasn't been identified yet, either because the obvious candidate property doesn't hold up, or because none has been proposed. Once identified, the candidate belongs in one of the sections above.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computePtc` | `Gloas/EpochProcessing.lean:442-450` | No standalone theorem has been identified yet. `initializePtcWindow_eq` states the seeded window in terms of it and says nothing about `computePtc` itself. The former candidate, agreement with `computePtcFromFulu`, went with that function at v1.7.0-beta.4 | proposed |  |


---

## Fulu

### Round-trip and conversion properties

Functions whose natural theorem is an inverse relationship with another Fulu function, applying one after the other returns the original value, at least under a stated precondition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeEpochAtSlot` | `Fulu/Time.lean:33` | `computeEpochAtSlot (computeStartSlotAtEpoch e) = e`, conditional on `e * SLOTS_PER_EPOCH < 2^64` at a symbolic preset. Closed unconditionally at both shipped presets, for `e < 2^61` at minimal and `e < 2^59` at mainnet | proved | `Proofs/Fulu/Time.lean` |
| `computeStartSlotAtEpoch` | `Fulu/Time.lean:45-47` | The same identity, seen from this side. The round trip is the row above | proved | `Proofs/Fulu/Time.lean` |

### Bounds and termination properties

Functions where the theorem is a numeric bound, no overflow, no underflow, never exceeding a spec constant, or a termination bound, a fuel parameter large enough for a bounded walk to finish.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `reserveChurn` | `Fulu/RegistryUpdates.lean:92` | It rejects with `.arithmetic` on a zero limit, the pyspec's `ZeroDivisionError`. It rejects with `.arithmetic` when the epoch add, the multiply, or the consumed add reaches `2^64`. Below every bound it returns the exact epoch and consumed total. A successful reservation returns a consumed total at least as large as the balance | proved | `Proofs/Fulu/Churn.lean` |
| `computeExitEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:109` | When the activation-exit epoch, the churn limit and the reservation succeed, the run succeeds, and its `balance_to_consume - exit_balance` subtraction cannot fault. Each activation-epoch, churn-limit or reservation fault passes through unchanged | proved | `Proofs/Fulu/Churn.lean` |
| `computeConsolidationEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:126` | The same claims over the consolidation fields and the consolidation limit | proved | `Proofs/Fulu/Churn.lean` |
| `modBalance` | `Fulu/Balances.lean:29` | On the pure box, the write through the infallible `[i]!` index is one plain record update: `modBalance (pureState state) i f = pureState { state with balances := state.balances.set! i.toNat (f state.balances[i.toNat]!) }`. This is the whole contract; the two mutators below build on it | proved | follow-up to #80, `Proofs/Fulu/Balances.lean` |
| `increaseBalance` | `Fulu/Balances.lean:43` | The run rejects an index past the end of `balances` with `.outOfBounds`, and an addition that leaves the `uint64` range with `.arithmetic`. In range and below that bound it returns the input value with exactly that one balance written, and that balance is the exact natural-number sum | proved | #80, `Proofs/Fulu/Balances.lean` |
| `decreaseBalance` | `Fulu/Balances.lean:54` | The run rejects an index past the end of `balances` with `.outOfBounds`. In range it returns the input value with exactly `saturatingSub balance delta` written, the spec's `saturating_sub` (v1.7.0-beta.4); that value reads back as the truncating `Nat` difference, so the `uint64` subtraction never wraps | proved | #80, `Proofs/Fulu/Balances.lean` |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:249` | The registry never exceeds `VALIDATOR_REGISTRY_LIMIT` | proposed |  |
| `getBeaconCommittee` | `Fulu/Committees.lean:184` | An active-validator count in `[32, 2^22]` implies every committee size is in `(0, MAX_VALIDATORS_PER_COMMITTEE]`. Dafny proves the same bound in `ActiveValidatorBounds` | proposed |  |
| `computeStartSlotAtEpoch` | `Fulu/Time.lean:45-47` | The function multiplies an epoch back to a slot. It faults with `.arithmetic` above `2^64`. It never faults on an epoch derived from a slot. The claim is open where the caller supplies the epoch | proved | `Proofs/Fulu/Time.lean` |
| `computeStartSlotAtEpoch` | `Gloas/EpochProcessing.lean:34` | The Fulu claims, restated at Gloas's own constant. Each theorem takes the Fulu proof term through the `Downgrade` bridge | proved | `Proofs/Gloas/Time.lean` |
| `computeStartSlotAtEpoch` | `Heze/EpochProcessing.lean:26` | The same claims at Heze's constant. The bridge reaches one fork up, so the proof terms come from Gloas | proved | `Proofs/Heze/Time.lean` |
| `computeActivationExitEpoch` | `Fulu/Time.lean:57-60` | The function adds `1 + MAX_SEED_LOOKAHEAD` to an epoch. It faults with `.arithmetic` when the sum reaches `2^64`. Below that bound it returns the exact sum. It never faults on an epoch derived from a slot, under a preset bound that both shipped presets satisfy | proved | `Proofs/Fulu/Time.lean` |
| `computeActivationExitEpoch` | `Gloas/EpochProcessing.lean:49` | The Fulu claims, restated at Gloas's own constants through the `Downgrade` bridge | proved | `Proofs/Gloas/Time.lean` |
| `computeActivationExitEpoch` | `Heze/EpochProcessing.lean:39` | The same claims at Heze's constants. The proof terms come from Gloas | proved | `Proofs/Heze/Time.lean` |
| `reserveChurn` | `Heze/EpochProcessing.lean:25` | The Fulu claims at Heze. The proof terms come from Gloas | proved | `Proofs/Heze/Churn.lean` |
| `computeExitEpochAndUpdateChurn` | `Heze/EpochProcessing.lean:73` | The Gloas claims at Heze, proved again over the Heze `State` | proved | `Proofs/Heze/Churn.lean` |
| `computeConsolidationEpochAndUpdateChurn` | `Heze/EpochProcessing.lean:79` | The Gloas claims at Heze, proved again over the Heze `State` | proved | `Proofs/Heze/Churn.lean` |

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeShuffledPermutation` | `Fulu/Committees.lean:56` | The body raises where the pyspec raises: at `indexCount = 0`, above `2^40`, and at round 256. A run succeeds exactly when the pyspec does not raise (`computeShuffledPermutation_eq_ok_iff`). It then returns a bijection on `[0, indexCount)`, stated as a `List.Perm` of `List.range` (`computeShuffledPermutation_perm`). The proof never reads the hash, so it holds for every hasher and cites no hash axiom. No prior art: Dafny stubbed shuffling to the identity, and Runtime Verification did not prove it either | proved | TBD-PR, `Proofs/Fulu/Shuffle.lean` |
| `getBeaconCommittee` | `Fulu/Committees.lean:184` | Over one epoch, every committee run succeeds and returns its slice of the shuffled active set (`getBeaconCommittee_ok`). The committees for every slot and committee index are a permutation of the active set (`getBeaconCommittee_partition`). No validator sits in two committees of the epoch (`getBeaconCommittee_nodup`). The slots are the spec's `compute_start_slot_at_epoch(e) + j`. The theorems do not establish a per-slot partition, since one slot's committees hold only that slot's share. The theorems assume four preset facts, which both shipped presets satisfy: `VALIDATOR_REGISTRY_LIMIT ≤ 2^40`, `SHUFFLE_ROUND_COUNT ≤ 256`, `(MAX_COMMITTEES_PER_SLOT + 1) * SLOTS_PER_EPOCH ≤ 2^23`, and `MIN_SEED_LOOKAHEAD + 1 ≤ EPOCHS_PER_HISTORICAL_VECTOR`. They also assume that the epoch's last slot fits in `uint64`, and that `e + EPOCHS_PER_HISTORICAL_VECTOR` does, which keeps `get_seed` from raising (`getSeed_ok`). The committees read `seedOf`, the seed of that run. The committee-size bound is the separate row under Bounds and termination properties | proved | TBD-PR, `Proofs/Fulu/Committees.lean` |
| `computeCommittee` | `Fulu/Committees.lean:157` | When the `uint64` products fit, `index < count`, and the shuffle's bounds hold, the run succeeds. Committee `index` of `count` is then the slice `[len * index / count, len * (index + 1) / count)` of `indices`, read through the shuffled permutation (`computeCommittee_ok`). For `0 < count`, committees `0 … count-1` laid end to end are a permutation of `indices` (`computeCommittee_partition`) | proved | TBD-PR, `Proofs/Fulu/Committees.lean` |
| `isSlashableAttestationData` | `Fulu/Operations.lean:39` | The test is true exactly for a double vote (different data, one target epoch) or a surround vote (`isSlashableAttestationData_iff`). The test compares the fields of the two data, as the pyspec's `data_1 != data_2` does. The statement needs no precondition on the index lists. Two different data with one target epoch are a double vote (`isSlashableAttestationData_of_ne`) | proved | `Proofs/Fulu/AttesterSlashing.lean` |
| `processRegistryUpdates` | `Fulu/EpochProcessing.lean:249` | One third of a joint claim with `initiateValidatorExit` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `initiateValidatorExit` | `Fulu/RegistryUpdates.lean:150` | One third of a joint claim with `processRegistryUpdates` and `computeExitEpochAndUpdateChurn`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |
| `computeExitEpochAndUpdateChurn` | `Fulu/RegistryUpdates.lean:109` | One third of a joint claim with `processRegistryUpdates` and `initiateValidatorExit`: a validator flows from active to exited at most once, and the churn consumed in an epoch never exceeds the churn limit | proposed |  |

### Monotonicity properties

Functions whose output only moves in one direction as their input grows or accumulates: never decreasing, never shrinking, never losing a previously-added element.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `computeEpochAtSlot` | `Fulu/Time.lean:33` | The epoch never decreases as the slot grows. A `uint64` division by a positive constant, so the proof needs no preset bound | proved | `Proofs/Fulu/Time.lean` |

### State-transition correctness

The block/slot/epoch-processing spine itself: the composition of the individual processing steps into the top-level state transition, and the properties that hold as a direct consequence of running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `processJustificationAndFinalization` | `Fulu/EpochProcessing.lean:102` | Casper FFG accountable safety: conflicting finalized and justified checkpoints imply that at least `1/3` of the stake is slashable. Needs an abstract FFG layer over the epoch-processing functions and a refinement back to them. Plausible liveness, that finalization stays possible with `>= 2/3` honest, comes after accountable safety and reuses that model. Apalache bounded-model-checked the 3SF form of the property (Konnov et al. 2025), so the result is checked up to a bound and remains unproved | proposed |  |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getAncestor` | `Fulu/ForkChoice.lean:135` | One third of a joint claim with `getHead` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `getHead` | `Fulu/ForkChoice.lean:304` | One third of a joint claim with `getAncestor` and `onBlock`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |
| `onBlock` | `Fulu/ForkChoice.lean:659` | One third of a joint claim with `getAncestor` and `getHead`: a valid store is a chain, ancestry is slot-monotone, and an accepted block stays accepted. Dafny proves the chain and slot-monotone parts as `aValidStoreIsAChain` | proposed |  |


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

### Censorship cost

`Proofs/Heze/CensorshipCost.lean` states the cost for a block from the previous slot
whose recorded inclusion-list answer is `false`, in three facts
(`unsatisfiedPayload_cost`):

- when the `getHead` loop reaches the pending node of the block with fuel left, and the
  EMPTY node is in the viable node list, it continues from the EMPTY node
  (`getHead_walk_pending_to_empty`);
- any child on the EMPTY edge, with the empty parent requests, leaves the bid
  unsettled in `processParentExecutionPayload`;
- at the epoch substep, where the entry for the slot of the bid still carries its
  withdrawal (`BidPaymentCarried`), the substep appends that entry if and only if it
  reaches the quorum (`processBuilderPendingPayments_run_bid`).

No theorem connects the child to the loop, because the model does not include the
proposer. The default `[ExecutionEngine]` answers `true` for every payload, so a
recorded `false` needs a non-default engine. `BidPaymentCarried` is a hypothesis about
the blocks between the bid and the epoch substep. A slashing of the block's proposer
clears the entry (`slashValidator`), and a child on the FULL edge settles it.
`unsatisfiedPayload_cost_of_run` derives the hypothesis from the chain and states the
three facts with it. The first block after the bid takes the EMPTY edge. No slashing of
any block reaches the proposer of the bid's block (`NoSlashingOf`).

`Proofs/Heze/PaymentFrame.lean` proves that the spec functions between the bid and the
epoch substep keep the state slot, the slot of the latest block header, the cached bid,
and the payment window (`windowView`), or the first three for a function that writes the
window (`spineView`). Each lemma takes a run between two plain states, and the tactic
`frame_invert` (`Proofs/Heze/FrameInvert.lean`) inverts the run one action at a time.

`Proofs/Heze/PaymentWriters.lean` states four writers of the window at one index:
`processExecutionPayloadBid`, `processAttestation`, `slashValidator` (with both slashing
handlers), and `settleBuilderPayment` with `applyParentExecutionPayload`. Each lemma gives
the withdrawal and the recorded proposer at every index. The fifth writer, the epoch
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
  (`LaterStore`) that holds the block at its root, keeps the answer at that root, whose
  current slot is the slot after the block, and whose slot increment does not overflow.

A `false` answer can come from another list's transaction.
`unsatisfiedPayload_of_recorded_false` gives `UnsatisfiedPayload` from a `LaterStore`
and a recorded `false`, without the arrival model. `inclusionList_missing_tx` states the
direction for one transaction: a missing transaction with no valid omission gives the
answer `false`. `inclusionList_missing_tx_cost` takes that answer to the three facts of
`unsatisfiedPayload_cost`. The block and answer conditions on the later store are per
key, so a handler run that writes only other roots keeps them. `onTickPerSlot_run_keeps`
shows that a per-slot tick keeps the `blocks` and `payloadInclusionListSatisfaction`
maps. The clock condition holds only in the slot after the block. A second envelope for
the same root records the answer again.

`Proofs/Heze/HeadAvoidsFull.lean` takes the one-step fact to the whole walk.
`inclusionList_missing_tx_head_avoids_full` covers every such later store whose
justified root is not below the FULL node of the block, and where the FULL node is
viable only with the EMPTY node (`EmptyViableWithFull`). There the head that `getHead`
returns is not below that FULL node. So the head does not extend the payload, and a
block on the FULL edge is never the head. Without the viability premise, `get_head` can
move to the FULL node: the viable node list can keep the FULL node as a leaf and drop
the EMPTY node, when every branch below it fails the checkpoint checks.

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
`pending r` steps to `empty r`, when `empty r` is viable. Take a store where `full r` is
viable only with `empty r`. A head strictly below `pending r` then lies below `empty r`.
`Proofs/Heze/HonestVoteSide.lean` shows that an honest vote on a head below `empty r` puts
its validator on `empty`. The `get_ancestor` walk climbs the parent chain of the head, and
its fuel is enough, because the roots of the chain are distinct keys of the block map.

`Proofs/Heze/LatestMessages.lean` traces each latest message to the attestation event that
wrote it, and that event checked the block and the slot of the vote.
`Proofs/Heze/FullSupport.lean` shows that a validator on `full` has a latest message from a
slot after the slot of `r`. `Proofs/Heze/PayloadRaceExec.lean` composes the pieces into
`race_empty_persists_exec`. `RaceSetting` puts every honest head of the window strictly below
`pending r`, with `full r` viable only with `empty r`. Every proposer score is the proposer
score of the justified state
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
`EpochCommittees` carries the bounds of the partition as fields: two preset facts, an active
set of at most `2^40` indices, below which `compute_shuffled_permutation` does not raise, and
a registry of at most `2^64` entries, so that its indices are distinct.
`RaceCommittees.of_epoch` keeps only the two balance conditions as premises.

A window of several epochs has more than one justified state. `race_empty_persists_long`
states the race with one justified state per slot (`RaceSetting.Long`), and
`race_empty_persists_exec` is its case with one justified state. `Proofs/Heze/RaceLong.lean` gives the
counting inequality after a full epoch of the window (`count_of_epoch`). Every validator that
is active at that epoch has voted (`EpochCommittees.votes_of_active`). So a margin of the
honest total over the adversarial total gives the count, with no bound on the number of
votes of a validator. `hcount_of_parts` joins it to `RaceCommittees.count` for the first part of the window.
The window still ends before the justified checkpoint passes `r`.

`Tests/HezeRaceWitness.lean` shows that the premises of `race_empty_persists_composed` can
hold together. Two honest nodes at the minimal preset run a window of slots 2 to 4 after a
block of slot 1. One node holds the payload and receives one adversarial vote for `full r`.
`raceWitness` checks every premise except `QsortMem` by `native_decide`.

The theorem has these hypotheses, bundled as `DichotomyHypotheses`:

- the envelope handler succeeds: the block state is present, the data is available, and
  the envelope verification succeeds;
- the block is in the store at a nonzero slot, and the dependent-root walk of the
  recorder returns a root; the list carries that key, `(slot - 1, dependent_root)`;
- the IL store is the result of the arrival list, from the seed of `getForkchoiceStore`;
- at the key of the list, the first arrival from its validator is the list, and its
  `onInclusionList` run judged it timely;
- at that key, the validator signs no second list;
- the EL satisfies `LawfulInclusionList` for an omission predicate that the reader
  supplies.

`arrivalHypotheses_two_keys` shows that the arrival hypotheses hold for a validator that
sends lists for two keys. The key carries the slot, so a list for one slot never shares
a key with a list for another slot. `Tests/HezeDichotomyWitness.lean` builds a store, an
envelope, and an honest list that meet every hypothesis.

### Safety and invariant preservation

Functions with a specific invariant, precondition bundle, or side-effect guarantee that should hold whenever the function runs: exactly-once behavior, mutual exclusion between cases, or a value staying untouched under some condition.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `getForkchoiceStore` | `Heze/ForkChoice.lean:483-513` | One half of a joint claim with `onExecutionPayloadEnvelope`. This is the initialization, the base case, of `VerifiedImpliesRecorded`. The `Prop` holds vacuously because `payloads` is empty, so `isPayloadVerified` is false at every root. The satisfaction map is empty with it. Stating the empty lookups needs laws `LawfulFcMap` does not yet give | proposed |  |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:442-464` | The other half of the joint claim with `getForkchoiceStore`. `VerifiedImpliesRecorded` says `isPayloadVerified store root = true` implies `FcMap.lookup store.payloadInclusionListSatisfaction root` is `some`. A successful `onExecutionPayloadEnvelope_run_eq_of_successful_checks` establishes it at the written root, because that equation inserts `payloads` and the satisfaction key there. Preservation at other roots waits on the missing other-key insert law. A rejected run has no post-state on `ForkChoiceStoreRun`. The store `recordPayloadInclusionListSatisfaction` returns inserts the bit and leaves `payloads` unchanged, and is outside this claim. A source audit identifies this function and `getForkchoiceStore` as the committed writers of the two maps. Global preservation still requires frame lemmas for the remaining committed handlers | proposed |  |
| `processInclusionList` | `Heze/ForkChoice.lean:140-156` | A list is stored only on the no-entry branch, and that branch inserts one `InclusionListEntry`, the signed list and its timeliness together, under `(slot, dependent_root)` and the sender. The stored-entry branch never changes `inclusionLists`, and it changes `equivocators` only by adding the sender, once, when the new list differs. At v1.7.0-beta.4 the timeliness lives in the entry, so the alpha.12 claim that every stored list root is a key of a separate timeliness map has no subject. Landed: the function has three results, the store unchanged, the sender added to the equivocators at the key, or the entry stored (`processInclusionList_cases`). Open: which inputs select each result | in progress | `Proofs/Heze/OnInclusionList.lean` |
| `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean:318-326` | Under `VerifiedImpliesRecorded`, a verified root cannot take the missing-record assert. The helper can still assert on an unverified root with no record. Establishing `VerifiedImpliesRecorded` on committed stores is the separate joint invariant claim—requiring initialization, envelope preservation, and frame preservation—not this reader row | proposed |  |
| `processBuilderPendingPayments` | `Heze/EpochProcessing.lean:137` | The Heze port of the Gloas row, including the total-read fault and the quorum-product fault. Given the total and `QuorumFits`, the run succeeds. It appends the withdrawal of every qualifying payment from the previous epoch to `builderPendingWithdrawals`, a progressive list with no limit, in slot order, and shifts the payment window down by `SLOTS_PER_EPOCH`. An entry is qualifying if and only if its weight reaches the quorum (`mem_qualifyingPaymentIndices_iff`). For one bid whose entry still carries its withdrawal, the substep queues that withdrawal if and only if the entry reaches the quorum (`processBuilderPendingPayments_run_bid`). This row does not prove that each payment settles exactly once across the protocol | proved | `Proofs/Heze/BuilderPendingPayments.lean` |
| `computeShuffledPermutation` | `Heze/EpochProcessing.lean:102` | Inherited from Fulu through Gloas. The same bijection on `[0, indexCount)` for the Heze constant | proved | TBD-PR, `Proofs/Heze/Shuffle.lean` |
| `computeCommittee` | `Heze/EpochProcessing.lean:107` | Inherited from Fulu through Gloas. The same slice partition for the Heze constant | proved | TBD-PR, `Proofs/Heze/Committees.lean` |
| `getBeaconCommittee` | `Heze/EpochProcessing.lean:108` | Inherited from Fulu through Gloas. The same per-epoch partition of the active set for the Heze constant, with the same seed premises. At v1.7.0-beta.4 the registry is a progressive list with no limit, so the theorems take the bounds that the spec itself needs in place of `VALIDATOR_REGISTRY_LIMIT ≤ 2^40`. The active set of the epoch has at most `2^40` indices: above that, `compute_shuffled_permutation` overflows `Uint32(position_bucket)` and raises. The nodup result also takes a registry of at most `2^64` entries, so that its indices are distinct `uint64` values | proved | TBD-PR, `Proofs/Heze/Committees.lean` |
| `isSlashableAttestationData` | `Heze/Operations.lean:25` | Inherited from Fulu through Gloas. The same double-vote-or-surround test for the Heze constant. Two different data with one target epoch are a double vote | proved | `Proofs/Heze/AttesterSlashing.lean` |
| `processAttesterSlashing` | `Heze/Operations.lean:30` | Inherited from Fulu through Gloas. When the data are slashable, both validity reads return `true` on the state, and a validator of both index lists is slashable there, the run does not reject with an assert (`processAttesterSlashing_run_not_assert`, under `QsortMem`). Each of the first three asserts rejects when its test returns `false`. Arithmetic and index faults in `slashValidator` stay possible, so the row does not claim that the run succeeds | proved | `Proofs/Heze/AttesterSlashing.lean` |
| `processAttestation` | `Heze/Operations.lean:57` | Inherited from Gloas. Landed: a target bit that a successful run sets belongs to an attesting index, in the list of the target epoch. The source of the attestation is the justified checkpoint of that epoch, and the target root is the block root at that epoch (`processAttestation_run_flags`, `processAttestation_explained`). With a matching source and target root, the run sets the target bit of each attesting index (`processAttestation_sets_target`). Along a chain run, each target flag of an epoch after the current epoch of the start state comes from an attestation that a block of the run includes (`ChainRun.flag_explained`). Open: the source and head flags, the builder-payment weight, and the proposer reward | in progress | `Proofs/Heze/Participation.lean` |
| `processParticipationFlagUpdates` | `Heze/EpochProcessing.lean:134` | Inherited from Fulu through Gloas. Landed: the run moves the target bit of the current list to the previous list, clears the current target bit, and keeps the slot (`processParticipationFlagUpdates_run`). Open: the full post-state | in progress | `Proofs/Heze/ParticipationFrame.lean` |

### State-transition correctness

The block/slot/epoch-processing spine and the properties that follow directly from running through it.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `weighJustificationAndFinalization` | `Heze/EpochProcessing.lean:115` | Inherited from Fulu through Gloas. The field lemmas on a plain value. After a successful run, the previous justified checkpoint is the old current one. The current one is the checkpoint of the current epoch when its target balance reaches two thirds, else the checkpoint of the previous epoch when its target balance does, else it stays. The bits shift by one and get the bit of each epoch that reaches two thirds. The finalized checkpoint follows the four finalization tests on the new bits (`finalizeRules`, `finalizeRules_cases`). The step reads a root only for an epoch that reaches two thirds (`weighJustificationAndFinalization_run_ok`). Every other field keeps its value (`weighJustificationAndFinalization_run_keeps`). A failed run fails in a `getBlockRoot` read for an epoch that reaches two thirds, with the error of that read, or in an overflow of a checked product or sum (`weighJustificationAndFinalization_run_error`) | proved | `Proofs/Heze/JustificationAndFinalization.lean` |
| `processJustificationAndFinalization` | `Heze/EpochProcessing.lean:116` | Inherited from Fulu through Gloas. In the first two epochs the run returns the state unchanged. After them it runs five reads in `Except`: the two participant sets, the total active balance, and the two target balances. A failed read ends the run with its error. Then it is the run of `weighJustificationAndFinalization` on the three balances (`processJustificationAndFinalization_run_eq`, `processJustificationAndFinalization_run_ok`) | proved | `Proofs/Heze/JustificationAndFinalization.lean` |
| `processJustificationAndFinalization` | `Heze/EpochProcessing.lean:116` | Landed: Casper FFG accountable safety on an abstract model of two chains, each with its own votes and stake (`ffg_accountable_safety`). Chain 1 finalizes `b`, chain 2 justifies a later checkpoint, and `b` is not on chain 2. Then validators with at least one third of the reference stake, less `5/3` of the two stake drifts, cast slashable votes. The model weighs a link at the epoch of its target or the next epoch, as the weigh step does. It assumes that the chains share their start checkpoints and agree below a common checkpoint (`CommonBase`, `Agree`). The bound on the drift of one chain run is `chainRun_drift_le`. Composed for two honest nodes from one anchor (`honestNodes_accountable`). The justified checkpoint of one node conflicts with the finalized checkpoint `f` of another under `getCheckpointBlock`. Then a root collision exists, or there is slashing evidence (`SlashingEvidence`). The evidence is pairs of indexed attestations that pass `is_slashable_attestation_data`, with one attestation valid on a state of each chain run. The common validators of the pairs hold a third of the total of the fork point, less `5/3` of the drift along each run after the fork point (`runDrift`). The premises add `QsortMem`, the anchor block as the block of the anchor state, `max (e₀ + 2) 3 ≤ f.epoch`, and ancestor paths that agree before that epoch | proved | `EthCLLib/Proofs/FFG/Safety.lean`, `Proofs/Heze/Accountable.lean`, `Proofs/Heze/ForkPoint.lean`, `Proofs/Heze/ChainAgree.lean`, `Proofs/Heze/RefDrift.lean`, `Proofs/Heze/VoteValid.lean` |
| `processJustificationAndFinalization` | `Heze/EpochProcessing.lean:116` | Refines Casper FFG justification and finalization over the placed votes of a chain run (`chain_refines`), under `RunTotals`. The abstract chain of the run (`ffgChain`) has the votes of the run, the checkpoint roots of the run, and the stake and the total of each weigh state (`ChainMatches`). At an epoch with no weigh state, the end state of the run gives the stake and the total. The two justified checkpoints at the end of the run are justified in the chain. The finalized checkpoint is finalized there, or it is a base checkpoint. The same holds for `processJustificationAndFinalization` on the end state, the pull-up that `computePulledUpTip` stores (`chain_refines_pullup`). The base holds the anchor checkpoints and the checkpoints that the weigh steps of the anchor epoch, the next epoch, and epoch 2 justify. Epoch 2 counts only when the anchor epoch is at most 2. The stake counts a validator active at the current or the previous epoch, as the previous-epoch test does. The run has validated blocks with nonzero state roots, and `2 * SLOTS_PER_EPOCH` is at most `SLOTS_PER_HISTORICAL_ROOT` | proved | `Proofs/Heze/FFGRefines.lean`, `Proofs/Heze/RunVotes.lean`, `Proofs/Heze/TargetStake.lean` |
| `processJustificationAndFinalization` | `Heze/EpochProcessing.lean:116` | Bounds the stake drift of a chain run (`chainRun_drift_le`). The distances of the link stakes over `vals`, plus the shortfall of the total active balance, are at most `driftBound`. The bound reads `st₀`, the end epoch `E`, the churn bounds, and the bounds of the run. The run ends at the epoch `E` of its end state, less than `EPOCHS_PER_SLASHINGS_VECTOR / 2` epochs after `st₀`. Each state of the run meets `StatePre`. The exit churn and the consolidation churn stay within their bounds. `sq * sq` is at most the total active balance, and `U` bounds the total active balance and the sum of the effective balances. `S` bounds each inactivity score. The deposit churn and each pending deposit amount stay below `2 ^ 63`, each balance stays below `2 ^ 64` less the downward hysteresis threshold, and the registry stays below `BUILDER_INDEX_FLAG = 2 ^ 40` validators. The spec relies on that boundary: at or above it, `apply_withdrawals` reads a validator withdrawal as a builder withdrawal (`is_builder_index`), and the beta.4 registry has no limit that would give it. Each withdrawal request of a block has an amount below `2 ^ 62` | proved | `Proofs/Heze/StakeDrift.lean`, `Proofs/Heze/DriftRun.lean`, `Proofs/Heze/DriftInv.lean`, `Proofs/Heze/DriftBound.lean` |
| `getBlockRootAtSlot` | `Heze/EpochProcessing.lean:43` | Inherited from Fulu through Gloas. A successful run passed both asserts and read the ring buffer (`getBlockRootAtSlot_run_ok`). Along a chain run of validated blocks with nonzero state roots, the ring buffer holds the root of the last block at or before each slot that it covers, or the root that the anchor state records (`ChainRun.rootsInv`, `rootAtSlot`). So the read returns that root on a state of the run (`RootsInv.read`) and on the state after the next `processSlot` (`RootsInv.read_slotWrite`). `processSlot` writes the filled header and its root (`processSlot_run_eq`) | proved | `Proofs/Heze/BlockRootsRun.lean`, `Proofs/Heze/HeaderFrame.lean` |
| `processBlockHeader` | `Heze/Operations.lean:31` | Landed: a successful run checked the header of the state it read. The block has a greater slot, and the parent root of the block is the root of that header (`processBlockHeader_run_ok`). The block is for the state slot and by the proposer of the state, the new header has the block's slot, and the slot, the cached bid, and the payment window stay (`processBlockHeader_run_spine`). Open: the reject paths | in progress | `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/PaymentWriters.lean` |
| `stateTransition` | `Heze/Transition.lean:81` | Landed: a successful run passes through a successful `processBlockHeader` run, so some state on the way has a header with a smaller slot than the block, and the parent root of the block is the root of that header (`stateTransition_run_header`). A successful run is a run of `processSlots` to the block's slot, then the block step: the signature check, `processBlock`, and the root check (`stateTransition_split`). `processSlots` is one slot step per slot (`processSlots_chainRun`). Open: the reject paths | in progress | `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/PaymentCarried.lean` |
| `processParentExecutionPayload` | `Heze/Operations.lean:69` | Landed: on the EMPTY edge (the child bid does not extend the cached parent block hash) with the empty parent requests, the run succeeds and returns the input state, so it settles no builder payment. On either edge, a successful run keeps the slot, the header slot, and the cached bid. It keeps the withdrawal and the recorded proposer of every window entry but the entry at the index of the latest header's slot in the half its epoch picks (`processParentExecutionPayload_run_withdrawal`). The row says nothing about the weights. Open: the request loops beyond the window, and the two `assert` rejects | in progress | `Proofs/Heze/ParentPayloadEmpty.lean`, `Proofs/Heze/PaymentWriters.lean` |

### Fork-choice correctness

Properties specific to the fork-choice store and the LMD-GHOST tree: agreement between two ways of computing the same relation, preconditions gating block/attestation acceptance, and correctness of the store's own bookkeeping.

| Function | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- |
| `shouldExtendPayload` | `Heze/ForkChoice.lean:333-356` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`: block lookup, the slot increment, `getCurrentSlot`, the slot assertion, `isPayloadVerified`, `isPayloadInclusionListSatisfied`, then the inherited Gloas tail. Named corollaries cover the prefix rejects, the FOCIL gate (unverified, missing record, recorded `false`, recorded `true`), the vote membership asserts, and the inherited Gloas accept and reject arms. Successful binds keep the intermediate runner states. A reject returns the error alone. The local envelope postconditions and the recorded-false composition are the first `onExecutionPayloadEnvelope` postcondition row. The branch where the recorded bit is `true` is the second. `VerifiedImpliesRecorded` is the joint claim with `getForkchoiceStore`. Transport to `Gloas.shouldExtendPayload` is the later row for this function | proved | `Proofs/Heze/ShouldExtendPayload.lean` |
| `getInclusionListCommittee` | `Heze/ForkChoice.lean:232-241` | Complete `.run` equation at `ForkChoiceStoreRun σ`: a `getBeaconCommittee` fault in the concatenation surfaces as `.transition`; empty concatenated indices throw the arithmetic error; a nonempty array returns `cyclicSample` of those indices and leaves the runner state unchanged | proved | follow-up to #82, `Proofs/Heze/GetInclusionListTransactions.lean` |
| `getInclusionListTransactions` | `Heze/ForkChoice.lean:191-195` | Pure at v1.7.0-beta.4. `mem_getInclusionListTransactions_iff`: a transaction is in the result exactly when the list of some item for `(slot, dependent_root)` carries it, where the item's sender is not an equivocator for the key and, at `onlyTimely = true`, its entry is timely. `getInclusionListTransactions_nodup`: the result holds no duplicate. The items are `inclusionListItems`, the map fold the spec's loop iterates. Under `LawfulFcMap`, the items are exactly the stored entries (`mem_inclusionListItems_iff`), and a timely entry from a non-equivocator gives each of its transactions (`mem_getInclusionListTransactions_of_stored`) | proved | `Proofs/Heze/GetInclusionListTransactions.lean` |
| `collectInclusionListTransactions` | removed | Out of scope: removed at v1.7.0-beta.4. Each stored entry carries its own timeliness, so no lookup can miss and `getInclusionListTransactions` filters and deduplicates in one pure step. This row's claim (equivocator exclusion, the timeliness filter, no duplicates) is now the proved `getInclusionListTransactions` row | out of scope |  |
| `recordPayloadInclusionListSatisfaction` | `Heze/ForkChoice.lean:426-434` | Complete `.run` equation at `ForkChoiceStoreRun (Store map)`: a block missing from `store.blocks` is `missingKey root`; a slot-zero block is the checked-sub arithmetic error; a dependent-root walk error propagates; a successful walk records `isInclusionListSatisfied payload ilTxs` at `root`, for the timely transactions `ilTxs` stored under `(block.slot - 1, dependent_root)`, and keeps the walk's runner state. At v1.7.0-beta.4 the function takes no state and collects without throwing | proved | follow-up to #82, `Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`, `Proofs/Heze/GetInclusionListTransactions.lean` (successful-path origin #82) |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:442-464` | `onExecutionPayloadEnvelope_run` is the complete compositional `.run` equation at `ForkChoiceStoreRun (Store map)`: missing `blockStates` is `.assert "envelope.beacon_block_root in store.block_states"`; failed data availability is `.assert "(isDataAvailable envelope.beaconBlockRoot)"`; verification and recorder errors propagate unchanged; success is the handler's final `set` of `blockStates` and `payloads` on the recorder's explicitly returned store, discarding the recorder-produced runner state. `onExecutionPayloadEnvelope_run_of_pureState` restates the whole equation over a plain block state `state`, stored as `pureState state`, and `onExecutionPayloadEnvelope_run_eq_of_successful_checks` restates the successful branch as the original store updated by three same-root `FcMap.insert` expressions. `verifyExecutionPayloadEnvelope_pureState` proves that a successful verification on `pureState state` returns `pureState state`, so the corollaries ask only that the verification succeeds | proved | #92, `Proofs/Heze/OnExecutionPayloadEnvelope.lean` (successful-path origin #84) |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:442-464` | Postconditions on the store `onExecutionPayloadEnvelope_run_eq_of_successful_checks` returns. Landed: under `[LawfulFcMap map Root]`, a lookup at the block root of the envelope returns the envelope in `payloads` and `some (isInclusionListSatisfied signedEnv.message.payload ilTxs)` in `payloadInclusionListSatisfaction`, where `ilTxs` is `getInclusionListTransactions` at the block's `(slot - 1, dependent_root)` key (`onExecutionPayloadEnvelope_run_pairing`). With the answer `false`, `inclusionList_dichotomy` gives `UnsatisfiedPayload` at any later store that holds the block and the answer at the root (`LaterStore`). `unsatisfiedPayload_of_recorded_false` makes that step without the arrival model. The laws hold for `treeMap` at `Root` keys (`EthCLLib/Proofs/LawfulFcMap.lean`, with the order laws in `EthCLLib/Spec/FiniteMap.lean`). A successful run keeps the IL store (`onExecutionPayloadEnvelope_keeps_ilStore`) and the block lookup at any root (`onExecutionPayloadEnvelope_keeps_block`). For an envelope at another root, it keeps the lookups at `r` of `payloads` and of the answer map (`onExecutionPayloadEnvelope_keeps_payload`, `onExecutionPayloadEnvelope_keeps_answer`). So a trace after the envelope handler with no second envelope for `r` gives `LaterStore` (`NodeTrace.laterStore`), and the missing-transaction result holds at the end of such a trace (`inclusionList_missing_tx_trace`). Open: the composition with the read-side characterizations `isPayloadInclusionListSatisfied_run` and `shouldExtendPayload_run`, and the end-to-end corollary from a successful envelope run to the extension decision. Other roots, `VerifiedImpliesRecorded` for the whole store, and the `true` bit are separate rows | in progress | `Proofs/Heze/OnExecutionPayloadEnvelope.lean`, `Proofs/Heze/InclusionDichotomy.lean`, `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |
| `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean:318` | The complete `.run` equation at `ForkChoiceStoreRun (Store map)`: a missing satisfaction key is the membership assert; a recorded value is returned only when the payload is verified, otherwise `false`. Corollaries name the missing-record reject, an unverified recorded value, a recorded `false`, and a recorded `true` with a verified payload. Success leaves `runnerStore` unchanged. Under `VerifiedImpliesRecorded`, the missing-record arm on a verified root is the later row for this function | proved | `Proofs/Heze/IsPayloadInclusionListSatisfied.lean` |
| `processInclusionList` | `Heze/ForkChoice.lean:140` | At most one stored list per validator per `(slot, dependent_root)` key. The inner map is keyed by the validator, so this holds by the store's shape. A second list from the same validator leaves the stored entry untouched; when it differs, the sender joins the key's equivocators. Every later list from that validator for the key takes the stored-entry branch and is ignored. Landed: under `ArrivalHypotheses` (no earlier list from the validator at the key, and only the one list from it after), a fold over an arrival list keeps the entry of the list with the timeliness of its first arrival, and keeps the validator out of the equivocators (`honestStored_of_arrivals`). Open: which inputs select each branch | in progress | `Proofs/Heze/OnInclusionList.lean` |
| `onInclusionList` | `Heze/ForkChoice.lean:541-592` | Landed: a successful run sets the store it read first with `processInclusionList` of the list and a timeliness bit, and the bit is `true` exactly when the list is for the current slot and the time into the slot is before the deadline `getInclusionListDueMs`, which does not raise (`onInclusionList_run_ok`, `InclusionListTimely`). With the frames of the other handlers, the IL store after a trace of successful handler runs from a seed with the empty IL store is `ilStoreOfArrivals` of the arrivals of the trace, each with the timeliness bit of its run (`NodeTrace.ilStore`). The anchor store of `getForkchoiceStore` is such a seed (`getForkchoiceStore_ilStore`). Open: the reject paths, one per check of the handler, and the deadline reject, where the product `INCLUSION_LIST_DUE_BPS * SLOT_DURATION_MS` overflows | in progress | `Proofs/Heze/OnInclusionList.lean`, `Proofs/Heze/NodeTrace.lean` |
| `onExecutionPayloadEnvelope` | `Heze/ForkChoice.lean:442-464` | On that same post-state, when `isInclusionListSatisfied signedEnv.message.payload ilTxs = true`, `isPayloadInclusionListSatisfied` returns `true` and `shouldExtendPayload` returns the inherited tail. The tail hypotheses stay in the statement: both PTC vote arrays, proposer boost, and parent fullness. The statement takes the stored bit. It does not assume the optimistic `ExecutionEngine` instance | proposed |  |
| `shouldExtendPayload` | `Heze/ForkChoice.lean:333-356` | Under `SharesEpbsView`, a shared prefix failure, an unverified root, and a verified root with a recorded `true` satisfaction bit give the same extension result as `Gloas.shouldExtendPayload`. Recorded `false` returns `false`. A missing satisfaction key asserts on the Heze side. `getPayloadStatusTiebreaker` is a separate row | proposed |  |
| `getPayloadStatusTiebreaker` | `Heze/ForkChoice.lean:358` | Landed: at a block from the previous slot, the EMPTY node scores `1`. The FULL node scores `0` when the payload is verified and its recorded inclusion-list answer is `false`. Both nodes have weight `0`, so `betterOf` keeps EMPTY. A restated body of the `getHead` loop then goes to EMPTY. Open: the FULL score `2` path. The other FULL score `0` paths: an unverified payload, and an answer `true` for a payload that is not both timely and available, with a proposer-boost block that is a child of the block on its EMPTY edge. Blocks that are not from the previous slot. The reachable rejects. The whole `getHead` walk is the `getHead` row | in progress | `Proofs/Heze/PayloadTiebreak.lean` |
| `getHead` | `Heze/ForkChoice.lean:370` | Landed: take a block from the previous slot with an unverified payload or a recorded `false` inclusion-list answer, whose FULL node is in the viable node list only with its EMPTY node (`EmptyViableWithFull`). A successful `getHead` run returns a head that is not the FULL node of the block and not below it in the node tree (`getHead_run_avoids_full`). The node tree (`NodeEdge`) has the three cases of `get_node_children`, without the viable-node filter and the verification. Each node has at most one parent (`NodeEdge.parent_unique`). The theorem assumes that the pending node of the justified root is not below the FULL node. `not_nodeBelow_full_of_slot_le` gives that from slots when block slots increase along parent links (`SlotsIncrease`). The walk theorems take `LawfulFcMap`, because `getNodeChildren` reads the blocks through `FcMap.fold`. `SlotsIncrease` holds at the end of every trace from the anchor store with no block at the anchor's parent root, or two distinct headers or blocks share a root (`NodeTrace.slotInv`). That proof assumes every `combine` returns 32 bytes. With no block at `r`, the head avoids the FULL node of `r` with no condition on the payload (`getHead_run_avoids_full_of_no_block`). The head has one of the three payload statuses (`getHead_run_status`). At an honest node in the slot after `r`, whose envelopes for `r` all omit a transaction of the honest inclusion list, the head avoids the FULL node of `r`, or a root collision exists (`honestNode_head_avoids_full`). That theorem assumes a justified block with a slot no greater than the slot of `r`, and `EmptyViableWithFull` at `r`. The head lies below the pending node of the justified root (`getHead_run_below_justified`). Open: `EmptyViableWithFull` from the checkpoint state, and the fuel bound of the Gloas row | in progress | `Proofs/Heze/HeadAvoidsFull.lean`, `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/HonestHead.lean`, `Proofs/Heze/HeadBelowJustified.lean` |
| `shouldBuildOnFull` | `Heze/ForkChoice.lean:308` | Landed: a successful run rejects a pending head (`shouldBuildOnFull_run_ne_pending`) and answers `false` at an EMPTY head, for every slot argument (`shouldBuildOnFull_run_empty`). An honest proposer on a head at `r` that avoids the FULL node of `r` builds on the EMPTY node of `r`, and `processParentExecutionPayload` leaves its state unchanged, so the block settles no builder payment. In a store whose block at `r` carries the latest bid of that state, fork choice puts the block on the EMPTY edge of `r` (`honestProposal_empty_of_root`). Open: the FULL head from the slot before, where the PTC votes decide. A proposer that builds on `get_proposer_head` after a re-org (`validator.md:194-196`) | in progress | `Proofs/Heze/HonestDuties.lean` |
| `getParentPayloadStatus` | `Heze/ForkChoice.lean:295` | Landed: when the parent block is in the store, the status is EMPTY exactly when the child bid's `parentBlockHash` differs from the parent bid's `blockHash`. Open: a theorem that equal hashes give `.ok payloadStatusFull` (the landed `iff` only rules out EMPTY), and the missing-parent reject | in progress | `Proofs/Heze/ParentPayloadEmpty.lean` |
| `onTick` | `Heze/ForkChoice.lean:376` | Landed: a successful run keeps the IL store (`onTick_keeps_ilStore`), and the lookups at any root of `blocks`, `payloads`, and `payloadInclusionListSatisfaction` (`onTick_keeps_rootView`). A successful run keeps the unrealized pair and raises no checkpoint epoch. Each realized checkpoint stays or takes the unrealized checkpoint of its kind, and the finalized epoch stays at most the justified epoch when both pairs are ordered (`onTick_growsAt`, `TickRel`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean`, `Proofs/Heze/CheckpointInvariants.lean` |
| `onBlock` | `Heze/ForkChoice.lean:382` | Landed: a successful run keeps the IL store (`onBlock_keeps_ilStore`), through the PTC replay and the pull-up. It keeps the lookups at any root of `payloads` and `payloadInclusionListSatisfaction` (`onBlock_keeps_payloadAnswer`). It keeps the block lookup at a root `r` when its block has another root, or when the lookup already returns its block (`onBlock_keeps_block`). A successful run for a known block leaves the store unchanged (`onBlock_run_of_known`). For a new block, it read the parent state, ran the state transition from it, and inserted the block and the post-state at the block root (`onBlock_run_ok`). It keeps the slot invariant, or two distinct headers or blocks share a root (`SlotInv.onBlock`). A successful run for a new block passed the two acceptance asserts: a full parent has a verified payload, and the checkpoint block of the parent at the finalized epoch is the finalized root (`onBlock_run_ok_asserts`). It writes the checkpoint pair of the post-state, then the pair that `processJustificationAndFinalization` writes on the post-state, each through `ckptPick` (`onBlock_run_ckpt`, `computePulledUpTip_run_ok`). It keeps the checkpoint invariant, or two distinct headers or blocks share a root (`CkptInv.onBlock`). Along a trace from the anchor store, each stored state ends a chain run from the anchor state over the blocks on the parent links of its root, the run ends at the block of the state, and each of the four store checkpoints comes from such a state (`NodeTrace.ckptInv`). In both pairs, the finalized epoch is at most the justified epoch. No checkpoint epoch goes down along a trace (`NodeTrace.ckptGrows`). Open: the ancestry claim of the Gloas row, between the block and the finalized checkpoint. `onBlock_run_ok_asserts` states only the assert | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean`, `Proofs/Heze/SlotsIncrease.lean`, `Proofs/Heze/CheckpointInvariants.lean`, `Proofs/Heze/BlockChain.lean` |
| `updateCheckpoints` | `Heze/ForkChoice.lean:372` | Inherited from Gloas. A record update of the two realized checkpoints. Each one takes its candidate when the candidate has a greater epoch, else it stays (`updateCheckpoints_eq_pick`, `ckptPick`). The two writes are separate, so the new justified checkpoint need not descend from the new finalized one. The order of their epochs holds when the store pair and the candidate pair are ordered (`ckptPick_ord`) | proved | `Proofs/Heze/CheckpointInvariants.lean` |
| `getCheckpointBlock` | `Heze/ForkChoice.lean:299` | Inherited from Gloas. A block is on the EMPTY side of `r` when its pending node is below `empty r`. Take a successful run from a root `j` that returns the root of such a block. Then `j` is on the EMPTY side too (`emptySide_of_checkpointBlock`). The proof uses `getAncestor_run_above` and needs no fuel bound. Under `SlotsIncrease`, no node below `empty r` is below `full r` (`below_emptySide_not_full`). The finality lock takes an honest node whose finalized block is on the EMPTY side of `r`. After a later trace, the head is not below `full r`, or two distinct headers or blocks share a root, or the justified checkpoint conflicts with that finalized checkpoint (`honestNode_finality_lock`, `Conflicting`). The store updates its justified and finalized checkpoints separately, so the theorem keeps the conflict case | proved | `Proofs/Heze/FinalityLock.lean` |
| `onPayloadAttestationMessage` | `Heze/ForkChoice.lean:380` | Landed: a successful run keeps the IL store (`onPayloadAttestationMessage_keeps_ilStore`), and the lookups at any root of the three maps (`onPayloadAttestationMessage_keeps_rootView`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |
| `onAttestation` | `Heze/ForkChoice.lean:471` | Landed: a successful run keeps the IL store (`onAttestation_keeps_ilStore`), and the lookups at any root of the three maps (`onAttestation_keeps_rootView`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |
| `onAttesterSlashing` | `Heze/ForkChoice.lean:472` | Landed: a successful run keeps the IL store (`onAttesterSlashing_keeps_ilStore`), and the lookups at any root of the three maps (`onAttesterSlashing_keeps_rootView`) | in progress | `Proofs/Heze/HandlerFrames.lean`, `Proofs/Heze/RootFrames.lean` |

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
