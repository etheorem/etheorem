# Future work

Deferred changes for EthCLSpecs. Each entry records what is left, why it waits, and
the shape it will take, so a later pass can pick it up whole rather than rediscover it.

## Provable indexing for the remaining total reads

### What is left

The error model already splits indexed reads two ways. A read whose index arrives from
block or external input rejects through `Except IndexError` (`sszGetIdx` / `bitlistGetIdx`
in `Spec/State.lean`, lifted by `liftErr`); a guarded read with an explicit
`assert (i < size)` reads the proof-carrying `xs[i]'hb.down` through `assertH`. What stays
on a total `[i]!` or `vget`, the provability residual, is every read whose index is in
range by construction but does not yet carry the proof. A proof over one of these unfolds
through the `Inhabited` default rather than a bounded lookup. The shapes:

- **Pure data-derived index reads.** The foundational accessors and index-list consumers:
  `getTotalBalance`, `getTotalActiveBalance`, `getActiveValidatorIndices`,
  `getUnslashedParticipatingIndices`, `getInactivityPenaltyDeltas`, and the committee and
  weighted-selection helpers. The index is a parameter or a validated list. Approach A or B
  below, and the invariant lemmas they rest on.
- **Loop and fold bodies.** Reads inside `for i in [0:n]`, `.foldl`, `.map`, `.all` over an
  array's own indices, where `i < n` holds but sits out of scope. The iteration carries the
  bound once restructured (`for h : i in [0:n]`, or `.attach` for the membership), the same
  `.attach` step Approach A uses.
- **`size - 1` reads.** A few `xs[xs.size - 1]!` (the last withdrawal, the previous
  consolidation). Each needs a non-emptiness `0 < xs.size` in scope.
- **`vget` on `Vector`.** The fixed-length reads, most indexed by a `Fin n` from a
  `Vector.ofFn` or a `[0:n]` loop. These become `v[i]'(…)` from the `Fin`'s `isLt` or the
  loop bound; `vget` is the total convenience until then.
- **`[i]?.getD default` on `Array`.** The `.toArray`-local reads that fall back to a default.
  Where the index is `findIdx?`-derived or loop-bounded they prove in range; where it is
  untrusted they join the `Except` set instead.

The last three shapes are local discharges, `Fin.isLt`, a non-emptiness hypothesis, a loop
`omega`, that `get_elem_tactic` closes at the read with no new lemma. The first two need
the invariant lemmas, so they set the pace (see the constraint below).

Outside this residual, and staying as they are: the `sszUpdate state with field[i]! := …`
writes. The bang there is SizzLean's infallible symbolic-cap element write, total by
design, not a masking read.

### Approach A: a proof parameter

A query that reads `validators[i]` for `i` drawn from `indices` takes the bound as an
optional proof, Lean's `autoParam`:

```lean
forkdef getTotalBalance (state : State) (indices : Array ValidatorIndex)
    (hvalid : ∀ i ∈ indices, i.toNat < (sszGet state validators).size := by …) : Gwei :=
  let validators := sszGet state validators
  indices.attach.foldl (fun acc ⟨i, hi⟩ =>
    acc + (validators[i.toNat]'(hvalid i hi)).effectiveBalance) 0
```

The fold runs over `indices.attach`, so each step carries `hi : i ∈ indices`, and
`hvalid i hi` discharges the read's bound. A plain `foldl` lambda gives `i` but no
membership, which is why `.attach` is needed. The read is then `[i]'(…)`, proof-carrying,
with no default.

The definition site changes little: the parameter, `foldl` to `attach.foldl`, and the
proof term in place of the bang. The cost lands at the callers. The default tactic cannot
prove `∀ i ∈ indices, …` for an arbitrary `indices`, so each call site owes the proof. A
spike on `getTotalBalance` with a `by sorry` default put the obligation at
`getTotalActiveBalance`, the reward-delta helpers, and the Gloas mirrors. The way to make
most call sites free is a small set of invariant lemmas the default tactic can find:

- `getActiveValidatorIndices` returns in-range indices,
  `∀ vi ∈ result, vi.toNat < (sszGet state validators).size`, a loop invariant over its
  `for i in [0:validators.size]`.
- the parallel-length invariant `(sszGet state balances).size = (sszGet state
  validators).size`, for the reward and penalty reads that index `balances` at a validator
  index. It now holds on every reachable Fulu and Gloas state: it is the `registrySizes`
  field of `SimpleStateInvariants`, which `ReachableState.simpleStateInvariants` proves
  (`Proofs/Fulu/ReachableInvariants.lean`, `Proofs/Gloas/ReachableInvariants.lean`). A
  call site that holds a reachable state can read it from there.

With those registered for `grind` / `aesop`, the `autoParam` default discharges at the
call sites and the consumers read as before.

### Approach B: a refined index-list type (preferred)

Bundle the proof into the index-list type instead of a per-call argument:

```lean
abbrev ValidIndices (state : State) :=
  { idx : Array ValidatorIndex // ∀ i ∈ idx, i.toNat < (sszGet state validators).size }
```

`getActiveValidatorIndices` returns `ValidIndices state`, proving validity once at the
producer, and `getTotalBalance` consumes it. The proof rides with the data through the
call graph, so consumers carry no obligation. This changes the index-list signatures, and
in exchange the invariant is proved in one place rather than restated at every consumer.
It is the cleaner threading and the one to reach for first.

### Constraint: land it whole, with no interim `sorry`

Approaches A and B rest on the invariant lemmas. Until those exist, the index-list proof
obligations can only be filled by `sorry`, which the build reports as a warning on every
affected declaration. We will not carry that interim state. The data-derived reads wait
until the lemmas and the threading land together, so the build stays clean throughout. The
local-discharge shapes (loop, `size - 1`, `vget`) need no lemma and could land sooner; they
are grouped into the same pass so the read surface changes once. Every total read is correct
already; each gains a proof when the pass runs.

## The premises left on the epoch-success theorems

`processEpoch_succeeds` (`SPECS_ARCHITECTURE.md` §11.5) proves one call. Three things stand
between it and a chain of calls, and a fourth is the gap list it found.

### A reward bound read off the state

`RewardsWithin R v` is a premise of each call. A flag reward is
`base_reward * weight * U / (A * WEIGHT_DENOMINATOR)`, where `U` is the participating balance
of the previous epoch and `A` is the current active balance. A participant was active in the
previous epoch, so `U` is at most `A` plus the stake that left the active set at the epoch
boundary. Exits are rate-limited by the churn, so that stake has a bound, and `U / A` has one
with it.

The bound is not a state fact yet. It needs an exit-flow invariant: for each future epoch `e`,
the stake whose `exit_epoch` is `e` stays within the churn budget that
`earliest_exit_epoch` and `exit_balance_to_consume` record. Every operation that creates an exit
must keep it: voluntary exits, execution-layer exit requests, slashings, consolidation
requests, and the ejections in `processRegistryUpdates`. That is block-side work. Its shape is
a new `EpochSafe` field and a lemma `rewardsWithin_of_exitFlow` that discharges the premise
from it. The worst-case reward then follows from `EFFECTIVE_BALANCE_INCREMENT`, the churn
limit and the base reward.

### Liveness and room at the next epoch

`processSlots_epoch_ok` ends at an `EpochSafe b n` state moved one slot on. The moved state
is not `EpochSafe` itself: `live`, `slotRoom` and the exit room read the slot. `slotRoom` and
the exit room can take a further count, as the balance room does. Liveness cannot. A validator
active at `E + MIN_SEED_LOOKAHEAD + 1` can leave before `E + MIN_SEED_LOOKAHEAD + 2`. A bound
that keeps the active set nonempty needs the activation and exit queues, the same accounting
as the reward bound.

### Blocks between epochs

No block-side proof keeps `EpochSafe`. The block operations grow the deposit and consolidation
queues, change balances, and create exits. The fields that need work are the queue caps
(`depositCap`, `consolidationCount`), the balance room, and the exit room. The structural
fields (the indices in the consolidation queue and the effective-balance cap) need the same
work for `processConsolidationRequest` and the deposit path. Proved on every reachable state,
they would join `SimpleStateInvariants`.

### The hash premise

`ZeroChunksOften` is a premise on the hash. A deterministic route exists for the proposer
and sync-committee selections. A candidate with the full `MAX_EFFECTIVE_BALANCE_ELECTRA` passes
every threshold, and the shuffle visits each candidate once per round, so one such validator
fills the selection within `size` rounds. That route rests on the shuffle bijection (the
`computeShuffledPermutation` row of `PROOF_LEDGER.md`). It cannot cover the Gloas
payload-timeliness committee, whose candidate list is one slot's committees and need not
contain such a validator.

### The silent wraps

`DISCREPANCIES.md` lists the sites where the model wraps and the pyspec raises. Each fix makes
the model raise there, and the success proofs then need the room that keeps the site in range.
For the reward numerator, the balance fold and the proposer lookahead's start slot, that is a
new `EpochSafe` field each. For the sync-committee pubkeys, it is a field that every pubkey in
the registry passes `KeyValidate`, which the deposit signature check gives on the block side.
