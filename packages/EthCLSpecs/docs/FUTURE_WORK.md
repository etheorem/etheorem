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
  index.

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

## Corpus pre-states as a witness searcher

### What is left

The pyspec vectors hold thousands of `pre.ssz` states under
`~/.cache/sizzlean/<tag>-<preset>/` (`THEOREM_VECTORS_ARCHITECTURE.md` §9.7). A
searcher reads the states for the fork and the preset. It filters them with the
check. It passes the survivors to the solver the way the built searcher passes a
built state. The states
come from disk and need no spec run. Some carry valid signatures and matching hashes.
That helps the theorems with sparse hypotheses, which the built catalog cannot serve.
A builder derives its keys from the validator index under the verify-off backend. A
builder that needs a real signature sits outside the catalog
(`THEOREM_VECTORS_ARCHITECTURE.md` §9.9).

### The shape it takes

One more `WitnessSearcher` value in the list. Nothing else changes. A corpus hint's data is
the vector path and the state root (§9.8's table), so the hint stays small enough to commit.

### Why it waits

No stage carries it. The searcher reads the pyspec vectors from disk, and the
`theorem-vectors` job downloads and pins no vector set today, so the corpus it needs does
not exist on a CI run. Heze waits one step further. Most of its theorems take a block or
store input. Block inputs come back with corpus blocks or a block builder, and the risk
list in `THEOREM_VECTORS_PLAN.md` puts neither in a stage.

## The next producer plan: the request-handler theorems

All three entries share one future consumer: the `withdrawal_request` and
`deposit_request` theorem families, the pyspec-operations plan's §0.
`THEOREM_VECTORS_PLAN.md`'s closing note records that plan.

### The reduction lemma over the `Option` lookups

The G2, G3, and G4 proofs in `Proofs/Fulu/ConsolidationRequest.lean` re-derive the switch
and request-gate discharges inline. Four copies exist, counting the ladder's own. The
shape is a second reduction lemma over the `Option` lookups, which the four proofs share.
The change waits because the statements are settled and the repetition is proof-local.

### The pubkey bridge's visibility

`validatorIndexByPubkey?_pureState` is public while its sibling bridges are private. The
decision, a re-export from `Proofs/Fulu.lean` or a `private` mark, waits for the lookup's
second consumer. The request-handler theorems do `findIdx?`-style lookups too.

### The mainnet-cost rule

Each both-preset consolidation line's mainnet check costs 15 to 18 seconds, and the
mainnet `BeaconState` encode/decode dominates. Three lines run at both presets now. A
fourth puts the per-generation mainnet cost near a minute. The rule: measure again before
adding the next both-preset line.

## Generator caveats waiting for a consumer

Each entry records a caveat in the generator with no consumer today. The entry names the
consumer that would make the caveat matter.

### The `Snappy.encode` size bound

The all-literals snappy writer in `EthCLLib/TheoremVectors/Snappy.lean` documents the
`2^32` input bound and does not check it. Above the bound the bytes it writes are
undecodable. No in-tree caller approaches the bound, so the writer stays as it is. The
shape, if an external caller ever appears, is a checked variant with an `Except String`
return.

### The operand-free operations handler

A future operations handler with no operand produces single-state records. The concrete
case is Gloas `process_withdrawals`. The epoch_processing format takes its runner's
name and pins the runner, so no format accepts such a record today:
`Formats.epochProcessingAccepts` requires the
`epoch_processing` runner, and `Formats.operationsAccepts` matches exactly two inputs.
The record stays unaccepted until the operations format grows an operand-free variant.
When that variant lands, its check still builds `caseMeta` from the constant
`{ blsSetting := 2 }`, leaving `executionValid` at its default, `true`. Both caveats
wait for a fork binding that maps such a handler. The binding author reads §13.6 of
`THEOREM_VECTORS_ARCHITECTURE.md` and this entry.
