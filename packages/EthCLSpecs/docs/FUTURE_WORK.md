# Future work

Deferred changes for EthCLSpecs. Each entry records what is left, why it waits, and
the shape it will take, so a later pass can pick it up whole rather than rediscover it.

## Provable indexing for the remaining total reads

### What is left

The error model already splits indexed reads two ways. A read whose index arrives from
block or external input rejects through `Except IndexError` (`sszGetIdx` / `getAt` /
`bitlistGetIdx` in `Spec/State.lean`, lifted by `liftErr`); a guarded read with an explicit
`assert (i < size)` reads the proof-carrying `xs[i]'hb.down` through `assertH`. What stays
on a total `[i]!` or `vget`, the provability residual, is every read whose index is in
range by construction but does not yet carry the proof. A proof over one of these unfolds
through the `Inhabited` default rather than a bounded lookup. The shapes:

- **Pure data-derived index reads.** The committee and weighted-selection helpers:
  `computeCommittee`'s permutation and `indices` reads after its position assert, and
  `cbwsAux`'s `perm`, `effBals`, and `indices` reads. The index is a permutation entry
  or a position below a length the helper already holds. Approach A or B below, and the
  invariant lemmas they rest on. The foundational accessors and index-list consumers
  (`getTotalBalance`, `getTotalActiveBalance`, `getUnslashedParticipatingIndices`,
  `getInactivityPenaltyDeltas`) read through `getAt` and raise `IndexError` as the pyspec
  does, so they are outside this residual. A proof parameter on one of them would trade
  that raise for an obligation on every caller.
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

Outside this residual, and staying as they are: the element writes
`{ state with field := state.field.set! i v }` and `state.field.modify i f`. SizzLean's
`set!` and `modify` leave the collection unchanged past the end. They are total by design,
and they mask no read.

### Approach A: a proof parameter

A query that reads `validators[i]` for `i` drawn from `indices` takes the bound as an
optional proof, Lean's `autoParam`:

```lean
forkdef getTotalBalance (state : State) (indices : Array ValidatorIndex)
    (hvalid : ∀ i ∈ indices, i.toPlainNat < state.validators.size := by …) :
    Checked Gwei := do
  let validators := state.validators
  let total ← indices.attach.foldlM (fun acc ⟨i, hi⟩ =>
    acc + (validators[i.toPlainNat]'(hvalid i hi)).effectiveBalance) (0 : Gwei)
  return max total Const.effectiveBalanceIncrementG
```

The sketch uses `getTotalBalance` because its call graph shows the cost. The
implemented body reads through `getAt` and raises `IndexError` instead (see the first
shape above). The fold runs over `indices.attach`, so each step carries
`hi : i ∈ indices`, and `hvalid i hi` discharges the read's bound. A plain `foldlM`
lambda gives `i` but no membership, which is why `.attach` is needed. The read is then
`[i]'(…)`, proof-carrying, with no default. The checked `Gwei` add keeps its range
fault, so the result stays `Checked`.

The definition site changes little: the parameter, `foldlM` to `attach.foldlM`, and the
proof term in place of the raising read. The cost lands at the callers. The default tactic cannot
prove `∀ i ∈ indices, …` for an arbitrary `indices`, so each call site owes the proof. A
spike on `getTotalBalance` with a `by sorry` default put the obligation at
`getTotalActiveBalance`, the reward-delta helpers, and the Gloas mirrors. The way to make
most call sites free is a small set of invariant lemmas the default tactic can find:

- `getActiveValidatorIndices` returns in-range indices,
  `∀ vi ∈ result, vi.toPlainNat < state.validators.size`, a loop invariant over its
  `for h : i in [0 : validators.size]` and the checked `CLUint64.ofNat? i` cast.
- the parallel-length invariant `state.balances.size = state.validators.size`, for the
  reward and penalty reads that index `balances` at a validator index.

With those registered for `grind` / `aesop`, the `autoParam` default discharges at the
call sites and the consumers read as before.

### Approach B: a refined index-list type (preferred)

Bundle the proof into the index-list type instead of a per-call argument:

```lean
abbrev ValidIndices (state : State) :=
  { idx : Array ValidatorIndex // ∀ i ∈ idx, i.toPlainNat < state.validators.size }
```

`getActiveValidatorIndices` returns `Checked (ValidIndices state)`, proving validity once
at the producer, and `getTotalBalance` consumes it. The proof moves with the data through the
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
