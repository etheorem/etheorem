# Theorem vectors: the witness search

This document is the design of record for the witness search and its
code-level walkthrough, one home instead of two. It carries the
architecture's §9 subsections under their own numbers, so a citation of
`§9.4` resolves here; `THEOREM_VECTORS_ARCHITECTURE.md` §9 states each
part's rule in one line and points here. Section references (§1.2, §8.2,
§10, §11.1, §14.3) point into the architecture document, as throughout
the design docs. The unnumbered sections at the end carry the measured
and corpus material. Corpus numbers are as of stage 10 (30 records,
October 2026); they drift, the rules do not.

## How a theorem becomes search problems

The reader classifies a theorem's binders and matches its conclusion to a
shape (§7). The prepare pass (§8) unfolds the hypotheses' spec predicates
into comparisons and splits them into disjuncts under the `maxDisjuncts`
cap. `.iffTrue` doubles every disjunct into two problems, one per direction,
marked `_t` and `_f`. Each problem — a flat conjunction of comparisons
with an index and, when present, a side — is one run of the loop below,
one record directory, one independent failure. `canBuilderCoverBid_iff`
is the worked example: its true side came from the built searcher, its two
false sides from built and random.
`isValidIndexedPayloadAttestation_eq_true_iff_checks` has five problems,
four of which write vectors; the fifth has reported `notFound` since
stage 4 without failing its siblings. The block-input rule (§1.2)
applies before the search: such a theorem runs the base searcher alone,
and the report carries the answer.

### 9.1 The byte boundary

Every value that crosses between the elaborator and compiled code is SSZ
bytes. A witness is `Array ByteArray`, one entry per input in binder order.
The probe (§11) decodes inside compiled code. This is the same wire boundary
`ForkInterface` uses, for the same reason: the framework half cannot name a
fork type, and a `ByteArray` names none.

### 9.2 The searcher interface

```lean
/-- What one searcher answered. -/
inductive SearchStep where
  | candidate (a : Assignment) (tag? : Option WitnessSearcherTag := none)
      -- goes through the probe's check before it counts; `tag?` names the
      -- searcher the record carries, `none` for the proposing searcher's own
  | nothing                      -- this searcher has no candidate; try the next
  | unsat                        -- the searcher proved `¬P`; stop the loop

structure WitnessSearcher where
  tag     : WitnessSearcherTag
  /-- Can this searcher try this disjunct at all? -/
  applies : Statement → Disjunct → Bool
  /-- Produce one answer. -/
  search  : SearchCtx → Statement → Disjunct → SearchM SearchStep
```

`SearchCtx` carries the probe, the binding, the preset, the manual terms of
this line, and the draw memo of the random searcher. `SearchM` is `MetaM`.
The redraw loop's budget is the `randomDraws` option per disjunct, and the
per-run heartbeat budget (§14.3) bounds the rest.

The full order is hint (§9.8), manual, base, bit-vector, built (§9.9),
random, and the command assembles the list per line. A line with manual
terms runs manual then bit-vector, with no base searcher: the author chose
those inputs, and a `default` witness would ignore that choice, for the
disjuncts the manual terms win and for the disjuncts they fail alike. A
line without manual terms runs base then bit-vector. A theorem with a
block input runs base alone (§1.2). The hint searcher comes first on every
list, and the built and random searchers follow the bit-vector searcher.
The rest is cheapest first.

`Witness/Searcher.lean` holds the loop:

```
for searcher in searchers:
  if searcher.applies stmt disjunct:
    match ← searcher.search ctx stmt disjunct with
    | .candidate a => if probe.check disjunct.index a then return .ok a
                      -- the check is compiled `decide P`; a failed check falls
                      -- through to the next searcher
    | .nothing     => continue
    | .unsat       => return .error .unsat      -- no later searcher can help
return .error (.notFound tried)
```

A searcher that cannot produce a candidate the check accepts has produced
nothing. The check is the single arbiter. `notFound` names every searcher
that ran on the disjunct, whether or not it proposed a candidate.

### 9.3 The check

`probe.check : Nat → Array ByteArray → Bool` takes the disjunct index and
the assignment, decodes the assignment, and evaluates `decide (P x)` for
that disjunct's conjunction, compiled. It never throws: a decode failure is
`false`. The decode is strict, so a corrupt record fails: a byte string
of a width other than the type's, and a `Fin n` value at or above `n`,
decode to `none`.

### 9.4 The core searchers

**Base.** Serialize `default` for every input and check. This is the one
searcher that runs on a theorem with a block input.
`getPtcElseOffset_lt_same_slot` passes here: `slot = 0` has no hypothesis
to fail.

The `default` state is never a candidate. Neither the base searcher nor
the manual fill proposes `default` for an input of the binding's
`stateType`.
The spec is not defined on the empty, all-inactive validator set:
`computePtcFromFulu`'s balance-weighted selection runs to its fuel bound
on it, minutes per committee, and no result follows. A state input comes
from a manual term, a hint (§9.8), or the built searcher (§9.9). A theorem
with an uncovered state input gets `nothing` from both searchers.

**Bit-vector.** Applies when every uncovered input has a type in `{UInt8,
UInt16, UInt32, UInt64, Bool}` or an SSZ alias of one (`Slot`, `Epoch`,
`Gwei`, `ValidatorIndex`, …), and every hypothesis is a bit-vector formula
after the prepare pass. A `Fin n` input enters as a `UInt64` with the
bound `x < n`, the probe's own codec (§11.2); the corpus's `Nat`-form
comparisons over a `Fin.val` side bridge to the stand-in's `UInt64` form
in the same step, and a comparison the bridge cannot express stays for an
honest reflection failure. The
searcher poses `¬P` and calls `bvDecide'` from
`Lean.Elab.Tactic.BVDecide.Frontend`, whose result type is
`MetaM (Except CounterExample Result)`. A `CounterExample` carries
`equations : Array (Expr × BVExpr.PackedBitVec)`. Each equation pairs an
input with a value, and the searcher serializes each value to its SSZ
width. A `Result` means `¬P` is a theorem, so the searcher returns
`Failure.unsat` and the loop stops: no later searcher can find what does
not exist.

Before the call, the searcher grounds every maximal closed scalar subterm
of the hypotheses in compiled code and substitutes the literal: a read of
a manual or drawn input (`state.builders[0]!.balance`), a preset constant
(`UInt64.ofNat slotsPerEpoch`), a crypto gate under the verify-off
backend. The solver abstracts an unreduced constant as an opaque atom and
returns a model around it, which the check rejects; the grounding keeps
the formula over the free scalars alone. It runs before and after the
unfold, so the unfold's products ground too.

With manual terms, the searcher takes the handoff of the manual searcher.
The manual terms fix the containers. A scalar that sits inside a
computation over a manual input is *coupled* (the builder index of
`canBuilderCoverBid_iff`, a read index), and the searcher walks it over a
grid of its 64 smallest values, 128 grid points per disjunct at most. At
each point the manual reads are closed, the grounding turns them into
literals, and the solver takes the remaining free scalars. A `¬P` proof at
one grid point is a fact about that point, so the searcher moves to the
next and answers `nothing` when every point fails. Only the solve on a
line with no manual terms, where the formula carries the whole disjunct,
answers `unsat`. A coupled scalar the grid misses falls to a later
searcher.

**Random plus solve.** Applies when at least one input is a container and
no block input is in play. It runs after the bit-vector searcher on every
list, manual lines included, and on a disjunct the manual terms fail the
drawn bytes replace the author's terms in the candidate. The probe draws the container
inputs with their `SampleableExt` instances (`probe.sample seed size`),
serialized; draw `k` of a theorem is a pure function of the seed, the
size, and `k`, and the theorem's disjuncts share it. The searcher then
collects every maximal subterm of the hypotheses that mentions a container input
and has a scalar literal form, evaluates each one through `probe.reads`
at the draw, and substitutes the literal. A scalar that indexes a drawn
container is coupled, and it walks the grid of the manual handoff bounded
by the drawn list's length; a read past a drawn list's end is never
evaluated: the probe's `safe` face (§11.1) answers, per read of the plan,
whether the index stays inside its collection at the candidate's bytes,
and every searcher, the solver's fixed points, and the shrink gate on it
before the compiled `reads` or `check` runs. What remains is a bit-vector
formula over the scalar inputs,
and the solver takes it with no unfold, because the grounding already
replaced the spec calls. A per-point `¬P` is a fact about that draw and
point, never the disjunct's `unsat`. The loop redraws up to
`theorem_vectors.randomDraws` (default 64) times when no point of a draw
gives a candidate the check accepts, and answers `nothing` after the
last. `canBuilderCoverBid_iff` is the target: a draw fixes the builder's
balance and pending total, and the solver picks a `bidAmount` on each
side of the bound. At mainnet the searcher answers `nothing` before any
draw when a container input's type is the binding's state type, because a
mainnet state's fixed-length vectors overflow the draw's recursion.

**Manual.** Applies when the line names manual terms (§14.3). A manual term
fixes some inputs to author-written terms, serialized through the probe
(`probe.manuals`). When the manual terms cover every input, the candidate
is the terms' serialized bytes, checked like any other. When they cover a
strict subset, the searcher answers `nothing` and the bit-vector searcher
takes the partial assignment for the rest. The assignment is one and the
prepare pass may split the theorem into several disjuncts (§8.2), so the
author's claim is per theorem: a fully covering set of manual terms that
wins no disjunct is a build error, and a disjunct the manual terms fail
falls through to the next searcher like any other candidate. A partial
set carries no claim of that strength; when no searcher finds a witness
around it, the disjunct reports `notFound`.

### 9.5 Generation

`Sampleable.lean` supplies the instances the probe needs:

- hand-written `SampleableExt` instances for `UInt8` through `UInt64` and
  `Bool`; `UInt64` draws a small value most of the time and a full-range
  value otherwise, so a draw reaches both sides of a protocol constant
  such as `minDepositAmountG`;
- one generic instance for every type with `SSZRepr`, driven by SizzLean's
  type description: each field by its own instance, each list bounded by its
  SSZ limit and by `Gen`'s size parameter, each fixed-length vector at its
  length, and the value rebuilt through the same structure the `SSZRepr`
  instance walks.

The draw runs in the probe's compiled `sample` face (§11.1). Each input
position's seed is hashed with the position, and each draw's seed with the
draw index, before it reaches the generator, so no two positions and no
two draws share a generator state, and the same `theorem_vectors.seed`
and size draw the same bytes.

The generic instance is what makes a `BeaconState` an input the search
produces on its own. A mainnet state has fixed-length vectors a minimal state
does not (`EPOCHS_PER_HISTORICAL_VECTOR` is 65536 against 64), and shrinking
cannot cut a fixed length. The size parameter bounds the lists, and the
report records the time per record so mainnet cost stays visible.

### 9.6 Shrink

After a witness from the random searcher passes, `Witness/Shrink.lean` asks
`probe.shrink a` for candidates, one shape step per container input: a
list's length cuts first (the half prefix, then the last element dropped),
then one element cut per field, so a smaller state is what the budget
buys first. The loop walks one call's whole list and keeps every
candidate that passes the check and whose wire size does not exceed the
current witness's; each kept candidate costs one step. It asks again
from the kept witness until no candidate passes or the budget
(`theorem_vectors.shrinkSteps`, default 40) runs out. The budget is
small because every candidate costs one compiled `decide` over a decoded
state. Scalars found by the solver are not shrunk, because a solver value
is a boundary point and shrinking would move it. A state from the built
searcher is shrunk by its knobs and never by its fields (§9.9).

### 9.7 Further searchers

One more searcher fits beside the built searcher once it exists. **Corpus
pre-states.** The pyspec vectors hold thousands of `pre.ssz` states under
`~/.cache/sizzlean/<tag>-<preset>/`. A searcher reads the states for the
fork and preset, filters them with the check, and passes survivors to the
solver the way the built searcher passes a built state. They come from disk and need
no spec run, and some carry valid signatures and matching hashes, which
helps with sparse hypotheses.

It is one more `WitnessSearcher` value in the list. Nothing else changes.

### 9.8 Hints: the first searcher

A search can be slow, and its result can change when the search changes. A
**hint** records how a witness was found, with enough data to rebuild the
candidate without searching. It is a hint and nothing more: the check still
decides, and a hint the check rejects sends the disjunct through the full
search.

**The hint searcher.** `Witness/Hint.lean` supplies a `WitnessSearcher` that
runs first. It applies when a hint exists for the theorem, preset, and
disjunct, and the mode is not `ignore`. Its `search` rebuilds the candidate
through the probe, and the loop's check validates it like any other
candidate. On success the record's `witnessSearcher` is `.hinted orig`. On
failure the loop continues with the next searcher, and the outcome line
says the hint failed.

**What a hint holds.** Only what the search decided, never the witness
bytes. A mainnet state is megabytes, and a hint must stay small enough to
commit.

| Searcher | Hint data |
| --- | --- |
| base | nothing beyond the searcher tag |
| bit-vector | the scalar literals the solver chose |
| built | the builder name, the knobs, the solved scalars |
| random plus solve | the generator seed, the size, the draw index, the solved scalars |
| manual | nothing beyond the searcher tag |
| corpus state, when it exists | the vector path and the state root |

The random draw replays from the seed, size, and index, because `Gen` is a
pure function of those. The entry records the candidate before the shrink,
and the replayed candidate goes through the same shrink loop (§9.6), which
keeps the records byte-identical across builds. The hint skips the redraw
loop and the solver. It does not skip the shrink, and for a state theorem
the shrink is the replay's whole cost: `canBuilderCoverBid_iff` replays in
20 seconds with the default budget and in under one second with the
budget at zero. The plan's stage 6 records the shrink's path in the entry, the
accepted candidates' indices per call, so a replay checks those
candidates alone.

**Where hints live.** In the spec half, committed:

```
EthCLSpecs/TheoremVectors/Hints/<fork>/<thm>.json
```

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "fingerprint": "0x…",
  "entries": [
    { "preset": "minimal", "disjunctIndex": 0, "side": true,
      "fingerprint": "0x…", "witnessSearcher": "random", "seed": 7,
      "size": 8, "draw": 3,
      "scalars": { "builderIndex": "3", "bidAmount": "32000000000" } },
    { "preset": "minimal", "disjunctIndex": 1, "side": false,
      "fingerprint": "0x…", "witnessSearcher": "random", "seed": 7,
      "size": 8, "draw": 3,
      "scalars": { "builderIndex": "3", "bidAmount": "40000000001" } } ] }
```

The fingerprint is FNV-1a over the theorem's name, the rendered input and
output types, the hypotheses and the conclusion's sides as the probe
rendered them, and the `SSZType` shape hash of every container input. The
shape hashes move with the preset, because a derived container's caps are
the preset's, so each entry carries the fingerprint of the run that wrote
it; the file-level field repeats the last run's and decides nothing. A
disjunct index names one DNF disjunct of the prepare pass (§8.2), so the
two sides of an `.iffTrue` never share one. Scalars are decimal strings,
because a `UInt64` can exceed the integer range a JSON reader is sure to
keep. The file is JSON (§12.3): the generator is its only
reader, and `Lean.Json` gives both directions from the hint structure's
derived instances.

An ordinary build never writes into the source tree, the same rule the
proof-coverage baseline follows. New and replaced hints go to
`<outDir>/hints/<fork>/<thm>.json`, and `just theorem-vectors-hints-update`
copies them over the committed ones. The diff reaches review, so a changed
witness is visible as a changed hint.

Every run writes its theorem's file, whether or not it won anything: a
replay re-records the entry it consumed under the current fingerprint,
so the file a replayed build writes is the file it read, and a run that
wins nothing replaces its preset's entries with none, so a survey's
candidate never outlives the line that overrode it. The merge keys on the
preset, and a second preset's run keeps the first's entries. The update
recipe copies and never deletes: a theorem that stops winning leaves its
committed file in place, and the report shows it as `failed` until someone
removes the file.

**The mode.** One option, `theorem_vectors.hints`:

| Value | Meaning |
| --- | --- |
| `use` (default) | read hints; search when one is missing or fails; write new hints to the output tree |
| `ignore` | search everything; write new hints |
| `require` | a hint the check rejects, or a disjunct whose witness came from a search, is an error; a disjunct no searcher wins reports `notFound` as in `use` |

**Staleness.** Each entry carries the fingerprint of the run that wrote
it. A mismatch with the current fingerprint does not reject the hint,
because the check decides. The outcome line records `hint: stale-replayed`
or `hint: stale-failed`, so the report shows which hints a spec change
touched. A new field in `BeaconState` changes every random draw of that
fork, and every random hint for the fork goes stale at once. That is the
expected behavior, and one run of the update recipe refreshes them.

**Why hints and the fixed seed both exist.** `theorem_vectors.seed` makes a
build deterministic. A hint adds two things. Cost: a build replays instead
of searching, which matters once mainnet runs. Stability: a new searcher
in the list, a different draw budget, or a new `Plausible` version would
otherwise change every random witness, and a client that holds the old
vectors would see churn. With hints, a witness changes only when the check
rejects it or when someone runs the update recipe on purpose.

A reused scalar witness (§10) writes a hint for the second preset too, so
its replay does not depend on the first preset having run.

### 9.9 State builders: the `built` searcher

The state is the hard half of a witness. A random draw produces a state
field by field, and that state breaks invariants the spec maintains: a
validator with an exit epoch before its activation, a slot behind its
checkpoints, a balance list longer than the validator list. A hypothesis
that depends on those invariants is sparse under random draws, and a client
replaying such a vector can reject the state for a reason that has nothing
to do with the theorem.

A **state builder** runs the spec itself to produce a reachable state from a
few knobs. Each fork has a small catalog, and the search tries the catalog
before it draws at random.

**The catalog.** One builder per row, in `EthCLSpecs/TheoremVectors/Builders/<Fork>.lean`:

| Builder | Builds | Knobs used |
| --- | --- | --- |
| `genesis` | the fork's genesis state from generated deposits, every validator active, the way the pyspec's `create_genesis_state` does | `validators`, `balance` |
| `advanced` | `genesis`, then `processSlots` to the target slot, so epoch transitions run and the state carries real justification, committees, and RANDAO mixes | `validators`, `slot` |
| `upgraded` | the parent fork's `advanced` state through the fork's own upgrade, so the fork-specific fields hold the values the upgrade gives them | `validators`, `slot` |
| `withQueue` | `advanced` plus pending deposits, withdrawals, or builder payments appended through the spec's own operations | `validators`, `slot`, `queue` |

Deposits need pubkeys and withdrawal credentials. Under the verify-off
backend any 48-byte value verifies, so a builder derives them from the
validator index, as the pyspec's `pubkeys` list does. A builder that needs a
real signature is outside this catalog. The catalog is per fork: Fulu has no
parent in the repository, so its catalog has no `upgraded` row.

**The interface.** The knobs are one framework type, so the framework half
can enumerate a grid without naming a fork:

```lean
structure Knobs where
  validators : Nat := 8
  slot       : Nat := 0
  balance    : Nat := 32000000000
  queue      : Nat := 0
  deriving Repr, BEq, Hashable
```

A builder is a fork constant of type `[Preset] → [Config] → Knobs → BeaconState`.
The binding lists its builders by name, as it lists the preset constants:

```lean
  builders := #[("genesis",   ``Builders.Gloas.genesis),
                ("advanced",  ``Builders.Gloas.advanced),
                ("upgraded",  ``Builders.Gloas.upgraded),
                ("withQueue", ``Builders.Gloas.withQueue)]
```

The probe gains one function, `build : (builder : Nat) → Knobs → ByteArray`,
which runs the named builder with the preset's instances bound and
serializes the state. A builder is a manual input with knobs that every
theorem of the fork gets for free, and it takes the manual terms' path
through the probe.

**The searcher.** `Witness/Built.lean` supplies the `built` searcher,
between the bit-vector and random searchers. It applies when exactly one
input has the binding's state type. Any other container input is drawn the
way the random searcher draws it, and the scalars are solved. It walks the knob grid,
cheapest first:

| Step | Builder | Knobs |
| --- | --- | --- |
| 1 | `genesis` | 8 validators |
| 2 | `advanced` | 8 validators, the first epoch boundary |
| 3 | `upgraded` | 8 validators, the first epoch boundary |
| 4 | `advanced` | 16 validators, slot 40 |
| 5 | `withQueue` | 16 validators, slot 40, queue 4 |
| 6 | `advanced` | 64 validators, slot 40 |

For each built state the searcher evaluates the container-only reads,
solves the scalars with the bit-vector searcher, and checks, the same loop
the random searcher runs over a draw. The random searcher runs only when
the grid fails.
The order is right because a built state is reachable and a random one is
not, so a built witness is worth more to a client. The option
`theorem_vectors.builtSteps` caps the grid, and the cap is lower at mainnet
by default, where `advanced` runs the spec over 65536-long vectors.

**Shrinking.** A built state is never shrunk field by field, because that
would break what the builder guaranteed. The searcher shrinks the knobs
instead: fewer validators, a lower slot, a shorter queue. The grid order is
the shrink order.

**The cache.** A built state is a pure function of the fork, the preset, the
builder, and the knobs, so its bytes are cached in the output tree:

```
<outDir>/built/<fork>/<preset>/<builder>/<validators>-<slot>-<balance>-<queue>.ssz
<outDir>/built/<fork>/<preset>/<builder>/<validators>-<slot>-<balance>-<queue>.stamp
```

Every theorem of the fork shares the entry, so a builder runs once per
build for each grid step it reaches, however many theorems use it. The
cache also outlives the build on a developer machine. The `.stamp` file
holds the Lake trace of the fork's `Builders` module, read from the `.trace`
file beside its `.olean`. Lake folds the traces of every import into that
file, so it changes when the module or anything it imports changes, which
includes the fork body. A spec change therefore invalidates every entry of
that fork, and the next build rebuilds them. `just theorem-vectors-clean` removes the cache with the rest of the
tree. The cache is never committed, because a mainnet entry is megabytes
and CI rebuilds it once per job.

**Hints.** A built witness has the smallest hint of any searcher: the builder
name, the knobs, and the solved scalars. It stays valid across `Plausible`
versions, because no generator is involved.


## Addendum: the draw memo and the handoffs

The draw memo holds one `Option ByteArray` slot per input position, not
one array per draw. That per-position shape is what lets searchers share
work: the built searcher fills the state position and leaves side positions
open, and a random win at the same draw index completes them (the
built-drive tests pin the partial overwrite). Partial manual terms are the
same idea at the assignment level: a term pins a subset, later searchers
search around the pins, and `notFound` only when all fail. A disjunct
every searcher failed records a `notFound` hint entry (added in stage 6),
and a non-stale replay skips that search entirely, which is how the
payload-attestation theorem's fifth problem stopped costing a full redraw
budget.

## Addendum: budgets

| Knob | Default | Bounds |
| --- | --- | --- |
| `randomDraws` | 64 | redraw attempts per disjunct |
| `randomSize` | — | the draw size scale |
| `shrinkSteps` | 40 | shrink walk length |
| `builtSteps` | 3 at mainnet, more at minimal | the builder knob grid depth |
| heartbeat budget | per run | total interpreted-elaboration work per run (§14.4) |

A searcher that exhausts its budget answers `nothing` and the next one
runs. A disjunct no searcher satisfies reports `notFound` with the tags it
tried, and (once hinted) skips the re-search on later builds.

## Addendum: costs, measured

The preset is the cost axis. A minimal `BeaconState` serializes to about
15.6 KB; a mainnet one to about 3.1 MB, a 200× difference driven by the
fixed-length vectors (`EPOCHS_PER_HISTORICAL_VECTOR` 65536 vs 64). Every
draw, evaluation, hash, shrink candidate, and record write scales with
it; shrinking cannot cut a fixed length. Measured anchors from stages 7
and 8: the built searcher's `processBuilderPendingPayments` took 2.0 s at
minimal and 18.8 s at mainnet; manual wins went from 1-2 s to about 9.4 s.
So a mainnet attempt costs roughly 5-10× a minimal one, with the same
number of attempts: the search's logical work is preset-independent, the
per-attempt price is not. Searcher economics at one preset, from the
corpus: base is free, bitVec is solver seconds, built is seconds (replay:
sub-second), manual is check-only, random is draws times the check price.

## Addendum: the corpus map

Which searcher won each of the 30 records, as of stage 10:

| Fork | Preset | Searcher | Records |
| --- | --- | --- | --- |
| fulu | minimal | manual | 4 |
| fulu | minimal | random | 1 |
| fulu | mainnet | manual | 4 |
| gloas | minimal | base | 3 |
| gloas | minimal | bitVec | 2 |
| gloas | minimal | built | 5 |
| gloas | minimal | random | 2 |
| gloas | minimal | manual | 5 |
| gloas | mainnet | manual | 2 |
| gloas | mainnet | built | 1 |
| gloas | mainnet | reused-minimal | 1 |

Sparse hypotheses are the norm: manual terms and builders produced 21 of
the 30. Pure defaults and solving cover the trivial tail, and the one
preset-transfer record proves the reuse path.

## Addendum: known limits and the composition future

- The random sampler cannot draw mainnet states (the recursion cap in
  §9.4). Making the draw iterative is a bounded fix; after it, random
  search at mainnet costs the measured 5-10× per attempt.
- The coupled grid bounds an index at 64 values and 128 points; a
  coupled scalar beyond that falls to a later searcher. An SMT solver
  with array theory would dissolve the grid, and enters as one more
  searcher: the check, not the solver, is the soundness anchor.
- Composition inside a disjunct exists as three hardwired handoffs
  (manual plus solver, partial manual terms, built plus random through the
  memo). The
  general form, a residual-disjunct recursion where one searcher's partial
  assignment becomes the next searcher's problem, is sketched in the
  plan's sparse-hypotheses risk: solve state fields from the comparison
  atoms and edit a built or drawn state instead of redrawing it.
- Block inputs stay out of scope (§1.2) until a block builder or corpus
  blocks exist; `FUTURE_WORK.md` holds the corpus pre-state searcher
  (§9.7), which composes with everything above as one more searcher.
