import SizzLeanBench.Timer
import SizzLeanBench.Runner
import SizzLeanBench.Fixtures
import SizzLeanBench.Scenarios.ColdRoot
import SizzLeanBench.Scenarios.BatchedWrites
import SizzLeanBench.Scenarios.BlockProcessing
import SizzLeanBench.Scenarios.ColdRootLarge
import SizzLeanBench.Scenarios.BatchedWritesLarge
import SizzLeanBench.Scenarios.BlockProcessingLarge
import SizzLeanBench.Scenarios.FuluStateTransition

/-!
# `SizzLeanBench`: microbenchmark library root

The bench is structured as a **scenarios × configurations ×
fixtures** grid. Every row measures the *same user code*
through different runtime choices, so the TSV reads as a clean
comparison rather than a collection of independent
microbenches.

```
just bench                       # writes packages/SizzLean/bench/<timestamp>.tsv
just bench-diff before.tsv after.tsv
```

## Two configurations

Both columns call the *same* user-facing methods, only the
construction differs. After construction, the user writes
`sszUpdate` / `.hashTreeRoot` / `.serialize` either way.

| Config | Construction | Effect |
|---|---|---|
| **pure** | (none, plain `T`) | `SSZ.hashTreeRoot Sha256 v` / `SSZ.serialize v` / `{ v with f := x }`. No library wrappers. |
| **cached** | `SSZ.FastBox v` | Every transparent optimisation (pending overlay, root Thunk memo, bytes Thunk memo, `@[specialize]`) fires automatically. |

There is no "Cached + Batch" or "Cached + Consing" column.
Both ship as *library primitives* (`sha256BatchCombine`,
`Node.mkPair`) but are not invoked from `merkleRootWithCache`'s
recursive walk or from `Node.ofShape` / `setAt`. They are not
on the user's normal interface, so they stay out of the bench.

## Three fixtures

| Fixture | Shape | Approx size | Depth | Tier |
|---|---|---|---|---|
| **Validator**       | 8 fixed-size fields (consensus `Validator` layout) | ~144 B | 4 | small |
| **ValidatorSet16**  | `Vector Validator 16`   | ~2.3 KB | 8  | small |
| **ValidatorSet256** | `Vector Validator 256`  | ~36 KB  | 12 | **large** |

Small fixtures (`Validator`, `ValidatorSet16`) exercise the
wrapper-overhead regime; the large fixture (`ValidatorSet256`)
exercises the per-operation amortisation regime where each
operation pays for hundreds of pair-hashes.

## Six scenarios, all reflecting realistic workloads

Each scenario is an operation sequence that maps to a real
consensus-client pattern. Artificial shapes (repeated reads of an
unchanged root, write-root-write-root cycles, repeated serialisation
of the same bytes) are excluded. They don't appear in production
consensus code, so measuring them would mislead. The six retained:

### Small tier (S1–S3, quick measurements, ~1 s wall-clock)

| # | Sequence | Production analogue |
|---|---|---|
| **S1 ColdRoot**        | build, root                          | Diagnostic sentinel: Box construction + first-walk overhead. Regressions here surface before they confound S2/S3. |
| **S2 BatchedWrites**   | build, set × 32, root                | One slot's state transition (small fixture). Many writes, one root. |
| **S3 BlockProcessing** | build, (set × 4, root, serialise) × 8 | Multi-slot processing: 8 consecutive slots, each applying writes + computing root + serialising. Closest to "consensus client running" on the small fixture. |

### Large tier (S4–S6, production-shape, longer wall-clock)

| # | Sequence | Production analogue |
|---|---|---|
| **S4 ColdRootLarge**         | build, root                                | Same sentinel as S1 on `ValidatorSet256` (depth 12). |
| **S5 BatchedWritesLarge**    | build, set × 512, root                     | One slot's state transition at near-mainnet scale. |
| **S6 BlockProcessingLarge**  | build, (set × 8, root, serialise) × 32     | Multi-slot processing at scale: 32 slots × per-slot work. The best single-number predictor of real-world cache performance. |

Total row count:

- **Small (S1, S2, S3):** 3 scenarios × 2 fixtures (Validator, VS16) × 2 configs = **12 rows**
- **Large (S4, S5, S6):** 3 scenarios × 1 fixture (VS256) × 2 configs = **6 rows**
- **Grand total: 18 rows**

## Layout

* `Timer.lean`: `IO.monoNanosNow` helpers.
* `Runner.lean`: TSV output + `runBench` driver.
* `Fixtures.lean`: `ValidatorShape`, `ValidatorSet16`,
  salt-driven builders, `consume` sink helper.
* `Scenarios/{ColdRoot, BatchedWrites, BlockProcessing,
  ColdRootLarge, BatchedWritesLarge,
  BlockProcessingLarge}.lean`: one file per scenario; small-
  tier files emit four TSV rows (Validator + VS16 × pure +
  cached), large-tier files emit two (VS256 × pure + cached).

## TSV column shape

```
label                                              iterations   median_ns   mean_ns   stddev_ns   min_ns   max_ns
```

`diff -u before.tsv after.tsv` is the comparator. The label
spells out the scenario, fixture, and config: `S<n>
<ScenarioName> · <Fixture> · <pure|cached>`. Grep by scenario,
by fixture, or by config as needed.
-/
