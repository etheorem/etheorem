# Spec arithmetic transition plan

Status: planned. The production transition has not started.

This temporary plan moves the current implementation to
[SPEC_ARITHMETIC.md](SPEC_ARITHMETIC.md). Remove this file when the final acceptance
stage completes. Keep lasting authoring rules in that contract and lasting findings
in `IMPLEMENTATION_NOTES.md` or `DISCREPANCIES.md`, as appropriate.

Scope: all consensus-spec code in `EthCLSpecs`, including Fulu, Gloas, Heze, shared
forms, constants, configuration values, helpers, containers, upgrades, and fork choice.
The transition includes the required `EthCLLib` and `SizzLean` changes, proof repairs,
runner interfaces, and benchmark fixtures. An unlisted numeric alias remains in scope.

## 1. Decisions

The user settled these decisions on 2026-11-15:

| Subject | Decision |
|---|---|
| Cost | Keep native-backed wrappers. Record compilation and run-time costs. Complete the transition regardless of those costs; there is no performance stop threshold. |
| Authoring | Explicit `Checked` result ascriptions are the reliable baseline. Compare them with bounded automatic elaboration. Preserve the same semantics in either form. |
| Binding | Bind local checked computations immediately in fork bodies. Check this through source review and behavior tests during the transition. |
| Configurations | Preserve checked behavior for arbitrary accepted configurations. Total operations require explicit premises. |
| Widths | Start with native-backed 64-bit and 8-bit wrappers. Share laws and generation; measure before choosing a generic width-indexed representation. |
| Coverage | Finish all consensus-spec arithmetic in `EthCLSpecs`, including sites omitted by the spike. |
| Linters | Defer implementation until after the transition. The separate [SPEC_ARITHMETIC_LINTING.md](SPEC_ARITHMETIC_LINTING.md) records that future work. |

The immediate-bind rule applies from the first migrated body. Linter implementation,
linter activation, and a new linter CI gate are outside this plan's completion criteria.
Existing project checks such as `just lint` continue to run.

## 2. Starting point and evidence

The branch started at `0215460`, with the original design draft over `417ca90`.
The spike lives on `specs-arithmetics-spike` at
`ff520aa5003804601bc72985f8429cce676d1b5b`. Re-author production changes against the
contract and pinned Python source. The spike provides examples and measurements.

Local source records, outside Git:

- `mb/spec-arithmetics-spike/README.md`, the index.
- `mb/spec-arithmetics-spike-plan.md`, the 24 findings and baseline table.
- `mb/spec-arithmetics-spike/reports/stage-8.md`, the final report.
- The earlier reports and reviews, especially Stages 2, 4, 5, and 7.

The following facts are carried here so implementation does not depend on local notes:

| Evidence | Consequence for the transition |
|---|---|
| `Gwei`, `Epoch`, `Slot`, `ValidatorIndex`, and flags moved across three forks in the spike | Their ports demonstrate the approach; inspect every formula again against Python |
| Full vector counts matched the baseline at both presets | Preserve individual case outcomes and add arithmetic edge pins absent from the vectors |
| 36 smoke failures came from packing wrappers as composite SSZ elements | Fix shape classification before changing any container field type |
| The scoped literal check left a wrapping `OfNat` instance accessible | Make literal construction safe without relying on scope |
| Three indexed-read probes favored ambient-monad errors | Keep index errors typed in pure helpers too; replace the spike's arithmetic-fault `getAt` |
| Non-literal `Nat` operands and prior do-binds exposed elaboration failures | Test these shapes before migration; support explicit result ascriptions |
| The spike repaired proofs without adding axioms beyond the baseline's existing set | Supply reusable arithmetic laws first and repair proofs within each unit migration |
| Coverage ended at 80 claims and 20 characterized declarations | Preserve contracts and tags; counts alone cannot establish preservation |
| Several units, constants, widths, and time values remained raw | Build a complete inventory instead of copying the spike's stopping point |

The first Fulu `Gwei` experiment changed 11 of 23 top-level modules and exposed 79
distinct build errors. It changed 14 function signatures. These figures describe a
partial port; they do not bound the full transition.

### Recorded cost

| Measurement | Baseline | Spike |
|---|---|---|
| Cold `lake build EthCLSpecs` | 6m58s, 607 jobs | 10m58s to 10m59s, two runs, 621 jobs; reported ratio 1.57 |
| Default profile | Reference | About +0.3% |
| Gloas mainnet epoch-processing suite | 154 cases, 124.50s | 154 cases, 124.95s; +0.36% |

The epoch measurement covers a vector suite, rather than an isolated `processEpoch`
call. Only `Fulu/EpochProcessing` received a module profile. Its do-element elaboration
grew by 63ms. This does not identify the operator elaborator's share or establish that
the slowdown is spread across modules. Parallel wall time divided by job count cannot
locate the cause. The spike's old 1.5-times stop threshold no longer applies.

### Initial analysis of an abbreviation alternative

A standalone probe on Lean 4.34.1 checked `abbrev CheckedUInt := UInt64` with a
high-priority scoped `HAdd CheckedUInt CheckedUInt (Except Unit CheckedUInt)`:

| Expression | Observed result |
|---|---|
| `a + b`, both binders typed as the alias | Selects the scoped checked operator |
| `a + 1`, inferred result | Selects raw `UInt64` addition; maximum plus one becomes zero |
| An oversized literal typed as the alias | Wraps to zero |
| `a + b` outside the operator scope | Uses raw wrapping addition |

The alias is definitionally equal to `UInt64`, so it supplies no separate instance
boundary. These results agree with the earlier `ScopedTest.lean` experiment.
This rejects abbreviation plus scoped instances as a complete solution. It makes no
claim about compile-time savings, which have not been measured for that candidate.

A syntax-controlled alias design would need extra machinery to prevent raw operators,
literal wrapping, and replay differences. The transition uses native-backed structures.
Stage 3 settles the authoring implementation on that representation.

## 3. Working rules and gates

- Read the pinned Python body before changing a formula. Old Lean code can hide raises
  in `Nat` intermediates and `UInt64.ofNat`; compiler errors do not enumerate those sites.
- Treat each unit migration as a complete slice through all forks, interfaces, tests,
  and proofs. Keep proof imports present at each completed integration point.
- Retype constants with their first affected consumer. Keep a list of temporary
  raw/checked crossings, with a reason and the stage that removes each one.
- Review every changed bind, branch, loop, cast, store, sum, and mixed `min`/`max`.
  Pair each targeted failure pin with a nearby success that reaches the same operation.
- Keep structural counters and termination measures separate from spec arithmetic.
  Bytes used as data remain codec values; arithmetic on a spec integer uses checked types.
- Record commands, revisions, case identities, skips, expected failures, and results.
  Do not hide a changed answer by moving its case out of scope.
- After proof changes, run `just proof-coverage-update`, inspect the generated diff,
  and run `just proof-coverage-check`. Record statement and axiom changes.
- Run builds and vector sweeps sequentially during measurements. Use a fixed job count
  and record cache state. Measure cold, no-op, and representative incremental builds.
- Record cost regressions and proceed. Optimize only with evidence that the change
  preserves the semantic contract; a performance threshold cannot block completion.
- Mark a task complete only after its stated verification passes. Report a correctness
  failure with its cause and repair it before dependent work starts.

### Commands

Run from the repository root with the existing native sources and Python environment
prepared. `just build-cli` rebuilds the runners before a vector run.

```bash
lake build
just ethcl-test
just build-cli
just lint
just check-citations
just check-constants
just proof-coverage-check
just ethcl-pyspec-smoke
```

For a development subset at a specific fork and preset:

```bash
just ethcl-pyspec "--fork=fulu --preset=minimal --subset=2 -n 6"
```

Use each affected fork and both presets. For the complete minimal sweep, run these
sequentially:

```bash
just ethcl-pyspec "--fork=fulu --preset=minimal --subset=0 -n 6"
just ethcl-pyspec "--fork=gloas --preset=minimal --subset=0 -n 6"
just ethcl-pyspec "--fork=heze --preset=minimal --subset=0 -n 6"
```

Full matrix and profiling commands:

```bash
PYTEST_JOBS=6 just ethcl-pyspec-full
just ethcl-profile
```

The six-worker setting matches the spike machine. Record a different fixed setting
when the implementation machine requires it. Preserve full case-level output when
comparing sweeps, beyond the console's counts.

## 4. Stages

Each stage depends on its predecessor. Split large tasks further while preserving the
completed-slice gates. Stages 4 through 8 use the common migration gate below.

**Common migration gate:** affected module builds, `lake build`, `just ethcl-test`,
rebuilt runners, project checks, coverage and axiom review, targeted arithmetic pins,
and development subsets for affected forks at both presets. Review bind placement
against the pinned source. Record build costs. Stage-specific sweeps add to this gate.

### Stage 0: complete inventory and baselines

- [x] **0.1 Inventory the full scope.** Enumerate numeric aliases, bare words, constants,
  configuration fields, casts, indexing, and operators in all `EthCLSpecs` consensus
  code. Include `ColumnIndex` and `CellIndex`, beyond the spike's unit list. Record
  numeric kind, width, consumers, fork inheritance, and the stage that migrates each item.
  *Done 2026-11-16: ~400 operator sites, ~230 cast sites, ~200 index sites, ~110 constants,
  and 10 numeric aliases inventoried with kind, consumers, inheritance, and stage;
  zero unassigned. Working record `mb/spec-arithmetic-implementation/inventory.md`
  (untracked); the stage rollup and counts land in `IMPLEMENTATION_NOTES.md` at Stage 10.*
- [x] **0.2 Capture fresh baselines.** Run the build, proof checks, full vector matrix,
  and profile. Keep the spike numbers as historical evidence. Record case identities,
  axioms, and reproducible cold, no-op, and incremental timings.
  *Done 2026-11-16 at `58ba389`: cold `lake build EthCLSpecs` 6m52s/607 jobs, no-op 0.5s,
  incremental 2m58s; coverage 78 claims (19 characterized, 58 touched of 625), no
  forbidden axioms; smoke and the full matrix at both presets match the spike's `main`
  counts case-for-case; profile medians 273.8ms `stateRoot`, 617.9ms `runBlocks`.
  Working record `mb/spec-arithmetic-implementation/baselines.md` (untracked).*
**Done when:** every current consensus arithmetic site has an assigned migration stage;
the build, proof, vector, and performance baselines have reproducible commands and results.

### Stage 1: SSZ packing and error prerequisites

- [ ] **1.1 Classify by SSZ shape.** Replace type-name-dependent packing decisions with
  shape-based classification. Handle an unresolved shape explicitly.
- [ ] **1.2 Pin cached writes.** Use a custom wrapper in SizzLean tests. Cover lists,
  vectors, chunk boundaries, repeated writes, and a root cached before the write.
  Compare serialization and cached roots with the updated plain value.
- [ ] **1.3 Preserve typed causes.** Define the arithmetic causes and their state/store
  mappings. Distinguish range failures from zero division where the runner catches
  `ValueError`. Recheck list-limit errors against `eth-ssz-specs` 0.1.0.
- [ ] **1.4 Test runner classification.** Cover pure, state, nested state, and store
  paths, including index errors and failed-state disposal. Keep decoding errors separate.

**Done when:** `lake build SizzLeanTests`, framework tests, the full build, project
checks, and smoke vectors pass. No fork numeric alias has changed yet. The cache test
reproduces the spike's stale-root failure if shape classification is reverted.

### Stage 2: checked arithmetic core and proof interface

- [ ] **2.1 Build safe construction.** Implement private wrappers, checked casts,
  proof-carrying constructors, safe literals, and SSZ representation laws. Test direct
  `OfNat`, aliases, delayed expected types, and imports without the authoring scope.
  Use `toPlainNat` for `Nat` results, `toCLInt` for `CLInt` results, and `toCLUint64?`
  for checked conversions to `CLUint64`. Reserve `toPlainInt` for Lean `Int` results.
  Apply these names when re-authoring the spike code and its proof lemmas.
- [ ] **2.2 Implement the operation matrix.** Cover `CLUint64` and `CLInt` arithmetic,
  mixed operands, intermediate overflow, and Python floor division.
  Implement 8-bit construction and the operations required by flags. Add wider
  framework operations identified by Stage 0 before their consumers migrate.
- [ ] **2.3 Implement total routes.** Add proof-carrying positive divisors, total
  same-width bitwise operations, and right shifts with nonnegative counts. Checked
  power and left shift use bounded overflow decisions with proofs.
- [ ] **2.4 Prove the reusable laws.** Supply success/value lemmas, checked-chain and
  fold laws, conversion laws, and lift laws. Provide a focused simp set and audit axioms.
- [ ] **2.5 Check the pinned oracle.** Exercise both operand orders, zero and maximum
  values, negative `CLInt` operands, narrowing, and every supported width boundary.

**Done when:** semantic and proof modules build independently of authoring elaborators;
the operation matrix has tests and laws; no unsafe literal route exists; the full
build and framework tests pass. Record construction and instance-synthesis costs.

### Stage 3: usable authoring surface and indexing

- [ ] **3.1 Settle operator elaboration on the native-backed wrappers.** Start with
  explicit `Checked` result ascriptions and exercise the known difficult expressions.
  Add bounded scoped elaboration if its readability benefit warrants the implementation
  work. Preserve unrelated core terms and retain the explicit ascription fallback.
  Pin the non-literal `Nat`, prior do-bind, whole-body, lambda, and inherited-body cases.
  Record compilation costs and proceed; cost is not an acceptance threshold.
- [ ] **3.2 Add size-aware indices.** Implement reads and writes for arrays, SSZ lists,
  vectors, and bit collections. Pure reads preserve `IndexError`; mixed fallible helpers
  use a common typed error channel. Test negative indices and empty collections.
- [ ] **3.3 Check constant and tier views.** Establish checked executable values and
  structural size views without duplicating constants. Test positivity premises through
  Fulu, Gloas, Heze, and a child override.
- [ ] **3.4 Exercise authoring rules.** Compile representative state-free, state, and
  store functions. Add behavior pins for dropped faults, empty loops, and short circuits.
  Review immediate binds manually. Keep linter work in its deferred document.

**Done when:** the full build and framework tests pass; representative formulas compile
with the documented ascription where needed; index errors retain their class; and no
trusted conversion is required merely to resolve an operator.

### Stage 4: `Gwei` across every fork

- [ ] **4.1 Move the alias and consumers.** Port balances, rewards, deposits, churn,
  withdrawals, builder balances, and fork-choice weights from the pinned Python bodies.
  Retype their constants and repair interfaces and benchmark fixtures.
- [ ] **4.2 Repair the proofs.** Restate successful and failing cases through the new
  laws. Include balance updates, builder payment and bid proofs, and checked total-balance
  folds. Preserve characterization tags and audit axioms.
- [ ] **4.3 Verify the complete slice.** Run the common gate, then the full vector matrix.
  Measure the build and profile here, before moving more aliases.

**Done when:** all three forks and their proofs use the migrated `Gwei` surface; vector
outcomes match or have a source-justified correction; and temporary crossings are listed.

### Stage 5: `Epoch` and `Slot`

- [ ] **5.1 Move `Epoch`.** Port activation, exit, withdrawability, slashing, and epoch
  computations across all forks, with their proofs. Pin the four former wrap sites:
  start-slot computation, activation-exit computation, validator exit, and withdrawal request.
- [ ] **5.2 Move `Slot`.** Port time-to-epoch helpers, transitions, committee calculations,
  ring buffers, and fork-choice slot expressions. Use positive-divisor views only with
  the required premises. Audit counter termination arguments.
- [ ] **5.3 Check evaluation order.** Resolve the `verifyCommitteeCoverage` failure-order
  corner against the runner's caught sets. Include state slots near the maximum.
- [ ] **5.4 Verify each unit slice.** Run the common gate after each alias migration.
  Run the complete minimal sweep at the end of the stage.

**Done when:** all epoch and slot arithmetic in scope has the prescribed behavior,
including generic presets and boundary inputs; proof contracts and coverage remain sound.

### Stage 6: all indices and plain-integer formulas

- [ ] **6.1 Move validator indices.** Port reads, writes, enumerations, selection loops,
  withdrawal cursors, and proofs. Remove unchecked conversions used solely for indexing.
- [ ] **6.2 Move the other indices.** Cover withdrawal, builder, committee, column, cell,
  and every other index in the Stage 0 inventory. Preserve builder-flag bit operations
  and prove their conversion laws.
- [ ] **6.3 Port plain arithmetic.** Use `CLInt` for Python lengths and signed formulas.
  Preserve `withdrawals[-1]`, zero-divisor behavior on empty registries, and the numeric
  kinds selected by mixed `min`/`max` and empty sums. Remove defaulting modulo helpers.
- [ ] **6.4 Verify.** Run the common gate for each index slice and the complete minimal
  sweep after all index and plain-integer consumers have moved.

**Done when:** every index family in scope has a checked or justified structural route;
all negative-index and empty-collection cases preserve Python behavior.

### Stage 7: clocks and remaining configuration arithmetic

- [ ] **7.1 Move time values.** Cover `timeMs`, `genesisTimeMs`, `slotDurationMs`, conversion
  helpers, and all clock consumers in state transitions and fork choice.
- [ ] **7.2 Preserve arbitrary configurations.** Use checked division where positivity
  is absent. Pin zero duration, boundary overflow, and nearby valid configurations.
  Close the `computeSlotAtTimeMs` mismatch with executable evidence.
- [ ] **7.3 Finish the constant audit.** Include Gloas threshold numerators/denominators
  and churn quotients. Distinguish checked constants from plain configuration integers.
- [ ] **7.4 Verify.** Run the common gate and complete minimal sweep.

**Done when:** generic configuration inputs preserve success/failure behavior, all
time arithmetic is accounted for, and the remaining constant inventory is empty.

### Stage 8: flags, widths, and full-scope closure

- [ ] **8.1 Move participation flags.** Port `addFlag` and `hasFlag`, including checked
  mask construction and short-circuit call placement. Repair proofs and codec fixtures.
- [ ] **8.2 Finish remaining widths and operators.** Cover every use of `Uint32`,
  `Uint256`, and any other width found in Stage 0. Distinguish data-only representations
  from arithmetic uses. Finish signed shifts and mixed-width conversions used in scope.
- [ ] **8.3 Re-author a complete body.** Use `process_pending_deposits` from the pinned
  text as the authoring check. Prefer structural iteration over the finite queue.
  Update the worked example in `docs/CODING_STYLE.md` with the resulting form.
- [ ] **8.4 Audit the whole scope again.** Review raw word operators, raw constructors,
  projections, `toPlainNat`, `toPlainInt`, `toCLInt`, `Nat` subtraction/division,
  defaulting reads, casts, and all
  temporary crossings. Give every remaining use a source or proof justification.
  This is a manual transition audit; automated enforcement remains deferred.
- [ ] **8.5 Verify.** Run the common gate and full vector matrix.

**Done when:** every inventory row has implemented behavior and evidence; no consensus
arithmetic site remains unreviewed because its module built without edits.

### Stage 9: repository-wide documentation audit

- [ ] **9.1 Find conflicting guidance.** Audit documentation throughout the repository,
  including READMEs, contributor and agent instructions, architecture documents, manuals,
  worked examples, and Lean module and declaration docstrings. Search for raw `UInt64`
  authoring guidance, unbounded-intermediate assumptions, wrapping conversions, error
  classification, obsolete conversion names, and arithmetic examples that omit binds.
- [ ] **9.2 Reconcile each finding.** Update current guidance and executable examples
  to match the implemented arithmetic contract. Check the actual result types behind
  conversion names. Preserve descriptions of intentionally raw arithmetic in other
  packages and clearly label historical measurements and superseded designs.
- [ ] **9.3 Verify documentation examples.** Build affected Lean modules and examples.
  Run the citation and project checks. Repeat the targeted searches and inspect remaining
  matches. Record each reviewed document and the resolution of each conflict.
- [ ] **9.4 Check document links and status.** Update the docs index and cross-references.
  Ensure current guidance describes the implemented state and keeps deferred linter
  work separate. Leave removal of this temporary plan to the final acceptance stage.

**Done when:** the repository-wide audit has a recorded scope and findings; every
identified conflict with the implemented arithmetic contract has a resolution; affected
examples and checks pass. Preserve the audit record in `IMPLEMENTATION_NOTES.md`.

### Stage 10: final acceptance and remove this plan

- [ ] **10.1 Run final checks.** Run the full build, framework/spec tests, rebuilt runners,
  project checks, coverage and axiom review, and the full vector matrix. Reuse Stage 8
  results where the executable code and inputs are unchanged.
- [ ] **10.2 Record final costs.** Repeat cold, no-op, and incremental measurements with
  the baseline method. Record profile and epoch-suite results. Explain measured causes
  and mark unknown causes explicitly. Accept the correct implementation regardless of cost.
- [ ] **10.3 Synchronize lasting documents.** Update the arithmetic contract, the authoring
  model's arithmetic row, framework architecture §§6 and 10, spec architecture, and
  implementation/discrepancy records. Keep claims aligned with code and tests.
- [ ] **10.4 Preserve completion evidence.** Move the final scope, chosen implementation,
  costs, and any remaining optimization work into `IMPLEMENTATION_NOTES.md`. Keep the
  deferred linter document separate. Track unrelated spike fixes independently.
- [ ] **10.5 Remove the temporary plan.** Delete this file and its links from the design
  document and docs index in the completion change. Retain the final-state contract
  and deferred linter document. Remove only scratch files created for this transition.

**Done when:** the full contract applies across all consensus code in `EthCLSpecs`,
the evidence is in lasting records, and this temporary plan has been removed.
