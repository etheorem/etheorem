# Theorem vectors: implementation plan

This file sequences the work that builds the generator
`THEOREM_VECTORS_ARCHITECTURE.md` describes. Each stage ends in a green build,
a committed diff, and an acceptance check a reviewer can run. Section numbers
in parentheses refer to `THEOREM_VECTORS_ARCHITECTURE.md`. The stages are in
dependency order, and a later stage never reopens an earlier one's
acceptance.

Contents:

- The corpus
- Rules for every stage
- Stage map
- Stage 0: scaffolding
- Stage 1: reader, selection, report
- Stage 2: probe, executor, records, function format
- Stage 3: prepare pass and the bit-vector source
- Stage 4: generation, the random source, shrink
- Stage 5: hints
- Stage 6: state builders
- Stage 7: run shapes and the pyspec format
- Stage 8: mainnet and witness reuse
- Stage 9: the other forks, CI, documentation
- Decision points
- Risks

---

## The corpus

The first input is the `Proofs/` corpus as of 2026-10-10: about 100 public
theorems, 9 in Fulu, about 50 in Gloas, and 39 in Heze. The first stages
target a handful of Gloas theorems over a `BeaconState` and scalars, and
Gloas gets the first binding, generator file, and builder catalog. Fulu and
Heze follow in stage 9, once the stage 1 report shows which of their
theorems are in scope.

The block-input rule (`THEOREM_VECTORS_ARCHITECTURE.md` §1.2) drops these files from the
corpus today:

| Fork | File | Block input |
| --- | --- | --- |
| Gloas | `ProcessOperations.lean` | `BeaconBlockBody` |
| Heze | `ShouldExtendPayload.lean` | `Store`, `BeaconBlock` |
| Heze | `OnExecutionPayloadEnvelope.lean` | `Store`, envelope |
| Heze | `RecordPayloadInclusionListSatisfaction.lean` | `Store`, `ExecutionPayload` |
| Heze | `IsPayloadInclusionListSatisfied.lean` | `Store` |

Most Heze theorems take a `Store`, so the Heze generator file starts short.
The base source still runs on these theorems, and a theorem whose
hypotheses accept a `default` block gets a vector that way.

---

## Rules for every stage

- **One commit per stage**, with the subject
  `feat(theorem-vectors): stage N, <title>`. The commit body lists the
  steps and the acceptance result. A stage that grows too large for one
  commit splits at a step boundary, never inside one, and each part names
  the stage and the steps it covers.
- **Green at every step.** `lake build EthCLLibTheoremVectors
  EthCLSpecsTheoremVectors theorem_vectors` passes after each step, and
  `just theorem-vectors` passes at the end of each stage from stage 2 on.
- **The shipped libraries stay untouched.** No module under `EthCLLib` or
  `EthCLSpecs` imports anything under `*.TheoremVectors`. The one exception
  is the marker attribute in `EthCLLib.Internal.ProofLedger` (stage 1).
- **Every module opens with a module docstring** that names the section of
  `THEOREM_VECTORS_ARCHITECTURE.md` it implements, sets `autoImplicit false`, and wraps its
  declarations in `EthCLLib.TheoremVectors` or `EthCLSpecs.TheoremVectors`.
- **No `sorry`, no committed `#eval`.** Assertions are `#guard` or `example`.
- **Tests sit beside the code.** Framework-half tests under
  `EthCLLib/TheoremVectors/Tests/` run over a toy fork binding. Spec-half
  pins under `EthCLSpecs/Tests/TheoremVectorsPins.lean` run over real
  theorems with known answers.
- **Deviations go in `IMPLEMENTATION_NOTES.md`**, under a theorem-vectors
  heading, in the same commit that makes them. `THEOREM_VECTORS_ARCHITECTURE.md` changes
  only when the design changes, in its own commit, with the reason.
- **The manifest moves with the dependency.** The stage that adds the
  `plausible` require runs `lake update` and commits the root
  `lake-manifest.json`.

---

## Stage map

```
 0 scaffolding
 │
 1 reader, selection, report ──────────────── decision point A
 │
 2 probe, executor, records, function format
 │
 3 prepare pass, bit-vector source
 │
 4 generation, random source, shrink ──────── decision point B
 │
 ├── 5 hints
 │
 ├── 6 state builders ─────────────────────── decision point C
 │
 7 run shapes, pyspec format
 │
 8 mainnet, witness reuse
 │
 9 other forks, CI, documentation
```

Stages 5 and 6 depend on stage 4 and on nothing else, so they can proceed in
either order or in parallel. Stage 7 needs stage 2 only, but it should not
start before stage 4 lands, so the pyspec case for a state-only handler gets
a built or random state and not a `default` one.

---

## Stage 0: scaffolding

**Goal.** Both libraries, the exe, and the dependency exist and build, with
the core types and nothing that runs.

**Steps.**

1. `packages/EthCLLib/lakefile.toml`: add the `plausible` require at
   `v4.29.0` and the `EthCLLibTheoremVectors` library (§2.3). Run
   `lake update` at the root and commit the manifest.
2. `packages/EthCLSpecs/lakefile.toml`: add the `EthCLSpecsTheoremVectors`
   library with the `theorem_vectors.outDir` option, and the
   `theorem_vectors` exe (§2.3).
3. `EthCLLib/TheoremVectors/Types.lean`: `PresetId`, `ShapeTag`,
   `WitnessSourceTag`, `Failure`, `ValueData`, `BoundRel`, `Knobs` (§5).
4. `EthCLLib/TheoremVectors/Yaml.lean`: the YAML writer for the
   client-facing files (§12.3), writer only, with `#guard` pins on the two
   shapes it renders: a `meta.yaml` as one flow line and a function-format
   file in block style, hex single-quoted in both. The generator's own files
   use `Lean.Json` with derived instances and need no module.
5. `EthCLLib/TheoremVectors/ForkBinding.lean`: `PresetInstances`,
   `ForkBinding` (§6).
6. `EthCLLib/TheoremVectors.lean` and `EthCLSpecs/TheoremVectors.lean`: the
   roots, importing what exists.
7. `EthCLSpecs/TheoremVectors/Main.lean`: the exe with argument parsing and
   every subcommand answering "not implemented" with exit code 2.
8. `.gitignore`: `packages/EthCLSpecs/theorem_vectors/`.
9. `Justfile`: `theorem-vectors` and `theorem-vectors-clean` (§17.2), the
   first one calling the stub exe.
10. Move the two design documents into the repository:
    `ARCHITECTURE.md` to
    `packages/EthCLSpecs/docs/THEOREM_VECTORS_ARCHITECTURE.md` and this
    file to `packages/EthCLSpecs/docs/THEOREM_VECTORS_PLAN.md`. List both in
    `packages/EthCLSpecs/docs/README.md`. From this step on the repository
    copies are the only copies, and every `ARCHITECTURE.md §n` citation in
    a module docstring or in `IMPLEMENTATION_NOTES.md` names the
    repository file. A design change edits the repository file in its own
    commit, as the rules above say.

**Acceptance.** The three targets build. `lake env lean` can
`import Plausible` from a scratch file under the framework half.
`just theorem-vectors-clean` runs and removes nothing that exists. The
docs index lists both documents, and no committed file cites a path
outside the repository.

---

## Stage 1: reader, selection, report

**Goal.** Every public theorem in `Proofs/` is read, classified, and listed
in a report. No witness is searched. This is the cheap pass that sizes the
rest.

**Steps.**

1. `Statement.lean`: `Input`, `InstanceKind`, `Statement`, `Shape`, the
   `forallTelescope` walk, binder classification (§7.1), target discovery
   through `Capture.isSpecFunction` (§7.2), shape matching in the order of
   §7.3.
2. `Scope.lean`: the block-input walk over input types (§7.4), with the
   function-type hit.
3. `EthCLLib/Internal/ProofLedger.lean`: the `@[theorem_vectors]` attribute
   and `theoremVectorsExt`, with the same validity checks `characterizes`
   runs (§14.1). This is the one edit to a shipped module.
4. `Outcome.lean`: the outcome structure with `deriving ToJson, FromJson`
   and its JSON file (§16.1), with `origin`, `shape`, `blockInputs`, and a
   `runs` list that stage 2 fills.
5. `Command.lean`: `theorem_vectors_fork`, the `characterized` and `tagged`
   clauses, named lines with `with` and `presets` parsed and stored, `skip`,
   the whole-file precedence pass (§14.3). At this stage a theorem's run
   reads the statement, writes the outcome with status `unsupported` or a
   placeholder `pending`, and logs one info line.
6. `Bindings/{Fulu,Gloas,Heze}.lean` and `Bindings.lean`: the three
   bindings with `builders := #[]` and `handlerOf := fun _ => none`.
7. `Generators/{Fulu,Gloas,Heze}.lean`: the header and
   `theorem_vectors characterized`.
8. `Report.lean` and the exe's `report`: the per-fork table from the outcome
   files (§16.2).
9. Tests: `EthCLSpecs/Tests/TheoremVectorsPins.lean` pins the reader's
   answer for ten theorems with known shapes, including one `.iffTrue`,
   one `.runOk` in each of its two forms, one `.bound`, one with a block
   input, one with an implicit value binder, and one with a function-typed
   input. `EthCLLib/TheoremVectors/Tests/Attribute.lean` checks that the
   attribute rejects a non-theorem and a theorem outside a fork namespace.

**Acceptance.** `just theorem-vectors` builds the generator library and
writes `report.md` with one row per public theorem of the three forks,
showing origin, shape, and block inputs, and an `.unsupported` reason where
the reader gave one. The pins pass.

---

## Stage 2: probe, executor, records, function format

**Goal.** A theorem with `default` inputs or author seeds produces a record
on disk, the record reads back, and the function format renders it.

**Steps.**

1. `Prepare.lean`, first form: one `Case` per theorem, the conjunction of
   its hypotheses, plus the `Decidable` synthesis check (§8.4). The unfold
   and split come in stage 3.
2. `Probe.lean`: the `Probe` structure (§11.1), the term builder (§11.2) with
   `check`, `seeds`, and `run`. `sample`, `shrink`, `reads`, and `build`
   return empty results until their stages. The precompiled helpers
   `runProbeOk`, `runProbeError`, and `compareBytes` live here.
3. `Execute.lean`: the per-shape outcome for `.eq` and `.bound` (§11.3), the
   agreement check as a build error.
4. `Witness/Source.lean`: `SearchStep`, `WitnessSource`, `SearchCtx`,
   `SearchM`, the loop with its fixed order (§9.2), and the `probe.check`
   call.
5. `Witness/Base.lean` and `Witness/Seed.lean` (§9.4).
6. `Preset.lean`, first form: bind the instance binders for one preset
   (§10). Reuse comes in stage 8.
7. `Record.lean`: `VectorValue`, `VectorRecord`, the directory writer and
   reader (§12.1, §12.4), and the read-back check (§12.5).
8. `Format.lean` and `Formats/Function.lean` (§13.1, §13.3).
9. The exe's `render` and `list` (§15).
10. `Seeds/Gloas.lean` with one seed, and the named lines in
    `Generators/Gloas.lean` for the acceptance theorems.
11. `Command.lean`: phases B1 through B8 wired end to end for one preset.
    From decision point A: `Statement.lean` writes the box-lemma reason
    (§7.3), `Report.lean` writes the summary counts (§16.2), and
    `Generators/Gloas.lean` carries `skip` lines with reasons for the four
    existentials (`initiateBuilderExit_run_inRange` and its three
    variants). The stage-1 `probe` clause becomes `survey` (§14.3): the
    same selection, phase A alone, status `unselected` in place of
    `pending`, no `presets` clause, origin `survey`. The `pending` status
    goes away with it, since every run now has a real status.
12. Tests: a toy fork binding under `EthCLLib/TheoremVectors/Tests/` with
    two theorems, one `.eq` over `UInt64` and one `.bound`, run through the
    probe and the record round trip. A pin that a deliberately wrong
    expected value (a toy theorem whose compiled `e` differs, built through
    an `opaque` constant) fails the agreement check.

**Acceptance.** `initializePtcWindow_lt`, `initializePtcWindow_lt_default`,
and `getPtcElseOffset_lt_same_slot` write records from `default` inputs.
Each record reads back and passes the read-back check. The function format
renders each one, and `report.md` lists them with status `written` and
source `base`. `just theorem-vectors` is green.

*Outcome.* Six records at `minimal`, five function files, the recipe green
in seven seconds. `getPtcElseOffset_lt_same_slot` writes from `default`
inputs with source `base`. The two window theorems write from seeds with
source `seed`, because the `default` state has no active validator and
`computePtcFromFulu` runs to its fuel bound on it; `initializePtcWindow_ge`
writes from a seed too. The design changes that followed sit in
`THEOREM_VECTORS_ARCHITECTURE.md`: the `default` state is never a
candidate and the seed's claim is per theorem (§9.4), a theorem with no
target still runs (§7.2) and the function format rejects its records
(§13.3), the probe term is an `Expr` tree over `ScalarCodec` (§11.2) with
a `defaults` field (§11.1) and the record layer's literals and roots in
`ProbeResult` (§5.5), the roots come from the binding's hasher (§11.4),
the record's payload nests under `value` (§12.2), and `render` hands
`check` a manifest (§13.2). Stage 3 step 7 carries the source changes.

---

## Stage 3: prepare pass and the bit-vector source

**Goal.** Scalar theorems get witnesses with no seed, hypotheses through
spec predicates split into cases, and `.iffTrue` gives two vectors.

**Steps.**

1. `Prepare.lean`, full form: the `simp only` lemma sets (§8.1), the DNF
   split with the `maxCases` cap (§8.2), the `.iffTrue` sides (§8.3).
2. `Witness/BitVec.lean`: the `bvDecide'` call, the `CounterExample`
   reader, serialization of each value to its SSZ width, the `unsat`
   answer (§9.4).
3. `Execute.lean`: the `.iffTrue` row (§11.3).
4. The `Probe` gains the case index on `check` for every case.
5. Record paths gain the case index and side (§12.1).
6. Tests: a toy theorem with a hypothesis `a < b ∨ a = b` splits into two
   cases and the equality case lands on the boundary. A toy theorem with an
   unsatisfiable hypothesis reports `unsat` and writes no record. A
   `.toNat` hypothesis rewrites to `UInt64` form.
7. `Witness/Base.lean` and `Witness/Seed.lean`, from the stage 2 outcome:
   neither proposes `default` for an input of the binding's `stateType`,
   and the seed's build error fires when the seed passes no case (§9.4).
   The `FUTURE_WORK.md` entry on a base-source cost guard goes away with
   it.

**Acceptance.** `getPtcElseOffset_lt_next_slot` writes a vector with no
seed. `canBuilderCoverBid_iff` writes two vectors from a state seed with
solved scalars. `isValidIndexedPayloadAttestation_eq_true_iff_checks`
splits into one case per check, and each case with a satisfiable
conjunction writes a record. The report shows source `bitVec` for the first.

*Outcome.* Twelve records at `minimal`, ten function files, the recipe
green in seconds. The first acceptance theorem writes from the solver
with no seed. `canBuilderCoverBid_iff` writes its true side and both
false-side cases once the seed state holds a builder below the floor;
the review fix put one at index 0.
`isValidIndexedPayloadAttestation_eq_true_iff_checks` splits into five
cases and writes the true side; its false sides need containers the seed
does not vary, and stage 4's random source takes them. The design changes
that followed sit in `THEOREM_VECTORS_ARCHITECTURE.md`: the per-line
source list (§9.2), the read grounding and the coupled-scalar grid
(§9.4), the partial seed's handoff (§9.4), and the unfold's body cutoff
(§8.1). The review fixes landed beside them: the positional order of the
generator lines with its error (§14.3), the heartbeat budget per run
(§14.4), and the `bne` / `ne` unfold lemmas that bring
`convertBuilderIndexToValidatorIndex_toBuilderIndex` to the solver. Stage
4 step 7 carries the remaining source change.

---

## Stage 4: generation, the random source, shrink

**Goal.** A theorem over a `BeaconState` gets a witness with no seed.

**Steps.**

1. `Sampleable.lean`: the scalar instances and the generic `SSZRepr`
   instance (§9.5). Start with the containers `BeaconState` reaches, and
   stop to reassess if the generic instance does not fall out of SizzLean's
   type description (decision point B).
2. `Probe.lean`: `sample`, `shrink`, and `reads`.
3. `Witness/Random.lean`: the draw, the read substitution, the solver call,
   the redraw loop with `randomDraws` (§9.4).
4. `Witness/Shrink.lean`: the shrink loop with `shrinkSteps` (§9.6).
5. The options `randomDraws`, `randomSize`, `shrinkSteps`, `seed` (§14.4).
6. Tests: the generic instance produces a decodable `BeaconState` at
   minimal for a fixed seed, and the same seed gives the same bytes. Shrink
   on a toy container reaches a smaller value that still passes a toy check.
7. `Witness/BitVec.lean`, from the stage 3 outcome: a `Fin n` input enters
   the solver as a `UInt64` with the bound `x < n` (§9.4), so a coupled or
   free `Fin` scalar no longer drops out of the search in silence. The
   solver's `Fin` values stay below `n`; the strict decode of §9.3
   refuses the rest.

**Acceptance.** `canBuilderCoverBid_iff` writes its three cases with no
seed, source `random`, and the shrunk state is smaller than the first
draw. `isValidIndexedPayloadAttestation_eq_true_iff_checks` writes three
of its four false-side cases from draws; the signature gate's negation
never holds under the verify-off backend (§8.1) and stays `notFound`.
The report records the seconds per record.

**Outcome.** Commit `c1dd12d`, with `52dbd4f` for the design. The
acceptance holds: `canBuilderCoverBid_iff` writes its three cases from
draws with no seed, the shrunk state is 15493 bytes against the 17635 of
the first draw, `isValidIndexedPayloadAttestation_eq_true_iff_checks`
writes three false sides from draws and reports the signature gate's
negation as `notFound after seed, bitVec, random`, and the report shows
the seconds per record. 15 records and 14 function files. The clean
recipe runs in 52 seconds, 50 of them the Gloas generator, against 11 at
stage 3. Decision point B closed: the generic instance fell out of the
type description. Four design changes: the random source's read set is
the container-mentioning subterms with a scalar literal form, the draws
are shared across a theorem's cases, the shrink keeps every passing
candidate of one call under a wire-size bound, and `SearchM` stays
`MetaM`. Two shortfalls carry into stage 5 steps 7 and 8: a read past a
drawn list's end panics in compiled code, 152 times per clean build, and
the sources' pure `applies` test misreads an alias as a container.

---

## Stage 5: hints

**Goal.** A second build replays every witness from committed hints and
runs no search.

**Steps.**

1. `Witness/Hint.lean`: the hint schema, the fingerprint, the reader and
   writer, and the hint source (§9.8).
2. The source order places the hint source first (§9.2).
3. `Command.lean`: the `theorem_vectors.hints` option, the
   `THEOREM_VECTORS_HINTS` variable read ahead of it, hint writing to
   `<outDir>/hints/`, and the `hint` field on the outcome line.
4. `EthCLSpecs/TheoremVectors/Hints/gloas/`: the first committed hints, from
   the update recipe.
5. `Justfile`: `theorem-vectors-hints-update` and
   `theorem-vectors-hints-rebuild` (§17.2).
6. Tests: a hint for a toy theorem replays and the outcome says `replayed`;
   a hint with a wrong scalar fails the check, the search runs, and the
   outcome says `failed`; `require` mode errors on a missing hint;
   `ignore` mode produces the same witness as the hint for a fixed seed.
7. `Witness/Random.lean`, from the stage 4 outcome: no read past a drawn
   list's end reaches compiled code. The coupled grid takes its bound from
   the drawn list's length, or the reads plan evaluates the bound before
   the read; a clean build prints no panic, and the per-record seconds
   drop with the wasted solves.
8. `Statement.lean` or `Scope.lean`, from the stage 4 outcome: the reader
   records each input's scalar kind once, in `MetaM`, and the sources'
   `applies` tests read it, so an alias never reads as a container and
   `scalarKind` runs once per input instead of once per source and case.
9. `Justfile`: the `theorem-vectors` recipe builds `EthCLLibTheoremVectors`
   and `EthCLSpecs.Tests.TheoremVectorsPins` before the generator, so the
   toy tests and the pins run with the recipe.

**Acceptance.** After `just theorem-vectors-hints-update` and a commit,
`just theorem-vectors-clean` followed by `just theorem-vectors` writes the
same records as before, and every outcome shows `hint: replayed`. Changing
one hint's scalar by hand to a value the case rejects leads to `failed` on
that case and `replayed` on the rest.

**Outcome.** Commit `4543c8a`, with `60a13d5` for the design. The
acceptance holds: the committed Gloas hints cover the ten theorems that
wrote records, a clean build replays all ten (`hint: replayed`), an
`ignore` build writes the same records byte for byte except the `source`
field (`hinted-<orig>` against `<orig>`) and the same hint files, a
hand-edited scalar the case rejects turns the run's field to `failed`
while the other nine replay, and `require` passes on the committed
corpus. A clean build prints no panic, the shortfall step 7 carried.
Steps 7 to 9 landed: the probe's `safe` face, the statement's scalar-kind
table, and the recipe that builds the tests and the pins. The clean
recipe still runs in 50 seconds, because the two state theorems cost 20
seconds each in every mode: `canBuilderCoverBid_iff`'s replay runs the
shrink again, and with the shrink budget at zero it replays in 0.9
seconds; the payload attestation theorem's case 4 is `notFound`, which
no entry records, so every build searches it for 64 draws. Both carry
into stage 6 steps 8 and 9. Design changes: the hints root is the
lakefile option `theorem_vectors.hintsDir`, the candidate carries the tag
the record names, the fingerprint is per entry, every run writes its
file and a replay re-records the entry it consumed, and `require`
enforces per case.

---

## Stage 6: state builders

**Goal.** A theorem over a `BeaconState` gets a reachable state before the
random source runs, and the state is built once per build.

**Steps.**

1. `Builders/Gloas.lean`: `genesis`, `advanced`, `upgraded`, `withQueue`
   (§9.9), each `[Preset] → [Config] → Knobs → BeaconState`, with pubkeys
   and credentials derived from the validator index.
2. `Bindings/Gloas.lean`: the `builders` list.
3. `Probe.lean`: `build`.
4. `Witness/Built.lean`: the source, the knob grid, knob shrinking, the
   cache with its `.trace` stamp (§9.9).
5. The option `builtSteps` with its per-preset default.
6. `Witness/Hint.lean`: the built hint row.
7. Tests: each Gloas builder's state decodes through the fork's
   `stateRoot`, and `advanced` at the first epoch boundary has a slot equal
   to `slotsPerEpoch`. The cache returns the same bytes on a second call
   and rebuilds when the stamp file changes.
8. `Witness/Hint.lean` and `Witness/Shrink.lean`, from the stage 5
   outcome: a random entry records the shrink's path, the indices of the
   accepted candidates in each `probe.shrink` call, and the replay checks
   those candidates alone instead of walking every call's list. The
   replay of `canBuilderCoverBid_iff` drops from 20 seconds to about one.
9. `Witness/Hint.lean`, from the stage 5 outcome: a case every source
   failed records a `notFound` entry under the run's fingerprint, and
   `use` mode skips the search for such an entry while it is not stale.
   The rebuild recipe refreshes it, and the outcome's `hint` field still
   reads `replayed`. The payload attestation theorem's case 4 stops
   costing 20 seconds per build.

**Acceptance.** `canBuilderCoverBid_iff` writes its two vectors with source
`built` before the random source runs. A second build reads the state from
the cache, and the report's seconds drop. The vector's state passes the
pyspec server's decode (`pyspec_server stateroot gloas <state.ssz>`).

*Outcome.* The acceptance holds on today's three-case split: the true
side and one false side of `canBuilderCoverBid_iff` write with source
`built` from the `withQueue` grid step (16 validators, slot 40, queue 4,
two builders onboarded by the spec's own onboarding step), and one false
side falls through to the random source, the draw satisfying where
the grid did not. The replayed vectors' states decode through
`pyspec_server stateroot gloas`. Steps 8 and 9 landed: a random entry
carries its shrink path and its replay walks the recorded candidates
alone, and a case every source failed records a `notFound` entry whose
non-stale replay skips the search, the re-recorded entry keeping the
skip stable across builds and update runs. A cold build replays the
built witness in 29 seconds and runs the recipe in 56, and the second
build reads every state from the cache, the built witness dropping to
15 seconds and the recipe to 25. Decision point C, measured: `advanced`
at the first epoch boundary builds in seconds, the same order as a
pyspec `epoch_processing` case at minimal, so the six-step grid stays;
the per-preset `builtSteps` cap (3 at mainnet) already bounds the
mainnet grid. The design changes that followed sit in
`IMPLEMENTATION_NOTES.md`: the builders carry the seams their bodies use
beside `[Preset] [Config]`, the grid's epoch boundary is the fork's own
`Const.slotsPerEpoch` read through the binding, `Witness/Built.lean`
imports `Witness.Random` for the shared point loop, the cache stamp is
the binding module's trace, and a built hint's replay fetches its bytes
through the cache.

---

## Stage 7: run shapes and the pyspec format

**Goal.** A state-only handler theorem produces a pyspec case the server
passes.

**Steps.**

1. `Execute.lean`: the `.runOk` and `.runError` rows (§11.3), through
   `runPure` and the precompiled helpers.
2. `Record.lean`: the `error` field and the absent `output.ssz` for
   `.runError`.
3. `Bindings/Gloas.lean`: `handlerOf` for the epoch-processing handlers the
   fork drives.
4. `Formats/Pyspec.lean`: `accepts`, `render`, and `check` through
   `runCase` (§13.4, §13.5).
5. The exe's `check` (§15).
6. `PySpecTests/harness.py`: accept `.ssz` where no `.ssz_snappy` exists,
   and a `--vectors` option pointing at a directory (§17.4).
7. Tests: a rendered pyspec case round-trips through `CaseRequest` and
   `runCase` at the toy level; a `.runError` record renders with no
   `post.ssz`.

**Acceptance.** `processBuilderPendingPayments_run` writes a pyspec case.
`lake exe theorem_vectors check` passes it through `runCase`, and
`pytest --vectors` under `PySpecTests` passes it through the server.

*Outcome.* The acceptance holds: the clean recipe renders the case at
`formats/pyspec/gloas/minimal/epoch_processing/builder_pending_payments/pyspec_tests/processBuilderPendingPayments_run_000`,
`theorem_vectors check` answers `1 passed, 0 failed` through `runCase`,
and `pytest --vectors ... --fork=gloas` passes it through the server.
Both characterized `.runOk` theorems write from the `built` source's
`genesis` step, `processBuilderPendingPayments_run` in 2.0 seconds and
`initiateBuilderExit_run_eq` in 2.7, and their committed built hints
replay on the next clean build. Twelve records, fifteen function files,
and one pyspec case at minimal; the clean recipe runs in 93 seconds. No
corpus theorem has the `.runError` shape yet, so its record and render
path is pinned by the toy tests alone. The design changes that followed
sit in `IMPLEMENTATION_NOTES.md`: `VectorFormat.accepts` takes the
`RenderEnv`, because §13.4's acceptance predicate needs the record's
binding; `ProbeResult` carries the error's `repr`; the harness resolves
raw `.ssz` beside `.ssz_snappy` and spawns the server from the repository
root, where the workspace manifest is complete. `initiateBuilderExit`
has no `handlerOf` entry, so its record renders through the function
format and no pyspec case.

---

## Stage 8: mainnet and witness reuse

**Goal.** One theorem produces vectors at both presets, and scalar
witnesses move between presets when they still hold.

**Steps.**

1. `Preset.lean`: the preset-free type check and the reuse path (§10), with
   `.reused` as the record's source and a hint for the second preset.
2. `Bindings/*`: the `mainnet` entries.
3. `Generators/Gloas.lean`: `presets minimal mainnet` on the acceptance
   theorems.
4. The built grid's mainnet cap, measured.
5. Tests: a toy scalar theorem reuses its witness at the second preset; a
   toy theorem whose hypothesis names a preset constant searches again.

**Acceptance.** The stage 2 theorems write records at both presets, and the
report shows per theorem whether the mainnet witness was reused or searched.
`processBuilderPendingPayments_run` passes the server at both presets. The
report's seconds per mainnet record are in the stage's commit body.

*Outcome.* The acceptance holds. `getPtcElseOffset_lt_same_slot` carries its
minimal witness to mainnet: every input type is free of the preset, the
carried bytes pass the mainnet check, and the record names `reused-minimal`.
The two window theorems win from their seeds at mainnet, about 9.4 seconds
each, their state types being preset-bound. `processBuilderPendingPayments_run`
wins from the `built` source's `genesis` step at mainnet in 18.8 seconds. A
clean rebuild replays all four (`hinted-reused-minimal`, `hinted-seed`,
`hinted-built`), every record byte-identical to the searched run apart from
the `source` field, and the `builder_pending_payments` case passes `runCase`
and the server at both presets. The mainnet cap held: the built cache holds
exactly one mainnet entry, the genesis step, so the 3-step cap cut nothing
the walk reached. The built seconds and the one cache entry are the
measurement §14.4's mainnet cap rests on. Commits: `7e52ceb` (the
preset-free check and the reuse path), `b8d3e99` (the two-preset toy fork
and the reuse tests), `c5f5b37` with `1dbcb8b` (the built source's draw
guard, which the mainnet run exposed), `adb13a8` (the generator lines and
the committed mainnet hints). The reuse source sits after the hint source,
a recorded deviation from §3's B2 sketch (`IMPLEMENTATION_NOTES.md`). Two
mainnet draw limits carry in `STAGE8_DEFERRED.md`: a mainnet state beside
another container input still overflows the draw, and the random source's
loop has no mainnet cap.

---

## Stage 9: the other forks, CI, documentation

**Goal.** Every fork runs, CI enforces the claims, and the user-facing
documentation names the generator.

**Steps.**

1. `Builders/Fulu.lean` and `Builders/Heze.lean`, with their `builders`
   lists. Fulu has no `upgraded` row.
2. `Generators/Fulu.lean` and `Generators/Heze.lean`: named lines, seeds,
   and `skip` lines with reasons for the block-input theorems. The Fulu
   lines need the reader's store rule to identify the run's state by type
   and the `runPure`-form `.runError` reading, both demanded by the Fulu
   corpus's two-state theorems.
3. `Hints/fulu/` and `Hints/heze/` from the update recipe.
4. `.github/workflows`: the `theorem-vectors` job (§17.3), with the output
   tree uploaded as an artifact.
5. Add the corpus pre-state source to `FUTURE_WORK.md`.
6. `packages/EthCLSpecs/README.md`: a short section on the vectors, the
   recipes, and where the output lands.
7. `CLAUDE.md` and `CONTRIBUTING.md`: a paragraph under *Adding a proof*
   on the two tags, the generator file, and the hint update recipe.

**Acceptance.** `just theorem-vectors` is green for all three forks. CI
runs the job and fails on a strict skip, a failed agreement check, a failed
read-back, or a failed pyspec check.

*Outcome.* The acceptance holds. Twenty-five records write from a clean
run, sixteen Gloas and nine Fulu, and a second clean run replays all
twenty-five from the committed hints, byte for byte except the `source`
field. Fulu writes its five balance branch theorems (four at both
presets through seeds, `no_wrap` at minimal through the random source);
its two `_run_eq` contracts stay `.eq` skips, their `match` right sides
claiming no run shape and their boxed output types nothing to record.
Heze writes none: both in-scope theorems take a `runnerStore` whose type
is the theorem's own `σ`, and the rest of its corpus sits behind the
block-input rule and the `FcMap` / `ExecutionEngine` seams, each with
its reason in the report. The Fulu lines forced two reader changes the
plan's step 2 now names: the run's state is identified by type, not by
position, and `.runError` reads the `runPure` form. Two carried items
from `STAGE8_DEFERRED.md` landed first, so no mainnet line could reach
the overflow they guard: the built source draws its side containers
alone, and the random source caps itself at mainnet over a state-typed
container. The builders landed for all three forks; Fulu's catalog is
`genesis` and `advanced`, Heze's fills the four rows behind a
config-tier `hezeForkVersion`, a product-lead decision and a deliberate
shipped-file exception the notes record. Heze's catalog serves no
theorem today. CI gains the `theorem-vectors` job with the artifact.
The design documents moved with the code that changed them: §7.3's
store rule and form list, §5.3's `Shape` sketch, §9.4's cap sentence,
§11.1's `sampleAt` face. `STAGE9_DEFERRED.md` closes every finding
closed or drops it with its reason.

---

## Decision points

**A, after stage 1.** If more than half of the in-scope theorems come out
`.unsupported`, the `Shape` set grows before stage 2 starts. Theorems with a
block input do not count toward that half.

*Outcome, from the stage 1 report (96 theorems: 8 Fulu, 49 Gloas, 39
Heze).* 50 theorems have no block input. 23 of them are `.unsupported`,
and 17 of the 23 are box lemmas (`KeepsUncached`, `ReturnsUncached`),
which no shape can express. Among the 33 that remain, 6 are
`.unsupported`: 4 existentials over a run's result, 1 function-typed
input, 1 unknown instance seam (`FcMap`). The shape set does not grow.
Stage 2 adds the box-lemma reason (§7.3) and the report's summary counts
(§16.2), and the generator files `skip` the existentials with reasons.
The `FcMap` seam stays unbound: every theorem that binds it also takes a
`Store`, so §1.2 puts it out of scope before the seam matters.

**B, during stage 4.** If the generic `SampleableExt` instance does not fall
out of SizzLean's type description, stop and choose between hand-written
instances for the containers `BeaconState` reaches and an extension to the
description. Record the choice in `IMPLEMENTATION_NOTES.md`.

**C, during stage 6.** If `advanced` at the first epoch boundary costs more
than a pyspec `epoch_processing` case at minimal, cut the grid to `genesis`
and `advanced` and move the rest behind a named line's seed.

---

## Risks

- **Hypotheses in `Nat` form.** Several proofs state bounds through
  `.toNat`. The bit-vector source needs them in `UInt64` form. The rewrite
  is a fixed `simp` set, but a hypothesis that mixes `Nat` arithmetic with
  no `UInt64` image stays out of reach. Stage 3 reports each one.
- **Unfolding blows up.** A predicate that unfolds through several layers
  can produce many disjuncts, and a `do`-elaborated predicate may not
  unfold to comparisons at all. The pass has a disjunct cap, and a theorem
  that hits it reports the count and falls back to the unsplit hypothesis.
- **`evalExpr` on spec terms.** The spec's functions are `precompileModules`,
  so evaluation is native. The probe's glue is interpreted, and a `match`
  in an interpreted term can trip matcher realization. The probe keeps
  every `match` in precompiled helpers, and stage 2 confirms.
- **The generic SSZ generator.** The random source rests on one
  `SampleableExt` instance per container, derived from SizzLean's type
  description. If the description is not open enough to drive a generator,
  each container needs a hand-written instance, and `BeaconState` alone has
  dozens of nested types. Decision point B holds this.
- **Sparse hypotheses.** Random draws do not find a verifying signature or
  a matching hash. Those theorems need a seed or a builder. If the Gloas
  list needs more than a handful of seeds, the seed file grows into a
  library of named states. A later source can solve state fields from the
  comparison atoms and edit a built or drawn state instead of redrawing
  it.
- **Plausible version drift.** The tag `v4.29.0` sits one patch behind the
  toolchain. A toolchain bump moves the tag with it, which is one more line
  in the bump checklist.
- **The block exclusion drops most of Heze.** Block inputs come back in
  scope with a block builder, which runs the spec to produce a valid block
  for a given state, or with corpus blocks from the pyspec `sanity/blocks`
  vectors. Neither is in a stage.
- **Mainnet cost.** A mainnet state has fixed-length vectors a minimal
  state does not: `EPOCHS_PER_HISTORICAL_VECTOR` is 65536 at mainnet and 64
  at minimal. Draws, builders, evaluation, hashing, and the record files all
  grow with it, and shrinking cannot cut a fixed length. Stage 8 measures
  the seconds per mainnet record before mainnet becomes a default anywhere.
- **Records outlive their build.** Lake tracks the generator modules, not
  the files they write. `just theorem-vectors-clean` removes the generator
  modules' build outputs with the directory, so the next build regenerates.
- **Hints go stale in sweeps.** A new field in `BeaconState` changes every
  random draw of a fork, and every random hint of that fork fails at once.
  The build still passes in `use` mode, the report shows the sweep, and one
  run of the update recipe refreshes the hints. Built hints survive, because
  they hold knobs and no draw.
- **Vectors without a consumer.** The function format tests nothing in a
  client until a client wires it up. The pyspec format has a consumer today.
  Stage 7 earns the most and should not slip behind polish on stages 4 to 6.
