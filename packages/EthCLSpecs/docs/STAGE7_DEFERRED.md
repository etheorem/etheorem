# Stage 7 deferred findings

Findings the stage-7 reviews classified as deferred (style, structure,
test coverage, or performance that is not a correctness issue), with the
reviewer wording preserved. The coordinator worked the list after the
last task: each item below now carries its outcome. Closed items record
the commit batch that fixed them; dropped items record the reason.

## Task 1: the `.runOk` / `.runError` rows

1. **The runOk miss branch drops the actual error.** CLOSED, cleanup
   batch A. The miss branch extracts the rejection's repr through
   `runProbeError` on the same `runPure` application, and the executor's
   disagreement print names the run's answer when the result carries
   one. Batch B's `toyWrongRunOk` pin holds it.

2. **Each serialization evaluates twice per run.** CLOSED, cleanup
   batch A. `runOkResult` / `runErrorResult` compute the comparison from
   their own arguments, the `eqRunResult` shape, so each serialization
   and each repr sits at one argument position. The miss assemblers keep
   `agree := false` unconditionally, so no comparison against empty
   bytes can accidentally agree.

3. **The agreement-false paths for the run shapes are untested.**
   CLOSED, cleanup batch B. `Tests/ToyRun.lean` holds the two
   disagreement fixtures (`@[implemented_by]` bodies that reject, and
   that return cleanly, where the kernel's bodies do not), and
   `Tests/Probe.lean` pins both throws, the `errorRepr` presence, and
   the message's repr. Mutation experiments flipped each miss
   assembler's `agree` and failed the matching pin.

4. **`Execute.handles?` is now the constant `none`.** CLOSED, cleanup
   batch B, by rewording: the seam stays as the extension point a future
   unrunnable shape would use, and the B0 comment says plainly that
   phase A reports an `.unsupported` statement before phase B starts.
   The dead-branch observation itself needs no action.

5. **`shapeTagOf` exists twice.** CLOSED, cleanup batch B. `Shape.tag?`
   in `Statement.lean` is the one mapping; `Command.lean` and
   `Tests/Probe.lean` call it.

6. **The `exTy` expression is built three times.** CLOSED, cleanup
   batch A. `probeResultExTy` serves all three sites.

7. **Two record-path checks in the test derive their paths
   differently.** CLOSED, cleanup batch B. Both derive fork, preset,
   case, and side from the records.

8. **Two compressed passages in the docs.** CLOSED, cleanup batch B.
   The notes bullet is split and names what the UTF-8 alternative
   loses; the comma in "one place, like its byte form" landed.

9. **"The output is a container" is an assumption stated as a fact.**
   CLOSED, cleanup batch A. Both sites state the row's rule as the
   code's rule, with the scalar-pre-state caveat named once.

## Task 2: the Gloas binding's `handlerOf`

1. **The operation-handler justification is false for one Gloas
   handler.** CLOSED in the pyspec-format commit. The docstring and
   field comment state the map's domain (the `epoch_processing`
   substeps; every other function gets no entry) and drop the reason.

2. **The guards pin three of seventeen entries.** CLOSED, cleanup
   batch B. One exhaustive list-shaped `#guard` covers all seventeen
   pairs, with the single-backtick fallback named as the reason it
   exists; the targeted guards stay.

3. **Environmental: two clean builds printed `PANIC at outOfBounds
   Init.GetElem:18` during the task-2 verification window.** CLOSED, no
   action, with the evidence preserved: ~10 sequential clean rebuilds
   and two concurrent invocations afterwards printed none; the two
   prints coincided with the only window where a second build system
   (an editor LSP issuing `lake setup-file` builds, and the coder
   agents' verification builds) ran against the same gitignored output
   tree. Build exit stayed 0 in every case. If a panic print reappears
   on a single isolated build, investigate the built-cache and record
   paths for an unguarded array read first.

## Task 3: the pyspec format

1. **The toy interface's clean-run arm fabricates an admitted reject.**
   CLOSED, cleanup batch C. The arm returns the post root like its
   sibling, so a regressed `toyFail` hits the driver's own "expected a
   rejection but ran clean" row.

2. **`pyspecCheck` discards `res.flagged`.** CLOSED, cleanup batch C.
   A flagged pass fails with the flag named; a genuine `IndexError`
   toy fixture drives the pin, with a mutation experiment behind it.
   §13.5 of `THEOREM_VECTORS_ARCHITECTURE.md` carries the rule in its
   own commit.

3. **A valid-vector-rejected replay row is unpinned.** CLOSED, cleanup
   batch C. The valid-marking record retargeted at the rejecting toy
   step pins the driver's `.error e, some _` row, with the needle on
   the reject's own text; the no-interface defensive branch has its
   pin. The remaining defensive branches (missing post path, missing
   binding) stay unpinned: two more rows of the same shape.

4. **`meta.yaml` is written, returned, and never read.** CLOSED,
   cleanup batch C. The docstring states that only the pre and post
   bytes come from the files and `caseMeta` is rebuilt from the
   constant.

5. **Scratch cleanup on a mid-drive throw.** DROPPED. The
   create-then-remove pattern is the whole suite's convention
   (`Tests/Probe.lean`, `Tests/Command.lean` say the same); the scratch
   dirs are gitignored and a mid-drive throw fails the build anyway.
   Changing the convention belongs to a suite-wide pass, not stage 7.

6. **Manifest overwrite under a filtered render.** CARRIED TO STAGE 9.
   `render --format <name>` overwrites `formats/manifest.json` with only
   that invocation's rows. Harmless for the current recipes; stage 9's
   CI job should render unfiltered or merge. One note in §15's harness
   docstring when stage 9 wires the job.

## Task 4: the pyspec harness switch

1. **Vacuous green when the `--vectors` walk collects zero cases.**
   CLOSED, cleanup batch D. An empty collection raises
   `pytest.UsageError` naming the directory and both filters.

2. **The missing-root failure is loud but anonymous.** CLOSED, cleanup
   batch D. `walk_vector_cases` raises `FileNotFoundError("--vectors
   root not found: …")` after an `is_dir` guard.

3. **The `decomp` closure name is now stale.** CLOSED, cleanup
   batch D. Renamed to `resolve`.

4. **State why the stems are uniform.** CLOSED, cleanup batch D. The
   union's comment states that `.ssz_snappy` holds no interior dot, so
   `Path.stem` strips it whole.

## Batch-review leftovers

- **The ran-clean pin's catch-all accepts any exception**
  (`Tests/Probe.lean`'s `expectRunErrorMiss` and the pre-existing
  `expectAgreementFailure`). CLOSED in the final polish: both catches
  discriminate `.error _ _` from other exceptions and rethrow the rest,
  the `expectRunOkMiss` pattern. A mutation check confirmed the real
  failure signal still surfaces through the discriminated catch.
- **`Shape.wire` and `Shape.tag?` spell the mapping twice**
  (`Statement.lean`). DROPPED. Both are exhaustive matches, so a new
  constructor fails both builds; routing one through the other saves
  two lines and costs an `Option` dance at every `wire` call site.
- **Failed-and-flagged rows do not name the flag** (the shared failure
  line in `pyspecCheck`). CLOSED in cleanup batch C's follow-up: the
  line appends `", flagged"` when the flag is set.
- **Unused `IndexError` open name** (`Tests/ToyFork.lean`). CLOSED in
  the same follow-up: dropped from the open list.
