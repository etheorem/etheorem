# Stage 9 deferred findings

Findings the stage-9 reviews classified as deferred (style, structure,
test coverage, or performance that is not a correctness issue), with the
reviewer wording preserved. The coordinator works the list after the
last task: each item carries its outcome when worked, and stays open
with its reason until then.

Worked so far: task 2's architecture sentence (task 3b); tasks 4+5's
four wording items and task 2's docstring clause (cleanup batch 1); the
memo-completion drive, the `pinStateRoot` collapse, and the panic trace
(cleanup batch 2).

## Task 1: the built source draws the side containers alone

1. **The §11.1 face table and the `Probe` module docstring lag the new
   `sampleAt` face.** CLOSED, task 3b and cleanup batch 1. The face
   table carries `sampleAt` since the reader-fix commit, and the module
   docstring's deviation accounting now reads against the current
   sketch.

2. **No toy pin drives the built-then-random memo interplay.** CLOSED,
   cleanup batch 2. The built source leaves draw 0's slot partial (the
   state position `none`), a later random win at draw 0 completes it, and
   `findDrawIndex` matches the completed slot. Each half is pinned
   separately (`Tests/BuiltDrive.lean`, `Tests/Hint.lean`); the
   completion path itself has no direct test. A drive that runs
   `builtSource` then `randomSource` over one shared `SearchCtx` on the
   two-container theorem closes it. The drive also fixed the
   regression's shape: a `drawAt` that overwrites slots wholesale is not
   observable (the random draw re-samples every container position, and
   `sampleAt` is pure), so the pin guards the partial overwrite that
   skips held positions, which the batch injected and watched fail.

3. **`drawAt` copies the whole outer memo on every call, and the
   `sampleAt` dispatch walks a linear `cond` chain.** DROPPED. Immaterial
   at the option defaults and per-theorem memo sizes; the entry stays as
   the cost's record of fact.

## Task 2: the random source's mainnet cap

1. **The architecture §9.4 sentence is still pending.** CLOSED, task 3b.
   The store-rule doc pass put the cap's sentence in §9.4 beside the
   reader changes.

2. **The cap covers the state type alone, not a state nested inside
   another container input.** DROPPED. A hypothetical mainnet theorem
   taking a wrapper container that holds a `BeaconState`, or any
   container with a preset-length 65536 fixed vector, still draws and
   still overflows `drawVector`. No corpus theorem reaches that today,
   and the built source's guard keys on the state type the same way. If
   such a theorem appears, the cap should generalize to key on the SSZ
   description's largest fixed-vector length; the entry stays here as
   the pointer.

3. **Pre-existing `unused variable containerIds` warning at
   `Witness/Random.lean:146` (`tryDraw`).** CLOSED, cleanup batch 1, and
   it went further than the rename the item asked for: the parameter had
   no reader at all, so the batch removed it and the write-only
   `CasePlan.containerIds` field with it.

4. **The `Tests/Random.lean` module docstring names two of the three
   pins.** CLOSED, cleanup batch 1.

## Task 3: the Fulu and Heze builder catalogs

1. **The builders pin block swallows `outOfBounds` panics, pre-existing
   and now doubled.** CLOSED, cleanup batch 2. `Tests/TheoremVectorsPins.lean`'s
   builders `run_cmd` emits 416 `PANIC at outOfBounds` messages (208 before
   the task; the new catalogs double the builder work). Interpreted
   evaluation logs the panic, returns `default`, and continues, so the
   build stays green and every state still decodes through its fork's
   strict `stateRoot`. A panic that returns `default` can in principle
   corrupt an evaluated value while the coarse checks stay satisfiable.
   Reproduction: `lake build EthCLSpecs.Tests.TheoremVectorsPins 2>&1 |
   grep -c PANIC`. Batch 2 traced the first panic: `process_epoch`'s
   per-validator `!` reads (`inactivityScores` in `EpochProcessing.lean`,
   the participation flags in `Accessors.lean`'s
   `getUnslashedParticipatingIndices`) against the lists the `genesis`
   builder leaves empty; each read answers `default` and drops the
   write-back, and the states still strictly decode. Sizing the lists in
   `genesis` would change every built state's bytes and churn the hints,
   so the fix is the honest comment at the pin block and the banner on
   the `just theorem-vectors` recipe. The count is 416, unchanged by
   design. The batch also dropped the block's stale "compiled fork body"
   clause: the panics' backtraces are interpreter frames only.

2. **`pinStateRoot` grew to three near-copies.** CLOSED, cleanup batch
   2. One helper takes the `ForkInterface`; all ten call sites name the
   interface; the error text is unchanged and the per-fork pin blocks
   stay separate.

3. **The per-fork catalogs duplicate `genesis`, `genesisValidator`,
   `runState`, and `queueDeposit`.** DROPPED. The duplication is
   type-forced: each fork's containers are distinct types at the flat
   namespace boundary, so a shared body needs converters the framework
   does not offer. The shareable part, the identity layer, has its one
   home in `Builders/Fulu.lean`. The entry stays as the record so a
   future reader does not fold the catalogs into a cross-fork generic.

## Tasks 4+5: the Fulu and Heze generator files

All four CLOSED, cleanup batch 1.

1. **A stranded `with` in the overflow bullet.** The sentence is split,
   and the coordinator review of the batch sharpened it further: the
   drawn balance can in principle land within 64 of `2 ^ 64` through the
   `UInt64` draw's wide arm, so the true claim is about the redraw
   budget, about one value in `2 ^ 59`, which the budget never meets.
2. **The seeds parenthetical over-names the module.** Now reads "two on
   the `Seeds.Fulu` states, two on inline `default` terms".
3. **The docstring and the inline comment repeat six sentences.** The
   inline comment carries the local seed facts alone.
4. **An uncorroborated exploratory claim.** Named: "an exploratory
   seedless line answered `notFound` within its draw budget".

## Task 7: the CI `theorem-vectors` job

1. **The `auto-config: false` comment is the file's shorthand.**
   DROPPED. The pinned action also runs the GitHub cache steps on the
   root `.lake`, which hold nothing here because the subpackages build
   into their own `.lake` directories. The `poseidon-proofs` job's
   comment makes the identical claim, so the wording is the file's
   established shorthand; no functional effect either way. The entry
   stays as the record.
