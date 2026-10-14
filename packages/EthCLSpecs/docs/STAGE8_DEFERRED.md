# Stage 8 deferred findings

Findings the stage-8 reviews classified as deferred (style, structure,
test coverage, or performance that is not a correctness issue), with the
reviewer wording preserved. The coordinator worked the list after the
last task: each item below carries its outcome. Closed items record the
commit batch that fixed them; dropped and carried items record the
reason.

## Task 1: the preset-free check and the reuse path

1. **`Hint.rebuildable` and `Hint.rebuild` disagree for a
   `.hinted (.reused _)` entry.** CLOSED, cleanup batch A. `rebuild`
   unwraps every replay wrapper through `plainSourceOf`, at any nesting
   depth, so a hand-edited wrapped entry rebuilds from the scalar table
   and `rebuildable` answers what `rebuild` attempts.

2. **The reuse path has no test and no live consumer yet.** CLOSED by
   task 2. The toy fork and the reuse tests pin the carry, the reseek,
   the negative `presetFree` direction, and the second-preset hint
   machinery end to end.

3. **`SearchCtx.earlierWins` defaults to `#[]`.** CLOSED, cleanup batch
   A. The default is gone; every construction site names the table, so
   a forgotten field is a build error.

4. **The reuse source's placeholder tag can misreport the tried list.**
   DROPPED. The corpus writes `presets minimal mainnet`, so the
   mismatch needs a mainnet-first line no line spells; a per-instance
   source factory costs more than the diagnostics string it fixes.

5. **Wins are pushed for statements that can never read them.** CLOSED,
   cleanup batch A. The push is gated on the same `presetFree` flag the
   read side gates on.

## Task 2: the reuse toy tests

1. **The carried scalar is the default `0`, so a value-corrupting
   `scalarsOf` write regression stays green.** CLOSED, cleanup batch B.
   `toyReuse`'s hypothesis excludes the base default, the carried
   scalar is the solver's nonzero choice, and the replay-rebuild pin
   fails under a write of `0` (the reviewer injected the regression and
   confirmed).

2. **No negative pin on `Preset.presetFree`.** CLOSED, cleanup batch B.
   `toyPresetBound`'s `Fin` input type names the preset; the mainnet
   run's `bitVec` expectation fails under a universally-true check
   (injected and confirmed).

3. **`toyReseek` alone cannot detect reuse being disabled.** CLOSED,
   cleanup batch B, as a wording fix: the docstrings state that a
   rejected proposal is inferred, the check leaving no trace in a
   winning run. The module's regression signal for a disabled reuse
   stays on `toyReuse`, which the same build always runs.

4. **`leOf` and `searchCtxOf` duplicate `Tests/Hint.lean`.** CLOSED,
   cleanup batch B. `Tests/Support.lean` holds the one `leOf` and the
   one parameterized `searchCtxOf`; the private copies and the
   run_cmd-local `let` are gone. Three construction sites stay inline
   with stated reasons (a pinned-empty `instConsts`, two seeded drives).

## Task 3: the Gloas theorems at both presets

1. **The built source's guarded draw still samples the state when
   another container input sits beside it.** CARRIED TO STAGE 9. The
   fix needs a draw that samples the non-state containers alone, a
   probe-face change, and no corpus theorem reaches the case today.
   Stage 9's forks must not run a mainnet line whose theorem reaches
   it before the fix lands.

2. **The random source's own draw loop has no mainnet cap.** CARRIED TO
   STAGE 9. Same overflow root; no corpus theorem runs the random
   source at mainnet. A cap or a per-position draw belongs there before
   a line runs one.

3. **The guard has no direct toy-level pin, and the fix commit's
   message overstates the toy tests' coverage.** CLOSED, cleanup batch
   B. `Tests/BuiltDrive.lean` drives the built source over a toy
   catalog: the state-only drive pins the empty memo (the guard), the
   beside-a-list drive pins draw 0 (the nonempty path). The
   `c5f5b37` message's overstated claim stays as written in history;
   this item is its correction of record.

4. **`Generators/Gloas.lean`'s module docstring drift.** CLOSED, cleanup
   batch C. The header names the four theorems that run at both presets
   and where the mainnet witness comes from.
