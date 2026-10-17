import Lean.Elab.Command
import EthCLLib.TheoremVectors.Command
import EthCLLib.TheoremVectors.Tests.ReuseFork
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Hint
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.Outcome
import EthCLLib.TheoremVectors.Tests.Support

/-!
# `EthCLLib.TheoremVectors.Tests.Reuse`: the witness-reuse path

Build-gate checks for §10's witness reuse over a two-preset toy fork
(`THEOREM_VECTORS_ARCHITECTURE.md` §10), driving the machinery task 1
landed: `Preset.presetFree`, `reuseSearcher`, the `.reused` hint arms, and
the command's `winsRef` threading.

The command drive runs three scalar theorems at `minimal mainnet`:

- `toyReuse`'s hypothesis `0 < x ∧ x < P.bound` excludes the base
  searcher's serialized default `0`, so the minimal run's witness is the
  solver's choice in `[1, 7]`: the minimal record names `bitVec`, and
  its hint entry carries the scalar table. Every value in `[1, 7]`
  satisfies `0 < x ∧ x < 32`, so the mainnet run wins from the reuse
  searcher: its record names `reused-minimal`, its bytes equal the
  minimal record's, and its hint entry holds the carried scalar table.
  The carry is a solver-chosen nonzero value, so a `scalarsOf` write
  regression that recorded a wrong value cannot pass: the replay drive
  rebuilds the carried entry to the minimal record's bytes.
- `toyReseek`'s minimal window `x < P.bound ∧ x + 4 > P.bound` admits
  only witnesses below 8, and none of them satisfies `x + 4 > 32`: the
  two windows are disjoint. What the outputs pin is the observable
  shape: both records name `bitVec`, and their input bytes differ. That
  a reuse proposal was made and rejected at mainnet is inferred. The
  check is the only witness of a rejection, and a winning run records
  no rejected proposal.
- `toyPresetBound`'s input type names the preset's own constant, so the
  preset-free type check marks the statement preset-bound and the reuse
  searcher never proposes at either preset: both runs search. The
  mainnet run's searcher names `bitVec` and no `reused-*` tag, the
  negative pin on `Preset.presetFree`: a check that answered `true`
  universally would carry the minimal witness, because the same bytes
  satisfy `1 < i.val` under both bounds, and name `reused-minimal` at
  mainnet.

The direct drives then pin the second-preset hint machinery on the files
the command drive wrote: the mainnet entry rebuilds from its scalar table
to the minimal record's bytes, and a fresh `Hint.searcher` replay at mainnet
wins with the tag `.hinted (.reused .minimal)` and logs one `replayed`
attempt.

## Lean idioms annotated

- The command drive runs inside the file's own `run_cmd` passes, the same
  shape `Tests/Command.lean` uses: the header and the two lines elaborate
  first, the outcome reader runs after them, and the final pass removes
  the scratch tree.
- The toy theorems bind `[P : Preset]`, whose class name's last
  component the reader's `instanceKindOf` classifies as the preset seam.
  The binder carries the name `P` because the hypotheses read `P.bound`,
  and an unnamed instance binder has no name to read through. The proof
  term is `rfl`, because each conclusion is definitionally `x = x`; the
  hypotheses are what the search solves.
- The scratch output tree lives under this package's `.lake/build`, which
  the gitignore carries.
- The drive assumes `THEOREM_VECTORS_HINTS` is unset, the assumption
  `Tests/Command.lean`'s `require` guard states: a developer shell that
  exports it breaks the drive.
-/

set_option autoImplicit false

open Lean
open Lean.Elab.Command

-- the same string `ReuseFork.scratchOutDir` spells; the option takes a
-- literal, so the two spellings must stay in step
set_option theorem_vectors.outDir ".lake/build/test-theorem-vectors-reuse"

namespace EthCLLib.TheoremVectors.Tests.Reuse

open EthCLLib.TheoremVectors.Tests.ReuseFork (Preset scratchOutDir)

/-- The identity the reuse theorem's conclusion states. -/
def reuseFun (x : UInt64) : UInt64 := x

/-- The identity the reseek theorem's conclusion states. -/
def reseekFun (x : UInt64) : UInt64 := x

/-- The minimal witness is the solver's choice in `[1, 7]`: the base
searcher's serialized default `0` fails `0 < x`, so the bit-vector
searcher wins and the minimal entry carries the scalar table. Every value in
`[1, 7]` satisfies `0 < x ∧ x < 32`, so the mainnet check accepts the
carried candidate and the reuse searcher carries it over unchanged. -/
theorem toyReuse [P : Preset] (x : UInt64) (_h : 0 < x ∧ x < P.bound) :
    reuseFun x = x := rfl

/-- The two windows are disjoint: every witness the minimal window
`x < 8 ∧ x + 4 > 8` admits sits below 8, and the mainnet window
`x + 4 > 32` starts at 29, so a carried minimal candidate could not
satisfy the mainnet hypothesis. What the run outputs pin is the
observable shape: both runs search, and the two witnesses' bytes
differ. That a reuse proposal was made and rejected is inferred, the
check being the only witness of it and a winning run leaving no trace
of a rejected proposal. The upper conjunct pins the minimal witness
below the mainnet window whatever model the solver returns. -/
theorem toyReseek [P : Preset] (x : UInt64)
    (_h : x < P.bound ∧ x + 4 > P.bound) :
    reseekFun x = x := rfl

/-- The identity the preset-bound theorem's conclusion states. -/
def presetBoundFun (n : Nat) : Nat := n

/-- The input type names the preset's own constant, so the type check
marks the statement preset-bound and the reuse searcher never proposes:
both runs search. -/
theorem toyPresetBound [P : Preset] (i : Fin (2 * P.bound.toNat))
    (_h : 1 < i.val) : presetBoundFun i.val = i.val := rfl

/-- The theorem's local name, the prefix strip the command runs
(`Command.lean`'s `runTheorem`). The toy theorems sit outside the fork's
proof namespace, so the strip leaves the full name; the path helpers go
through this one function, so the drives read the paths the command
actually wrote. -/
private def localNameOf (thm : Name) : String :=
  thm.replacePrefix
    (EthCLLib.Internal.proofNamespaceOf
      EthCLLib.TheoremVectors.Tests.ReuseFork.reuseBinding.fork)
    .anonymous
  |>.toString

/-- The outcome file of one of this module's theorems, read back. -/
private def readOutcome (thm : Name) : CommandElabM Outcome := do
  let path := EthCLLib.TheoremVectors.Tests.ReuseFork.scratchOutDir /
    "outcomes" / "toypresets" / (localNameOf thm ++ ".json")
  liftIO <| Outcome.read path

/-- One theorem's record directory at one preset, disjunct 0, no side. -/
private def recordDirOf (thm : Name) (p : EthCLLib.TheoremVectors.PresetId) :
    System.FilePath :=
  EthCLLib.TheoremVectors.Record.disjunctDir
    EthCLLib.TheoremVectors.Tests.ReuseFork.scratchOutDir "toypresets" p
    (localNameOf thm) 0 none

/-- One theorem's output-tree hint file, read back. -/
private def readHints (thm : Name) :
    IO (Option EthCLLib.TheoremVectors.HintFile) :=
  EthCLLib.TheoremVectors.Hint.read?
    (EthCLLib.TheoremVectors.Hint.file
      (EthCLLib.TheoremVectors.Tests.ReuseFork.scratchOutDir / "hints")
      "toypresets" (localNameOf thm))

-- the open activates the commands' scoped syntax
open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLLib.TheoremVectors.Tests.ReuseFork.reuseBinding
theorem_vectors EthCLLib.TheoremVectors.Tests.Reuse.toyReuse presets minimal mainnet
theorem_vectors EthCLLib.TheoremVectors.Tests.Reuse.toyReseek presets minimal mainnet
theorem_vectors EthCLLib.TheoremVectors.Tests.Reuse.toyPresetBound presets minimal mainnet

/-- Read one outcome file back and pin the two runs' shapes: the preset,
the status, and the searcher tag each run wrote. -/
private def pinRuns (o : Outcome) (minimalSearcher mainnetSearcher : String) :
    CommandElabM Unit := do
  unless o.runs.size == 2 do
    throwError s!"{o.theorem}: {o.runs.size} runs, expected 2"
  let r0 := o.runs[0]!
  unless r0.preset == some .minimal && r0.status == .written &&
      r0.witnessSearcher == some minimalSearcher do
    throwError s!"{o.theorem}: the minimal run is {repr r0}, expected \
      minimal / written / {minimalSearcher}"
  let r1 := o.runs[1]!
  unless r1.preset == some .mainnet && r1.status == .written &&
      r1.witnessSearcher == some mainnetSearcher do
    throwError s!"{o.theorem}: the mainnet run is {repr r1}, expected \
      mainnet / written / {mainnetSearcher}"

-- The command drive's answers: the reuse theorem's minimal witness is
-- the solver's choice in `[1, 7]` (the base default `0` fails `0 < x`),
-- and it carries over byte-identical, so the carried scalar is a
-- nonzero value the solver chose; the base default fails the new
-- hypothesis, so a scalar-table write of `0` cannot pass. The reseek
-- theorem's windows are disjoint, so both of its runs searched. The
-- preset-bound theorem's input type names the preset, so reuse never
-- proposes for it: both runs searched fresh. The reuse theorem's
-- minimal run is won by the bit-vector searcher, because the base
-- searcher's serialized default `0` fails `0 < x`.
run_cmd do
  pinRuns (← readOutcome `EthCLLib.TheoremVectors.Tests.Reuse.toyReuse)
    "bitVec" "reused-minimal"
  pinRuns (← readOutcome `EthCLLib.TheoremVectors.Tests.Reuse.toyReseek)
    "bitVec" "bitVec"
  -- `toyPresetBound`'s mainnet `"bitVec"` expectation is the negative
  -- pin on `Preset.presetFree`: the preset-bound input type sends the
  -- run to a fresh search, and the theorem's docstring records why a
  -- carried witness would otherwise pass.
  pinRuns (← readOutcome `EthCLLib.TheoremVectors.Tests.Reuse.toyPresetBound)
    "bitVec" "bitVec"

  -- ── the records: the reuse theorem's two records carry byte-identical
  -- witnesses, and the mainnet record's searcher reads back as
  -- `.reused .minimal` through the tag reader's `reused-` prefix
  let reuseMin ← liftIO <| Record.read (recordDirOf
    `EthCLLib.TheoremVectors.Tests.Reuse.toyReuse .minimal)
  let reuseMain ← liftIO <| Record.read (recordDirOf
    `EthCLLib.TheoremVectors.Tests.Reuse.toyReuse .mainnet)
  unless reuseMin.record.witnessSearcher == .bitVec do
    throwError s!"toyReuse: the minimal record's searcher is \
      {reuseMin.record.witnessSearcher.tag}, expected bitVec"
  unless reuseMain.record.witnessSearcher == .reused .minimal do
    throwError s!"toyReuse: the mainnet record's searcher is \
      {reuseMain.record.witnessSearcher.tag}, expected reused-minimal"
  unless reuseMin.inputBytes == reuseMain.inputBytes do
    throwError "toyReuse: the mainnet record's input bytes differ from \
      the minimal record's; the witness did not carry over unchanged"
  -- the minimal witness is the solver's, in `[1, 7]`: the base default
  -- `0` fails `0 < x`, so a write regression that lost the solver's
  -- choice would leave bytes outside the window
  let v := Tests.Support.leOf reuseMin.inputBytes[0]!
  unless 0 < v && v < 8 do
    throwError s!"toyReuse: the minimal witness {v} left its window \
      [1, 7]"

  -- ── the reseek records: a fresh witness at mainnet, whose decoded
  -- value satisfies the mainnet hypothesis, while the minimal record's
  -- satisfies the minimal one
  let reseekMin ← liftIO <| Record.read (recordDirOf
    `EthCLLib.TheoremVectors.Tests.Reuse.toyReseek .minimal)
  let reseekMain ← liftIO <| Record.read (recordDirOf
    `EthCLLib.TheoremVectors.Tests.Reuse.toyReseek .mainnet)
  unless reseekMin.record.witnessSearcher == .bitVec do
    throwError s!"toyReseek: the minimal record's searcher is \
      {reseekMin.record.witnessSearcher.tag}, expected bitVec"
  unless reseekMain.record.witnessSearcher == .bitVec do
    throwError s!"toyReseek: the mainnet record's searcher is \
      {reseekMain.record.witnessSearcher.tag}, expected bitVec"
  unless reseekMin.inputBytes != reseekMain.inputBytes do
    throwError "toyReseek: the mainnet record's input bytes equal the \
      minimal record's; a fresh search should have run"
  unless Tests.Support.leOf reseekMin.inputBytes[0]! < 8 do
    throwError s!"toyReseek: the minimal witness {Tests.Support.leOf
      reseekMin.inputBytes[0]!} misses its own window"
  unless Tests.Support.leOf reseekMin.inputBytes[0]! + 4 > 8 do
    throwError s!"toyReseek: the minimal witness {Tests.Support.leOf
      reseekMin.inputBytes[0]!} misses its own window"
  unless Tests.Support.leOf reseekMain.inputBytes[0]! < 32 do
    throwError s!"toyReseek: the mainnet witness {Tests.Support.leOf
      reseekMain.inputBytes[0]!} misses the mainnet window"
  unless Tests.Support.leOf reseekMain.inputBytes[0]! + 4 > 32 do
    throwError s!"toyReseek: the mainnet witness {Tests.Support.leOf
      reseekMain.inputBytes[0]!} misses the mainnet window"

  -- ── the output tree's hint files: a `.bitVec` entry at minimal (the
  -- solver's win carries the scalar table), a `.reused .minimal` entry
  -- at mainnet whose scalar table covers the input `x`, and two
  -- `.bitVec` entries for the reseek theorem
  let some reuseFile ← liftIO <| readHints
    `EthCLLib.TheoremVectors.Tests.Reuse.toyReuse
    | throwError "toyReuse: the output tree's hint file did not read back"
  let some reuseMinE := reuseFile.entries.find? fun e => e.preset == .minimal
    | throwError "toyReuse: the hint file holds no minimal entry"
  let some reuseMainE := reuseFile.entries.find? fun e => e.preset == .mainnet
    | throwError "toyReuse: the hint file holds no mainnet entry"
  unless reuseMinE.witnessSearcher == .bitVec do
    throwError s!"toyReuse: the minimal entry names \
      {reuseMinE.witnessSearcher.tag}, expected bitVec"
  unless reuseMinE.scalars.scalars.any fun (n, _) => n == "x" do
    throwError "toyReuse: the minimal entry holds no scalar for `x`"
  unless reuseMainE.witnessSearcher == .reused .minimal do
    throwError s!"toyReuse: the mainnet entry names \
      {reuseMainE.witnessSearcher.tag}, expected reused-minimal"
  unless reuseMainE.scalars.scalars.any fun (n, _) => n == "x" do
    throwError "toyReuse: the mainnet entry holds no scalar for `x`"
  let some reseekFile ← liftIO <| readHints
    `EthCLLib.TheoremVectors.Tests.Reuse.toyReseek
    | throwError "toyReseek: the output tree's hint file did not read back"
  let some reseekMinE := reseekFile.entries.find? fun e => e.preset == .minimal
    | throwError "toyReseek: the hint file holds no minimal entry"
  let some reseekMainE := reseekFile.entries.find? fun e => e.preset == .mainnet
    | throwError "toyReseek: the hint file holds no mainnet entry"
  unless reseekMinE.witnessSearcher == .bitVec do
    throwError s!"toyReseek: the minimal entry names \
      {reseekMinE.witnessSearcher.tag}, expected bitVec"
  unless reseekMainE.witnessSearcher == .bitVec do
    throwError s!"toyReseek: the mainnet entry names \
      {reseekMainE.witnessSearcher.tag}, expected bitVec"

-- The replay drive at mainnet, on the files the command drive wrote: the
-- mainnet entry's fingerprint matches a fresh probe's, the scalar-table
-- rebuild answers the minimal record's bytes, and the hint searcher replays
-- the entry under `.hinted (.reused .minimal)` with one `replayed` log
-- line.
run_cmd do
  liftTermElabM do
    let binding := EthCLLib.TheoremVectors.Tests.ReuseFork.reuseBinding
    let thm := `EthCLLib.TheoremVectors.Tests.Reuse.toyReuse
    Statement.readIn binding thm fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyReuse: expected one disjunct, got {disjuncts.size}"
      let d := disjuncts[0]!
      let (info, probe) ←
        match ← Probe.ofStatement binding .mainnet ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toyReuse: the probe refused to build: {e}"
      let fp := Hint.fingerprint stmt.thm info
      let some file ← liftM (m := IO) (readHints thm)
        | throwError "toyReuse: the output tree's hint file did not read back"
      let some mainnetE := file.entries.find? fun e => e.preset == .mainnet
        | throwError "toyReuse: the hint file holds no mainnet entry"
      unless mainnetE.fingerprint == some fp do
        throwError s!"toyReuse: the mainnet entry's fingerprint \
          {mainnetE.fingerprint} differs from the fresh probe's {fp}"
      -- the scalar-table rebuild (task 1's `Hint.rebuild` arm): the
      -- entry's table answers the minimal record's input bytes
      let sctx ← Tests.Support.searchCtxOf binding .mainnet
        ReuseFork.scratchOutDir "" stmt ctx info probe
      let some rebuilt ← Hint.rebuild sctx stmt mainnetE
        | throwError "toyReuse: the mainnet entry rebuilt no candidate"
      let minRB ← liftM (m := IO) (Record.read (recordDirOf thm .minimal))
      unless rebuilt == minRB.inputBytes do
        throwError "toyReuse: the scalar-table rebuild differs from the \
          minimal record's input bytes"
      -- the rebuild reads the table: a mutated entry rebuilds to the
      -- mutated value, so the carried witness's bytes come from the
      -- entry's scalars and never from the missing-scalar fallback.
      -- `24` satisfies the carried hypothesis (`0 < 24 ∧ 24 < 32`), so
      -- the mutated rebuild stays a candidate the mainnet window admits
      let mutatedVals : Array (String × Nat) :=
        mainnetE.scalars.scalars.map fun (n, _) => (n, 24)
      let mutated := { mainnetE with scalars := { scalars := mutatedVals } }
      let some mutatedB ← Hint.rebuild sctx stmt mutated
        | throwError "toyReuse: the mutated entry rebuilt no candidate"
      unless Tests.Support.leOf mutatedB[0]! == 24 do
        throwError s!"toyReuse: the mutated entry rebuilt \
          {Tests.Support.leOf mutatedB[0]!}, expected 24"
      -- the replay: the hint searcher runs first and wins under
      -- `.hinted (.reused .minimal)`
      let log ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let hintSearcher := Hint.searcher .use (some file) fp log
      match ← searchDisjunct #[hintSearcher, baseSearcher, bitVecSearcher] sctx stmt d with
      | .ok (a, won) =>
        unless won == .hinted (.reused .minimal) do
          throwError s!"toyReuse: expected a `.hinted (.reused .minimal)` \
            win, got {won.tag}"
        unless a == minRB.inputBytes do
          throwError "toyReuse: the replayed candidate differs from the \
            minimal record's input bytes"
      | .error f =>
        throwError s!"toyReuse: the replay found nothing: {repr f}"
      let logV ← log.get
      unless logV == #[(d.index, HintAttempt.replayed)] do
        throwError s!"toyReuse: expected one replayed attempt, got \
          {repr logV}"

-- Remove the scratch output tree, the suite's create-then-remove
-- convention.
run_cmd do
  IO.FS.removeDirAll EthCLLib.TheoremVectors.Tests.ReuseFork.scratchOutDir

end EthCLLib.TheoremVectors.Tests.Reuse
