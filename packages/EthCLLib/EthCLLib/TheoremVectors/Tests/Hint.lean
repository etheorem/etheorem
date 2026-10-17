import Lean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Hint
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Witness.Random
import EthCLLib.TheoremVectors.Witness.Shrink
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.Random
import EthCLLib.TheoremVectors.Tests.Support

/-!
# `EthCLLib.TheoremVectors.Tests.Hint`: the hint schema and the replay

Build-gate checks for stage 5 (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8):

- the fingerprint is a stable `0x…` hash that moves with its input;
- the hint file round trips through its derived JSON, and the scalars map
  writes decimal strings;
- a hint replays a bit-vector witness: the search's first source rebuilds
  the candidate, the loop's check accepts it, the record's source is
  `.hinted bitVec`, and the outcome folds the log to `replayed`;
- a hint with a wrong scalar fails the check, the search runs, and the
  outcome says `failed`;
- a stale fingerprint replays under `stale-replayed`;
- a random witness records its draw key (`seed`, `size`, `draw`), and the
  replay rebuilds the very draw bytes;
- a random entry carries the shrink path (§9.6, the plan's stage-6 step
  8), the traced replay's endpoint matches the original's, the walk
  re-records the same path, a bogus trace fails the replay, and a
  traceless entry replays through the full walk;
- `ignore` never applies the hint and the fixed-seed search lands on the
  same witness the hint recorded;
- the `hint` field's fold: `missing` with no file, `ignored` in `ignore`
  mode, `none` when no disjunct ran.

The command-level `require` error sits in `Tests/Command.lean`, where the
`#guard_msgs` machinery can watch it fail a build.

## Lean idioms annotated

- The drives run inside `run_cmd` with `liftTermElabM` and fold inside the
  reader's telescope scope, the same shapes the stage-2 to stage-4 test
  modules use. The scratch hint tree lives under this package's
  `.lake/build`, which the gitignore carries, and the final step removes
  it.
-/

set_option autoImplicit false

open Lean
open EthCLLib.Spec (HasherTag)

namespace EthCLLib.TheoremVectors.Tests.Hint

/-- The scratch hints root, under the package's gitignored build tree. -/
def scratchRoot : System.FilePath := ".lake/build/test-theorem-vectors-hints"

/-- The toy binding, whose state type is the toy container, the same
binding the random test drives. -/
def hintBinding : ForkBinding :=
  EthCLLib.TheoremVectors.Tests.Random.toyBoxBinding

/-- The toy function under the scalar pin. -/
def toyFun (x : UInt64) : UInt64 := x + 3

/-- The scalar pin's theorem: the `default` candidate `(0, 0)` fails the
hypothesis, so the base source cannot win and the solver must. -/
theorem toyBound [HasherTag] (a b : UInt64) (_h : a < b ∧ 0 < b) :
    toyFun a = a + 3 := rfl

/-- The evaluated probe for one drive theorem. -/
private def builtProbe (ctx : StatementCtx) (disjuncts : Array Disjunct) :
    MetaM (ProbeInfo × Probe) := do
  match ← Probe.ofStatement hintBinding .minimal ctx disjuncts #[] with
  | .ok r => pure r
  | .error e => throwError s!"the probe refused to build: {e}"

/-- Write one theorem's hint file into the scratch tree. -/
private def writeHints (thmLocal : String) (fp : String)
    (entries : Array HintEntry) : IO Unit :=
  Hint.write (Hint.file scratchRoot "toybase" thmLocal)
    { «theorem» := `EthCLLib.TheoremVectors.Tests.Hint.toy, fingerprint := fp, entries := entries }

/-- The scratch file of one theorem, read back. -/
private def readHints (thmLocal : String) : IO (Option HintFile) :=
  Hint.read? (Hint.file scratchRoot "toybase" thmLocal)

end EthCLLib.TheoremVectors.Tests.Hint

open Lean.Elab.Command
open EthCLLib.TheoremVectors
open EthCLLib.TheoremVectors.Tests.Hint in
run_cmd do
  liftTermElabM do
    -- ── the fingerprint pins: a stable `0x…` hash that moves with its
    -- input
    unless (fingerprintOf "abc").startsWith "0x" do
      throwError "the fingerprint is not a `0x…` hash"
    unless fingerprintOf "abc" == fingerprintOf "abc" do
      throwError "the fingerprint is not stable"
    unless fingerprintOf "abc" != fingerprintOf "abd" do
      throwError "the fingerprint ignores its input"
    -- ── the JSON pins: the file round trips, and the scalars map writes
    -- decimal strings, never bare numbers (§9.8)
    let scalars : HintScalars := { scalars := #[("bidAmount", 32000000001)] }
    unless toJson scalars == Json.mkObj [("bidAmount", Json.str "32000000001")] do
      throwError s!"the scalars map is not decimal strings: {toJson scalars}"
    let entry : HintEntry := { preset := .minimal, disjunctIndex := 0, side := some true, source := .random, seed := some 7, size := some 8, draw := some 3, scalars := scalars }
    let f : HintFile := { «theorem» := `T, fingerprint := "0x01", entries := #[entry] }
    match fromJson? (α := HintFile) (toJson f) with
    | .ok f2 =>
      unless f2 == f do
        throwError s!"the hint JSON round trip changed the file: {repr f2}"
    | .error e => throwError s!"the hint JSON round trip failed to parse: {e}"
    -- ── the `hint` field's fold
    unless Hint.runHintField .use none .minimal 1 0 #[] == some "missing" do
      throwError "no file should fold to `missing`"
    unless Hint.runHintField .ignore none .minimal 1 0 #[] == some "ignored" do
      throwError "mode `ignore` should fold to `ignored`"
    unless Hint.runHintField .use none .minimal 0 0 #[] == none do
      throwError "no disjunct should fold to no field"
    let emptyFile : HintFile := { «theorem» := `T, fingerprint := "", entries := #[] }
    unless Hint.runHintField .use (some emptyFile) .minimal 1 0 #[] ==
        some "missing" do
      throwError "a file without entries should fold to `missing`"
    unless Hint.runHintField .use (some f) .minimal 1 1 #[] ==
        some "missing" do
      throwError "a fresh win beside replays should fold to `missing`"

    -- ── the bit-vector replay: search, record, replay, and the record's
    -- source is `.hinted bitVec`
    Statement.readIn hintBinding `EthCLLib.TheoremVectors.Tests.Hint.toyBound
      fun ctx => do
      let stmt ← Scope.classify hintBinding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyBound: expected one disjunct, got {disjuncts.size}"
      let d := disjuncts[0]!
      let (info, probe) ← builtProbe ctx disjuncts
      let fp := Hint.fingerprint stmt.thm info
      -- the search without hints: the base defaults fail, the solver wins
      let sctx ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let (a0, won0) ← match ← searchDisjunct #[baseSource, bitVecSource] sctx stmt d with
        | .ok r => pure r
        | .error f => throwError s!"toyBound: the search found nothing: {repr f}"
      unless won0 == .bitVec do
        throwError s!"toyBound: expected the bit-vector source to win, \
          got {won0.tag}"
      unless Tests.Support.leOf a0[0]! < Tests.Support.leOf a0[1]! && Tests.Support.leOf a0[1]! ≥ 1 do
        throwError s!"toyBound: the witness ({Tests.Support.leOf a0[0]!}, {Tests.Support.leOf a0[1]!}) \
          missed its window"
      -- the entry the command would write
      let some e ← Hint.entryOf sctx stmt d a0 won0 0 8 fp
        | throwError "toyBound: the winning witness produced no hint entry"
      unless e.source == .bitVec do
        throwError s!"toyBound: the entry names {e.source.tag}, expected bitVec"
      unless e.scalars.scalars.any fun (n, _) => n == "a" do
        throwError "toyBound: the entry holds no scalar for `a`"
      -- the replay: the hint source runs first and wins under `.hinted`
      writeHints "toyBound" fp #[e]
      let some file ← readHints "toyBound"
        | throwError "toyBound: the hint file did not read back"
      let log ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let hintSrc := Hint.source .use (some file) fp log
      let sctx2 ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      match ← searchDisjunct #[hintSrc, baseSource, bitVecSource] sctx2 stmt d with
      | .ok (a1, won1) =>
        unless won1 matches .hinted (.bitVec) do
          throwError s!"toyBound: expected a hinted replay, got {won1.tag}"
        unless probe.check d.index a1 do
          throwError "toyBound: the replayed candidate failed the check"
        unless a1 == a0 do
          throwError "toyBound: the replay differs from the searched witness"
      | .error f =>
        throwError s!"toyBound: the replay found nothing: {repr f}"
      let logV ← log.get
      unless logV == #[(d.index, .replayed)] do
        throwError s!"toyBound: expected one replayed attempt, got {repr logV}"
      unless Hint.runHintField .use (some file) .minimal disjuncts.size 0 logV ==
          some "replayed" do
        throwError "toyBound: the outcome should say `replayed`"
      -- a wrong scalar: the hint fails, the search runs, the outcome says
      -- `failed`
      let zeroed := e.scalars.scalars.map fun (n, _) => (n, 0)
      let wrong : HintEntry := { e with scalars := { scalars := zeroed } }
      writeHints "toyBound" fp #[wrong]
      let some wrongFile ← readHints "toyBound"
        | throwError "toyBound: the wrong-scalar file did not read back"
      let log3 ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let hint3 := Hint.source .use (some wrongFile) fp log3
      let sctx3 ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      match ← searchDisjunct #[hint3, baseSource, bitVecSource] sctx3 stmt d with
      | .ok (_, won3) =>
        unless won3 == .bitVec do
          throwError s!"toyBound: after the failed hint the search should \
            win again, got {won3.tag}"
      | .error f =>
        throwError s!"toyBound: after the failed hint the search found \
          nothing: {repr f}"
      let log3V ← log3.get
      unless log3V == #[(d.index, HintAttempt.failed)] do
        throwError s!"toyBound: expected one failed attempt, got {repr log3V}"
      unless Hint.runHintField .use (some wrongFile) .minimal disjuncts.size 0
          log3V == some "failed" do
        throwError "toyBound: the outcome should say `failed`"
      -- a stale fingerprint: the replay still answers, under
      -- `stale-replayed`. The entry carries the operative fingerprint,
      -- so the stale stamp goes on it.
      let staleE : HintEntry := { e with fingerprint := some "0xdeadbeef" }
      writeHints "toyBound" "0xdeadbeef" #[staleE]
      let some staleFile ← readHints "toyBound"
        | throwError "toyBound: the stale file did not read back"
      let log4 ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let hint4 := Hint.source .use (some staleFile) fp log4
      let sctx4 ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      match ← searchDisjunct #[hint4, baseSource, bitVecSource] sctx4 stmt d with
      | .ok (_, won4) =>
        unless won4 matches .hinted (.bitVec) do
          throwError s!"toyBound: the stale hint should replay, got {won4.tag}"
      | .error f =>
        throwError s!"toyBound: the stale hint did not replay: {repr f}"
      let log4V ← log4.get
      unless log4V == #[(d.index, HintAttempt.staleReplayed)] do
        throwError s!"toyBound: expected one stale-replayed attempt, got \
          {repr log4V}"
      unless Hint.runHintField .use (some staleFile) .minimal disjuncts.size 0
          log4V == some "stale-replayed" do
        throwError "toyBound: the outcome should say `stale-replayed`"

    -- ── the random replay: the entry records the draw key, and the replay
    -- rebuilds the very draw bytes; `ignore` searches and lands on the
    -- same witness
    Statement.readIn hintBinding
      `EthCLLib.TheoremVectors.Tests.Random.toyBoxBound fun ctx => do
      let stmt ← Scope.classify hintBinding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyBoxBound: expected one disjunct, got {disjuncts.size}"
      let d := disjuncts[0]!
      let (info, probe) ← builtProbe ctx disjuncts
      let fp := Hint.fingerprint stmt.thm info
      -- the search without hints: the base source refuses the state type,
      -- the random source wins (the random test pins the same answer)
      let sctx ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let (a0, won0) ←
        match ← searchDisjunct #[baseSource, bitVecSource, randomSource] sctx stmt d with
        | .ok r => pure r
        | .error f => throwError s!"toyBoxBound: the search found nothing: {repr f}"
      unless won0 == .random do
        throwError s!"toyBoxBound: expected the random source to win, \
          got {won0.tag}"
      -- the entry records the draw key: seed, size, draw
      let some e ← Hint.entryOf sctx stmt d a0 won0 0 8 fp
        | throwError "toyBoxBound: the winning draw produced no hint entry"
      unless e.source == .random do
        throwError s!"toyBoxBound: the entry names {e.source.tag}, expected random"
      unless e.seed == some 0 && e.size == some 8 && e.draw.isSome do
        throwError s!"toyBoxBound: the draw key is incomplete: \
          {repr e.seed} {repr e.size} {repr e.draw}"
      -- a draw is a pure function of the seed, the size, and the index,
      -- so the replay rebuilds the same container bytes from the entry's
      -- key (§9.8)
      let raw := probe.sample (e.seed.getD 0 + e.draw.getD 0) (e.size.getD 8)
      unless raw == a0 do
        throwError "toyBoxBound: the draw does not replay from its key"
      -- the shrink path the command records for the entry (the plan's
      -- stage-6 step 8), and its endpoint
      let (shrunk0, tr0) ← shrinkTraceWitness probe d.index 40 a0
      unless shrunk0 == a0 || !tr0.isEmpty do
        throwError "toyBoxBound: the shrink recorded no path for a \
          smaller witness"
      -- the replay, with the trace in the entry: the hint source hands
      -- back the pre-shrink draw, and the recorded path walks it to the
      -- same endpoint the original reached
      let traced : HintEntry := { e with shrink := some tr0 }
      writeHints "toyBoxBound" fp #[traced]
      let some file ← readHints "toyBoxBound"
        | throwError "toyBoxBound: the hint file did not read back"
      let log ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let sctx2 ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let hintSrc := Hint.source .use (some file) fp log
      let a1 ←
        match ← searchDisjunct #[hintSrc, baseSource, bitVecSource, randomSource]
            sctx2 stmt d with
        | .ok (a, won) =>
          unless won matches .hinted (.random) do
            throwError s!"toyBoxBound: expected a hinted replay, got {won.tag}"
          pure a
        | .error f =>
          throwError s!"toyBoxBound: the replay found nothing: {repr f}"
      unless a1 == a0 do
        throwError "toyBoxBound: the replay differs from the searched draw"
      let some shrunk1 ← shrinkReplayWitness probe d.index tr0 a1
        | throwError "toyBoxBound: the recorded path did not replay"
      unless shrunk1 == shrunk0 do
        throwError "toyBoxBound: the traced replay's endpoint differs from \
          the original's"
      -- the walk re-records the same path from the same draw, so the
      -- refreshed entry is the entry the replay consumed (§9.8)
      let (_, tr1) ← shrinkTraceWitness probe d.index 40 a1
      unless tr1 == tr0 do
        throwError "toyBoxBound: the replay re-recorded a different path"
      -- a recorded path the candidate list does not reach fails at the
      -- command's shrink step, which falls back to the full walk and
      -- records its own path; the pre-shrink replay itself still passes
      -- the check, because the check is the same `decide` the original
      -- run answered
      let bogus? ← shrinkReplayWitness probe d.index #[#[999]] a0
      unless bogus?.isNone do
        throwError "toyBoxBound: a bogus trace replayed"
      -- a traceless entry replays through the full walk, the stage-5
      -- rule for entries written before the trace existed
      writeHints "toyBoxBound" fp #[e]
      let some file2 ← readHints "toyBoxBound"
        | throwError "toyBoxBound: the hint file did not read back"
      let log2 ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let sctx4 ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let hintSrc2 := Hint.source .use (some file2) fp log2
      let a2 ←
        match ← searchDisjunct #[hintSrc2, baseSource, bitVecSource, randomSource]
            sctx4 stmt d with
        | .ok (a, won) => pure (a, won)
        | .error f =>
          throwError s!"toyBoxBound: the traceless replay found nothing: {repr f}"
      unless a2.1 == a0 && (a2.2 matches .hinted (.random)) do
        throwError "toyBoxBound: the traceless replay diverged"
      let shrunk2 ← shrinkWitness probe d.index 40 a2.1
      unless shrunk2 == shrunk0 do
        throwError "toyBoxBound: the traceless replay's shrink diverged from \
          the original's"
      -- `ignore`: the hint never applies, and the fixed-seed search lands
      -- on the same witness
      let logIg ← IO.mkRef (#[] : Array (Nat × HintAttempt))
      let hintIg := Hint.source .ignore (some file) fp logIg
      let sctx3 ← Tests.Support.searchCtxOf hintBinding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      match ← searchDisjunct #[hintIg, baseSource, bitVecSource, randomSource]
          sctx3 stmt d with
      | .ok (a2, won2) =>
        unless won2 == .random do
          throwError s!"toyBoxBound: mode `ignore` should search, got \
            {won2.tag}"
        unless a2 == a0 do
          throwError "toyBoxBound: mode `ignore` drew a different witness \
            for the fixed seed"
      | .error f =>
        throwError s!"toyBoxBound: mode `ignore` found nothing: {repr f}"
      let logIgV ← logIg.get
      unless logIgV.isEmpty do
        throwError "toyBoxBound: mode `ignore` logged a hint attempt"
      unless Hint.runHintField .ignore (some file) .minimal disjuncts.size 0
          logIgV == some "ignored" do
        throwError "toyBoxBound: the outcome should say `ignored`"

    -- the scratch tree goes away
    IO.FS.removeDirAll scratchRoot
