import Lean
import EthCLLib.TheoremVectors.ClientResults
import EthCLLib.TheoremVectors.Formats.Function
import EthCLLib.TheoremVectors.Report

/-!
# `EthCLLib.TheoremVectors.Tests.ClientResults`: the client answers' read-back

Build-gate checks for the client harness's results file
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.3) and its two readers. The toy
writes a `client-results.json` with one `passed`, one `failed`, and one
`skipped` entry into a scratch outDir under this package's gitignored
`.lake/build`, renders the matching toy function-format files, and pins
the three `check` answers plus the `noConsumer` answer for a record with
no entry, both with the file in place and with the file absent (the
harness-never-ran state), plus the malformed-file error the read
contract promises. The report's Formats cell (§16.2) is pinned
over the same entries: `prysm passed`, `prysm failed`, `prysm skipped`,
and the empty cell for the theorem no entry ran. A theorem with one
passed and one failed disjunct pins the worst-answer-wins aggregation. The
skipped entry's
file name carries the `_t` side marker, so the report's join pins the
side-marker strip in `ClientResults.thmOfPath` too.

The final `run_cmd` removes the scratch tree.
-/

set_option autoImplicit false

open Lean
open Lean.Elab.Command

namespace EthCLLib.TheoremVectors.Tests.ClientResults

/-- The scratch outDir, under the package's gitignored build tree. -/
private def toyOut : System.FilePath := ".lake/build/test-client-results"

/-- The toy render environment: the scratch outDir, and a bindings
table that answers `none` everywhere (the function format's `check`
reads the outDir alone). -/
private def toyEnv : RenderEnv where
  outDir := toyOut
  bindings := fun _ => none

/-- One toy entry, in the harness's own directory and file-name shapes
(§13.3): the target directory holds the file, and the file name carries
the theorem, the disjunct index, and the side marker. -/
private def entry (file : String) (status : ClientStatus)
    (detail : String) : ClientResult :=
  { path := s!"formats/function/gloas/minimal/EthCLSpecs.Toy.toyFn/{file}",
    fork := "gloas", preset := "minimal", pyspecName := "toy_fn",
    status, detail }

/-- The toy entries: one per status, each naming its theorem, plus the
two `toyMixed` entries whose cells must aggregate to `prysm failed`. -/
private def toyResults : Array ClientResult :=
  #[ entry "EthCLSpecs.Proofs.Gloas.toyPass_0.yaml" .passed
       "post state matched (bytes and root)",
     entry "EthCLSpecs.Proofs.Gloas.toyFail_0.yaml" .failed
       "the client computed 7, the vector expects 5",
     entry "EthCLSpecs.Proofs.Gloas.toySkip_0_t.yaml" .skipped
       "tabled skip: the coverage table maps the target to nothing",
     entry "EthCLSpecs.Proofs.Gloas.toyMixed_0.yaml" .passed "matched",
     entry "EthCLSpecs.Proofs.Gloas.toyMixed_1.yaml" .failed
       "the client computed 9, the vector expects 4" ]

/-- One toy record, `.runOk` shape, at the toy target. -/
private def toyRecord (thm : Name) (side : Option Bool) : VectorRecord :=
  { «theorem» := thm, fork := "gloas", preset := .minimal,
    target := some `EthCLSpecs.Toy.toyFn, pyspecName := some "toy_fn",
    shape := .runOk, disjunctIndex := 0, side, inputs := #[],
    output := none, error := none, witnessSearcher := .random }

/-- The toy theorems, in the order of `toyResults`' theorems, plus the
theorem no entry ran. -/
private def toyThms : Array Name :=
  #[`EthCLSpecs.Proofs.Gloas.toyPass, `EthCLSpecs.Proofs.Gloas.toyFail,
    `EthCLSpecs.Proofs.Gloas.toySkip, `EthCLSpecs.Proofs.Gloas.toyMixed,
    `EthCLSpecs.Proofs.Gloas.toyNone]

/-- The sides the toy records carry: the skipped entry's file name ends
in `_t`, so its record marks the side. -/
private def toySide (thm : Name) : Option Bool :=
  if thm == `EthCLSpecs.Proofs.Gloas.toySkip then some true else none

/-- The toy files to render, one pair per function-format file: the
mixed theorem renders two disjuncts, the others one. -/
private def toyFiles : Array (Name × Nat) :=
  #[(`EthCLSpecs.Proofs.Gloas.toyPass, 0), (`EthCLSpecs.Proofs.Gloas.toyFail, 0),
    (`EthCLSpecs.Proofs.Gloas.toySkip, 0), (`EthCLSpecs.Proofs.Gloas.toyMixed, 0),
    (`EthCLSpecs.Proofs.Gloas.toyMixed, 1), (`EthCLSpecs.Proofs.Gloas.toyNone, 0)]

/-- Render one toy function-format file, and return the written path. -/
private def renderToy (thm : Name) (disjunctIndex : Nat) : IO System.FilePath := do
  let files ← Formats.function.render toyEnv
    ({ toyRecord thm (toySide thm) with disjunctIndex }) #[] none
  unless files.size == 1 do
    throw (IO.userError s!"toy render: {files.size} files for {thm}, expected 1")
  return files[0]!

/-- A `CheckResult` as a message string. The inductive carries no
`Repr`, so the failure text spells the answer by hand. -/
private def showCheck : CheckResult → String
  | .passed     => "passed"
  | .failed d   => s!"failed ({d})"
  | .noConsumer => "noConsumer"

/-- Check one toy record, and fail unless the answer matches the
expected one, detail included. -/
private def expectCheck (thm : Name) (disjunctIndex : Nat)
    (file : System.FilePath) (expected : CheckResult) : IO Unit := do
  let res ← Formats.function.check toyEnv
    ({ toyRecord thm (toySide thm) with disjunctIndex }) #[file]
  unless showCheck res == showCheck expected do
    throw (IO.userError s!"toy check {thm}: got {showCheck res}, \
      expected {showCheck expected}")

/-- How many times a needle occurs in a report. -/
private def countOf (needle text : String) : Nat :=
  (text.splitOn needle).length - 1

run_cmd do
  liftIO do
    -- A failed earlier run leaves its scratch tree behind, and a stale
    -- results file in it would poison this run's no-file pin below.
    -- Remove before starting.
    if ← toyOut.pathExists then IO.FS.removeDirAll toyOut
    IO.FS.createDirAll toyOut
    -- Render first: the entries' paths must be the files' paths exactly,
    -- the way the real harness walks the rendered tree.
    let files ← toyFiles.mapM fun (thm, ci) => renderToy thm ci
    -- With no results file, every record answers noConsumer: the
    -- harness never ran.
    for ((thm, ci), file) in toyFiles.zip files do
      expectCheck thm ci file .noConsumer
    -- Write the results file, then pin the answers: the three
    -- statuses, the mixed theorem's two disjuncts, and the no-entry answer.
    IO.FS.writeFile (ClientResults.file toyOut)
      ((toJson toyResults).render.pretty (width := 100) ++ "\n")
    let rs ← ClientResults.read toyOut
    unless rs.size == 5 do
      throw (IO.userError s!"toy results: {rs.size} entries, expected 5")
    expectCheck `EthCLSpecs.Proofs.Gloas.toyPass 0 files[0]! .passed
    expectCheck `EthCLSpecs.Proofs.Gloas.toyFail 0 files[1]!
      (.failed "the client computed 7, the vector expects 5")
    expectCheck `EthCLSpecs.Proofs.Gloas.toySkip 0 files[2]! .noConsumer
    expectCheck `EthCLSpecs.Proofs.Gloas.toyMixed 0 files[3]! .passed
    expectCheck `EthCLSpecs.Proofs.Gloas.toyMixed 1 files[4]!
      (.failed "the client computed 9, the vector expects 4")
    expectCheck `EthCLSpecs.Proofs.Gloas.toyNone 0 files[5]! .noConsumer
    -- The report's Formats cell (§16.2): one cell per status, empty for
    -- the theorem no entry ran. The skipped row joins through the `_t`
    -- side marker, which pins `thmOfPath`'s strip. The mixed theorem's
    -- passed and failed disjuncts aggregate to `prysm failed`, the worst
    -- answer wins, so the counts are one pass, two fails, one skip.
    let outcomes := toyThms.map fun thm =>
      { «theorem» := thm, target := none, shape := "runOk",
        origin := OutcomeOrigin.named, blockInputs := #[],
        disjuncts := 1,
        runs := #[{ preset := some .minimal, status := .written,
                    records := 1 }] : Outcome }
    let text := Report.render #[("gloas", outcomes)] #[] rs
    unless countOf "prysm passed" text == 1 do
      throw (IO.userError "toy report: expected exactly one `prysm passed` cell")
    unless countOf "prysm failed" text == 2 do
      throw (IO.userError "toy report: expected exactly two `prysm failed` cells")
    unless countOf "prysm skipped" text == 1 do
      throw (IO.userError "toy report: expected exactly one `prysm skipped` cell")
    let noneRow := (text.splitOn "\n").find? fun l => l.contains "toyNone"
    match noneRow with
    | none => throw (IO.userError "toy report: no row for `toyNone`")
    | some l =>
      unless !l.contains "prysm" do
        throw (IO.userError s!"toy report: the no-entry row carries a client cell: {l}")
    -- An empty client array, the harness-never-ran state, leaves every
    -- Formats cell empty.
    let bare := Report.render #[("gloas", outcomes)] #[] #[]
    unless countOf "prysm" bare == 0 do
      throw (IO.userError "toy report: empty client array left client cells in")
    -- A present file that does not parse is an error, per the read
    -- contract: the harness wrote it, so a mismatch is a defect.
    IO.FS.writeFile (ClientResults.file toyOut) "{ not json"
    let malformed ← try
      let rs' ← ClientResults.read toyOut
      pure (some rs'.size)
    catch _ =>
      pure (none : Option Nat)
    unless malformed.isNone do
      throw (IO.userError "toy results: a malformed file read back")
    -- Remove the scratch output tree.
    IO.FS.removeDirAll toyOut

end EthCLLib.TheoremVectors.Tests.ClientResults
