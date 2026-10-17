import Lean.Elab.Command
import EthCLLib.TheoremVectors.Command
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.Tests.InheritanceReplay
import EthCLLib.PySpecTests.Interface

/-!
# `EthCLLib.TheoremVectors.Tests.Command`: the generator commands over a toy fork

Build-gate checks for the command surface (`THEOREM_VECTORS_ARCHITECTURE.md` §14.3), over
the toy fork `EthCLLib.Tests.InheritanceReplay.Base`: one line of each
kind, with the outcomes read back and asserted, and the `#guard_msgs`
rejections (a `skip` below the clause that ran its theorem, a stale
`skip`, a named line below a clause that ran its theorem, a named line
and a skip line on one theorem, and a duplicated named line).

The scratch output tree lives under this package's `.lake/build`, so the
gitignore carries it and the final `run_cmd` removes it.
-/

set_option autoImplicit false

open Lean.Elab.Command

set_option theorem_vectors.outDir ".lake/build/test-theorem-vectors"

namespace EthCLLib.Proofs.Base

/-- Characterizes the toy fork's `callee`; the named line below wins over
this claim (§14.3). -/
@[characterizes EthCLLib.Tests.InheritanceReplay.Base.callee]
theorem callee_eq : EthCLLib.Tests.InheritanceReplay.Base.callee = 1 := rfl

/-- The skip line below excludes this claim from discovery. -/
@[characterizes EthCLLib.Tests.InheritanceReplay.Base.callee]
theorem callee_skipped : EthCLLib.Tests.InheritanceReplay.Base.callee = 1 := rfl

/-- The `@[theorem_vectors]` positive control: a tagged theorem under a
registered fork's proof namespace. -/
@[theorem_vectors] theorem callee_touched :
    EthCLLib.Tests.InheritanceReplay.Base.callee = 1 := rfl

/-- Survey-only: the survey clause selects every public theorem under the
fork's proof namespace that no other clause or line selected. -/
theorem callee_survey : EthCLLib.Tests.InheritanceReplay.Base.callee = 1 := rfl

end EthCLLib.Proofs.Base

-- the open activates the commands' scoped syntax
open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding

-- §14.3's positional order: the named lines and the `skip` lines precede
-- the discovery clauses, so the clauses never run an excluded theorem.
theorem_vectors! callee_eq presets minimal
theorem_vectors skip callee_skipped "covered by callee_eq"

theorem_vectors characterized
theorem_vectors tagged
theorem_vectors survey

namespace EthCLLib.TheoremVectors.Tests.Command

/-- A theorem no discovery clause selects; the stale `skip` below must
fail against it. -/
theorem unrelated : 1 = 1 := rfl

/-- Mode `require`'s theorem: declared below the survey clause, so no
clause ran it and the named line at the file's end is its first run. The
build holds no committed hint for it, so `require` must fail. -/
theorem callee_require : EthCLLib.Tests.InheritanceReplay.Base.callee = 1 :=
  rfl

/-- Read one outcome file back through the derived parser. -/
private def readOutcome (thmLocal : String) : Lean.Elab.Command.CommandElabM Outcome := do
  let path := (".lake/build/test-theorem-vectors" : System.FilePath) /
    "outcomes" / "toybase" / (thmLocal ++ ".json")
  liftIO <| Outcome.read path

-- The command surface's answers: named wins over characterized, the skip
-- excludes and records, `!` carries strictness, tagged discovery claims
-- its theorem, and the survey takes only the residual.
run_cmd do
  let named ← readOutcome "callee_eq"
  unless named.origin == .named do
    throwError s!"toy named line: origin is {named.origin.tag}, expected named"
  unless named.runs.any fun r => r.preset == some .minimal
      && r.status == .written do
    throwError "toy named line: expected one written minimal run"
  let skipped ← readOutcome "callee_skipped"
  unless skipped.origin == .skipped do
    throwError s!"toy skip line: origin is {skipped.origin.tag}, expected skipped"
  let touched ← readOutcome "callee_touched"
  unless touched.origin == .tagged do
    throwError s!"toy tagged: origin is {touched.origin.tag}, expected tagged"
  unless touched.runs.all fun r => r.status == .written do
    throwError "toy tagged: expected written runs"
  let residual ← readOutcome "callee_survey"
  unless residual.origin == .survey do
    throwError s!"toy survey: origin is {residual.origin.tag}, expected survey"
  unless residual.runs.size == 1
      && residual.runs[0]! == { preset := none, status := .unselected } do
    throwError s!"toy survey: expected one unselected run, got \
      {repr residual.runs}"
  let dir := (".lake/build/test-theorem-vectors" : System.FilePath) /
    "outcomes" / "toybase"
  let files ← dir.readDir
  unless files.size == 4 do
    throwError s!"toy outcomes: {files.size} files, expected exactly 4"

-- Two named lines for one theorem are an error. The guard sits first on
-- purpose: under a record-then-run pass the rejected line would stay in
-- the store and every later guard would fail with this message instead
-- of its own.
/-- error: theorem_vectors: two named lines select `EthCLLib.Proofs.Base.callee_eq`; one theorem runs once (§14.3) -/
#guard_msgs (error) in
theorem_vectors callee_eq

-- A `skip` line below a discovery clause that already ran its theorem is
-- an error (§14.3): the clause's run came without the exclusion.
/-- error: theorem_vectors: `EthCLLib.Proofs.Base.callee_touched` already ran under a discovery clause above this skip line; move the skip line above the discovery clauses (§14.3) -/
#guard_msgs (error) in
theorem_vectors skip callee_touched "covered above"

-- A `skip` of a theorem no discovery clause selects is an error.
/-- error: theorem_vectors: `skip EthCLLib.TheoremVectors.Tests.Command.unrelated` selects a theorem no discovery clause selects (§14.3) -/
#guard_msgs (error) in
theorem_vectors skip EthCLLib.TheoremVectors.Tests.Command.unrelated "stale"

-- A named line after a discovery clause that already ran its theorem is
-- an error (§14.3): the discovery run had no manual terms and warned. The
-- survey clause ran `callee_survey` above, so the named line here must
-- move up.
/-- error: theorem_vectors: `EthCLLib.Proofs.Base.callee_survey` already ran under a discovery clause above this line; move the named line above the discovery clauses (§14.3) -/
#guard_msgs (error) in
theorem_vectors callee_survey

-- A named line and a skip line for one theorem contradict: the skip
-- would overwrite the named run's outcome (§14.3).
/-- error: theorem_vectors: `EthCLLib.Proofs.Base.callee_eq` has a named line and a skip line; one or the other (§14.3) -/
#guard_msgs (error) in
theorem_vectors skip callee_eq "covered by the named line"

-- Mode `require` (§9.8): the theorem runs with no committed hint, and the
-- missing hint is a build error. The theorem is declared below the
-- survey clause, so the clause's pass never ran it and this named line is
-- the theorem's first and only run. The `set_option ... in` form keeps
-- the mode scoped to the guarded command; the guard assumes
-- `THEOREM_VECTORS_HINTS` is unset, which a developer shell that exports
-- it breaks.
/-- error: theorem_vectors: mode `require`: the hint for case 0 of `EthCLLib.TheoremVectors.Tests.Command.callee_require` at minimal is missing or failed the check (§9.8) -/
#guard_msgs (error) in
set_option theorem_vectors.hints "require" in
theorem_vectors EthCLLib.TheoremVectors.Tests.Command.callee_require

-- Remove the scratch output tree.
run_cmd do
  IO.FS.removeDirAll ".lake/build/test-theorem-vectors"

end EthCLLib.TheoremVectors.Tests.Command
