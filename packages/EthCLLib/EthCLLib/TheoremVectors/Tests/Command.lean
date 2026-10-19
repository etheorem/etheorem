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
and a skip line on one theorem, a duplicated named line, a `skip` of a
registered theorem, and a registered theorem only `survey` selects).

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

/-- The registration fixture: one `UInt64` input, whose witness the
registration below spells (`EthCLLib.Internal.ManualTerms`) and whose
named line sits above the discovery clauses. The equation runs in `Nat`,
so `callee`'s `rfl` proof carries, and the input crosses the byte
boundary through the `UInt64` wire codec. -/
theorem callee_add (v : UInt64) :
    EthCLLib.Tests.InheritanceReplay.Base.callee + v.toNat = 1 + v.toNat :=
  rfl

end EthCLLib.Proofs.Base

-- The fixture's registration: the witness for `v`, recorded in the
-- theorem's own file (§14.6). `open EthCLLib.Internal in` activates the
-- registration command's scoped syntax for this one command.
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.callee_add
  v := 0

-- the open activates the commands' scoped syntax
open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding

-- §14.3's positional order: the named lines and the `skip` lines precede
-- the discovery clauses, so the clauses never run an excluded theorem.
theorem_vectors! callee_eq presets minimal
-- the registered theorem's named line: its manual terms come from the
-- registration above
theorem_vectors callee_add presets minimal
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
-- its theorem, the survey takes only the residual, and the registered
-- theorem's named run consumes the registration's manual terms.
run_cmd do
  let named ← readOutcome "callee_eq"
  unless named.origin == .named do
    throwError s!"toy named line: origin is {named.origin.tag}, expected named"
  unless named.runs.any fun r => r.preset == some .minimal
      && r.status == .written do
    throwError "toy named line: expected one written minimal run"
  let added ← readOutcome "callee_add"
  unless added.origin == .named do
    throwError s!"toy registration fixture: origin is {added.origin.tag}, \
      expected named"
  unless added.runs.any fun r => r.preset == some .minimal
      && r.status == .written do
    throwError s!"toy registration fixture: expected one written minimal \
      run, got {repr added.runs}"
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
  unless files.size == 5 do
    throwError s!"toy outcomes: {files.size} files, expected exactly 5"

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
/-- error: theorem_vectors: mode `require`: the hint for disjunct 0 of `EthCLLib.TheoremVectors.Tests.Command.callee_require` at minimal is missing or failed the check (§9.8) -/
#guard_msgs (error) in
set_option theorem_vectors.hints "require" in
theorem_vectors EthCLLib.TheoremVectors.Tests.Command.callee_require

-- The two registration precedence checks (§14.3). Order matters: a failed
-- line leaves no state, but a registration persists. The skip guard's own
-- pass holds the skip line in `skipSet`, so the theorem stays out of the
-- survey selection and the registration-plus-skip contradiction is the
-- error that fires. The skip never records, so the survey guard's own
-- pass survey-selects the same registered theorem, and the survey check
-- fires there. The outer namespace ends above, so the fixture's name is
-- `EthCLLib.Proofs.Base.callee_skip_refused` and the registration and the
-- skip line resolve to it.
end EthCLLib.TheoremVectors.Tests.Command

namespace EthCLLib.Proofs.Base

/-- The registered-and-skipped fixture: the registration below persists
through both guards, and neither line records anything. -/
theorem callee_skip_refused (v : UInt64) :
    EthCLLib.Tests.InheritanceReplay.Base.callee + v.toNat = 1 + v.toNat :=
  rfl

end EthCLLib.Proofs.Base

open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.callee_skip_refused
  v := 0

/-- error: theorem_vectors: `EthCLLib.Proofs.Base.callee_skip_refused` has witness terms registered with `theorem_vectors_manual` and a skip line; a registered theorem runs, so drop the skip line (§14.3) -/
#guard_msgs (error) in
theorem_vectors skip EthCLLib.Proofs.Base.callee_skip_refused "registered theorems run"

/-- error: theorem_vectors: `EthCLLib.Proofs.Base.callee_skip_refused` has witness terms registered with `theorem_vectors_manual` and only the survey clause selects it; give the theorem a named line above the discovery clauses (§14.3) -/
#guard_msgs (error) in
theorem_vectors survey

-- Remove the scratch output tree.
run_cmd do
  IO.FS.removeDirAll ".lake/build/test-theorem-vectors"
