import Lean
import EthCLLib.TheoremVectors.Outcome

/-!
# `EthCLLib.TheoremVectors.Report`: `report.md`

The report pass (`THEOREM_VECTORS_ARCHITECTURE.md` §16.2): the exe's `report` subcommand
folds the outcome files into one Markdown file with one table per fork.
The table is the review surface, so a reader sees which theorems produce
vectors, which do not, and why. The columns are the §16.2 columns; the
`Formats` cell stays empty until the pyspec check lands in stage 7.

The summary line above the tables counts the theorems with outcomes, the
box lemmas (§7.3), and the theorems with block inputs (§16.2, and decision
point A's outcome in the plan), so the other `.unsupported` rows read as
the shape gaps they are. A run that carries a reason writes it in its
status cell. The theorem list with block inputs follows each table (§16.2's
closing list); the records-no-format list prints `(none)` until a format
check fails in a later stage.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- One table row: the theorem's outcome and one of its runs. -/
private structure Row where
  outcome : Outcome
  run     : RunOutcome

/-- The status cell: the status tag, plus the run's reason when it has
one. -/
private def statusCell (run : RunOutcome) : String :=
  match run.reason with
  | some r => s!"{run.status.tag} ({r})"
  | none => run.status.tag

/-- The optional cells print empty until their stage fills them. -/
private def optCell : Option String → String
  | some s => s
  | none => ""

/-- The preset cell; a survey run carries no preset (§16.1). -/
private def presetCell (run : RunOutcome) : String :=
  match run.preset with
  | some p => p.tag
  | none => ""

/-- Is the outcome a box lemma? The reader's reason names the family
(§7.3), and the run carries it. -/
private def isBoxLemma (o : Outcome) : Bool :=
  o.runs.any fun r => r.reason.any fun reason => reason.startsWith "box lemma"

/-- The block-input list under a fork's table (§16.2). -/
private def blockInputSection (os : Array Outcome) : String :=
  let withBlocks := os.filter fun o => !o.blockInputs.isEmpty
  if withBlocks.isEmpty then
    ""
  else
    "\nTheorems with block inputs (§1.2): only the base source may run.\n\n" ++
      String.intercalate "\n" (withBlocks.toList.map fun o =>
        s!"- `{o.theorem}`: {String.intercalate ", "
          (o.blockInputs.toList.map (fun n => s!"`{n}`"))}")

/-- One fork's section: the heading, the table, and the block-input list. -/
private def forkSection (forkTag : String) (os : Array Outcome) : String :=
  let rows : Array Row :=
    os.flatMap fun o => o.runs.map fun run => { outcome := o, run }
  let table :=
    "| Theorem | Origin | Shape | Preset | Status | Source | Hint | Records | Formats | Seconds |\n" ++
    "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |\n" ++
    String.join (rows.toList.map fun r =>
      s!"| `{r.outcome.theorem}` | {r.outcome.origin.tag} | {r.outcome.shape} \
         | {presetCell r.run} | {statusCell r.run} | {optCell r.run.source} \
         | {optCell r.run.hint} | {r.run.records} | | \
         {optCell (r.run.seconds.map toString)} |\n")
  "## " ++ forkTag ++ "\n\n" ++ table ++ blockInputSection os ++ "\n\n"

/-- The report text for every fork with outcomes, fork tags in name order
(§16.2). The summary counts the theorems with outcomes, the box lemmas,
and the theorems with block inputs. -/
def Report.render (forks : Array (String × Array Outcome)) : String :=
  let total := forks.foldl (init := 0) fun acc (_, os) => acc + os.size
  let boxLemmas := forks.foldl (init := 0) fun acc (_, os) =>
    acc + (os.filter isBoxLemma).size
  let withBlocks := forks.foldl (init := 0) fun acc (_, os) =>
    acc + (os.filter fun o => !o.blockInputs.isEmpty).size
  "# Theorem vectors report\n\n" ++
    s!"{total} theorems with outcomes; {boxLemmas} box lemmas (§7.3, \
      no shape can express them); {withBlocks} theorems with block \
      inputs (§1.2, base source only).\n\n" ++
    String.join (forks.toList.map fun (forkTag, os) => forkSection forkTag os) ++
    "## Records no format accepted\n\n(none)\n"

/-- Collect every fork's outcomes from the output tree and write
`<outDir>/report.md`. Returns the fork sections the report holds. -/
def Report.write (outDir : System.FilePath) : IO Nat := do
  let forkTags ← Outcome.forks outDir
  let mut forks : Array (String × Array Outcome) := #[]
  for forkTag in forkTags do
    forks := forks.push (forkTag, ← Outcome.readFork outDir forkTag)
  IO.FS.writeFile (outDir / "report.md") (Report.render forks)
  return forks.size

end EthCLLib.TheoremVectors
