import Lean
import EthCLLib.TheoremVectors.Formats.Function

/-!
# `EthCLLib.TheoremVectors.Tests.Function`: the function format's `function:` line

Build-gate check for the function format's central line
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.3): the field carries the record's
`specName`, the target's pyspec name, and falls back to the Lean target
name when the reader read none. The drive renders the format twice over a
hand-built record, once with `specName := none` and once with
`specName := some "toy_set_bal"`. It pins the rendered file's
`function:` line both ways. It also pins the directory spelling, which
keeps the Lean target name either way, so a client's path join never
depends on the field.

The scratch output tree lives under this package's `.lake/build`, so the
gitignore carries it and the final `run_cmd` removes it.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors.Tests.Function

/-- The scratch output root this module's drive writes and removes. -/
def scratchOut : System.FilePath := ".lake/build/test-theorem-vectors-function"

/-- The toy render environment: the scratch outDir, and a bindings table
that answers `none` everywhere (the render reads the record alone). -/
def toyEnv : RenderEnv := { outDir := scratchOut, bindings := fun _ => none }

/-- The hand-built record (§13.3): a target and the toy theorem's name,
no inputs and no output, because the pin reads the `function:` line and
the directory alone. -/
def toyRecord (specName : Option String) : VectorRecord :=
  { «theorem» := `EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk,
    fork := "toyrun", preset := .minimal,
    target := some `EthCLLib.TheoremVectors.Tests.ToyRun.toySetBal,
    specName, shape := .runOk, caseIndex := 0, side := none,
    inputs := #[], output := none, error := none, source := .base }

/-- The `function:` line of a rendered file. -/
private def functionLine (file : System.FilePath) : IO String := do
  let text ← IO.FS.readFile file
  match (text.splitOn "\n").find? (·.startsWith "function: ") with
  | some l => pure l
  | none => throw (IO.userError s!"function render: no `function:` line \
    in {file}")

/-- The rendered file's path for the toy record: the target directory
keeps the Lean target name, and the file name carries the theorem and the
case index. -/
private def expectedPath : System.FilePath :=
  scratchOut / "formats" / "function" / "toyrun" / "minimal" /
    "EthCLLib.TheoremVectors.Tests.ToyRun.toySetBal" /
    "EthCLLib.TheoremVectors.Tests.ToyRun.toyRunOk_0.yaml"

open Lean.Elab.Command in
run_cmd do
  liftIO do
    -- A failed earlier run leaves its scratch tree behind. Remove first.
    if ← scratchOut.pathExists then IO.FS.removeDirAll scratchOut
    IO.FS.createDirAll scratchOut
    -- `specName := none`: the field falls back to the Lean target name,
    -- and the directory spells that name
    let files ← Formats.function.render toyEnv (toyRecord none) #[] none
    unless files.size == 1 do
      throw (IO.userError s!"function render: {files.size} files, expected 1")
    unless files[0]!.toString == expectedPath.toString do
      throw (IO.userError s!"function render: path is {files[0]!}, \
        expected {expectedPath}")
    unless (← functionLine files[0]!) ==
        "function: EthCLLib.TheoremVectors.Tests.ToyRun.toySetBal" do
      throw (IO.userError s!"function render: the fallback line is \
        {← functionLine files[0]!}")
    -- `specName := some`: the spec name reaches the field, and the
    -- directory keeps the Lean target name
    let named ← Formats.function.render toyEnv
      (toyRecord (some "toy_set_bal")) #[] none
    unless named.size == 1 && named[0]!.toString == expectedPath.toString do
      throw (IO.userError s!"function render: the named record wrote \
        {named.map (·.toString)}, expected [{expectedPath}]")
    unless (← functionLine named[0]!) == "function: toy_set_bal" do
      throw (IO.userError s!"function render: the spec-name line is \
        {← functionLine named[0]!}")
    IO.FS.removeDirAll scratchOut

end EthCLLib.TheoremVectors.Tests.Function
