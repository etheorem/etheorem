import Lean
import SizzLean
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Built
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.Random
import EthCLLib.TheoremVectors.Tests.Support

/-!
# `EthCLLib.TheoremVectors.Tests.BuiltDrive`: the built source's guarded draw

Build-gate checks for `builtSource.search`'s draw guard
(`THEOREM_VECTORS_ARCHITECTURE.md` §9.9), the toy-level coverage the
stage-8 review found missing: every other test binding carries an empty
builder catalog, so the built source never applies at the toy level, and
a refactor that restored the unconditional draw would fail only in the
generator's mainnet elaboration, never in a test.

The module carries its own builder and binding. The catalog's display
name is `"genesis"`, the built grid's first step, because the source
walks the fixed grid of display names and skips the steps the catalog
does not name (`Witness/Built.lean`). The builder is `Knobs → ToyBox`,
the shape `applyAcrossInstances` applies (`Probe.lean`): one explicit
`Knobs` binder, the result the binding's state type, and zero instance
binders, which the walk fills fine.

Two drives run the same built win at minimal:

- a state-only statement: the search wins with the tag `.built`, the
  candidate's decoded `tag` is the builder's 5, and the search context's
  `drawMemo` reads back empty. The guard's point: a statement whose
  state is the only container input never draws. Before `c5f5b37` the
  memo held draw 0.
- the state beside a second container input: the search still wins
  `.built`, the state slot still carries the builder's bytes, and the
  memo now holds draw 0's bytes, whose list slot the candidate carries.

## Lean idioms annotated

- The drives run inside `run_cmd` with `liftTermElabM` and fold inside
  the reader's telescope scope (`Statement.readIn`), the same shapes the
  stage-4 to stage-6 test modules use.
- The module imports `Tests/Random.lean` for the `ToyBox` container, the
  `Tests/Hint.lean` precedent for one test module importing another.
- The built cache writes under this module's own scratch root, which the
  last pass removes; no other test's cache tree sees the entries.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors.Tests.BuiltDrive

/-- The scratch output root for the built cache, under the package's
gitignored build tree. -/
def scratchRoot : System.FilePath := ".lake/build/test-theorem-vectors-builtdrive"

/-- The toy builder: the grid's knobs arrive, the toy state ignores
them. The tag is 5 and the list is fixed, so every grid step the
catalog's name reaches builds the same bytes. -/
def toyBuilder (_k : Knobs) : Tests.Random.ToyBox :=
  ⟨5, ⟨#[1, 2], by decide⟩⟩

/-- The toy binding with a nonempty builder catalog: the one builder the
built grid's first step names. -/
def toyBuiltBinding : ForkBinding :=
  { Tests.Random.toyBoxBinding with
      builders :=
        #[("genesis", `EthCLLib.TheoremVectors.Tests.BuiltDrive.toyBuilder)] }

/-- The projection the state-only drive's conclusion states. -/
def toyBuiltFun (b : Tests.Random.ToyBox) : UInt64 := b.tag

/-- The state-only drive's theorem: the state is the only container
input, so the built source's draw guard skips the draw. -/
theorem toyBuiltThm (b : Tests.Random.ToyBox) (_h : b.tag < 100) :
    toyBuiltFun b = b.tag := rfl

/-- The projection the two-container drive's conclusion states, the
list carried beside the state. -/
def toyBuiltFun2 (b : Tests.Random.ToyBox)
    (_xs : SizzLean.Repr.SSZList UInt64 4) : UInt64 := b.tag

/-- The two-container drive's theorem: a drawn list sits beside the
state, so the built source's draw guard keeps the draw. -/
theorem toyBuiltThm2 (b : Tests.Random.ToyBox)
    (xs : SizzLean.Repr.SSZList UInt64 4) (_h : b.tag < 100) :
    toyBuiltFun2 b xs = b.tag := rfl

end EthCLLib.TheoremVectors.Tests.BuiltDrive

open Lean.Elab.Command
open EthCLLib.TheoremVectors
open EthCLLib.TheoremVectors.Tests.BuiltDrive in
run_cmd do
  liftTermElabM do
    let binding := toyBuiltBinding
    -- ── drive one, the guard's empty path: a state-only statement wins
    -- from the builder and never draws
    Statement.readIn binding
      `EthCLLib.TheoremVectors.Tests.BuiltDrive.toyBuiltThm fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (cases, _) ← Prepare.pass stmt
      unless cases.size == 1 do
        throwError s!"toyBuiltThm: expected one case, got {cases.size}"
      let c := cases[0]!
      let (info, probe) ←
        match ← Probe.ofStatement binding .minimal ctx cases #[] with
        | .ok r => pure r
        | .error e =>
          throwError s!"toyBuiltThm: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf toyBuiltBinding .minimal
        scratchRoot "" stmt ctx info probe
      match ← searchCase #[builtSource] sctx stmt c with
      | .ok (a, won) =>
        unless won == .built do
          throwError s!"toyBuiltThm: expected a `.built` win, got {won.tag}"
        unless probe.check c.index a do
          throwError "toyBuiltThm: the built candidate failed the check"
        -- the candidate's state input decodes to the builder's state
        match SizzLean.SSZ.deserialize (T := Tests.Random.ToyBox) a[0]! with
        | .ok b =>
          unless b.tag == 5 do
            throwError s!"toyBuiltThm: the built state's tag is {b.tag}, \
              expected 5"
        | .error e =>
          throwError s!"toyBuiltThm: the built bytes did not decode: \
            {repr e}"
        -- the guard's point: a state-only statement never draws, the
        -- memo reads back empty
        unless (← sctx.drawMemo.get).isEmpty do
          throwError "toyBuiltThm: the draw memo is not empty; a \
            state-only statement must never draw"
      | .error f =>
        throwError s!"toyBuiltThm: the built source found nothing: \
          {repr f}"
    -- ── drive two, the guard's nonempty path: a container beside the
    -- state keeps the draw
    Statement.readIn binding
      `EthCLLib.TheoremVectors.Tests.BuiltDrive.toyBuiltThm2 fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (cases, _) ← Prepare.pass stmt
      unless cases.size == 1 do
        throwError s!"toyBuiltThm2: expected one case, got {cases.size}"
      let c := cases[0]!
      let (info, probe) ←
        match ← Probe.ofStatement binding .minimal ctx cases #[] with
        | .ok r => pure r
        | .error e =>
          throwError s!"toyBuiltThm2: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf toyBuiltBinding .minimal
        scratchRoot "" stmt ctx info probe
      match ← searchCase #[builtSource] sctx stmt c with
      | .ok (a, won) =>
        unless won == .built do
          throwError s!"toyBuiltThm2: expected a `.built` win, got \
            {won.tag}"
        unless probe.check c.index a do
          throwError "toyBuiltThm2: the built candidate failed the check"
        -- the state slot still carries the builder's bytes
        match SizzLean.SSZ.deserialize (T := Tests.Random.ToyBox) a[0]! with
        | .ok b =>
          unless b.tag == 5 do
            throwError s!"toyBuiltThm2: the built state's tag is {b.tag}, \
              expected 5"
        | .error e =>
          throwError s!"toyBuiltThm2: the built bytes did not decode: \
            {repr e}"
        -- the guard kept the draw: the memo holds exactly draw 0, and
        -- the candidate's list slot carries its bytes
        let memo ← sctx.drawMemo.get
        unless memo.size == 1 && memo[0]!.isSome do
          throwError s!"toyBuiltThm2: the draw memo holds {memo.size} \
            slots, expected one drawn slot"
        let seed := theorem_vectors.seed.get (← getOptions)
        let size := theorem_vectors.randomSize.get (← getOptions)
        unless memo[0]! == some (probe.sample seed size) do
          throwError "toyBuiltThm2: the memo's entry is not draw 0"
        unless a[1]! == (memo[0]!.getD #[]).getD 1 emptyBytes do
          throwError "toyBuiltThm2: the list slot does not carry the \
            drawn bytes"
      | .error f =>
        throwError s!"toyBuiltThm2: the built source found nothing: \
          {repr f}"

-- the scratch tree goes away
run_cmd do
  let dir := EthCLLib.TheoremVectors.Tests.BuiltDrive.scratchRoot
  if ← dir.pathExists then
    IO.FS.removeDirAll dir
