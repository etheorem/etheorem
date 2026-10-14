import Lean
import SizzLean
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Built
import EthCLLib.TheoremVectors.Witness.Hint
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
  memo's draw-0 slot holds the side position's bytes alone: `none` at
  the state position, and at the side position the bytes `sampleAt`
  produces. The state's draw never evaluates.

A third drive runs the completion path the first two only pin as
halves: `builtSource` leaves draw 0's slot partial, then `randomSource`
runs on the same `SearchCtx`, draws at index 0, completes the slot, and
wins. The hint entry the win records (`Hint.entryOf`) must name the
completed slot, so its draw key is draw 0.

A fourth pin sits beside drive two: the `sample` and `sampleAt` faces
agree byte for byte at every position of the toy statement, which is the
invariant the per-position memo rests on (§9.4, §9.9).

## Lean idioms annotated

- The drives run inside `run_cmd` with `liftTermElabM` and fold inside
  the reader's telescope scope (`Statement.readIn`), the same shapes the
  stage-4 to stage-6 test modules use.
- The module imports `Tests/Random.lean` for the `ToyBox` container and
  `Witness/Hint.lean` for the entry the completion drive reads back, the
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

/-- The completion drive's theorem: the hypothesis reads the drawn
container and holds of every draw, so the random source's first draw
wins and the slot that win completes is draw 0's. -/
theorem toyBuiltThm3 (b : Tests.Random.ToyBox)
    (xs : SizzLean.Repr.SSZList UInt64 4) (_h : b.tag ≤ b.tag) :
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
        -- the guard kept the side draw: the memo holds exactly draw 0,
        -- the state position's entry is `none`, and the side position's
        -- entry is the bytes `sampleAt` produces, which the candidate's
        -- list slot carries
        let memo ← sctx.drawMemo.get
        unless memo.size == 1 && memo[0]!.isSome do
          throwError s!"toyBuiltThm2: the draw memo holds {memo.size} \
            slots, expected one drawn slot"
        let seed := theorem_vectors.seed.get (← getOptions)
        let size := theorem_vectors.randomSize.get (← getOptions)
        -- the two sample faces agree byte for byte at every position,
        -- the invariant the per-position draw rests on
        let full := probe.sample seed size
        for i in [0:full.size] do
          unless probe.sampleAt seed size i == full[i]! do
            throwError s!"toyBuiltThm2: sampleAt {i} disagrees with the \
              sample face at that position"
        -- past the inputs the per-position face answers the empty bytes
        unless probe.sampleAt seed size full.size == emptyBytes do
          throwError "toyBuiltThm2: sampleAt past the inputs did not \
            answer the empty bytes"
        let slot := memo[0]!.getD #[]
        unless slot[0]?.join.isNone do
          throwError "toyBuiltThm2: the memo holds bytes for the state \
            position; the built draw must sample the side positions alone"
        unless slot[1]?.join == some (probe.sampleAt seed size 1) do
          throwError "toyBuiltThm2: the memo's side entry is not draw 0's \
            bytes at position 1"
        unless a[1]! == probe.sampleAt seed size 1 do
          throwError "toyBuiltThm2: the list slot does not carry the \
            drawn bytes"
      | .error f =>
        throwError s!"toyBuiltThm2: the built source found nothing: \
          {repr f}"
    -- ── drive three, the completion path: the built source leaves draw
    -- 0's slot partial, a random win on the same context completes it,
    -- and the hint entry the win records names the completed slot's
    -- draw key (§9.4, §9.8)
    Statement.readIn binding
      `EthCLLib.TheoremVectors.Tests.BuiltDrive.toyBuiltThm3 fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (cases, _) ← Prepare.pass stmt
      unless cases.size == 1 do
        throwError s!"toyBuiltThm3: expected one case, got {cases.size}"
      let c := cases[0]!
      let (info, probe) ←
        match ← Probe.ofStatement binding .minimal ctx cases #[] with
        | .ok r => pure r
        | .error e =>
          throwError s!"toyBuiltThm3: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf toyBuiltBinding .minimal
        scratchRoot "" stmt ctx info probe
      let seed := theorem_vectors.seed.get (← getOptions)
      let size := theorem_vectors.randomSize.get (← getOptions)
      -- the built half: the win leaves draw 0's slot partial, the state
      -- position `none`, the side position `some`
      match ← searchCase #[builtSource] sctx stmt c with
      | .ok (_, won) =>
        unless won == .built do
          throwError s!"toyBuiltThm3: expected a `.built` win, got \
            {won.tag}"
      | .error f =>
        throwError s!"toyBuiltThm3: the built source found nothing: \
          {repr f}"
      -- the random half on the same context: its draw at index 0
      -- completes the slot, and the always-true read lets that draw win
      match ← searchCase #[randomSource] sctx stmt c with
      | .ok (a, won) =>
        unless won == .random do
          throwError s!"toyBuiltThm3: expected a `.random` win, got \
            {won.tag}"
        -- the completed slot: the state position holds bytes now, and
        -- the side position's entry is unchanged
        let memo ← sctx.drawMemo.get
        unless memo.size ≥ 1 && memo[0]!.isSome do
          throwError "toyBuiltThm3: the draw memo lost draw 0's slot"
        let slot := memo[0]!.getD #[]
        unless slot[0]?.join.isSome do
          throwError "toyBuiltThm3: draw 0's state position is still \
            empty; the random draw did not complete the slot"
        unless slot[1]?.join == some (probe.sampleAt seed size 1) do
          throwError "toyBuiltThm3: draw 0's side entry changed under \
            the random draw"
        -- the hint entry the win records: `findDrawIndex` matches the
        -- completed slot, so the draw key is draw 0
        let some e ← Hint.entryOf sctx stmt c a won seed size
          (Hint.fingerprint stmt.thm info)
          | throwError "toyBuiltThm3: the random win produced no hint \
            entry; the completed slot did not match"
        unless e.source == .random do
          throwError s!"toyBuiltThm3: the entry names {e.source.tag}, \
            expected random"
        unless e.seed == some seed && e.size == some size &&
            e.draw == some 0 do
          throwError s!"toyBuiltThm3: the draw key is not the completed \
            slot's: {repr e.seed} {repr e.size} {repr e.draw}"
      | .error f =>
        throwError s!"toyBuiltThm3: the random source found nothing: \
          {repr f}"

-- the scratch tree goes away
run_cmd do
  let dir := EthCLLib.TheoremVectors.Tests.BuiltDrive.scratchRoot
  if ← dir.pathExists then
    IO.FS.removeDirAll dir
