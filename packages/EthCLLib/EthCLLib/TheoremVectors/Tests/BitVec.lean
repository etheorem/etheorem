import Lean
import EthCLLib.Spec.Hasher
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.Manual
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Tests.ToyFork
import EthCLLib.TheoremVectors.Tests.Support

/-!
# `EthCLLib.TheoremVectors.Tests.BitVec`: the prepare pass and the solver

Build-gate checks for stage 3 (`THEOREM_VECTORS_ARCHITECTURE.md` §8.2, §9.4):
a hypothesis `a < b ∨ a = b` splits into two disjuncts; the solver's witness for
an equality disjunct lands on the boundary; an unsatisfiable hypothesis
answers `unsat` and proposes no candidate; a `.toNat` hypothesis rewrites
to `UInt64` form, which is what makes it solvable; a manual term that
makes the residual formula unsatisfiable answers `notFound`, never
`unsat`, because the vacuity the solver proved is a fact about one manual
input; a split past the cap falls back to the unsplit hypothesis with a
note (§8.2); and
a disjunct with no `Decidable` instance is reported and dropped (§8.4). The
drives run the search loop's searchers over the toy fork's scalar theorems.

## Lean idioms annotated

- The drives run inside `run_cmd` with `liftTermElabM`, because the reader,
  the prepare pass, and the solver are `MetaM`.
- Every drive folds inside the reader's telescope scope
  (`Statement.readIn`), because the statement, the disjuncts, and the free
  variables cannot leave it.
- `searchDisjunct` answers `Except Failure`; the drive pattern-matches the
  answer, so a searcher that silently finds nothing fails the test instead
  of passing it.
-/

set_option autoImplicit false

open Lean
open EthCLLib.Spec (HasherTag)

namespace EthCLLib.TheoremVectors.Tests.BitVec

/-- The toy function under test. -/
def toyFun (x : UInt64) : UInt64 := x + 3

/-- The split pin's theorem: one hypothesis, two disjuncts. -/
theorem toySplit [HasherTag] (a b : UInt64) (_h : a < b ∨ a = b) :
    toyFun a = a + 3 := rfl

/-- The solver's drive theorem: the split plus a bound `default` fails, so
the bit-vector searcher must find both disjuncts' witnesses, and the
equality disjunct's witness lands on the boundary. -/
theorem toySplitSolve [HasherTag] (a b : UInt64) (_h : (a < b ∨ a = b) ∧ 0 < b) :
    toyFun a = a + 3 := rfl

/-- The unsat pin's theorem: no `UInt64` satisfies `a < a`. -/
theorem toyUnsat [HasherTag] (a _b : UInt64) (_h : a < a) :
    toyFun a = a + 3 := rfl

/-- The `.toNat` pin's theorem: the hypothesis is `Nat`-level, the bridge
set rewrites it to `a + 1 = b`, and the solver reads `UInt64` form. -/
theorem toyToNat [HasherTag] (a b : UInt64) (_h : a.toNat + 1 = b.toNat) :
    toyFun a = a + 3 := rfl

/-- The manual-handoff pin's theorem, over a toy binding whose state type
is `UInt64`: the manual term fixes `s` to `0`, which makes the residual
hypothesis `a < s` hold for no `a` at that term. The disjunct is `notFound`
at the term, never `unsat`: the solver's vacuity proof covers this one
manual term alone, and other manual terms admit witnesses. -/
theorem toyManual [HasherTag] (s : UInt64) (a : UInt64) (_h : a < s) :
    toyFun a = a + 3 := rfl

/-- The cap-fallback pin's theorem: seventeen disjuncts, one past the
default cap (§8.2). The prepare pass keeps the unsplit hypothesis and
reports the fallback. -/
theorem toyManyDisjuncts [HasherTag] (a : UInt64)
    (h : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨
         a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨
         a = 15 ∨ a = 16) :
    toyFun a = a + 3 := by
  cases h <;> simp [toyFun]

/-- The dropped-disjunct pin's theorem: the hypothesis is a proposition
variable, which carries no `Decidable` instance, so the prepare pass
reports the disjunct and drops it (§8.4). -/
theorem toyNoDecidable [HasherTag] (q : Prop) (_hq : q) : toyFun 0 = 3 := rfl

/-- A type alias the way the fork bodies spell one (`Gwei` for `UInt64`). -/
abbrev toyWei : Type := UInt64

/-- A read whose type is the alias: the grounding gate's own example. -/
def toyBal (_ : UInt64) : toyWei := 3

/-- The alias-read pin's theorem: the manual term fixes `s`, the read
`toyBal s` has the alias type, and the searcher must ground it. A gate that
names only the bare scalar types refuses the read, the solver abstracts
it into a spurious model, and the disjunct reads `notFound` (§9.4). -/
theorem toyAliasRead [HasherTag] (s a : UInt64) (_h : toyBal s ≤ a) :
    toyFun a = a + 3 := rfl

end EthCLLib.TheoremVectors.Tests.BitVec

open Lean.Elab.Command
open EthCLLib.TheoremVectors
open EthCLLib.TheoremVectors.Tests.BitVec in
run_cmd do
  liftTermElabM do
    let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
    -- ── the split pin: `a < b ∨ a = b` is two disjuncts, neither an iff side
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toySplit fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, dropped) ← Prepare.pass stmt
      unless dropped.isEmpty do
        throwError "toySplit: the prepare pass dropped a note"
      unless disjuncts.size == 2 do
        throwError s!"toySplit: expected two prepared disjuncts, got {disjuncts.size}"
      unless disjuncts.all (fun d => d.side.isNone) do
        throwError "toySplit: the disjuncts carry iff sides"
    -- ── the solver's drive: both disjuncts found, the equality disjunct on the
    -- boundary
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toySplitSolve fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 2 do
        throwError s!"toySplitSolve: expected two prepared disjuncts, got {disjuncts.size}"
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toySplitSolve: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher]
      let (ltDisjunct, eqDisjunct) :=
        if disjuncts[0]!.hyps[0]!.isAppOf ``LT.lt then
          (disjuncts[0]!, disjuncts[1]!)
        else
          (disjuncts[1]!, disjuncts[0]!)
      for d in [ltDisjunct, eqDisjunct] do
        match ← searchDisjunct searchers sctx stmt d with
        | .ok (a, won) =>
          unless won == .bitVec do
            throwError s!"toySplitSolve disjunct {d.index}: expected the \
              bit-vector searcher to win, got {won.tag}"
          unless probe.check d.index a do
            throwError s!"toySplitSolve disjunct {d.index}: the candidate \
              failed the check"
          unless a.size == 2 && Tests.Support.leOf a[1]! ≥ 1 do
            throwError s!"toySplitSolve disjunct {d.index}: the witness \
              ({Tests.Support.leOf a[0]!}, {Tests.Support.leOf a[1]!}) missed its window"
          if d.index == eqDisjunct.index then
            unless Tests.Support.leOf a[0]! == Tests.Support.leOf a[1]! do
              throwError s!"toySplitSolve disjunct {d.index}: the equality \
                disjunct's witness is not on the boundary"
          else
            unless Tests.Support.leOf a[0]! < Tests.Support.leOf a[1]! do
              throwError s!"toySplitSolve disjunct {d.index}: the witness is \
                not below its bound"
        | .error f =>
          throwError s!"toySplitSolve disjunct {d.index}: {repr f}"
    -- ── the unsat pin: the solver proves the disjunct vacuous, no candidate
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyUnsat fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyUnsat: expected one prepared disjunct, got {disjuncts.size}"
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toyUnsat: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok _ => throwError "toyUnsat: the search found a witness"
      | .error .unsat => pure ()
      | .error f => throwError s!"toyUnsat: {repr f}"
    -- ── the `.toNat` pin: the bridge rewrite exposes `UInt64` form, and
    -- the solver solves it
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyToNat fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyToNat: expected one prepared disjunct, got {disjuncts.size}"
      -- the rewritten hypothesis names no `.toNat` any more
      unless !(disjuncts[0]!.conj.getUsedConstants.contains `UInt64.toNat) do
        throwError "toyToNat: the conjunction still names `UInt64.toNat`"
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toyToNat: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok (a, won) =>
        unless won == .bitVec && probe.check 0 a do
          throwError "toyToNat: the bit-vector searcher's candidate failed"
        unless Tests.Support.leOf a[0]! + 1 == Tests.Support.leOf a[1]! do
          throwError s!"toyToNat: the witness ({Tests.Support.leOf a[0]!}, {Tests.Support.leOf a[1]!}) \
            does not satisfy a + 1 = b"
      | .error f => throwError s!"toyToNat: {repr f}"
    -- ── the manual-handoff pin: the manual term fixes `s` to 0, the
    -- residual `a < s` is unsatisfiable at that term, and the disjunct is
    -- `notFound`, never `unsat` (§9.4: the vacuity is about one manual
    -- input). The base searcher refuses the state input, so the search
    -- runs manual then the bit-vector handoff alone.
    let stateBinding : ForkBinding :=
        { EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding with
            stateType := `UInt64 }
    Statement.readIn stateBinding `EthCLLib.TheoremVectors.Tests.BitVec.toyManual fun ctx => do
      let stmt ← Scope.classify stateBinding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyManual: expected one prepared disjunct, got {disjuncts.size}"
      -- the manual term `0`, elaborated in the telescope like a
      -- `with` term
      let stx ← `(term| 0)
      let manualTerm ← (Lean.Elab.Term.withoutErrToSorry
        (Lean.Elab.Term.elabTermAndSynthesize stx (some (.const ``UInt64 [])))).run'
      let manualTerm ← Lean.instantiateMVars manualTerm
      let (info, probe) ← match ← Probe.ofStatement stateBinding .minimal ctx disjuncts #[(0, manualTerm)] with
        | .ok r => pure r
        | .error e => throwError s!"toyManual: the probe refused to build: {e}"
      let instConsts ← stmt.instances.mapM fun (_, kind) =>
        match Preset.constOf stateBinding .minimal kind with
        | .ok c => pure c
        | .error e => throwError e
      -- `Support.searchCtxOf` carries no manual terms; this drive fixes
      -- input 0, so the construction stays inline
      let sctx : SearchCtx :=
        { probe, info, binding := stateBinding, preset := PresetId.minimal,
          inputFvars := ctx.inputFvars, instFvars := ctx.instFvars,
          instConsts := instConsts, manualTerms := #[(0, manualTerm)],
          drawMemo := ← IO.mkRef #[], outDir := Tests.ToyFork.scratchOutDir,
          builtStamp := "", earlierWins := #[] }
      -- §9.4: the base searcher's `applies` refuses the state input, so
      -- the search loop never proposes the `default` state
      if baseSearcher.applies sctx stmt disjuncts[0]! then
        throwError "toyManual: base should refuse the state input"
      -- §9.4: the manual searcher refuses a partial set of manual terms
      -- that leaves the state input to the `default` fill
      if manualSearcher.applies sctx stmt disjuncts[0]! then
        throwError "toyManual: the manual searcher should refuse manual \
          terms over an uncovered state input"
      -- manual then bit-vector: the disjunct ends notFound
      let searchers : Array WitnessSearcher := #[manualSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok _ => throwError "toyManual: the search found a witness at an \
          unsatisfiable manual term"
      | .error .unsat => throwError "toyManual: the disjunct reported unsat, \
          but the vacuity is about one manual term"
      | .error (.notFound _ _) => pure ()
      | .error f => throwError s!"toyManual: {repr f}"
    -- ── the cap-fallback pin: seventeen disjuncts pass the cap, the pass
    -- keeps the unsplit hypothesis, and the note reports the fallback
    -- (§8.2)
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyManyDisjuncts fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, dropped) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyManyDisjuncts: expected one fallback disjunct, got \
          {disjuncts.size}"
      unless dropped.size == 1 && dropped[0]!.contains "disjunct cap" do
        throwError s!"toyManyDisjuncts: expected the cap note, got {repr dropped}"
      unless disjuncts[0]!.hyps.size == 1 do
        throwError "toyManyDisjuncts: the fallback lost the unsplit hypothesis"
      -- the fallback disjunct still carries its `Decidable` instance and
      -- solves
      unless disjuncts[0]!.hyps[0]!.getUsedConstants.contains ``Or do
        throwError "toyManyDisjuncts: the unsplit hypothesis lost its disjuncts"
    -- ── the dropped-disjunct pin: no `Decidable` instance for the disjunct's
    -- conjunction, so the pass reports the disjunct and drops it (§8.4)
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyNoDecidable fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, dropped) ← Prepare.pass stmt
      unless disjuncts.isEmpty do
        throwError s!"toyNoDecidable: expected no disjuncts, got {disjuncts.size}"
      unless dropped.size == 1
          && dropped[0]!.contains "no `Decidable` instance" do
        throwError s!"toyNoDecidable: expected the drop note, got \
          {repr dropped}"
    -- ── the alias-read pin: the manual read's type is the alias, and
    -- the searcher grounds it to the literal, so the solver takes the
    -- residual formula and the check accepts its model (§9.4)
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyAliasRead fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyAliasRead: expected one prepared disjunct, got \
          {disjuncts.size}"
      let stx ← `(term| 0)
      let manualTerm ← (Lean.Elab.Term.withoutErrToSorry
        (Lean.Elab.Term.elabTermAndSynthesize stx (some (.const ``UInt64 [])))).run'
      let manualTerm ← Lean.instantiateMVars manualTerm
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[(0, manualTerm)] with
        | .ok r => pure r
        | .error e => throwError s!"toyAliasRead: the probe refused to build: {e}"
      let instConsts ← stmt.instances.mapM fun (_, kind) =>
        match Preset.constOf binding .minimal kind with
        | .ok c => pure c
        | .error e => throwError e
      -- `Support.searchCtxOf` carries no manual terms; this drive fixes
      -- input 0, so the construction stays inline
      let sctx : SearchCtx :=
        { probe, info, binding, preset := PresetId.minimal,
          inputFvars := ctx.inputFvars, instFvars := ctx.instFvars,
          instConsts := instConsts, manualTerms := #[(0, manualTerm)],
          drawMemo := ← IO.mkRef #[], outDir := Tests.ToyFork.scratchOutDir,
          builtStamp := "", earlierWins := #[] }
      let searchers : Array WitnessSearcher := #[manualSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok (a, won) =>
        unless won == .bitVec do
          throwError s!"toyAliasRead: expected the bit-vector searcher to \
            win, got {won.tag}"
        unless probe.check disjuncts[0]!.index a do
          throwError "toyAliasRead: the candidate failed the check"
      | .error f =>
        throwError s!"toyAliasRead: the search found no witness: {repr f}"

namespace EthCLLib.TheoremVectors.Tests.BitVec

/-- The `Fin` bridge's theorem (§9.4): the input is a `Fin`, the bound
rejects the base searcher's zero, and the solver's stand-in must land in
`[2, 5)`. -/
theorem toyFinBound [HasherTag] (i : Fin 5) (h : 1 < i.val) :
    i.val + 1 ≤ 5 := by omega

/-- The stand-in lookup's pin (§9.4): a free scalar precedes the `Fin`
in binder order, so the bridge must walk `free`'s pairs and not the
`Fin`-only positions when it names the stand-in. -/
theorem toyFinAfterScalar [HasherTag] (_s : UInt64) (i : Fin 5)
    (h : 1 < i.val) : i.val + 1 ≤ 5 := by omega

/-- The bridge's equality pin (§9.4): the hypothesis is a `Nat`-form
equality over the `Fin.val` read, which bridges to the stand-in's
`UInt64` equality. -/
theorem toyFinEq [HasherTag] (i : Fin 5) (h : i.val = 3) :
    i.val + 1 = 4 := by omega

end EthCLLib.TheoremVectors.Tests.BitVec

open Lean.Elab.Command
open EthCLLib.TheoremVectors
open EthCLLib.TheoremVectors.Tests.BitVec in
run_cmd do
  liftTermElabM do
    let binding := EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding
    -- ── the `Fin` bridge pin: the solver takes the input as a `UInt64`
    -- with the bound `u < n`, the candidate decodes through `Fin`'s own
    -- codec, and the check holds
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyFinBound fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyFinBound: expected one prepared disjunct, got {disjuncts.size}"
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toyFinBound: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok (a, won) =>
        unless won == .bitVec do
          throwError s!"toyFinBound: expected the bit-vector searcher to \
            win, got {won.tag}"
        unless probe.check disjuncts[0]!.index a do
          throwError "toyFinBound: the candidate failed the check"
        let v := Tests.Support.leOf a[0]!
        unless 1 < v && v < 5 do
          throwError s!"toyFinBound: the witness value {v} left its window"
      | .error f =>
        throwError s!"toyFinBound: the search found no witness: {repr f}"
    -- ── the stand-in lookup's pin: the same drive with a free scalar
    -- ahead of the `Fin` in binder order
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyFinAfterScalar fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyFinAfterScalar: expected one prepared disjunct, got {disjuncts.size}"
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toyFinAfterScalar: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok (a, won) =>
        unless won == .bitVec do
          throwError s!"toyFinAfterScalar: expected the bit-vector searcher \
            to win, got {won.tag}"
        unless probe.check disjuncts[0]!.index a do
          throwError "toyFinAfterScalar: the candidate failed the check"
        let v := Tests.Support.leOf a[1]!
        unless 1 < v && v < 5 do
          throwError s!"toyFinAfterScalar: the witness value {v} left its \
            window"
      | .error f =>
        throwError s!"toyFinAfterScalar: the search found no witness: {repr f}"
    -- ── the equality pin: the hypothesis is a `Nat`-form equality over
    -- the `Fin.val` read, and the bridge's `UInt64` equality carries it
    Statement.readIn binding `EthCLLib.TheoremVectors.Tests.BitVec.toyFinEq fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      let (disjuncts, _) ← Prepare.pass stmt
      unless disjuncts.size == 1 do
        throwError s!"toyFinEq: expected one prepared disjunct, got {disjuncts.size}"
      let (info, probe) ← match ← Probe.ofStatement binding .minimal ctx disjuncts #[] with
        | .ok r => pure r
        | .error e => throwError s!"toyFinEq: the probe refused to build: {e}"
      let sctx ← Tests.Support.searchCtxOf binding .minimal
        Tests.ToyFork.scratchOutDir "" stmt ctx info probe
      let searchers : Array WitnessSearcher := #[baseSearcher, bitVecSearcher]
      match ← searchDisjunct searchers sctx stmt disjuncts[0]! with
      | .ok (a, won) =>
        unless won == .bitVec do
          throwError s!"toyFinEq: expected the bit-vector searcher to win, \
            got {won.tag}"
        unless probe.check disjuncts[0]!.index a do
          throwError "toyFinEq: the candidate failed the check"
        let v := Tests.Support.leOf a[0]!
        unless v == 3 do
          throwError s!"toyFinEq: the witness value {v} missed the \
            equality"
      | .error f =>
        throwError s!"toyFinEq: the search found no witness: {repr f}"
