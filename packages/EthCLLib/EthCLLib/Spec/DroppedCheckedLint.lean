import Lean

/-!
# `EthCLLib.Spec.DroppedCheckedLint`: the dropped-expression linter (SPIKE)

The §4.3 dropped-expression hazard (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md`):
an arithmetic expression is a `Checked` value, and a `let x := e` binds it without
executing it. The fault inside `e` is only examined where a path *binds* `x` (`← x`).
If some return path never does, the model returns a value there where the pyspec
raises at the assignment. The design document states this as an author rule; this
prototype makes a build gate of it.

What it flags: a `let x := e` whose type is `Checked _` (`Except ArithFault _`, or a
lift of it through `StateT` / `ReaderT`) where the let body has one return path that
references `x` and another that does not. All paths using it is the §4.3 allowed
layout split; no path using it is dead code, which the core unused-variable linter
owns.

How it works: a `Lean.Linter` over the elaborated `Expr` values of the declarations
each command adds (`Lean.Linter.getNewDecls` over the command's info trees). The
path analysis walks the value; `ite` branches and lambda continuations (`bind`
continuations, matcher alternatives, loop bodies) are the branch points, and a path
is a route to a `pure` (or to a bare monadic value such as the `total` of the §4.3
example) that does not cross a use of the binder.

Elaboration shapes. A pure let inside a `do` block does not reach the value as a
`letE`: do-notation elaborates it as `have`, that is `letFun e (fun x => body)`, a
const application with no type annotation on the binder. The scan treats `letFun`
like `letE` and recovers the type by `inferType` on the value. A `letE` binder and a
`letFun` binder are both loose bvars, so each let substitutes a fresh marker fvar
for its binder before the use analysis.

Spike quality. The approximations, each conservative toward silence except the last:

- The type filter is syntactic: head constants `Checked`, `Except ArithFault`,
  `ExceptT ArithFault`, and one `StateT` / `ReaderT` lift. A plain `def` alias of
  `Checked` escapes it (the fork DSL types aliases through `forkabbrev`, which emits
  an `abbrev`, so fork bodies do not write the escaping shape).
- A branch whose tail throws propagates its fault and yields no return paths, so it
  cannot hide a dropped fault; a branch that descends into an opaque helper applied
  to non-lambda arguments yields no paths either, which can silence a hazard.
- Continuation lambdas are transparent, so a use of `x` inside a `foldlM` body
  counts as a use on every path through the enclosing statement, not only on the
  loop's own.
- The `letFun` type check runs `inferType`; when the value's type still carries the
  monad metavariable after instantiation (a `liftM` whose monad instance search
  postponed, the elaborated form of a lifted `do` block), the filter stays silent.
  `EthCLLib/Tests/DroppedCheckedLint.lean` pins that silence.

Off by default. A module turns it on with `set_option linter.droppedChecked true`
after its imports; `EthCLLib/Tests/DroppedCheckedLint.lean` gates the §4.3 example
through `#guard_msgs`, and the fork-body run is a fork-body file's own `set_option`.
-/

set_option autoImplicit false

namespace EthCLLib.Spec.DroppedCheckedLint

open Lean Lean.Elab Command

register_option linter.droppedChecked : Bool := {
  defValue := false
  descr := "flag a `let` that binds a `Checked` value some return path never uses \
    (SPEC_ARITHMETIC.md §4.3, the dropped-expression hazard)"
}

/-! ## The type filter

`true` for the types whose value is an unexecuted arithmetic expression. `Checked`
is `Except ArithFault`'s reducible alias, so both spellings match at the head. The
recursive arms match the lifted monad structurally (a subterm of the argument), so
the recursion is structural. -/

private def isArithTy : Expr → Bool
  -- `Checked α`, applied or partial
  | .app (.const `EthCLLib.Spec.Checked _) _ => true
  -- `Except ArithFault α` / `ExceptT ArithFault m α`, applied or partial
  | .app (.app (.const ``Except _) (.const `EthCLLib.Spec.ArithFault _)) _ => true
  | .app (.app (.const ``ExceptT _) (.const `EthCLLib.Spec.ArithFault _)) _ => true
  -- one lift, monad-constructor form: `StateT σ (Except ArithFault …)`
  | .app (.app (.const ``StateT _) _)
      (.app (.app (.const ``Except _) (.const `EthCLLib.Spec.ArithFault _)) _) => true
  | .app (.app (.const ``ReaderT _) _)
      (.app (.app (.const ``Except _) (.const `EthCLLib.Spec.ArithFault _)) _) => true
  -- one lift, applied form: `StateT σ m α` / `ReaderT ρ m α`; the error monad is the
  -- middle argument of the spine, the last one is the result type
  | .app (.app (.app (.const ``StateT _) _) m) _ => isArithTy m
  | .app (.app (.app (.const ``ReaderT _) _) m) _ => isArithTy m
  | _ => false

/-! ## The path analysis

`pathUses x e` returns one `Bool` per return path of the monadic term `e`: whether
the path evaluates an expression containing `x`. Branch points are `ite` and the
lambda arguments of any application; a branch whose tail throws yields no paths. -/

private partial def pathUses (x : FVarId) (e : Expr) : Array Bool :=
  match e with
  | .app _ _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if (fn.isConstOf ``Pure.pure || fn.isConstOf ``Except.ok) && args.size ≥ 1 then
      -- `return e` / the tail value, in `pure` or constructor form: the expression
      -- the path returns
      #[args[args.size - 1]!.containsFVar x]
    else if fn.isConstOf ``ite && args.size == 5 then
      -- `ite`: args are `[α, c, inst, t, f]`; the condition runs on every path
      let base := pathUses x args[3]! ++ pathUses x args[4]!
      if args[1]!.containsFVar x then base.map (fun _ => true) else base
    else if fn.containsFVar x
        || (args.filter (·.isLambda |>.not)).any (·.containsFVar x) then
      -- an argument outside the branch points evaluates on every path
      #[true]
    else
      (args.filter (·.isLambda)).flatMap (pathUses x)
  | .letE _ _ v b _ => if v.containsFVar x then #[true] else pathUses x b
  -- a lambda is its body: a bind continuation, a matcher alternative, a loop body
  | .lam _ _ b _ => pathUses x b
  | .mdata _ e' => pathUses x e'
  | .proj _ _ e' => pathUses x e'
  -- a leaf in value position (the fvar `total` of the §4.3 example, a const, …)
  | _ => #[e.containsFVar x]

/-! ## The scan

One pass over a declaration's value, collecting the findings. The `Nat` thread keeps
each let's marker fvar unique, so a nested let's marker never collides with an
enclosing one. The monad serves the `letFun` type check (`inferType`; the elaborated
`have` carries no annotation on its binder). -/

/-- One scan step: walk `e` with marker counter `s`, returning the next counter and
the findings. -/
private partial def scanStep (e : Expr) (s : Nat) : CommandElabM (Nat × Array MessageData) := do
  match e with
  | .letE n t v b _ =>
    let (s1, acc) ← scanStep v s
    if isArithTy t then
      -- `b` refers to the binder through loose bvar 0; substitute a fresh marker
      -- fvar so the fvar-based use analysis can see it.
      let marker : FVarId := { name := Name.mkSimple s!"_droppedCheckedMarker{s1}" }
      let body := b.instantiate1 (.fvar marker)
      let ps := pathUses marker body
      let (s2, acc') ← scanStep body (s1 + 1)
      let msgs := if ps.contains true && ps.contains false then
        acc'.push m!"'let {n}' binds a `Checked` value that some return path never uses: the path returns without examining the fault, where the pyspec raises at the assignment (SPEC_ARITHMETIC.md §4.3, dropped expression)"
        else acc'
      pure (s2, acc ++ msgs)
    else do
      let (s2, acc') ← scanStep b s1
      pure (s2, acc ++ acc')
  -- `have x := v; rest`: the elaborated pure let of a `do` block; the binder's
  -- type is not stored, so recover it from the value
  | .app _ _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``letFun && args.size ≥ 2 then
      let v := args[args.size - 2]!
      let f := args[args.size - 1]!
      let (s1, acc) ← scanStep v s
      let ty ← tryCatch
          (liftTermElabM (do instantiateMVars (← Meta.inferType v)))
          (fun _ => pure (.const `EthCLLib.Spec.DroppedCheckedLint.unknownType []))
      if isArithTy ty then
        let rawBody := match f with | .lam _ _ b _ => b | _ => f
        let marker : FVarId := { name := Name.mkSimple s!"_droppedCheckedMarker{s1}" }
        let body := rawBody.instantiate1 (.fvar marker)
        let ps := pathUses marker body
        let (s2, acc') ← scanStep body (s1 + 1)
        let msgs := if ps.contains true && ps.contains false then
          acc'.push m!"'let x' binds a `Checked` value that some return path never uses: the path returns without examining the fault, where the pyspec raises at the assignment (SPEC_ARITHMETIC.md §4.3, dropped expression)"
          else acc'
        pure (s2, acc ++ msgs)
      else do
        let (s2, acc') ← scanStep f s1
        pure (s2, acc ++ acc')
    else
      args.toList.foldlM
        (fun (s, acc) arg => do
          let (s1, acc') ← scanStep arg s
          pure (s1, acc ++ acc'))
        (s, #[])
  | .lam _ _ b _ => scanStep b s
  | .mdata _ e' => scanStep e' s
  | .proj _ _ e' => scanStep e' s
  | _ => pure (s, #[])

/-- The linter: over every declaration the command adds, scan its value. -/
private def runDroppedChecked : Syntax → CommandElabM Unit := fun cmdStx => do
  unless linter.droppedChecked.get (← getOptions) do return
  let env ← getEnv
  let mut seen : NameSet := {}
  for tree in ← getInfoTrees do
    for declName in Lean.Linter.getNewDecls tree do
      if seen.contains declName then continue
      seen := seen.insert declName
      let some ci := env.find? declName | continue
      let some v := ci.value? | continue
      let (_, msgs) ← scanStep v 0
      for msg in msgs do
        Lean.Linter.logLintIf linter.droppedChecked cmdStx m!"{declName}: {msg}"

initialize addLinter { run := runDroppedChecked, name := `EthCLLib.Spec.DroppedCheckedLint.linter }

end EthCLLib.Spec.DroppedCheckedLint
