import EthCLLib.Proofs.Preserves
import SizzLean.Proofs.SSZListSet
import SizzLean.Proofs.ProgressiveListSet

/-!
# `EthCLSpecs.Proofs.StepTactics`: the frame tactics the fork step proofs share

Each fork states its own step invariant over its own `BeaconState`: `StepInv`, `FrameEq`,
`coreFields` and `listSizes` in `Proofs/<Fork>/StateInvariants.lean`. The tactics here prove
the leaves and call sites of a `KeepsCore` proof against whichever fork's names are in scope
where they run. Each tactic builds those names with `mkIdent`, which leaves them without macro
scopes, so they resolve in the namespace of the proof that uses the tactic. A Fulu proof gets
the Fulu `coreFields`, and a Gloas proof gets the Gloas one.

* `frame_eq` closes `FrameEq w v` when `w` is a record update of `v` that leaves the six core
  values and the five list sizes alone, or overwrites list entries in place.
* `frame_leaf` closes `StepInv c w` from some `StepInv c v` hypothesis by `frame_eq`.
* `frame_close` closes a step-invariant leaf by `assumption` or `frame_leaf`.
* `call h`, `call_ro h`, `call_box h` step over a call to a `KeepsCore` step, a `ReadsOnly`
  accessor, and a step that writes only the box it is handed.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

/-- Close a `FrameEq w v` goal where `w` is a record update of `v`: the six core values agree
by `rfl` or after splitting an `if` the update holds, and the list sizes agree by `rfl` or
through a `set!` size lemma. -/
syntax "frame_eq" : tactic

macro_rules
  | `(tactic| frame_eq) => do
    let coreFields := Lean.mkIdent `coreFields
    let listSizes := Lean.mkIdent `listSizes
    `(tactic| first
      | exact ⟨rfl, rfl⟩
      | exact ⟨rfl, by
          simp [$listSizes:ident, box_reduce, SizzLean.Proofs.sszListSet!_size,
            SizzLean.Proofs.progressiveListSet!_size]⟩
      | (constructor
         <;> (simp only [$coreFields:ident, $listSizes:ident, box_reduce]
              <;> (repeat' split_ite)
              <;> simp [box_reduce, SizzLean.Proofs.sszListSet!_size,
                    SizzLean.Proofs.progressiveListSet!_size])))

open Lean Elab Tactic in
/-- Close a `StepInv c w` leaf from some `StepInv c v` hypothesis, when `w` is a record update of
`v` that `frame_eq` handles. It tries each `StepInv` hypothesis, most recent first: a `subst`
reorders the context, so the right one need not be the last. A hypothesis counts when its type
is an application of a constant named `StepInv`, in any fork's namespace. -/
elab "frame_leaf" : tactic => withMainContext do
  let isStepInv (e : Expr) : Bool := match e.getAppFn.constName? with
    | some (.str _ s) => s == "StepInv"
    | _ => false
  let ofFrameEq := mkIdent `StepInv.of_frameEq
  for ld in (← getLCtx).decls.toList.reverse.filterMap id do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless isStepInv ty do continue
    let saved ← saveState
    try
      let h ← Term.exprToSyntax ld.toExpr
      evalTactic (← `(tactic| (refine $ofFrameEq $h ?_) <;> (frame_eq; done)))
      return
    catch _ =>
      saved.restore
  throwError "frame_leaf: no StepInv hypothesis gives the goal by a frame step"

/-- Close a step-invariant leaf: a hypothesis that states it, or a record update of the state
some `StepInv` hypothesis is about. -/
macro "frame_close" : tactic => `(tactic| first | assumption | frame_leaf)

/-- Step over a call to a `KeepsCore` step: the rest of the body runs from a state that
satisfies the same `StepInv`. `frame_close` proves the premise once the goal has fixed the
start, which may be a record update of an earlier state. -/
macro "call " h:term : tactic =>
  `(tactic| refine EthCLLib.Proofs.Preserves.run ($h _) (by frame_close) (fun _ _ _ => ?_))

/-- Step over a call to a `ReadsOnly` accessor. -/
syntax "call_ro " term : tactic

macro_rules
  | `(tactic| call_ro $h) => do
    let stepInv := Lean.mkIdent `StepInv
    `(tactic| refine EthCLLib.Proofs.Preserves.run
      (EthCLLib.Proofs.ReadsOnly.preserves (P := $stepInv _) $h) (by frame_close)
      (fun _ _ _ => ?_))

/-- Step over a call that writes only the box it is handed, such as `increaseBalance`. `h`
takes the `StepInv` fact for the handed value, which `frame_close` proves once the goal has
fixed that value, and returns one for the value of the box it hands back. The threaded state
stays, and the returned box is `pureState s'`. -/
macro "call_box " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunEnsures.weaken ($h (by frame_close)) (fun _ _ hbox => ?_)
             obtain ⟨hst, _, hb, _⟩ := hbox
             subst hst hb))

/-- A write whose box is an `if` over record updates, such as `modifyState fun state => if c
then sszUpdate state with … else state`: split the box's guards to prove, branch by branch, that
the written box is the uncached box of its own view. The postcondition at that view is left for
the walk. -/
macro "write_split" : tactic =>
  `(tactic| (refine EthCLLib.Proofs.runEnsures_modifyThe_view ?_ ?_
             (simp only [box_reduce] <;> (repeat' split_ite) <;> rfl)))

end EthCLSpecs.Proofs
