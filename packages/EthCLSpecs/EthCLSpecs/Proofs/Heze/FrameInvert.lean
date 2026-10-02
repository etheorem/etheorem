import EthCLSpecs.Heze.Transition
import EthCLSpecs.Proofs.Heze.KeepsUncached.Slots
import EthCLLib.Proofs.Frame

/-!
# `EthCLSpecs.Proofs.Heze.FrameInvert`: frame facts by run inversion

A frame fact says that a successful run keeps a view of the state. A frame lemma states it
over plain values only:

```lean
(h : (processX …).run (pureState t) = .ok (a, pureState t')) :
    view (pureState t') = view (pureState t)
```

`frame_invert h` proves such a fact. It inverts `h` one action at a time, with the run
lemmas of `EthCLLib/Proofs/Run.lean`:

- A bind splits at a `pureState` midpoint (`run_bind_eq_ok_pure`). The first action keeps
  the uncached box: the `keepsUncached_*` lemma of a spec function or `keeps_uncached`
  proves it. The tactic inverts the run of the first action for the view of the midpoint,
  and then the run of the continuation.
- A read (`get`, `getThe`) passes the start box to the continuation, and so does an
  `assert`.
- An `if`, a dependent `if`, or a `match` splits into its branches.
- A write (`modifyState g`, `set t`) ends in a record update of the start box. `is_pure`
  names it as `pureState` of a value, and `view_trans_hyp` proves that the update keeps the
  view.
- A call of a spec function closes by a frame lemma of that function. A frame lemma carries
  the attribute `@[frame]`, which indexes it by the function its run hypothesis names. A call
  without a frame lemma unfolds. A lemma may keep one value of the view: it concludes
  `view (pureState t') = c` from the hypothesis `view (pureState t) = c`. A `@[frame_proj]`
  lemma takes a frame fact of one view to a frame fact of a smaller view.
- A write that the rules above do not cover closes by a `@[frame_close]` lemma, whose
  hypotheses the context holds.
- A loop goes through an invariant lemma that also reads the threaded state
  (`forIn_run_inv_state` and its forms). The invariant says that the state is `pureState` of a
  value with the start view, and that each state part of the accumulator is too.

Inside the inversion, each goal is a tree of conjunctions of facts of one shape,
`∃ u, x = pureState u ∧ view (pureState u) = v`. Here `x` is the end state of a run, or a
state value that a run returns. A helper that returns a state value (`increaseBalance`,
`applyDeltas`) has a `_ret` lemma for the value it returns, with the view of its state
argument. The tactic proves the fact for the value that the first action of a bind returns,
and the continuation uses it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open Lean Meta Elab Tactic

/-! ## The `@[frame]` index -/

/-- The frame lemmas of each spec function, by the name of the function. -/
initialize frameExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (f, l) => m.insert f (((m.find? f).getD #[]).push l)
    addImportedFn := fun es => es.foldl (init := {}) fun m a =>
      a.foldl (init := m) fun m (f, l) => m.insert f (((m.find? f).getD #[]).push l)
  }

/-- The spec function whose run the last run hypothesis of a frame lemma inverts. -/
def frameTarget (type : Expr) : MetaM Name :=
  forallTelescope type fun xs _ => do
    for x in xs.reverse do
      let t ← instantiateMVars (← inferType x)
      if let some (_, lhs, _) := t.eq? then
        if lhs.isAppOfArity ``StateT.run 5 then
          if let some c := (lhs.getArg! 3).getAppFn.constName? then return c
    throwError "frame: the lemma has no run hypothesis of a spec function"

initialize registerBuiltinAttribute {
  name := `frame
  descr := "a frame lemma of a spec function, for `frame_invert`"
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do throwError "frame: the attribute is global only"
    let info ← getConstInfo decl
    let f ← MetaM.run' (frameTarget info.type)
    modifyEnv (frameExt.addEntry · (f, decl))
}

/-- The frame lemmas of the spec function `f`, the last one first. -/
def frameLemmas (f : Name) : CoreM (Array Name) := do
  return (((frameExt.getState (← getEnv)).find? f).getD #[]).reverse

/-- The projection lemmas: each takes a frame fact of one view to a frame fact of another. -/
initialize frameProjExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun a n => a.push n
    addImportedFn := fun es => es.foldl (init := #[]) fun a e => a ++ e
  }

initialize registerBuiltinAttribute {
  name := `frame_proj
  descr := "a lemma that takes a frame fact of one view to a frame fact of another"
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do throwError "frame_proj: the attribute is global only"
    modifyEnv (frameProjExt.addEntry · decl)
}

/-- The projection lemmas. -/
def frameProjs : CoreM (Array Name) := do
  return frameProjExt.getState (← getEnv)

/-- The closing lemmas: each proves `V t = v` for a write `t` that the other rules do not
cover, from hypotheses that the context holds. -/
initialize frameCloseExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun a n => a.push n
    addImportedFn := fun es => es.foldl (init := #[]) fun a e => a ++ e
  }

initialize registerBuiltinAttribute {
  name := `frame_close
  descr := "a lemma that proves the view of a write, for `frame_invert`"
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do throwError "frame_close: the attribute is global only"
    modifyEnv (frameCloseExt.addEntry · decl)
}

/-- The closing lemmas. -/
def frameCloses : CoreM (Array Name) := do
  return frameCloseExt.getState (← getEnv)

/-- Close a goal `V t = v` by a `@[frame_close]` lemma, whose hypotheses the context holds.
Before it, rewrite each `pureState q` of the goal back to the write `t` that a hypothesis
`t = pureState q` names. -/
syntax "pv_close_lemma" : tactic

/-- The body of `pv_close_lemma`. -/
def pvCloseLemma : TacticM Unit := withMainContext do
    let lemmas ← frameCloses
    let tryAll : TacticM Unit := do
      let g ← getMainGoal
      let some (_, glhs, grhs) := (← instantiateMVars (← g.getType)).eq?
        | throwError "pv_close_lemma: the goal is no equation"
      for l in lemmas do
        let saved ← saveState
        try
          -- A cheap filter first: the lemma reads the view of the goal, and its right side
          -- matches at reducible transparency. A lemma of another fact then never unfolds the
          -- view of the goal.
          let fits ← g.withContext do
            let (_, _, concl) ← forallMetaTelescopeReducing
              (← inferType (← mkConstWithFreshMVarLevels l))
            let some (_, llhs, lrhs) := concl.eq? | return false
            unless llhs.getAppFn.constName? == glhs.getAppFn.constName? do return false
            withReducible (isDefEq lrhs grhs)
          saved.restore
          unless fits do continue
          evalTactic (← `(tactic| (apply $(mkIdent l)) <;> with_reducible assumption))
          return
        catch _ => saved.restore
      throwError "pv_close_lemma: no lemma closes the goal"
    let saved ← saveState
    try tryAll; return
    catch _ => saved.restore
    -- The `some` branch of `appendState`: name the list that `sszAppend?` builds, so the goal
    -- reads the write of that list.
    let tgt ← instantiateMVars (← getMainTarget)
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
      unless l.isAppOf ``Option.map && r.isAppOfArity ``Option.some 2 do continue
      let s' := r.appArg!
      unless s'.isFVar && (tgt.find? (· == s')).isSome do continue
      let saved ← saveState
      try
        let x := mkIdent (← mkFreshUserName `x)
        let hx := mkIdent (← mkFreshUserName `hx)
        let hs := mkIdent (← mkFreshUserName `hs)
        evalTactic (← `(tactic| (
          obtain ⟨$x:ident, $hx:ident, $hs:ident⟩ :=
            Option.map_eq_some_iff.mp $(mkIdent d.userName):ident
          subst $hs:ident)))
        -- The substituted write applies a lambda. Reduce it, so that the lemmas match.
        let g ← getMainGoal
        replaceMainGoal [← g.replaceTargetDefEq (← Core.betaReduce (← g.getType))]
        tryAll
        return
      catch _ => saved.restore
    -- Rewrite the named boxes back to their writes.
    let tgt ← instantiateMVars (← getMainTarget)
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let some (_, _, r) := (← instantiateMVars d.type).eq? | continue
      unless r.isAppOf ``EthCLLib.Proofs.pureState do continue
      unless (tgt.find? (· == r)).isSome do continue
      let saved ← saveState
      try
        evalTactic (← `(tactic| rw [← $(mkIdent d.userName):ident]))
        -- This file declares `view_trans_hyp` below. Parse it when the tactic runs.
        let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `tactic "view_trans_hyp"
        try evalTactic stx
        catch _ => tryAll
        return
      catch _ => saved.restore
    throwError "pv_close_lemma: no lemma closes the goal"

elab_rules : tactic
  | `(tactic| pv_close_lemma) => pvCloseLemma

/-! ## Rules for views -/

/-- Let `s'` be the `some` of `Option.map g o`. Then `s'` has `f = v` when `s` has `f = v`
and every `g a` has the `f` of `s`. `sszAppend? s field x` unfolds to such a map, with `g`
a write of the list `field`. -/
theorem view_of_map_some {σ α β : Type} {s s' : σ} {g : α → σ} {o : Option α}
    {f : σ → β} {v : β} (h : Option.map g o = some s') (hs : f s = v)
    (hg : ∀ a, f (g a) = f s) : f s' = v := by
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [hg a, hs]

/-- A run that keeps the state keeps every view. A spec function that only reads the state
has one frame lemma, with the conclusion `(pureState t').view = (pureState t).view`, and this
projection serves each view. -/
theorem frame_of_reads {T β : Type} [SizzLean.SSZRepr T] [EthCLLib.Spec.HasherTag]
    {V : SizzLean.Cache.SSZ.Box EthCLLib.Spec.HasherTag.H T → β} {a b : T}
    (h : (EthCLLib.Proofs.pureState a).view = (EthCLLib.Proofs.pureState b).view) :
    V (EthCLLib.Proofs.pureState a) = V (EthCLLib.Proofs.pureState b) := by
  have hab : a = b := h
  rw [hab]

/-- A successful bind from `pureState v`, whose first action keeps the state. The first
action ends in `pureState v`, and the rest runs from it. A frame lemma with the conclusion
`(pureState t').view = (pureState v).view` gives `hx`. -/
theorem run_bind_eq_ok_keep {T ε α β : Type} [SizzLean.SSZRepr T] [EthCLLib.Spec.HasherTag]
    {x : StateT (SizzLean.Cache.SSZ.Box EthCLLib.Spec.HasherTag.H T) (Except ε) α}
    {k : α → StateT (SizzLean.Cache.SSZ.Box EthCLLib.Spec.HasherTag.H T) (Except ε) β}
    {v : T} {r : β × SizzLean.Cache.SSZ.Box EthCLLib.Spec.HasherTag.H T}
    (hk : EthCLLib.Proofs.KeepsUncached x)
    (hx : ∀ a t', x.run (EthCLLib.Proofs.pureState v) = .ok (a, EthCLLib.Proofs.pureState t') →
      (EthCLLib.Proofs.pureState t').view = (EthCLLib.Proofs.pureState v).view)
    (h : (x >>= k).run (EthCLLib.Proofs.pureState v) = .ok r) :
    ∃ a, x.run (EthCLLib.Proofs.pureState v) = .ok (a, EthCLLib.Proofs.pureState v) ∧
      (k a).run (EthCLLib.Proofs.pureState v) = .ok r := by
  obtain ⟨a, w, h1, h2⟩ := EthCLLib.Proofs.run_bind_eq_ok_pure hk h
  have hw : w = v := hx a w h1
  subst hw
  exact ⟨a, h1, h2⟩

/-- One step of a pure update chain that the `do` notation compiles to a join point `J`:
an `if` that passes the updated state `a` or the state `b` to `J`. The result has the
view of `s` when `J` keeps the view and `a` and `b` have the view of `s`.

The `do` notation writes `let mut state … if c then state := …` as
`have J := fun state y => rest; if c then J a () else J b ()`. Inlining `J` copies `rest`
into both branches, and six such steps grow the term by a factor of 64. With this lemma,
each join point gets one proof (`jp_level`). -/
theorem view_jp_ite {σ β : Type} (f : σ → β) {c : Prop} {dc : Decidable c}
    {J : σ → PUnit → Id σ} {a b s : σ}
    (hJ : ∀ s y, f (J s y) = f s) (ha : f a = f s) (hb : f b = f s) :
    f (@ite (Id σ) c dc (pure PUnit.unit >>= fun y => J a y)
        (pure PUnit.unit >>= fun y => J b y)) = f s := by
  cases dc
  · exact (hJ b _).trans hb
  · exact (hJ a _).trans ha

/-- Prove `∀ s y, view (J s y) = view s` for the join point `J`, a `let` in the context,
from the same fact `h` for the join point that `J` calls. `simp -zeta` unfolds `J` and
keeps the `have` bindings of its body. `extract_lets` moves them to the context, so the
next join point stays a name. -/
syntax "jp_level " ident ident : tactic
macro_rules
  | `(tactic| jp_level $J $h) => `(tactic| (
      intro s _
      simp -zeta only [$J:ident]
      extract_lets
      refine EthCLSpecs.Proofs.Heze.view_jp_ite _ $h ?_ rfl
      dsimp -zeta +zetaDelta only
      cases s <;> with_unfolding_all rfl))

/-- `forIn_array_run_inv_state` for a loop over an `SSZList`. The `ForIn` instance of
`SSZList` runs the loop over the underlying array. -/
theorem forIn_sszList_run_inv_state {σ ε α β : Type} {cap : Nat} (P : β → σ → Prop)
    {f : α → β → StateT σ (Except ε) (ForInStep β)} {xs : SizzLean.Repr.SSZList α cap}
    (hstep : ∀ a ∈ xs.val.toList, ∀ (r : β) (s : σ) (st : ForInStep β) (s' : σ),
      P r s → (f a r).run s = .ok (st, s') → P st.value s')
    {init : β} {s : σ} {r : β} {s' : σ} (hinit : P init s)
    (h : (forIn xs init f).run s = .ok (r, s')) : P r s' :=
  EthCLLib.Proofs.forIn_array_run_inv_state P hstep hinit h

/-- One step of a proof of `view x = view y`, where `x` is a pure update of `y`. -/
syntax "view_step" : tactic
/-- Close a goal `view x = view y`, where `x` is a pure update of `y`. -/
syntax "view_solve" : tactic
macro_rules
  | `(tactic| view_solve) => `(tactic| (repeat' view_step) <;> done)
macro_rules
  | `(tactic| view_step) => `(tactic| first
      | with_reducible rfl
      | refine EthCLLib.Proofs.view_forIn_range _ _ (fun _ _ => ?_) _ _
      | refine EthCLLib.Proofs.view_forIn_array _ _ (fun _ _ => ?_) _ _
      | refine EthCLLib.Proofs.view_forIn_list _ _ (fun _ _ => ?_) _ _
      | simp only [bind_pure, pure_bind, Id.run_bind, Id.run_pure,
          EthCLLib.Proofs.forInStep_value_yield, EthCLLib.Proofs.forInStep_value_done]
      | unfold EthCLSpecs.Heze.modValidator
      | unfold EthCLSpecs.Heze.modBalance
      | split
      | with_unfolding_all rfl)

/-- Write each `MProd` and `Prod` projection function as a primitive projection, and
reduce a projection of an anonymous constructor. A loop accumulator reaches a goal in
several forms: `r.snd.fst` from the `have`s of the `do` notation, `r.2.1` after `dsimp`,
and `⟨a, b, c⟩.2.1` after a `match` on `r`. This function gives them one form. -/
def normProj (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let e := match e.getAppFn.constName?, e.getAppNumArgs with
      | some ``MProd.fst, 3 => Expr.proj ``MProd 0 e.appArg!
      | some ``MProd.snd, 3 => Expr.proj ``MProd 1 e.appArg!
      | some ``Prod.fst, 3 => Expr.proj ``Prod 0 e.appArg!
      | some ``Prod.snd, 3 => Expr.proj ``Prod 1 e.appArg!
      | _, _ => e
    match e with
    | .proj _ i c =>
      -- `MProd.mk α β a b` and `Prod.mk α β a b`: field `i` is argument `2 + i`.
      if (c.isAppOfArity ``MProd.mk 4 || c.isAppOfArity ``Prod.mk 4) then
        return .done (c.getArg! (2 + i))
      return .done e
    | _ => return .done e)

/-- The uncached box of `w` as a constructor term. `Box.ofPure` is private, so `simp` cannot
unfold `pureState` to the constructor on its own. With this form, `simp` reduces the box
`match`es of a write on `pureState w` to the record update of `w`. -/
theorem pureState_eq_uncached {T : Type} [SizzLean.SSZRepr T] [EthCLLib.Spec.HasherTag]
    (w : T) :
    EthCLLib.Proofs.pureState w = SizzLean.Cache.SSZ.Box.uncached
      (H := EthCLLib.Spec.HasherTag.H)
      { view := w } := rfl

/-- The definitions under the namespace `EthCLSpecs.Proofs.Heze` that the view `V` reads,
with the definitions they read in turn. -/
partial def viewDefs (V : Expr) : MetaM (Array Name) := do
  let rec go (e : Expr) (acc : Array Name) (depth : Nat) : MetaM (Array Name) := do
    let mut acc := acc
    for c in e.getUsedConstants do
      unless (`EthCLSpecs.Proofs.Heze).isPrefixOf c && !acc.contains c do continue
      let some (.defnInfo d) := (← getEnv).find? c | continue
      acc := acc.push c
      if depth > 0 then acc ← go d.value acc (depth - 1)
    return acc
  go V #[] 3

/-- Close a goal `V t = V (pureState w)`, where `t` is a pure update of `pureState w`. The
boxes reduce to records of `w`, `V` unfolds to field reads, and the `if`s split. -/
def viewValue (V : Expr) : TacticM Unit := withMainContext do
  let names ← viewDefs V
  let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  evalTactic (← `(tactic| (
    simp only [EthCLSpecs.Proofs.Heze.pureState_eq_uncached, EthCLLib.Spec.stateRoot,
      SizzLean.Cache.SSZ.Box.hashTreeRoot, SizzLean.Cache.SSZ.Box.view, $ids,*]
    all_goals first
      | rfl
      | (repeat' split) <;> rfl)))

/-- Close a goal `f t = v` from a hypothesis `h : f s = v`, where `t` is a pure update of
the state `s`. The tactic tries the hypotheses from the last one to the first. It takes `h`
only when `s` occurs in `t`.

The tactic first writes the projections of the goal and of `s` in one form (`normProj`),
then replaces `s` in `f t = f s` by a new variable. It proves `f t = f s` by `view_solve`.
When `t` writes `s` through a nested update, the box `match` of the outer write is on a
term, and `split` cannot reduce it. Then a case split on the box `s` reduces both writes. -/
syntax "view_trans_hyp" : tactic

elab_rules : tactic
  | `(tactic| view_trans_hyp) => withMainContext do
    let goal0 ← getMainGoal
    let tgt ← instantiateMVars (← goal0.getType)
    let some (_, _, rhs) := tgt.eq?
      | throwError "view_trans_hyp: the goal is not an equality"
    let goal ← goal0.replaceTargetDefEq (← normProj tgt)
    let some (_, lhs, _) := (← goal.getType).eq?
      | throwError "view_trans_hyp: the goal is not an equality"
    unless lhs.isApp do throwError "view_trans_hyp: the goal is not `f t = v`"
    replaceMainGoal [goal]
    for fvarId in (← getLCtx).getFVarIds.reverse do
      let decl ← fvarId.getDecl
      if decl.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars decl.type).eq? | continue
      unless r == rhs && l.isApp && l.appFn! == lhs.appFn! do continue
      let s ← normProj l.appArg!.headBeta
      unless (lhs.appArg!.find? (· == s)).isSome do continue
      let saved ← saveState
      try
        -- `m : f t = f s`, and `m.trans h` closes the goal.
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs (mkApp l.appFn! s))
        goal.assign (← mkEqTrans m (mkFVar fvarId))
        -- On `pureState` of a value, both sides reduce to values: try that first.
        if s.isAppOf ``EthCLLib.Proofs.pureState then
          let beforeRfl ← saveState
          try
            replaceMainGoal [m.mvarId!]
            viewValue l.appFn!
            return
          catch _ => beforeRfl.restore
        -- Name `s`, so that `split` and `cases` see a variable.
        let (sId, g) ← if s.isFVar then pure (s.fvarId!, m.mvarId!) else do
          let (fvars, g) ← m.mvarId!.generalize #[{ expr := s }]
          pure (fvars[0]!, g)
        replaceMainGoal [g]
        let afterName ← saveState
        try
          evalTactic (← `(tactic| view_solve))
        catch _ =>
          afterName.restore
          let cases ← g.cases sId
          setGoals (cases.map (·.mvarId)).toList
          evalTactic (← `(tactic| all_goals with_unfolding_all rfl))
        return
      catch _ =>
        saved.restore
    throwError "view_trans_hyp: no hypothesis closes the goal"

/-! ## The inversion -/

/-- The program, the start state, and the result of a run hypothesis
`prog.run s = .ok r`. -/
def runParts? (t : Expr) : Option (Expr × Expr × Expr) := do
  let (_, lhs, rhs) ← t.eq?
  guard (lhs.isAppOfArity ``StateT.run 5)
  guard (rhs.isAppOfArity ``Except.ok 3)
  return (lhs.getArg! 3, lhs.getArg! 4, rhs.getArg! 2)

/-- The fixed data of one inversion. -/
structure FrameCtx where
  /-- The view. -/
  V : Expr
  /-- The view value that the facts claim. -/
  v : Expr
  /-- Whether the threaded state keeps the view `v`. A `_ret` lemma claims the view of a
  returned value only, and the threaded state has another view. -/
  stateView : Bool

/-- A new identifier with a fresh name, for a hypothesis the inversion adds. -/
def freshId (base : Name) : TacticM Ident := do
  return mkIdent (← mkFreshUserName base)

/-- The local hypothesis with the user name `n`. -/
def hypOf (n : Name) : TacticM FVarId := withMainContext do
  return (← getLocalDeclFromUserName n).fvarId

/-- The type of the local hypothesis with the user name `n`. -/
def hypType (n : Name) : TacticM Expr := withMainContext do
  instantiateMVars (← (← hypOf n).getType)

/-- Run `k`, then clear the hypothesis that `hn` named before it from every goal left. A step
of the inversion derives a new run hypothesis from `hn`, and the old one only grows the
context that each later `subst` and `cases` rewrites. -/
def withConsume {α : Type} (hn : Name) (k : TacticM α) : TacticM α := do
  let fv ← hypOf hn
  let r ← k
  let gs ← (← getGoals).mapM fun g => do
    if (← g.withContext do return (← getLCtx).contains fv) then g.tryClear fv else pure g
  setGoals gs
  return r

/-- Run a tactic on the main goal, and return the goals it leaves. -/
def runTac (stx : TSyntax `tactic) : TacticM (List MVarId) := do
  evalTactic stx
  getGoals

/-- `∃ u, x = pureState u ∧ V (pureState u) = v`, the fact the inversion proves of a state
`x`. With `view := false`, the fact `∃ u, x = pureState u` only. -/
def pvFact (ctx : FrameCtx) (x : Expr) (view := true) : TacticM Expr := do
  let xs ← Term.exprToSyntax x
  let Vs ← Term.exprToSyntax ctx.V
  let vs ← Term.exprToSyntax ctx.v
  let stx ← if view then
      `(∃ u, $xs = EthCLLib.Proofs.pureState u ∧ $Vs (EthCLLib.Proofs.pureState u) = $vs)
    else `(∃ u, $xs = EthCLLib.Proofs.pureState u)
  let e ← Tactic.elabTerm stx none
  instantiateMVars e

/-- Beta-reduce the goal, or the hypothesis `h` with `frame_beta at h`. -/
syntax "frame_beta" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| frame_beta) => withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    replaceMainGoal [← g.replaceTargetDefEq (← Core.betaReduce t)]
  | `(tactic| frame_beta at $h) => withMainContext do
    let g ← getMainGoal
    let d ← getLocalDeclFromUserName h.getId
    let t ← instantiateMVars d.type
    replaceMainGoal [← g.replaceLocalDeclDefEq d.fvarId (← Core.betaReduce t)]

/-- Close a goal `V x = v`. -/
syntax "pv_view" : tactic
macro_rules
  | `(tactic| pv_view) => `(tactic| first
      | with_reducible assumption
      | (frame_beta; with_reducible assumption)
      | view_trans_hyp
      | (simp -zeta only [EthCLLib.Spec.stateRoot, SizzLean.Proofs.hashTreeRoot_uncachedBox]
         view_trans_hyp)
      | pv_close_lemma
      | (refine EthCLSpecs.Proofs.Heze.view_of_map_some ‹_› ‹_› fun _ => ?_
         first
           | with_unfolding_all rfl
           | (dsimp only; split <;> with_unfolding_all rfl)))

/-- Close an `IsPure x` goal. `is_pure` covers a record update. The `some` branch of
`appendState` writes a box that `isPure_of_map_eq_some` covers. -/
syntax "pv_pure" : tactic
macro_rules
  | `(tactic| pv_pure) => `(tactic| first
      | exact ⟨_, rfl⟩
      | (frame_beta; is_pure)
      | (simp -zeta only [EthCLLib.Spec.stateRoot, SizzLean.Proofs.hashTreeRoot_uncachedBox]
         is_pure)
      | exact EthCLLib.Proofs.isPure_of_map_eq_some (fun _ => ⟨_, rfl⟩) (by assumption))

/-- The parts of a fact: the state `x`, and whether the fact claims a view. -/
def factParts? (t : Expr) : MetaM (Option (Expr × Bool)) := do
  let t ← whnfR (← instantiateMVars t)
  unless t.isAppOfArity ``Exists 2 do return none
  lambdaTelescope (t.getArg! 1) fun _ b => do
    let b ← whnfR b
    if b.isAppOfArity ``And 2 then
      let some (_, x, _) := (b.getArg! 0).eq? | return none
      return some (x, true)
    let some (_, x, _) := b.eq? | return none
    return some (x, false)

/-- Reduce the projections of a loop step and of a tuple in `e`: `(yield a).value` to `a`,
and a projection of an anonymous constructor to its field. -/
def normStep (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Meta.transform e (post := fun e => do
    if e.isAppOfArity ``ForInStep.value 2 then
      let a := e.appArg!
      if a.isAppOfArity ``ForInStep.yield 2 || a.isAppOfArity ``ForInStep.done 2 then
        return .done a.appArg!
    return .done e)
  normProj e

/-- Close a fact `∃ u, x = pureState u ∧ V (pureState u) = v`, or a conjunction of them. -/
partial def pvClose : TacticM Unit := do
  if (← getGoals).isEmpty then return
  withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  if tgt.isConstOf ``True then
    evalTactic (← `(tactic| trivial))
    return
  if tgt.isAppOfArity ``And 2 then
    let gs ← runTac (← `(tactic| refine ⟨?_, ?_⟩))
    for g in gs do
      setGoals [g]
      pvClose
    return
  let some (x, view) ← factParts? tgt | throwError "pvClose: the goal is no fact: {tgt}"
  -- The fast path: `x` reduces by projections to `pureState u`, and a hypothesis gives the
  -- view of `pureState u`.
  let x' ← normStep x
  if x'.isAppOf ``EthCLLib.Proofs.pureState then
    let saved ← saveState
    try
      let us ← Term.exprToSyntax x'.appArg!
      if view then
        evalTactic (← `(tactic| exact ⟨$us, rfl, by with_reducible assumption⟩))
      else
        evalTactic (← `(tactic| exact ⟨$us, rfl⟩))
      return
    catch _ => saved.restore
  let xs ← Term.exprToSyntax x
  let u ← freshId `u
  let hu ← freshId `hu
  evalTactic (← `(tactic|
    obtain ⟨$u, $hu⟩ : EthCLLib.Proofs.IsPure $xs := by pv_pure))
  if view then
    evalTactic (← `(tactic| (
      refine ⟨$u, $hu, ?_⟩
      rw [← $hu:ident]
      all_goals pv_view)))
  else
    evalTactic (← `(tactic| exact ⟨$u, $hu⟩))

/-- Substitute an equation `e : a = b` into the goal: by `subst` when a side is a variable,
through `pureState_inj` when both sides are `pureState`, and by `rw` otherwise. -/
partial def substEq (e : Ident) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  withMainContext do
  let some (_, a, b) := (← hypType e.getId).eq? | throwError "substEq: not an equation"
  if (a.isFVar && !b.containsFVar a.fvarId!) || (b.isFVar && !a.containsFVar b.fvarId!) then
    evalTactic (← `(tactic| subst $e:ident))
  else if a.isAppOf ``EthCLLib.Proofs.pureState && b.isAppOf ``EthCLLib.Proofs.pureState then
    evalTactic (← `(tactic| replace $e := EthCLLib.Proofs.pureState_inj $e))
    substEq e
  else if a.getAppFn.isConst && b.getAppFn.isConst &&
      (← isConstructorApp a) && (← isConstructorApp b) then
    -- Two constructor terms: `cases` matches the arguments, or closes a goal whose
    -- constructors differ.
    evalTactic (← `(tactic| first | cases $e:ident | rw [$e:ident] | skip))
  else
    evalTactic (← `(tactic| first | rw [$e:ident] | skip))

/-- The heads of loops that `frame_invert` runs through an invariant. -/
def loopHeads : List Name :=
  [``ForIn.forIn, ``ForIn'.forIn', ``List.foldlM, ``Array.foldlM, ``EthCLLib.Spec.fuelLoop]

/-- The heads of the reads of the state. -/
def getHeads : List Name :=
  [``MonadState.get, ``MonadStateOf.get, ``getThe, ``get]

/-- The heads of the writes of the state by `set`. -/
def setHeads : List Name :=
  [``MonadStateOf.set, ``MonadState.set, ``set]

/-- The `keepsUncached_*` or `returnsUncached_*` lemma of the spec function `c`, by name. -/
def uncachedLemma? (pre : String) (c : Name) : CoreM (Option Name) := do
  let n := (`EthCLSpecs.Proofs.Heze).str (pre ++ c.getString!)
  return if (← getEnv).contains n then some n else none

/-- Prove `KeepsUncached x` for the first action `x` of a bind: by the `keepsUncached_*`
lemma of the spec function `x` calls, or by `keeps_uncached`. -/
syntax "frame_keeps" : tactic

elab_rules : tactic
  | `(tactic| frame_keeps) => withoutRecover <| withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let x := tgt.appArg!
    if let some c := x.getAppFn.constName? then
      if let some l ← uncachedLemma? "keepsUncached_" c then
        try
          evalTactic (← `(tactic| apply $(mkIdent l)))
          return
        catch _ => pure ()
      if let some l ← uncachedLemma? "returnsUncached_" c then
        try
          let xs ← Term.exprToSyntax x
          evalTactic (← `(tactic| (
            have hr : EthCLLib.Proofs.ReturnsUncached $xs := by apply $(mkIdent l)
            exact fun v b s hh => (hr v b s hh).2)))
          return
        catch _ => pure ()
    evalTactic (← `(tactic| keeps_uncached))
    unless (← getGoals).isEmpty do throwError "frame_keeps: `keeps_uncached` left goals"

/-- Name the program of a run hypothesis after a head `let`, `have`, or beta-redex. -/
def normHead (hn : Name) : TacticM Bool := withMainContext do
  let h ← hypOf hn
  let t ← instantiateMVars (← h.getType)
  let some (prog, _, _) := runParts? t | return false
  let prog' : Option Expr := match prog with
    | .letE _ _ val body _ => some (body.instantiate1 val)
    | .mdata _ e => some e
    | _ =>
      if prog.isAppOfArity ``letFun 4 then
        some ((prog.getArg! 3).bindingBody!.instantiate1 (prog.getArg! 2))
      else if prog.isHeadBetaTarget then some prog.headBeta
      else none
  let some prog' := prog' | return false
  let some (_, lhs, rhs) := t.eq? | return false
  let lhs' := mkAppN lhs.getAppFn (lhs.getAppArgs.set! 3 prog')
  let t' ← mkEq lhs' rhs
  let g ← (← getMainGoal).replaceLocalDeclDefEq h t'
  replaceMainGoal [g]
  return true

/-- The paths from a value of type `ty` to its parts of the state type `σ`, each as a list
of `MProd` and `Prod` projections. -/
partial def statePaths (σ ty : Expr) : MetaM (List (List Name)) := do
  let ty ← whnfR (← instantiateMVars ty)
  if ← withReducible (isDefEq ty σ) then return [[]]
  let ps := match ty.getAppFn.constName? with
    | some ``MProd => some (``MProd.fst, ``MProd.snd)
    | some ``Prod => some (``Prod.fst, ``Prod.snd)
    | _ => none
  let some (pf, ps) := ps | return []
  let args := ty.getAppArgs
  unless args.size == 2 do return []
  let l ← statePaths σ args[0]!
  let r ← statePaths σ args[1]!
  return l.map (pf :: ·) ++ r.map (ps :: ·)

/-- The facts of a value `a` with state parts: one fact per part, joined by `And`, with the
fact `first` in front. -/
def partsFact (ctx : FrameCtx) (σ a : Expr) (first : Option Expr) (view := true) :
    TacticM (Option Expr) := do
  let paths ← statePaths σ (← inferType a)
  let mut fact := first
  for path in paths do
    let part ← path.foldlM (fun e n => mkAppM n #[e]) a
    let f ← pvFact ctx part (view := view)
    fact := some (← match fact with
      | none => pure f
      | some g => mkAppM ``And #[g, f])
  return fact

/-- The invariant of a loop: the state is `pureState` of a value with the view `v`, and so
is each state part of the accumulator. With `partsView := false`, the parts are
`pureState` of values only: an accumulator that starts from a state argument has the view
of that argument. -/
def loopInv (ctx : FrameCtx) (σ β : Expr) (partsView : Bool) : TacticM Expr :=
    withMainContext do
  withLocalDeclD `acc β fun acc => withLocalDeclD `st σ fun st => do
    let sf ← pvFact ctx st (view := ctx.stateView)
    let some p ← partsFact ctx σ acc (some sf) (view := partsView) | throwError "loopInv"
    mkLambdaFVars #[acc, st] p

/-- Split a hypothesis that is a conjunction of facts `∃ u, x = pureState u ∧ …`, and
substitute each equation `x = pureState u`. -/
partial def useFacts (hn : Name) : TacticM Unit := withMainContext do
  let t ← whnfR (← hypType hn)
  if t.isAppOfArity ``And 2 then
    let a ← freshId `ha
    let b ← freshId `hb
    evalTactic (← `(tactic| obtain ⟨$a, $b⟩ := $(mkIdent hn)))
    useFacts a.getId
    useFacts b.getId
    return
  let some (_, view) ← factParts? t | return
  let u ← freshId `u
  let e ← freshId `he
  if view then
    let hv ← freshId `hv
    evalTactic (← `(tactic| obtain ⟨$u, $e, $hv⟩ := $(mkIdent hn)))
  else
    evalTactic (← `(tactic| obtain ⟨$u, $e⟩ := $(mkIdent hn)))
  substEq e

/-- Split a variable of a tuple type into its parts, recursively, so that its projections
reduce. -/
partial def splitTuple (x : Name) : TacticM Unit := withMainContext do
  let ty ← whnfR (← hypType x)
  unless ty.isAppOf ``MProd || ty.isAppOf ``Prod do return
  let a ← freshId `x
  let b ← freshId `x
  evalTactic (← `(tactic| obtain ⟨$a, $b⟩ := $(mkIdent x)))
  splitTuple a.getId
  splitTuple b.getId

/-- The heads of actions that read the state and never write it: lifted `Except` values,
checked reads and arithmetic, and `pure`. -/
def readHeads : List Name :=
  [``EthCLLib.Spec.liftErr, ``EthCLLib.Spec.sszGetIdx, ``EthCLLib.Spec.arrGetIdx,
    ``EthCLLib.Spec.checkedAdd, ``EthCLLib.Spec.checkedSub, ``EthCLLib.Spec.checkedMul,
    ``EthCLLib.Spec.throwArithmetic, ``EthCLLib.Spec.throwListFull,
    ``EthCLLib.Spec.sszOfArrayM, ``MonadExcept.ofExcept, ``Pure.pure]

/-- Prove the goal `s' = s` from a run `hn : x.run s = .ok (a, s')` of an action `x` that only
reads the state. -/
partial def readKeeps (hn : Name) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  if ← normHead hn then return ← readKeeps hn
  let hI := mkIdent hn
  let t ← hypType hn
  let some (prog, _, _) := runParts? t | throwError "readKeeps: no run"
  let some c := prog.getAppFn.constName? | throwError "readKeeps: no head"
  if c == ``MonadExcept.ofExcept then
    evalTactic (← `(tactic| exact (EthCLLib.Proofs.run_ofExcept_eq_ok $hI).2))
  else if c == ``Pure.pure then
    evalTactic (← `(tactic| exact (EthCLLib.Proofs.run_pure_eq_ok_state $hI).2))
  else if c == ``MonadExcept.throw || c == ``MonadExceptOf.throw || c == ``throwThe then
    evalTactic (← `(tactic| cases $hI:ident))
  else if c == ``ite then
    let gs ← runTac (← `(tactic|
      rcases EthCLLib.Proofs.run_ite_eq_ok $hI with ⟨-, $hI⟩ | ⟨-, $hI⟩))
    for g in gs do
      setGoals [g]
      readKeeps hn
  else if ← isMatcher c then
    let gs ← runTac (← `(tactic| split at $hI:ident))
    for g in gs do
      setGoals [g]
      readKeeps hn
  else if readHeads.contains c then
    let ci := mkIdent c
    evalTactic (← `(tactic| unfold $ci:ident at $hI:ident))
    readKeeps hn
  else throwError "readKeeps: {c} may write the state"

/-- After `split` on a `match` of a tuple, substitute each equation `⟨a, b⟩ = ⟨x, y⟩` that the
split adds, so that the branch reads the parts of the tuple. -/
partial def substTupleEqs : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let found ← withMainContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      let some (_, l, r) := t.eq? | continue
      let isTuple (e : Expr) := e.isAppOfArity ``MProd.mk 4 || e.isAppOfArity ``Prod.mk 4
      if isTuple l && isTuple r then return some d.fvarId
    return none
  let some fv := found | return
  let saved ← saveState
  try
    let gs ← (← getMainGoal).cases fv
    setGoals (gs.map (·.mvarId)).toList
  catch _ =>
    saved.restore
    return
  substTupleEqs

/-- One step of a loop: invert the body run `hb` from the invariant `hPr` of the start. -/
syntax "frame_loop_step " ident ident : tactic

/-- The invariant of a loop at its start. -/
syntax "frame_loop_init" : tactic

/-- Prove the goal `goal` as a new hypothesis named `n`, by `k` on a goal of its own. -/
def assertBy (n : Name) (goal : Expr) (k : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let mv ← g.withContext (mkFreshExprSyntheticOpaqueMVar goal)
  let g ← g.assert n goal mv
  let (_, g) ← g.intro1P
  setGoals [mv.mvarId!]
  k
  unless (← getGoals).isEmpty do
    throwError "frame_invert: goals remain: {← getGoals}"
  setGoals [g]

mutual

/-- Invert the run hypothesis `hn` for the goal, a conjunction of facts
`∃ u, x = pureState u ∧ V (pureState u) = v`. -/
partial def frameInv (ctx : FrameCtx) (hn : Name) : TacticM Unit := withMainContext do
  if ← normHead hn then return ← frameInv ctx hn
  let t ← hypType hn
  let some (prog, _, _) := runParts? t
    | throwError "frame_invert: {hn} is no run hypothesis: {t}"
  let hI := mkIdent hn
  let some c := prog.getAppFn.constName?
    | throwError "frame_invert: no constant at the head of {prog}"
  if c == ``Bind.bind && prog.getAppNumArgs == 6 then
    return ← frameBind ctx hn (prog.getArg! 4)
  if c == ``ite then
    withConsume hn <| evalTactic (← `(tactic|
      rcases EthCLLib.Proofs.run_ite_eq_ok $hI with ⟨-, $hI⟩ | ⟨-, $hI⟩))
    for g in ← getGoals do
      setGoals [g]
      frameInv ctx hn
    return
  if c == ``dite then
    withConsume hn <| evalTactic (← `(tactic|
      rcases EthCLLib.Proofs.run_dite_eq_ok $hI with ⟨_, $hI⟩ | ⟨_, $hI⟩))
    for g in ← getGoals do
      setGoals [g]
      frameInv ctx hn
    return
  if ← isMatcher c then
    let gs ← runTac (← `(tactic| split at $hI:ident))
    for g in gs do
      setGoals [g]
      substTupleEqs
      frameInv ctx hn
    return
  if c == ``Pure.pure then
    let hr ← freshId `hr
    let hs ← freshId `hs
    evalTactic (← `(tactic|
      obtain ⟨$hr, $hs⟩ := EthCLLib.Proofs.run_pure_eq_ok_state $hI))
    substEq hs
    substEq hr
    return ← pvClose
  if c == ``MonadExcept.throw || c == ``MonadExceptOf.throw || c == ``throwThe then
    evalTactic (← `(tactic| cases $hI:ident))
    return
  if c == ``MonadExcept.ofExcept then
    let he ← freshId `he
    let hs ← freshId `hs
    evalTactic (← `(tactic|
      obtain ⟨$he, $hs⟩ := EthCLLib.Proofs.run_ofExcept_eq_ok $hI))
    substEq hs
    return ← pvClose
  if c == ``modifyThe || c == ``EthCLSpecs.Heze.modifyState then
    let hs ← freshId `hs
    evalTactic (← `(tactic| have $hs := EthCLLib.Proofs.run_modifyThe_eq_ok $hI))
    substEq hs
    return ← pvClose
  if setHeads.contains c then
    let hs ← freshId `hs
    evalTactic (← `(tactic| have $hs := EthCLLib.Proofs.run_set_state_eq _ _ _ _ $hI))
    substEq hs
    return ← pvClose
  if loopHeads.contains c then
    let hP ← frameLoopFact ctx hn
    useFacts hP
    return ← pvClose
  frameCallee ctx hn c

/-- A bind `x >>= k` at the head of the program of `hn`. -/
partial def frameBind (ctx : FrameCtx) (hn : Name) (x : Expr) : TacticM Unit :=
    withMainContext do
  let hI := mkIdent hn
  let xc := x.getAppFn.constName?
  -- A read passes the start box to the continuation.
  if xc.any getHeads.contains then
    evalTactic (← `(tactic| replace $hI := EthCLLib.Proofs.run_get_bind_eq_ok _ _ _ $hI))
    return ← frameInv ctx hn
  -- An `assert` passes the start box to the continuation.
  if xc == some ``ite then
    let saved ← saveState
    try
      withConsume hn <| evalTactic (← `(tactic|
        obtain ⟨-, $hI⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ $hI))
      return ← frameInv ctx hn
    catch _ => saved.restore
  -- A read-only action keeps the start box.
  if xc.any readHeads.contains then
    let saved ← saveState
    try
      let a ← freshId `a
      let s1 ← freshId `s
      let h1 ← freshId `h
      let h2 ← freshId `h
      let hs ← freshId `hs
      withConsume hn <| evalTactic (← `(tactic|
        obtain ⟨$a, $s1, $h1, $h2⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ $hI))
      let hsT ← withMainContext do
        let t ← hypType h1.getId
        let some (_, s, _) := runParts? t | throwError "frame_invert: no run"
        mkEq (mkFVar (← hypOf s1.getId)) s
      assertBy hs.getId hsT (readKeeps h1.getId)
      withMainContext do
        evalTactic (← `(tactic| subst $hs:ident))
        evalTactic (← `(tactic| clear $h1:ident))
      return ← frameInv ctx h2.getId
    catch _ => saved.restore
  -- A loop, `set t`, or an action without a `KeepsUncached` fact: the inversion of the first
  -- action names its end state as `pureState` of a value.
  let generic : TacticM Unit := do
    let a ← freshId `a
    let s1 ← freshId `s
    let h1 ← freshId `h
    let h2 ← freshId `h
    withConsume hn <| evalTactic (← `(tactic|
      obtain ⟨$a, $s1, $h1, $h2⟩ := EthCLLib.Proofs.run_bind_eq_ok _ _ _ _ $hI))
    let factWith (view : Bool) : TacticM Expr := withMainContext do
      let sE := mkFVar (← hypOf s1.getId)
      let aE := mkFVar (← hypOf a.getId)
      let sf ← pvFact ctx sE (view := ctx.stateView)
      return (← partsFact ctx (← inferType sE) aE (some sf) (view := view)).get!
    let hf ← freshId `hf
    let saved ← saveState
    try
      assertBy hf.getId (← factWith true) (frameInv ctx h1.getId)
    catch _ =>
      saved.restore
      assertBy hf.getId (← factWith false) (frameInv ctx h1.getId)
    withMainContext do evalTactic (← `(tactic| clear $h1:ident))
    splitTuple a.getId
    withMainContext do
      evalTactic (← `(tactic| try dsimp only at $(mkIdent hf.getId):ident))
    useFacts hf.getId
    frameInv ctx h2.getId
  if xc.any (fun c => loopHeads.contains c || setHeads.contains c) then return ← generic
  -- The general bind: split at a `pureState` midpoint.
  let a ← freshId `a
  let w ← freshId `w
  let h1 ← freshId `h
  let h2 ← freshId `h
  let savedKeeps ← saveState
  try
    withConsume hn <| evalTactic (← `(tactic|
      obtain ⟨$a, $w, $h1, $h2⟩ :=
        EthCLLib.Proofs.run_bind_eq_ok_pure (by frame_keeps) $hI))
  catch _ =>
    savedKeeps.restore
    return ← generic
  -- The view of the midpoint, and the facts of a state value the first action returns.
  let (midFact, fullFact, pureFact) ← withMainContext do
    let wE := mkFVar (← hypOf w.getId)
    let aE := mkFVar (← hypOf a.getId)
    let mid ← mkAppM ``EthCLLib.Proofs.pureState #[wE]
    let midFact ← if ctx.stateView then some <$> pvFact ctx mid else pure none
    let fullFact ← partsFact ctx (← inferType mid) aE midFact
    let pureFact ← partsFact ctx (← inferType mid) aE midFact (view := false)
    pure (midFact, fullFact, pureFact)
  if let some fact := fullFact then
    let hf ← freshId `hf
    let saved ← saveState
    try
      assertBy hf.getId fact (frameInv ctx h1.getId)
    catch ex =>
      -- The returned value may have another view: keep that it is `pureState` of a value,
      -- or else the midpoint fact only.
      saved.restore
      try
        assertBy hf.getId pureFact.get! (frameInv ctx h1.getId)
      catch _ =>
        saved.restore
        let some mf := midFact | throw ex
        assertBy hf.getId mf (frameInv ctx h1.getId)
    useFacts hf.getId
  withMainContext do
    evalTactic (← `(tactic| clear $h1:ident))
  frameInv ctx h2.getId

/-- A call of a spec function `c` at the head of the program of `hn`. A frame lemma of `c`
closes it. Otherwise `c` unfolds. -/
partial def frameCallee (ctx : FrameCtx) (hn : Name) (c : Name) : TacticM Unit :=
    withMainContext do
  let hI := mkIdent hn
  let lemmas ← frameLemmas c
  unless lemmas.isEmpty do
    let saved ← saveState
    try
      -- The end state is `pureState` of a value, by the `KeepsUncached` fact of the call.
      let t ← hypType hn
      let some (prog, _, r) := runParts? t | throwError "frame_invert: no run"
      let progS ← withMainContext do Term.exprToSyntax prog
      if r.appArg!.isFVar then
        let hk ← freshId `hk
        let hk0 ← freshId `hk
        let w ← freshId `w
        let hw ← freshId `hw
        evalTactic (← `(tactic|
          have $hk0 : EthCLLib.Proofs.KeepsUncached $progS := by frame_keeps))
        evalTactic (← `(tactic| have $hk := $hk0 _ _ _ $hI))
        let sS ← withMainContext do Term.exprToSyntax r.appArg!
        evalTactic (← `(tactic|
          generalize $hw:ident : SizzLean.Cache.SSZ.Box.view $sS = $w at $hk:ident))
        evalTactic (← `(tactic| subst $hk:ident))
      -- A returned state value is `pureState` of a value, by the `ReturnsUncached` fact.
      let t ← hypType hn
      let some (_, _, r) := runParts? t | throwError "frame_invert: no run"
      if r.appFn!.appArg!.isFVar then
        if let some l ← uncachedLemma? "returnsUncached_" c then
          let u ← freshId `u
          let hr ← freshId `hr
          let hr0 ← freshId `hr
          evalTactic (← `(tactic|
            have $hr0 : EthCLLib.Proofs.ReturnsUncached $progS := by apply $(mkIdent l)))
          evalTactic (← `(tactic| have $hr := $hr0 _ _ _ $hI))
          let hu ← freshId `hu
          evalTactic (← `(tactic| obtain ⟨⟨$u, $hu⟩, -⟩ := $hr))
          evalTactic (← `(tactic| subst $hu:ident))
      -- Name each state argument that is a write as `pureState q`, so the lemma unifies with
      -- the call. The equation stays, for `pv_close_lemma`.
      let t ← hypType hn
      if let some (prog, s, _) := runParts? t then
        let σ ← withMainContext do inferType s
        for arg in prog.getAppArgs do
          let isState ← withMainContext do
            try withReducible (isDefEq (← inferType arg) σ) catch _ => pure false
          unless isState do continue
          if arg.isAppOf ``EthCLLib.Proofs.pureState || arg.isFVar then continue
          let q ← freshId `q
          let hq ← freshId `hq
          let argS ← withMainContext do Term.exprToSyntax arg
          evalTactic (← `(tactic|
            obtain ⟨$q, $hq⟩ : EthCLLib.Proofs.IsPure $argS := by pv_pure))
          evalTactic (← `(tactic| rw [$hq:ident] at $hI:ident))
      -- Close each fact by a frame lemma of `c`, or by a projection of one. The ascription
      -- names the view, so the parameters of a view such as `partView cur i` unify.
      let Vs ← withMainContext do Term.exprToSyntax ctx.V
      let direct ← lemmas.mapM fun l => `(tactic| (
        have hl : $Vs _ = $Vs _ := $(mkIdent l) $hI
        refine hl.trans ?_
        pv_view))
      -- A lemma that keeps one view value takes the fact of the start as a hypothesis.
      let withStart ← lemmas.mapM fun l => `(tactic|
        exact $(mkIdent l) $hI (by with_reducible assumption))
      let projs ← frameProjs
      let viaProj ← lemmas.flatMapM fun l => projs.mapM fun p => `(tactic| (
        refine Eq.trans ($(mkIdent p) ($(mkIdent l) $hI)) ?_
        pv_view))
      let alts := direct ++ viaProj ++ withStart
      frameCloseWith alts
      return
    catch _ =>
      saved.restore
  -- No frame lemma closes the call: unfold `c`.
  let ci := mkIdent c
  evalTactic (← `(tactic| first | unfold $ci:ident at $hI:ident | delta $ci:ident at $hI:ident))
  frameInv ctx hn

/-- Close a conjunction of facts, each `∃ u, pureState w = pureState u ∧ V (pureState u) = v`,
by the tactic `close` for `V (pureState w) = v`. -/
partial def frameCloseWith (alts : Array (TSyntax `tactic)) : TacticM Unit :=
    withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  if tgt.isConstOf ``True then
    evalTactic (← `(tactic| trivial))
    return
  if tgt.isAppOfArity ``And 2 then
    let gs ← runTac (← `(tactic| refine ⟨?_, ?_⟩))
    for g in gs do
      setGoals [g]
      frameCloseWith alts
    return
  let some (_, view) ← factParts? tgt | throwError "frame_invert: the goal is no fact"
  unless view do
    evalTactic (← `(tactic| exact ⟨_, rfl⟩))
    return
  evalTactic (← `(tactic| refine ⟨_, rfl, ?_⟩))
  for alt in alts do
    let saved ← saveState
    try
      evalTactic alt
      return
    catch _ =>
      saved.restore
  throwError "frame_invert: no frame lemma closes the call"

/-- The invariant fact of the loop at the head of the program of `hn`: the end state and
the state parts of the returned accumulator are `pureState` of values with the view `v`.
The function returns the name of the fact. -/
partial def frameLoopFact (ctx : FrameCtx) (hn : Name) : TacticM Name := do
  let isFuel ← withMainContext do
    let t ← hypType hn
    pure <| (runParts? t).any fun (p, _, _) => p.isAppOf ``EthCLLib.Spec.fuelLoop
  let go (partsView : Bool) : TacticM Name :=
    if isFuel then frameFuelLoopFact ctx hn partsView else frameLoopFactWith ctx hn partsView
  let saved ← saveState
  try go true
  catch _ =>
    saved.restore
    go false

/-- `frameLoopFact`, with the views of the accumulator parts or without them. -/
partial def frameLoopFactWith (ctx : FrameCtx) (hn : Name) (partsView : Bool) :
    TacticM Name := withMainContext do
  let hI := mkIdent hn
  let t ← hypType hn
  let some (prog, s, r) := runParts? t | throwError "frame_invert: no run"
  let c := prog.getAppFn.constName!
  let σ ← inferType s
  let β ← inferType r.appFn!.appArg!
  let P ← loopInv ctx σ β partsView
  let Ps ← Term.exprToSyntax P
  let hP ← freshId `hP
  let lem : Name ← match c with
    | ``ForIn'.forIn' => do
      let coll ← whnfR (prog.getArg! 1)
      pure <| if coll.isAppOf ``List then ``EthCLLib.Proofs.forIn'_run_inv_state
        else ``EthCLLib.Proofs.forIn'_range_run_inv_state
    | ``List.foldlM => pure ``EthCLLib.Proofs.foldlM_run_inv_state
    | ``Array.foldlM => pure ``EthCLLib.Proofs.foldlM_array_run_inv_state
    | _ => do
      let coll ← whnfR (prog.getArg! 1)
      pure <| if coll.isAppOf ``List then ``EthCLLib.Proofs.forIn_run_inv_state
        else if coll.isAppOf ``Std.Legacy.Range then ``EthCLLib.Proofs.forIn_range_run_inv_state
        else if coll.isAppOf ``SizzLean.Repr.SSZList then
          ``EthCLSpecs.Proofs.Heze.forIn_sszList_run_inv_state
        else ``EthCLLib.Proofs.forIn_array_run_inv_state
  let lemI := mkIdent lem
  -- The holes become goals after `h` fixes the loop: the body step, the start, and the
  -- main goal, in that order.
  withConsume hn <| evalTactic (← `(tactic| have $hP := $lemI:ident ($Ps) ?_ ?_ $hI))
  let gs ← getGoals
  unless gs.length == 3 do throwError "frame_invert: the loop lemma left {gs.length} goals"
  -- The main goal holds `hP`. The step goal is a `∀`. The start goal is the rest.
  let mut main? : Option MVarId := none
  let mut step? : Option MVarId := none
  let mut init? : Option MVarId := none
  for g in gs do
    if (← g.withContext do return (← getLCtx).findFromUserName? hP.getId |>.isSome) then
      main? := some g
    else if (← whnfR (← instantiateMVars (← g.getType))).isForall then step? := some g
    else init? := some g
  let (some step, some init, some main) := (step?, init?, main?)
    | throwError "frame_invert: the loop lemma left goals of an unknown shape"
  setGoals [step]
  let hPr ← freshId `hPr
  let hb ← freshId `hb
  evalTactic (← `(tactic| intro _ _ _ _ _ _ $hPr $hb))
  evalTactic (← `(tactic| frame_loop_step $hPr $hb))
  unless (← getGoals).isEmpty do throwError "frame_invert: the loop step remains"
  setGoals [init]
  evalTactic (← `(tactic| frame_loop_init))
  unless (← getGoals).isEmpty do throwError "frame_invert: the loop start remains"
  setGoals [main]
  return hP.getId

/-- `frameLoopFact` for `fuelLoop`: the invariant `P` of the loop value and the state, and the
fact `Q` of the result and the state. -/
partial def frameFuelLoopFact (ctx : FrameCtx) (hn : Name) (partsView : Bool) :
    TacticM Name := withMainContext do
  let hI := mkIdent hn
  let t ← hypType hn
  let some (prog, s, r) := runParts? t | throwError "frame_invert: no run"
  let σ ← inferType s
  let β ← inferType (prog.getArg! 5)
  let α ← inferType r.appFn!.appArg!
  let P ← loopInv ctx σ β partsView
  let Q ← loopInv ctx σ α partsView
  let Ps ← Term.exprToSyntax P
  let Qs ← Term.exprToSyntax Q
  let hP ← freshId `hP
  withConsume hn <| evalTactic (← `(tactic|
    have $hP := EthCLLib.Proofs.fuelLoop_run_inv_state ($Ps) ($Qs) ?_ ?_ ?_ ?_ $hI))
  let gs ← getGoals
  let mut main? : Option MVarId := none
  let mut rest : Array MVarId := #[]
  for g in gs do
    if (← g.withContext do return (← getLCtx).findFromUserName? hP.getId |>.isSome) then
      main? := some g
    else rest := rest.push g
  let some main := main? | throwError "frame_invert: no main goal after the fuel loop lemma"
  unless rest.size == 4 do throwError "frame_invert: the fuel loop lemma left {rest.size} goals"
  -- `hnext` and `hdone`: invert a step from the invariant.
  for g in rest[0:2] do
    setGoals [g]
    let hPr ← freshId `hPr
    let hb ← freshId `hb
    evalTactic (← `(tactic| intro _ _ _ _ $hPr $hb))
    evalTactic (← `(tactic| frame_loop_step $hPr $hb))
    unless (← getGoals).isEmpty do throwError "frame_invert: a fuel loop step remains"
  -- `hexhausted`: the state part stays the same, and the fuel-out value is plain data.
  setGoals [rest[2]!]
  let hPr ← freshId `hPr
  evalTactic (← `(tactic| intro _ _ $hPr))
  evalTactic (← `(tactic| frame_beta at $hPr:ident))
  useFacts hPr.getId
  evalTactic (← `(tactic| frame_beta))
  pvClose
  unless (← getGoals).isEmpty do throwError "frame_invert: the fuel-out case remains"
  setGoals [rest[3]!]
  evalTactic (← `(tactic| frame_loop_init))
  unless (← getGoals).isEmpty do throwError "frame_invert: the fuel loop start remains"
  setGoals [main]
  return hP.getId

end

/-- The data of an inversion from a goal: a fact `∃ u, x = pureState u ∧ V (pureState u) = v`,
or a conjunction of facts. The first conjunct is the fact of the threaded state. -/
partial def ctxOf (tgt : Expr) : MetaM (Option FrameCtx) := do
  let tgt ← whnfR (← instantiateMVars tgt)
  if tgt.isAppOfArity ``And 2 then
    if let some c ← ctxOf (tgt.getArg! 0) then return some c
    return ← ctxOf (tgt.getArg! 1)
  unless tgt.isAppOfArity ``Exists 2 do return none
  lambdaTelescope (tgt.getArg! 1) fun _ b => do
    let b ← whnfR b
    unless b.isAppOfArity ``And 2 do return none
    let some (_, l, v) := (b.getArg! 1).eq? | return none
    return some { V := l.appFn!, v, stateView := true }

/-- Whether the first fact of a goal claims a view. -/
partial def firstFactViews (tgt : Expr) : MetaM Bool := do
  let tgt ← whnfR (← instantiateMVars tgt)
  if tgt.isAppOfArity ``And 2 then return ← firstFactViews (tgt.getArg! 0)
  let some (_, view) ← factParts? tgt | return false
  return view

elab_rules : tactic
  | `(tactic| frame_loop_step $hPr $hb) => withoutRecover <| withMainContext do
    let tgt ← getMainTarget
    let some ctx ← ctxOf tgt | throwError "frame_loop_step: the goal claims no view"
    let ctx := { ctx with stateView := ← firstFactViews tgt }
    -- Name the parts of the accumulator, so that the body reads variables.
    let hbT ← instantiateMVars (← (← hypOf hb.getId).getType)
    for fv in (collectFVars {} hbT).fvarIds do
      let ty ← whnfR (← instantiateMVars (← fv.getType))
      if ty.isAppOf ``MProd || ty.isAppOf ``Prod then
        splitTuple (← fv.getUserName)
    withMainContext do
      evalTactic (← `(tactic| frame_beta at $hPr:ident))
      evalTactic (← `(tactic| try dsimp only at $hPr:ident))
    useFacts hPr.getId
    withMainContext do
      evalTactic (← `(tactic| try simp only [EthCLLib.Proofs.forInStep_value_yield,
        EthCLLib.Proofs.forInStep_value_done]))
      evalTactic (← `(tactic| frame_beta))
    frameInv ctx hb.getId

elab_rules : tactic
  | `(tactic| frame_loop_init) => withoutRecover do
    evalTactic (← `(tactic| frame_beta))
    pvClose

/-- Prove a frame fact `V (pureState t') = V (pureState t)` from a run hypothesis
`h : prog.run (pureState t) = .ok (a, pureState t')`, or the fact
`V (pureState b) = V (pureState u)` of a state value `pureState b` that the run returns. The
module docstring describes the inversion. -/
syntax "frame_invert " ident : tactic

elab_rules : tactic
  | `(tactic| frame_invert $h) => withoutRecover <| withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let some (_, l, rv) := tgt.eq? | throwError "frame_invert: the goal is no equation"
    let t ← instantiateMVars (← (← hypOf h.getId).getType)
    let some (prog, s, r) := runParts? t | throwError "frame_invert: {h} is no run hypothesis"
    -- A goal with holes, from a term `f (by frame_invert h)`: the run fixes the end state
    -- and the start state.
    if tgt.hasMVar then
      discard <| isDefEq l.appArg! r.appArg!
      discard <| isDefEq rv.appArg! s
    let tgt ← instantiateMVars tgt
    let some (_, l, rv) := tgt.eq? | throwError "frame_invert: the goal is no equation"
    let V := l.appFn!
    let x := l.appArg!
    -- The goal is a frame fact when its state is the end state of the run.
    let stateView := r.appArg! == x
    let Vs ← Term.exprToSyntax V
    let xs ← Term.exprToSyntax x
    let vs ← Term.exprToSyntax rv
    let hv ← freshId `hv
    -- The goal as a fact, and the view of the start as a hypothesis.
    evalTactic (← `(tactic| (
      have $hv : $vs = $vs := rfl
      suffices hfact : ∃ u, $xs = EthCLLib.Proofs.pureState u ∧
          $Vs (EthCLLib.Proofs.pureState u) = $vs by
        obtain ⟨_, hx, hfv⟩ := hfact
        rw [hx]
        exact hfv)))
    -- Unfold the function at the head of the program once.
    if let some c := prog.getAppFn.constName? then
      if (`EthCLSpecs.Heze).isPrefixOf c || (`EthCLSpecs.Proofs.Heze).isPrefixOf c then
        let ci := mkIdent c
        evalTactic (← `(tactic|
          first | unfold $ci:ident at $h:ident | delta $ci:ident at $h:ident))
    frameInv { V, v := rv, stateView } h.getId

/-! ## The weigh step

The weigh step reads the state, forms its checked products and sums, reads up to two block
roots, and writes once, at the end. The run inversion of `frame_invert` inlines the two join
points of the root reads into both branches of each `if`, and the term grows too large. So
the weigh step takes the rules of `KeepsAt` (`EthCLLib/Proofs/Frame.lean`) instead, with
each join point named by `extract_lets` and proved once.

`KeepsAt` quantifies over every start state, the cached boxes too. The write at the end is a
record update only on an uncached box. So the rules carry the view together with a flag
that says that the box is uncached (`boxUncached`). The write then needs the view fact on
an uncached box only (`keepsAt_modifyThe_uncached`). -/

/-- Whether a box is uncached. -/
def boxUncached {H T : Type} [SizzLean.Hasher H] [SizzLean.SSZRepr T] :
    SizzLean.Cache.SSZ.Box H T → Bool
  | .uncached _ => true
  | .cached _ => false

/-- A write keeps the view `V` and the uncached flag when, on each uncached box, it returns
an uncached box with the view of its argument. -/
theorem keepsAt_modifyThe_uncached {H T ε β : Type} [SizzLean.Hasher H] [SizzLean.SSZRepr T]
    {V : SizzLean.Cache.SSZ.Box H T → β} {v : β}
    (g : SizzLean.Cache.SSZ.Box H T → SizzLean.Cache.SSZ.Box H T)
    (hg : ∀ u, boxUncached (g (.uncached u)) = true ∧ V (g (.uncached u)) = V (.uncached u)) :
    EthCLLib.Proofs.KeepsAt (fun s => (V s, boxUncached s)) (v, true)
      (modifyThe _ g : StateT (SizzLean.Cache.SSZ.Box H T) (Except ε) PUnit) := by
  intro s a s' hs hrun
  injection hrun with hrun
  injection hrun with _ hrun
  subst hrun
  cases s with
  | cached _ => simp [boxUncached] at hs
  | uncached u =>
    obtain ⟨hu, hv⟩ := hg u
    simp only [Prod.mk.injEq] at hs ⊢
    exact ⟨hv.trans hs.1, hu⟩

/-- An `if` keeps a field when both branches keep it. -/
theorem keepsAt_ite {σ ε α β : Type} {f : σ → β} {v : β} {c : Prop} [Decidable c]
    {x y : StateT σ (Except ε) α} (hx : EthCLLib.Proofs.KeepsAt f v x)
    (hy : EthCLLib.Proofs.KeepsAt f v y) : EthCLLib.Proofs.KeepsAt f v (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-- The root read of the weigh step: an `if` that reads a root or takes the default, then
the join point `k`. -/
theorem keepsAt_ite_bind {σ ε α γ β : Type} {f : σ → β} {v : β} {c : Prop} [Decidable c]
    {x : StateT σ (Except ε) α} {d : α} {k : α → StateT σ (Except ε) γ}
    (hx : EthCLLib.Proofs.KeepsAt f v x) (hk : ∀ r, EthCLLib.Proofs.KeepsAt f v (k r)) :
    EthCLLib.Proofs.KeepsAt f v (if c then x >>= k else pure d >>= k) :=
  keepsAt_ite (EthCLLib.Proofs.KeepsAt.bind hx hk)
    (EthCLLib.Proofs.KeepsAt.bind (EthCLLib.Proofs.KeepsAt.pure d) hk)

/-- The frame fact of a run from a `KeepsAt` fact of the view and the uncached flag. -/
theorem frame_of_keepsAt [EthCLSpecs.Heze.Preset] [EthCLLib.Spec.HasherTag] {β α : Type}
    {V : EthCLSpecs.Heze.State → β} {t t' : EthCLSpecs.Heze.BeaconState} {x : HezeRun α} {a : α}
    (hk : EthCLLib.Proofs.KeepsAt (fun s => (V s, boxUncached s))
      (V (EthCLLib.Proofs.pureState t), true) x)
    (h : x.run (EthCLLib.Proofs.pureState t) = .ok (a, EthCLLib.Proofs.pureState t')) :
    V (EthCLLib.Proofs.pureState t') = V (EthCLLib.Proofs.pureState t) :=
  congrArg Prod.fst (hk _ _ _ rfl h)

/-- One step of a `KeepsAt` proof over the weigh step. The write at the end splits on the
six conditions of its pure update, and each branch keeps the view by `rfl`. -/
syntax "weigh_keeps_step" : tactic
macro_rules
  | `(tactic| weigh_keeps_step) => `(tactic| first
      | with_reducible_and_instances
          refine EthCLLib.Proofs.KeepsAt.get_bind fun _ _ => ?_
      | with_reducible_and_instances exact EthCLLib.Proofs.KeepsAt.pure _
      | with_reducible_and_instances exact EthCLLib.Proofs.KeepsAt.throw _
      | with_reducible_and_instances exact EthCLLib.Proofs.KeepsAt.ofExcept _
      | (with_reducible_and_instances
           refine EthCLSpecs.Proofs.Heze.keepsAt_modifyThe_uncached _ fun _ => ?_
         simp only [Id.run]
         repeat' split
         all_goals exact ⟨rfl, rfl⟩)
      | with_reducible_and_instances refine EthCLLib.Proofs.KeepsAt.bind ?_ fun _ => ?_
      | refine EthCLSpecs.Proofs.Heze.keepsAt_ite ?_ ?_
      | split
      | simp only [EthCLLib.Spec.checkedAdd]
      | simp only [EthCLLib.Spec.checkedMul]
      | simp only [EthCLLib.Spec.throwArithmetic]
      | simp only [EthCLLib.Spec.liftErr]
      | simp only [EthCLSpecs.Heze.modifyState]
      | unfold EthCLSpecs.Heze.getBlockRoot
      | unfold EthCLSpecs.Heze.getBlockRootAtSlot
      | (dsimp only; fail_if_success done))

/-- Prove `KeepsAt (fun s => (V s, boxUncached s)) (v, true)` for the run of
`weighJustificationAndFinalization`. The first `extract_lets` names the four reads of the
state. Each later one names the `if` of a justification and the join point after its root
read. -/
syntax "weigh_keeps" : tactic
macro_rules
  | `(tactic| weigh_keeps) => `(tactic| (
      unfold EthCLSpecs.Heze.weighJustificationAndFinalization
      refine EthCLLib.Proofs.KeepsAt.get_bind fun _ _ => ?_
      extract_lets _ _ _ _
      refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
      refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
      extract_lets _ _ jp
      refine EthCLSpecs.Proofs.Heze.keepsAt_ite_bind (by repeat' weigh_keeps_step) fun _ => ?_
      simp -zeta only [jp]
      refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
      refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
      extract_lets _ _ jp2
      refine EthCLSpecs.Proofs.Heze.keepsAt_ite_bind (by repeat' weigh_keeps_step) fun _ => ?_
      simp -zeta only [jp2]
      repeat' weigh_keeps_step))

/-- The state value with the four fields that the weigh step writes set to their defaults:
the justification bits and the three checkpoints. -/
def weighRestView [EthCLSpecs.Heze.Preset] [EthCLLib.Spec.HasherTag]
    (st : EthCLSpecs.Heze.State) : EthCLSpecs.Heze.BeaconState :=
  let v := st.view
  { v with
    justificationBits := default
    previousJustifiedCheckpoint := default
    currentJustifiedCheckpoint := default
    finalizedCheckpoint := default }

section
variable [EthCLSpecs.Heze.Preset] [EthCLLib.Spec.HasherTag]

-- The walk of `weigh_keeps` checks each of the 64 branches of the pure update by `rfl`.
set_option maxHeartbeats 1000000 in
/-- The weigh step keeps every field but the four that it writes. -/
theorem weigh_frame_rest {t t' : EthCLSpecs.Heze.BeaconState} {a : PUnit}
    {totalActive prevTarget currTarget : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.weighJustificationAndFinalization (StateTransition := HezeRun)
      totalActive prevTarget currTarget).run (EthCLLib.Proofs.pureState t)
        = .ok (a, EthCLLib.Proofs.pureState t')) :
    weighRestView (EthCLLib.Proofs.pureState t') = weighRestView (EthCLLib.Proofs.pureState t) := by
  refine frame_of_keepsAt (V := weighRestView) ?_ h
  weigh_keeps

set_option maxHeartbeats 1000000 in
/-- `processJustificationAndFinalization` keeps every field but the four that the weigh step
writes. The genesis guard keeps the state. Otherwise five `Except` reads run, then the weigh
step. -/
theorem jf_frame_rest {t t' : EthCLSpecs.Heze.BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processJustificationAndFinalization (StateTransition := HezeRun)).run
      (EthCLLib.Proofs.pureState t) = .ok (a, EthCLLib.Proofs.pureState t')) :
    weighRestView (EthCLLib.Proofs.pureState t') = weighRestView (EthCLLib.Proofs.pureState t) := by
  refine frame_of_keepsAt (V := weighRestView) ?_ h
  unfold EthCLSpecs.Heze.processJustificationAndFinalization
  refine EthCLLib.Proofs.KeepsAt.get_bind fun _ _ => ?_
  refine keepsAt_ite (EthCLLib.Proofs.KeepsAt.pure _) ?_
  refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
  refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
  refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
  refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
  refine EthCLLib.Proofs.KeepsAt.bind (by repeat' weigh_keeps_step) fun _ => ?_
  weigh_keeps

end

/-- Prove `V (pureState t') = V (pureState t)` from a run `h` of
`weighJustificationAndFinalization` from `pureState t` to `pureState t'`, for a view `V` that
reads none of the four fields that the weigh step writes. `weigh_frame_rest` gives the fact
for `weighRestView`. Such a view `V` of a state value equals `V` of its `weighRestView` by
definition, so `congrArg` carries the fact to `V`. -/
syntax "weigh_frame " term:max ident : tactic
macro_rules
  | `(tactic| weigh_frame $V $h) => `(tactic| (
      have hr := congrArg (fun r => $V (EthCLLib.Proofs.pureState r))
        (EthCLSpecs.Proofs.Heze.weigh_frame_rest $h)
      exact hr))

/-- `weigh_frame` for `processJustificationAndFinalization`, through `jf_frame_rest`. -/
syntax "jf_frame " term:max ident : tactic
macro_rules
  | `(tactic| jf_frame $V $h) => `(tactic| (
      have hr := congrArg (fun r => $V (EthCLLib.Proofs.pureState r))
        (EthCLSpecs.Proofs.Heze.jf_frame_rest $h)
      exact hr))

end EthCLSpecs.Proofs.Heze
