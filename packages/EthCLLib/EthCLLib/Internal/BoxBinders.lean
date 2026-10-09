import Lean
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.Internal.BoxBinders`: the plain-value binder check

`SPECS_ARCHITECTURE.md` §11.1 keeps fork-body theorems over plain SSZ values:
a statement binds `v : BeaconState`, never a boxed `State`. This module is the
walk behind the check that enforces the rule. The proof-coverage report
(`scripts/ProofCoverage.lean`) runs it over every fork-body theorem, and the
fixture pins (`EthCLSpecs.Tests.BoxBinderPins`) run it over thirteen statements
of known answers, so the walk cannot rot to "always pass" unnoticed.

A statement enters the scope of the check when it names a constant under a
registered fork's namespace (`boxCheckScopes` below). Within scope, the walk
reports every *quantifier* whose bound type is the boxed state:

* a `forallE` in proposition position, which is a theorem's own telescope
  binder, a hypothesis, or an arrow's domain in the logical part;
* the witness binder of an `Exists`, which the elaborator keeps inside a lambda
  passed to `Exists`.

The walk does not look at lambdas inside program terms: a `do` block, an
`appendState` expansion, or a `fun` passed to `forIn` binds a variable in
program text, and none of them claims something about every box. It also does
not look at the domain of a function-typed parameter, such as
`g : Box → StateT …` or a predicate `P : State → Prop`: a function over boxes
is a program, not a quantified claim.

Proposition position is tracked structurally, never inferred at each node. A
theorem's type is a proposition, so the walk starts there with the flag set.
In proposition position every `forallE` is a quantifier, and its body stays in
proposition position. The walk enters a binder's domain only when that domain
is itself a proposition, and `isPropShaped` answers exactly that one question.
A sort is never a proposition, so `Prop` itself answers `false`, and the
domain of a predicate parameter is never entered. The `Exists` body is in
proposition position by construction.

## Lean idioms annotated on first appearance

* `headBeta`, never `whnf`: the walk reads binder types that hold loose bound
  variables (an earlier telescope binder's variable inside a later type), and
  `whnf` panics on loose bvars. `headBeta` is syntactic, so it is safe there.
  Reducible heads (`State` is an `abbrev`) unfold through `env.find?` by hand.
* `getReducibilityStatusCore`: the environment's own record of a constant's
  reducibility attribute. `abbrev` sets `.reducible`, so the check sees through
  every fork's `State`.
* Structural recursion on a `Nat` fuel instead of `partial def`: the walk
  spends one unit of fuel per node it opens, so termination needs no
  well-founded measure, and a fuel of zero answers `false` / no findings
  instead of diverging on a pathological term.
* `isPropShaped` answers syntactically: follow the spine of the expression to
  its head constant, strip that constant's type down to its result sort, and
  check for `Prop`. The walk never infers a type, so loose bvars stay safe.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.Internal

/-- The head that ends the walk with a finding: the boxed state, in either
flavour. -/
def boxHeadName : Name := `SizzLean.Cache.SSZ.Box

/-- Is the head of `t` the boxed state, after unfolding reducible constants?

`t` may hold loose bound variables, so nothing here whnfs. The walk follows
`headBeta` and applications; a reducible definition head unfolds to its body
with the arguments spliced in, which is how the fork `State` abbrev meets
`boxHeadName`. -/
def isBoxType (env : Environment) (t : Expr) : Bool :=
  isBoxTypeAux env 20 t
where
  isBoxTypeAux (env : Environment) : Nat → Expr → Bool
    | 0, _ => false
    | fuel+1, t =>
      let t := t.consumeMData.headBeta
      match t.getAppFn with
      | .const c ls =>
        if c == boxHeadName then true
        else match env.find? c with
          | some (.defnInfo d) =>
            if getReducibilityStatusCore env c == .reducible then
              isBoxTypeAux env fuel
                ((d.value.instantiateLevelParams d.levelParams ls).beta t.getAppArgs)
            else false
          | _ => false
      | _ => false

/-- Might `t` be a proposition?

A conservative syntactic answer: `true` when the expression's spine lands on a
head whose type ends in the `Prop` sort, `false` when the walk cannot see
through it. A `false` costs at most one missed nested quantifier under an
exotic hypothesis; a wrong `true` would be a false finding, so the walk keeps
the undecided cases out. Loose bvars are safe, since no type is inferred.
A sort is never a proposition, so `Prop` itself answers `false`, which is what
keeps the domain of a `P : State → Prop` parameter out of the walk. -/
def isPropShaped (env : Environment) (t : Expr) : Bool :=
  isPropShapedAux env 20 t
where
  /-- The result sort of a constant's type: strip the domains, then read the
  codomain. `some true` is `Prop`, `some false` is another sort, `none` is a
  codomain the walk does not recognize as a sort. -/
  resultSort : Nat → Expr → Option Bool
    | 0, _ => none
    | fuel+1, t =>
      match t.consumeMData with
      | .forallE _ _ b _ => resultSort fuel b
      | .sort l          => some (l == Level.zero)
      | _                => none

  isPropShapedAux (env : Environment) : Nat → Expr → Bool
    | 0, _ => false
    | fuel+1, t =>
      match t.consumeMData with
      | .forallE _ _ b _ => isPropShapedAux env fuel b
      | .const c _ =>
        match env.find? c with
        | some info => resultSort fuel info.type == some true
        | none      => false
      | .app _ _ =>
        let t := t.consumeMData.headBeta
        match t.getAppFn.consumeMData with
        | .const c _ =>
          match env.find? c with
          | some info => resultSort fuel info.type == some true
          | none      => false
        | _ => false
      | .letE _ _ _ b _ => isPropShapedAux env fuel b
      | _ => false

/-- The logical connectives whose arguments are propositions. The walk descends
into the arguments of one of these in proposition position; every other
application head walks its arguments as program values, so a function type
passed as an explicit type argument is never read as a quantifier. Implication
needs no entry here: `p → q` is a `forallE`, and the `forallE` case already
carries proposition position through its body. -/
def propConnectives : Array Name := #[`And, `Or, `Iff, `Not]

/-- The boxed-state quantifiers of a theorem statement, in walk order.

`e` is the statement of a theorem, so the walk starts in proposition position
and tracks the position structurally from there: a `forallE` body stays in
proposition position, an `Exists` body is one by construction, and a
hypothesis is entered only when `isPropShaped` confirmed it as a proposition.
The arguments of a logical connective (`propConnectives`) stay in proposition
position; the arguments of any other application are program values, even in
proposition position. Lambdas inside program terms stay closed. -/
def boxQuantifiers (env : Environment) (e : Expr) : Array (Name × Expr) :=
  boxQuantifiersAux env 400 e true #[]
where
  boxQuantifiersAux (env : Environment) : Nat → Expr → Bool →
      Array (Name × Expr) → Array (Name × Expr)
    | 0, _, _, acc => acc
    | fuel+1, e, inProp, acc =>
      match e.consumeMData with
      | .forallE n t b _ =>
        let acc :=
          if inProp && isBoxType env t then acc.push (n, t) else acc
        let acc := boxQuantifiersAux env fuel b true acc
        if isPropShaped env t then boxQuantifiersAux env fuel t true acc else acc
      | .app _ _ =>
        let e := e.consumeMData.headBeta
        if e.getAppFn.isConstOf ``Exists then
          match e.getAppArgs.back? with
          | some pred =>
            match pred.consumeMData with
            | .lam n t b _ =>
              let acc := if isBoxType env t then acc.push (n, t) else acc
              boxQuantifiersAux env fuel b true acc
            | _ => acc
          | none => acc
        else
          -- Arguments of a logical connective are propositions; arguments of
          -- anything else are program values, even in proposition position.
          -- Both are walked, and the lambda case closes program text.
          let inArg := inProp && propConnectives.any (e.getAppFn.isConstOf ·)
          let acc := boxQuantifiersAux env fuel e.getAppFn inArg acc
          e.getAppArgs.foldl (init := acc) fun acc a =>
            boxQuantifiersAux env fuel a inArg acc
      | .lam _ _ _ _ => acc
      | .letE _ _ v b _ =>
        boxQuantifiersAux env fuel b inProp (boxQuantifiersAux env fuel v inProp acc)
      | .mdata _ b => boxQuantifiersAux env fuel b inProp acc
      | .proj _ _ b => boxQuantifiersAux env fuel b inProp acc
      | _ => acc

/-- The namespaces that put a theorem in the plain-value check's scope: every
registered fork's namespace. -/
def boxCheckScopes (env : Environment) : Array Name :=
  registeredForks env

/-- Does the statement name a constant under one of the scope namespaces? -/
def namesFork (scopes : Array Name) (t : Expr) : Bool :=
  t.getUsedConstants.any fun c => scopes.any (·.isPrefixOf c)

/-- The plain-value check for one theorem, as the problem line it draws.

`thm` is the theorem's stored name, which is what a marker is recorded under,
and `type` is its statement. The marker is decided first: a `@[box_generic]`
theorem passes only in scope and with a boxed-state quantifier to point at, so
a marked theorem that names no fork constant, or binds no box, fails as stale.
An unmarked theorem draws a finding when it is in scope and quantifies over
the box. Everything else passes. -/
def boxBinderProblem? (env : Environment) (scopes : Array Name) (marked : NameSet)
    (thm : Name) (type : Expr) : Option String :=
  let hits := boxQuantifiers env type
  let inScope := namesFork scopes type
  let shown := (privateToUserName? thm).getD thm
  if marked.contains thm then
    if !inScope then
      some s!"{shown} carries `@[box_generic]` but names no fork constant, so \
        the plain-value check never applies to it and the marker is stale. \
        Drop it. See CONTRIBUTING.md, *Adding a proof*."
    else if hits.isEmpty then
      some s!"{shown} carries `@[box_generic]` but binds no boxed state, so the \
        marker is stale. Drop it. See CONTRIBUTING.md, *Adding a proof*."
    else none
  else if inScope && !hits.isEmpty then
    let (binder, binderType) := hits[0]!
    some s!"{shown} binds {binder} : {toString binderType}, a boxed state. A \
      fork-body theorem quantifies over plain values. See CONTRIBUTING.md, \
      *Adding a proof*. To claim the box on purpose, tag the theorem \
      `@[box_generic \"reason\"]`."
  else none

end EthCLLib.Internal
