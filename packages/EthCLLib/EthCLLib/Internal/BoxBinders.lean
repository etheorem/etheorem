import Lean
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.Internal.BoxBinders`: the plain-value binder check

The pure-state-theorems plan (§2, rule 1) keeps fork-body theorems over plain
SSZ values: a statement binds `v : BeaconState`, never a boxed `State`. This
module is the walk behind the check that enforces the rule. The proof-coverage
report (`scripts/ProofCoverage.lean`) runs it over every fork-body theorem, and
the fixture pins (`EthCLSpecs.Tests.BoxBinderPins`) run it over four statements
of known answers, so the walk cannot rot to "always pass" unnoticed.

A statement enters the scope of the check when it names a constant under a
registered fork's namespace (`EthCLSpecs.Fulu.*`, `EthCLSpecs.Gloas.*`,
`EthCLSpecs.Heze.*`). Within scope, the walk reports every *quantifier* whose
bound type is the boxed state:

* a `forallE` whose body is a proposition, which is a theorem's own telescope
  binder, a hypothesis, or an arrow's domain in the logical part;
* the witness binder of an `Exists`, which the elaborator keeps inside a lambda
  passed to `Exists`.

The walk does not look at lambdas inside program terms: a `do` block, an
`appendState` expansion, or a `fun` passed to `forIn` binds a variable in
program text, and none of them claims something about every box. It also does
not look at the domain of a function-typed parameter, such as
`g : Box → StateT …`: a function over boxes is a program, not a quantified
claim. The two positions are separated by the same test: recurse into a
binder's type only when that type is itself a proposition (a hypothesis), and
never into a lambda's body.

The generic lemmas in `EthCLSpecs.Proofs.Run` and
`EthCLSpecs.Proofs.KeepsUncached` quantify over boxes by design. They name no
fork constant, so the scope test leaves them alone, and none needs the
`box_generic` marker today. A box-level lemma that later names a fork constant
enters the scope and carries the marker.

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
* `Expr.isProp`-style questions are answered syntactically by `isPropShaped`:
  follow the spine of the expression to its head constant, strip that
  constant's type down to its result sort, and check for `Prop`. The walk never
  infers a type, so loose bvars stay safe.
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
the undecided cases out. Loose bvars are safe, since no type is inferred. -/
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
      | .sort l => l == Level.zero
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

/-- The boxed-state quantifiers of a theorem statement, in walk order.

`e` is the statement of a proposition. The walk reports `(binderName,
binderType)` at exactly the two quantifier positions of the module docstring,
and descends into a hypothesis's type only when that type is itself a
proposition. Lambdas inside program terms stay closed. -/
def boxQuantifiers (env : Environment) (e : Expr) : Array (Name × Expr) :=
  boxQuantifiersAux env 400 e #[]
where
  boxQuantifiersAux (env : Environment) : Nat → Expr →
      Array (Name × Expr) → Array (Name × Expr)
    | 0, _, acc => acc
    | fuel+1, e, acc =>
      match e.consumeMData with
      | .forallE n t b _ =>
        let acc :=
          if isPropShaped env b && isBoxType env t then acc.push (n, t) else acc
        let acc := boxQuantifiersAux env fuel b acc
        if isPropShaped env t then boxQuantifiersAux env fuel t acc else acc
      | .app _ _ =>
        let e := e.consumeMData.headBeta
        if e.getAppFn.isConstOf ``Exists then
          match e.getAppArgs.back? with
          | some pred =>
            match pred.consumeMData with
            | .lam n t b _ =>
              let acc := if isBoxType env t then acc.push (n, t) else acc
              boxQuantifiersAux env fuel b acc
            | _ => acc
          | none => acc
        else
          -- A logical connective's arguments are propositions or program
          -- values; both are walked, and the lambda case closes program text.
          let acc := boxQuantifiersAux env fuel e.getAppFn acc
          e.getAppArgs.foldl (init := acc) fun acc a =>
            boxQuantifiersAux env fuel a acc
      | .lam _ _ _ _ => acc
      | .letE _ _ v b _ => boxQuantifiersAux env fuel b (boxQuantifiersAux env fuel v acc)
      | .mdata _ b => boxQuantifiersAux env fuel b acc
      | .proj _ _ b => boxQuantifiersAux env fuel b acc
      | _ => acc

/-- The namespaces that put a theorem in the plain-value check's scope: every
registered fork body. -/
def boxCheckScopes (env : Environment) : Array Name :=
  registeredForks env

/-- Does the statement name a constant under one of the scope namespaces? -/
def namesFork (scopes : Array Name) (t : Expr) : Bool :=
  t.getUsedConstants.any fun c => scopes.any (·.isPrefixOf c)

end EthCLLib.Internal
