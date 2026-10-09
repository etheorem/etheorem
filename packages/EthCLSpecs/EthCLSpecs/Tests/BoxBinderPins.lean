import EthCLLib.Internal.BoxBinders
import EthCLLib.Internal.ProofLedger
import EthCLLib.Spec
import EthCLSpecs.Gloas.State
import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Tests.BoxBinderPins`: the plain-value check pins

`SPECS_ARCHITECTURE.md` §11.1 keeps fork-body theorems over plain values, and
`scripts/ProofCoverage.lean` enforces the rule with the walk in
`EthCLLib.Internal.BoxBinders`. The fixture theorems here hold that walk
to statements of known answers, so a check that rots to "always pass" fails
this module instead of passing quietly:

* `bindsState` quantifies over the boxed `State` and draws one finding.
* `bindsPlain` binds `BeaconState` and passes.
* `lambdaInProgram` states a spec write inline in the `modifyState` shape, whose
  lambda over the state is program text, and passes.
* `nestedForall` hides a `∀ s : State` inside a hypothesis and draws one
  finding.
* `predicateParam` takes a predicate over `State` as a parameter; the walk
  never enters its domain, so it passes.
* `predicateBody` takes a predicate parameter and quantifies over `State` with
  a bound variable at the body's head; proposition position carries the walk
  through, so `s` draws one finding.

Each fixture names a fork constant, so each is in scope: a failing fixture that
is out of scope would pass for the wrong reason. Four more fixtures pin the
remaining edges. A `Store` binder holds a `State` inside a field type, and the
head is `Store`, so it passes. A function-typed parameter over `State` is a
domain, not a quantified claim, so it passes. `markedBindsBox` is marked and
binds the box, so it is accepted, and `markedBindsNone` fails as stale.
`outOfScopeMarker` is marked but names no fork constant, so the check never
applies to it and the marker is stale.

The gate at the bottom runs the walk and the verdict on all eleven fixtures
and throws on any mismatched answer, so `lake build EthCLSpecsTests` is the
gate. `run_cmd` runs at elaboration time, prints nothing, and a `throwError`
in it fails the build.

They sit in `EthCLSpecsTests` for the reason the other pin modules do: the
lakefile declares that library for build gates, and a gate compiled into
`EthCLSpecs` is weight every consumer of the fork body carries.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.BoxBinderPins

open EthCLLib.Spec (MapKind FcMap HasherTag)
open EthCLLib.Internal (boxQuantifiers boxCheckScopes namesFork boxGenerics)
open EthCLSpecs.Gloas (Preset State BeaconState modifyState)
open EthCLSpecs.Heze (Store)
open EthCLSpecs.Proofs.Gloas (GloasRun)

/-- In scope, and binds the boxed `State`: one finding. -/
theorem bindsState [Preset] [HasherTag] :
    ∀ (state : State), True := fun _ => trivial

/-- In scope, and binds the plain value: no finding. -/
theorem bindsPlain [Preset] [HasherTag] :
    ∀ (v : BeaconState), True := fun _ => trivial

/-- In scope. The statement carries the spec's own write, the `modifyState`
lambda over the state with an `sszUpdate` expansion inside. The monad is pinned
by ascription, because `state_preamble` emits `modifyState` with hygiene-mangled
binder names, so a named argument cannot reach the monad parameter. The lambda
is program text inside an equation, so the walk reports nothing. -/
theorem lambdaInProgram [Preset] [HasherTag] :
    ∀ (v : BeaconState),
      ((modifyState fun state =>
          sszUpdate state with builderPendingPayments :=
            sszGet state builderPendingPayments) : GloasRun PUnit)
        = ((modifyState fun state =>
          sszUpdate state with builderPendingPayments :=
            sszGet state builderPendingPayments) : GloasRun PUnit) → True :=
  fun _ _ => trivial

/-- In scope. The boxed `State` quantifier sits inside a hypothesis, one
`forallE` below the theorem's own binder: still one finding. -/
theorem nestedForall [Preset] [HasherTag] :
    ∀ (v : BeaconState), (∀ (s : State), True) → True := fun _ _ => trivial

/-- In scope. A `Store` binder holds a `State` inside a field type; the walk
reads the head only, and the head is `Store`. No finding. -/
theorem storeBinder {map : MapKind} [EthCLSpecs.Heze.Preset] [HasherTag] [FcMap map] :
    ∀ (store : Store map), True := fun _ => trivial

/-- In scope. A function over boxes is a program, not a quantified claim: the
parameter's type head is an arrow, and the walk never enters it. No finding. -/
theorem functionBinder [Preset] [HasherTag] :
    ∀ (f : State → State), True := fun _ => trivial

/-- In scope. A predicate over the state is a parameter, not a quantified
claim: the walk enters no function domain, whatever its result sort. No
finding. -/
theorem predicateParam [Preset] [HasherTag] :
    ∀ (P : State → Prop), True := fun _ => trivial

/-- In scope. The body of the `s` quantifier has a bound variable at its head,
so no inference can see a proposition there. Proposition position is tracked
structurally, so `s` still draws one finding. -/
theorem predicateBody [Preset] [HasherTag] :
    ∀ (P : State → Prop) (s : State), P s → True := fun _ _ _ => trivial

/-- The marker on a theorem that binds the box: the check accepts it. -/
@[box_generic "a box-level flavour fact; the seed of a cached ≡ pure equivalence"]
theorem markedBindsBox [Preset] [HasherTag] :
    ∀ (state : State), True := fun _ => trivial

/-- The marker on a theorem that binds no box: the check fails it as stale. -/
@[box_generic "stale on purpose: this fixture must draw the stale-marker finding"]
theorem markedBindsNone [Preset] [HasherTag] :
    ∀ (v : BeaconState), True := fun _ => trivial

/-- The marker on a theorem that names no fork constant: the check never
applies to such a theorem, so the marker can never be graded, and it fails as
stale. -/
@[box_generic "stale on purpose: this fixture is out of the check's scope"]
theorem outOfScopeMarker : True := trivial

end EthCLSpecs.Tests.BoxBinderPins

/-! The gate: run the walk and the verdict on all eleven fixtures and throw on
any mismatched answer. `#guard` cannot reach the environment a reducible
unfolding needs, and a committed `#eval` fails `just lint`, so the gate is a
`run_cmd`: it runs at elaboration time, prints nothing, and a `throwError` in
it fails the build. -/

open Lean EthCLLib.Internal in
run_cmd do
  let env ← getEnv
  let ns := `EthCLSpecs.Tests.BoxBinderPins
  let typeOf (n : Name) : Lean.Elab.Command.CommandElabM Expr := do
    let some info := env.find? (ns ++ n)
      | throwError "BoxBinderPins: fixture {n} is missing"
    return info.type
  let scopes := boxCheckScopes env
  let marked := (boxGenerics env).foldl (init := ({} : NameSet)) fun acc (t, _) =>
    acc.insert t
  let check (label : String) (ok : Bool) : Lean.Elab.Command.CommandElabM Unit :=
    unless ok do throwError "BoxBinderPins: {label}"
  for (name, wantHits, wantMarked, wantProblem) in #[
    (`bindsState,        1, false, true),
    (`bindsPlain,        0, false, false),
    (`lambdaInProgram,   0, false, false),
    (`nestedForall,      1, false, true),
    (`storeBinder,       0, false, false),
    (`functionBinder,    0, false, false),
    (`predicateParam,    0, false, false),
    (`predicateBody,     1, false, true),
    (`markedBindsBox,    1, true,  false),
    (`markedBindsNone,   0, true,  true),
    (`outOfScopeMarker,  0, true,  true)] do
    let t ← typeOf name
    check s!"{name}: the fixture's scope answer is part of the pin"
      (namesFork scopes t == (name != `outOfScopeMarker))
    let hits := boxQuantifiers env t
    check s!"{name}: expected {wantHits} boxed-state quantifier(s), found {hits.size}"
      (hits.size == wantHits)
    let markedHere := marked.contains (ns ++ name)
    check s!"{name}: marker present = {markedHere}, expected {wantMarked}"
      (markedHere == wantMarked)
    let problem := boxBinderProblem? env scopes marked (ns ++ name) t
    check s!"{name}: expected the verdict to draw a problem: {wantProblem}, got \
      {problem.isSome}"
      (problem.isSome == wantProblem)
