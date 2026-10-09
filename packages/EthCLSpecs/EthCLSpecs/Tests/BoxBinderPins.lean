import EthCLLib.Internal.BoxBinders
import EthCLLib.Internal.ProofLedger
import EthCLLib.Spec
import EthCLSpecs.Gloas.State
import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Tests.BoxBinderPins`: the plain-value check pins

The pure-state-theorems plan (§5, Phase 3) keeps fork-body theorems over plain
values, and `scripts/ProofCoverage.lean` enforces the rule with the walk in
`EthCLLib.Internal.BoxBinders`. The fixture theorems here hold that walk
to statements of known answers, so a check that rots to "always pass" fails
this module instead of passing quietly:

* `bindsState` quantifies over the boxed `State` and draws one finding.
* `bindsPlain` binds `BeaconState` and passes.
* `lambdaInProgram` states a spec write inline in the `modifyState` shape, whose
  lambda over the state is program text, and passes.
* `nestedForall` hides a `∀ s : State` inside a hypothesis and draws one
  finding.

Each fixture names a fork constant, so each is in scope: a failing fixture that
is out of scope would pass for the wrong reason. Three more shapes pin the
false-positive edges: a `Store` binder (a `State` inside a field type, head
`Store`, accepted), a function-typed parameter over `State` (a domain, not a
quantified claim, accepted), and the marker: `markedBindsBox` is accepted, and
`markedBindsNone` fails as stale.

The `#eval` at the bottom runs the walk on all eight and throws on any
mismatched answer, so `lake build EthCLSpecsTests` is the gate.

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

/-- The marker on a theorem that binds the box: the check accepts it. -/
@[box_generic "a box-level flavour fact; the seed of a cached ≡ pure equivalence"]
theorem markedBindsBox [Preset] [HasherTag] :
    ∀ (state : State), True := fun _ => trivial

/-- The marker on a theorem that binds no box: the check fails it as stale. -/
@[box_generic "stale on purpose: this fixture must draw the stale-marker finding"]
theorem markedBindsNone [Preset] [HasherTag] :
    ∀ (v : BeaconState), True := fun _ => trivial

end EthCLSpecs.Tests.BoxBinderPins

/-! The gate: run the walk on all eight fixtures and throw on any mismatched
answer. `#guard` cannot reach the environment a reducible unfolding needs, so
the `#eval` runs the checks in `CoreM` and turns a wrong answer into a build
error. -/

open Lean EthCLLib.Internal in
#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let ns := `EthCLSpecs.Tests.BoxBinderPins
  let typeOf (n : Name) : Lean.CoreM Lean.Expr := do
    let some info := env.find? (ns ++ n)
      | throwError "BoxBinderPins: fixture {n} is missing"
    return info.type
  let scopes := boxCheckScopes env
  let marked := (boxGenerics env).foldl (init := ({} : Lean.NameSet)) fun acc (t, _) =>
    acc.insert t
  let check (label : String) (ok : Bool) : Lean.CoreM Unit :=
    unless ok do throwError "BoxBinderPins: {label}"
  for (name, wantHits, wantMarked) in #[
    (`bindsState,      1, false),
    (`bindsPlain,      0, false),
    (`lambdaInProgram, 0, false),
    (`nestedForall,    1, false),
    (`storeBinder,     0, false),
    (`functionBinder,  0, false),
    (`markedBindsBox,  1, true),
    (`markedBindsNone, 0, true)] do
    let t ← typeOf name
    check s!"{name}: the fixture must name a fork constant, so it is in scope"
      (namesFork scopes t)
    let hits := boxQuantifiers env t
    check s!"{name}: expected {wantHits} boxed-state quantifier(s), found {hits.size}"
      (hits.size == wantHits)
    let markedHere := marked.contains (ns ++ name)
    check s!"{name}: marker present = {markedHere}, expected {wantMarked}"
      (markedHere == wantMarked)
