import EthCLLib

/-!
# `EthCLLib.Tests.PreambleSection`: the header-macro self-test

Exercises the two-macro section header (`EthCLLib.Spec.Header`) on a toy fork, so
the behavior is checked at build (`FRAMEWORK_ARCHITECTURE.md` §14):

- `state_preamble Toy` declares `State` (the boxed `Toy`) and the concrete-domain
  `modifyState`, once;
- `state_section` opens the `section` itself and brings the transition variables into
  scope (closed by the matching `end`);
- a step writes `modifyState fun state => sszUpdate state with …` with **no**
  `(state : State)` annotation, the payoff of the concrete-domain `modifyState`, and
  it both typechecks and *runs* at the fast config;
- `fork_choice_section` opens its section and establishes the store-machine variables.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Cache
open SizzLean.Hasher
open SizzLean.Repr

namespace EthCLLib.Tests.PreambleSection

/-- A local preset stand-in (the cap machinery is covered by `ContainerForm`). -/
class Preset where
  dummy : Nat := 0

/-- A local config stand-in (`state_section` brings `[Config]` into scope). -/
class Config where
  dummy : Nat := 0

@[reducible] def mini : Preset := {}

/-- A two-field toy container standing in for a fork's `BeaconState`. -/
forkcontainer Toy where
  slot : UInt64
  flag : UInt64

/-! ## The once-per-fork preamble -/

-- Declares `abbrev State := Box HasherTag.H Toy` and the concrete-domain `modifyState`.
state_preamble Toy

/-! ## A state-transition section (the macro opens the `section`) -/

state_section

/-- A step written with **no** binder annotation: the concrete-domain `modifyState`
from the preamble types `state : State`, and `state_section` brought the monad and
instances into scope. -/
def bumpSlot : StateTransition Unit :=
  modifyState fun state => sszUpdate state with slot := sszGet state slot + 1

/-- A second annotation-free step, writing a different field. -/
def setFlag (v : UInt64) : StateTransition Unit :=
  modifyState fun state => sszUpdate state with flag := v

end   -- closes the section opened by `state_section`

/-! ## The steps run at the fast config -/

/-- `bumpSlot` executes over a cached `Sha256` box: `slot 41 → 42`, with the binder
typed annotation-free. -/
example :
    (letI : Preset := mini
     letI : HasherTag := fastHasherTag
     let box0 : @State mini fastHasherTag := SSZ.CachedBox Sha256 ({ slot := 41, flag := 7 } : @Toy mini)
     let action : EStateM StateTransitionError (@State mini fastHasherTag) Unit := bumpSlot
     match action.run box0 with
     | .ok _ st   => sszGet st slot
     | .error _ _ => 0)
      = 42 := by native_decide

/-- `setFlag` executes likewise: `flag → 9`. -/
example :
    (letI : Preset := mini
     letI : HasherTag := fastHasherTag
     let box0 : @State mini fastHasherTag := SSZ.CachedBox Sha256 ({ slot := 41, flag := 7 } : @Toy mini)
     let action : EStateM StateTransitionError (@State mini fastHasherTag) Unit := setFlag 9
     match action.run box0 with
     | .ok _ st   => sszGet st flag
     | .error _ _ => 0)
      = 9 := by native_decide

/-! ## A fork-choice section (the macro opens the `section`) -/

/-- A toy store. `fork_choice_section` names the struct `Store`, so the test does too.
A `map`-typed field uses the `map` parameter, as the real `Store` does (`blocks`, …). -/
forkstruct Store (map : MapKind) where
  blocks    : map UInt64 UInt64
  finalized : UInt64

fork_choice_section map

/-- A pure store query naming `Store map`, as the real fork-choice read layer does. -/
def finalizedOf (store : Store map) : UInt64 := store.finalized

/-- A store handler, confirming `fork_choice_section` opened the section and brought the
store-machine variables (`Store map`, `StoreTransition`, the constraints) into scope. -/
def readFinalized : StoreTransition UInt64 := do
  return finalizedOf (← get)

/-- A store mutator, confirming the `MonadStateOf (Store map)` constraint is in scope. -/
def bumpFinalized : StoreTransition Unit :=
  modify fun store => { store with finalized := store.finalized + 1 }

end   -- closes the section opened by `fork_choice_section`

end EthCLLib.Tests.PreambleSection
