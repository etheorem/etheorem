import EthCLLib

/-!
# `EthCLLib.Tests.PreambleSection`: the header-macro self-test

Exercises the section header (`EthCLLib.Spec.Header`) on a toy fork, so the
behavior is checked at build (`FRAMEWORK_ARCHITECTURE.md` §14):

- `state_preamble Toy` declares `State` (the plain `Toy`) and the concrete-domain
  `modifyState`, once;
- `state_section` opens the `section` itself and brings the transition variables into
  scope (closed by the matching `end`);
- a step writes `modifyState fun state => sszUpdate state with …` with **no**
  `(state : State)` annotation, the payoff of the concrete-domain `modifyState`, and
  it both typechecks and *runs* at the fast config;
- the seven helpers run on the plain fork in both monads, `StateT State
  (Except StateTransitionError)` and `EStateM StateTransitionError State`: `sszGet`,
  `sszUpdate` (through `bumpSlot` / `setFlag`), `sszModify` (through `bumpXsHead`),
  `appendState`, `setOrAppendState`, `getStateRoot` (through `rootAfterBump`) and
  `runToRoot`;
- `sszOfArrayM` raises `.listFull` on too many elements;
- `appendState` appends to a list with room and raises `.listFull` on a full one.
  `setOrAppendState` appends, overwrites, or raises `.outOfBounds`, as the spec's
  `set_or_append_list` does;
- `fork_choice_section` opens its section and establishes the store-machine variables.

A plain state carries no Merkle cache, so `getStateRoot` and `runToRoot` take every root
as a full `SSZ.hashTreeRoot` of the record; the roots are
compared against `SSZ.hashTreeRoot Sha256` of the expected plain record, closed by
`native_decide` (CLAUDE.md, *Proofs involving SSZ hashes*).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
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

/-- A toy container standing in for a fork's `BeaconState`. `xs` is a list field with a
limit of 2, small enough that a test can fill it. -/
forkcontainer Toy where
  slot : UInt64
  flag : UInt64
  xs   : SSZList UInt64 2

/-! ## The once-per-fork preamble -/

-- Declares `abbrev State := Toy` (the plain record) and the concrete-domain
-- `modifyState`.
state_preamble Toy

-- `State` is the plain record: it *is* `Toy`, a `Toy` literal types as `State` with no
-- wrapper (the section's `s0` below pins the literal form).
example : @State mini = @Toy mini := rfl

/-! ## A state-transition section (the macro opens the `section`) -/

state_section

/-- A step written with **no** binder annotation: the concrete-domain `modifyState`
from the preamble types `state : State`, and `state_section` brought the monad and
instances into scope. On the plain state `sszGet` is the projection and `sszUpdate`
the record update, so this *is* `fun state => { state with slot := state.slot + 1 }`. -/
def bumpSlot : StateTransition Unit :=
  modifyState fun state => sszUpdate state with slot := sszGet state slot + 1

/-- A second annotation-free step, writing a different field. -/
def setFlag (v : UInt64) : StateTransition Unit :=
  modifyState fun state => sszUpdate state with flag := v

/-- The spec's read-modify-write through `sszModify`: the list head incremented in
place, the path named once. -/
def bumpXsHead : StateTransition Unit :=
  modifyState fun state => (sszModify state xs[0]! := fun v => v + 1)

/-- The spec's `state.xs.append(v)`. -/
def appendX (v : UInt64) : StateTransition Unit :=
  appendState xs v

/-- The spec's `set_or_append_list(state.xs, i, v)`. -/
def setOrAppendX (i : CLUint64) (v : UInt64) : StateTransition Unit :=
  setOrAppendState xs i v

/-- The spec's `state.xs = List[uint64, 2](a)`, through `sszOfArrayM`. -/
def setXs (a : Array UInt64) : StateTransition Unit := do
  let l : SSZList UInt64 2 ← sszOfArrayM "xs" a
  modifyState fun state => sszUpdate state with xs := l

/-- The spec's state root taken inside a step: `bumpSlot`, then `getStateRoot`. On the
plain state this reads the record and recomputes the root in full. -/
def rootAfterBump : StateTransition ByteArray := do
  bumpSlot
  getStateRoot

end   -- closes the section opened by `state_section`

/-! ## The steps run in `EStateM` -/

section EStateMRuns

local instance : Preset := mini
local instance : HasherTag := fastHasherTag

/-- The plain starting state, no wrapper. -/
def s0 : State := { slot := 41, flag := 7, xs := ⟨#[1], by decide⟩ }

/-- Run `action` from `xs = [1]`. The result is `.inl` of the list, or `.inr` of the
reject. `Sum` has `DecidableEq`, so `native_decide` can compare it. -/
def runXs (action : EStateM StateTransitionError State Unit) :
    Array UInt64 ⊕ StateTransitionError :=
  match action.run s0 with
  | .ok _ st   => .inl (sszGet st xs).toArray
  | .error e _ => .inr e

/-- `bumpSlot` executes over the plain record: `slot 41 → 42`, with the binder typed
annotation-free. -/
example :
    (let action : EStateM StateTransitionError State Unit := bumpSlot
     match action.run s0 with
     | .ok _ st   => sszGet st slot
     | .error _ _ => 0)
      = 42 := by native_decide

/-- `setFlag` executes likewise: `flag → 9`. -/
example :
    (let action : EStateM StateTransitionError State Unit := setFlag 9
     match action.run s0 with
     | .ok _ st   => sszGet st flag
     | .error _ _ => 0)
      = 9 := by native_decide

/-- `sszModify` read-modify-writes the list head: `[1] → [2]`. -/
example : runXs bumpXsHead = .inl #[2] := by native_decide

/-- An append with room: `[1] → [1, 5]`. -/
example : runXs (appendX 5) = .inl #[1, 5] := by native_decide

/-- An append to a full list raises `.listFull`, as `eth-ssz-specs` 0.1.0's `List.append`
does (`SSZValueError`, a `ValueError`). -/
example : runXs (do appendX 5; appendX 6) = .inr (.listFull "xs") := by native_decide

/-- `set_or_append_list` at the length appends. -/
example : runXs (setOrAppendX 1 5) = .inl #[1, 5] := by native_decide

/-- `set_or_append_list` inside the list overwrites. -/
example : runXs (setOrAppendX 0 9) = .inl #[9] := by native_decide

/-- `set_or_append_list` past the end raises the spec's `IndexError`, `.outOfBounds`. -/
example : runXs (setOrAppendX 3 9) = .inr (.outOfBounds 3 1) := by native_decide

/-- An array up to the limit becomes the list. -/
example : runXs (setXs #[4, 5]) = .inl #[4, 5] := by native_decide

/-- An array over the limit raises `.listFull`, as `eth-ssz-specs` 0.1.0's `List`
constructor does (a pydantic `ValidationError`, also a `ValueError`). -/
example : runXs (setXs #[4, 5, 6]) = .inr (.listFull "xs") := by native_decide

/-- `getStateRoot` inside the step: the root of the bumped record. -/
example :
    (match (rootAfterBump : EStateM StateTransitionError State ByteArray).run s0 with
     | .ok root _ => some root
     | .error _ _ => none)
      = some (SSZ.hashTreeRoot Sha256
        ({ slot := 42, flag := 7, xs := ⟨#[1], by decide⟩ } : Toy)) := by native_decide

/-- `runToRoot` in `EStateM`: run `bumpSlot`, root the post-state. `Except` carries no
`DecidableEq`, so both gates below compare through `Option`. -/
example :
    (let action : EStateM StateTransitionError State Unit := bumpSlot
     match runToRoot s0 action with
     | .ok root => some root
     | .error _ => none)
      = some (SSZ.hashTreeRoot Sha256
        ({ slot := 42, flag := 7, xs := ⟨#[1], by decide⟩ } : Toy)) := by native_decide

/-- … and the reject propagates: a full-list append roots nothing. -/
example :
    (let action : EStateM StateTransitionError State Unit := do appendX 5; appendX 6
     match runToRoot s0 action with
     | .error e => some e
     | .ok _    => none)
      = some (.listFull "xs") := by native_decide

end EStateMRuns

/-! ## The steps run in `StateT` -/

section StateTRuns

local instance : Preset := mini
local instance : HasherTag := fastHasherTag

/-- Run `action` in the pure column, from the same starting state. -/
def runXsT (action : StateT State (Except StateTransitionError) Unit) :
    Array UInt64 ⊕ StateTransitionError :=
  match action.run s0 with
  | .ok (_, st) => .inl (sszGet st xs).toArray
  | .error e    => .inr e

/-- `bumpSlot` in the pure column: `slot 41 → 42`. -/
example :
    (let action : StateT State (Except StateTransitionError) Unit := bumpSlot
     match action.run s0 with
     | .ok (_, st) => sszGet st slot
     | .error _    => 0)
      = 42 := by native_decide

/-- `sszModify` read-modify-writes the list head: `[1] → [2]`. -/
example : runXsT bumpXsHead = .inl #[2] := by native_decide

/-- An append with room: `[1] → [1, 5]`. -/
example : runXsT (appendX 5) = .inl #[1, 5] := by native_decide

/-- An append to a full list raises `.listFull` here too. -/
example : runXsT (do appendX 5; appendX 6) = .inr (.listFull "xs") := by native_decide

/-- `set_or_append_list` at the length appends. -/
example : runXsT (setOrAppendX 1 5) = .inl #[1, 5] := by native_decide

/-- `set_or_append_list` inside the list overwrites. -/
example : runXsT (setOrAppendX 0 9) = .inl #[9] := by native_decide

/-- An array up to the limit becomes the list. -/
example : runXsT (setXs #[4, 5]) = .inl #[4, 5] := by native_decide

/-- `getStateRoot` inside the step: the root of the bumped record. -/
example :
    (match (rootAfterBump : StateT State (Except StateTransitionError) ByteArray).run s0 with
     | .ok (root, _) => some root
     | .error _      => none)
      = some (SSZ.hashTreeRoot Sha256
        ({ slot := 42, flag := 7, xs := ⟨#[1], by decide⟩ } : Toy)) := by native_decide

/-- `runToRoot` in the pure column: run `bumpSlot`, root the post-state. -/
example :
    (let action : StateT State (Except StateTransitionError) Unit := bumpSlot
     match runToRoot s0 action with
     | .ok root => some root
     | .error _ => none)
      = some (SSZ.hashTreeRoot Sha256
        ({ slot := 42, flag := 7, xs := ⟨#[1], by decide⟩ } : Toy)) := by native_decide

/-- … and the reject propagates: the pure column carries no state on its error
branch, so a full-list append roots nothing. -/
example :
    (let action : StateT State (Except StateTransitionError) Unit :=
       do appendX 5; appendX 6
     match runToRoot s0 action with
     | .error e => some e
     | .ok _    => none)
      = some (.listFull "xs") := by native_decide

end StateTRuns

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
