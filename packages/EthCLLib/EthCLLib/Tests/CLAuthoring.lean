import EthCLLib

/-!
# `EthCLLib.Tests.CLAuthoring`: the authoring rules exercised

`SPEC_ARITHMETIC.md` §4.3 and §4.7 on representative functions of each shape
the fork bodies use.
The module pins, in order:

- **The state-free `Checked` shape** (§4.3's reward formula): immediate binds,
  one bind per expression, each step tested. The dropped-fault pin and the
  short-circuit pin state the *correct* form; each carries a comment naming the
  incorrect form that would fail it. A failing shape cannot be pinned in a
  building module, so the incorrect forms live in the comments, and the pin
  states the behavior that only the correct form produces.
- **The empty loop and the early return** (§4.3, "bind placement against the
  source, including empty loops, early returns"): a `for` over an empty
  collection forms no fault, and an early return skips a would-be fault. The
  pins fail under the hoisted binds the comments name.
- **The store shape** (§4.7's store context; §4.4's prose covers the store
  channel): a `fork_choice_section` handler doing
  checked arithmetic over store fields, and the `on_block`-shaped nested
  composition, whose inner arithmetic fault surfaces as
  `.transition (.arithmetic …)`. The 3.1 store pin in `Tests/CLCheckedElab.lean`
  covered the wrap over a stand-in `Nat` store; this is the same route through
  the real `forkstruct` / `fork_choice_section` machinery.

The state-function shape (§4.4's `StateTransition` row over the fork section
pattern) lives in `EthCLSpecs.Tests.AuthoringShapes`, because it exercises the
fork's `State` / `modifyState` / constant views that only a fork body has.
-/

set_option autoImplicit false

namespace EthCLLib.Tests.CLAuthoring

open EthCLLib.Spec

/-! ## The state-free `Checked` shape (§4.3) -/

/-- The §4.3 reward formula, state-free:
`base_reward * weight * unslashed_participating_increments // (active_increments
* WEIGHT_DENOMINATOR)`. Each factor binds immediately, one bind per
expression; the division is the function's returned `Checked` expression, the
§4.3 result form, so the numerator's fault surfaces before any quotient is
formed. -/
def weightedReward (baseReward weight unslashedIncrements activeIncrements
    denominator : CLUint64) : Checked CLUint64 := do
  let numerator ← baseReward * weight * unslashedIncrements
  let scaling ← activeIncrements * denominator
  numerator / scaling

-- The whole chain succeeds: 6 * 4 * 1 // (2 * 3) = 4.
example : weightedReward 6 4 1 2 3 = .ok 4 := by decide

-- The test runs per operation: the numerator max * 2 passes 2^64 and the
-- route faults there, even though the quotient max * 2 // 2 would have fit
-- exactly.
example : weightedReward 18446744073709551615 2 1 1 2
  = .error (.range "*" 64 18446744073709551615 2) := by decide

-- A zero scaling factor faults at the division, after the numerator bound
-- (24 = 6 * 4 * 1).
example : weightedReward 6 4 1 2 0 = .error (.zeroDivisor "//" 64 24) := by decide

/-- The dropped-fault hazard of §4.3, in its corrected form: the sum binds
immediately, so the fault surfaces on *both* branches of the use. -/
def useTotalBound (useIt : Bool) (a b : CLUint64) : Checked CLUint64 := do
  let total ← a + b
  if useIt then pure total else pure 0

-- The pin that discriminates. The incorrect form `let total := a + b` (no `←`)
-- compiles in the contract §4.3's shape (`if useIt then total else return 0`)
-- and in the bind-at-use shape: `total : Checked CLUint64`, and the path that
-- never examines it computes no fault, so useTotal-shaped code would return
-- `.ok 0` here where the pyspec raises. This pin fails under it.
example : useTotalBound false 18446744073709551615 1 = .error (.range "+" 64 18446744073709551615 1) := by
  decide

-- The bound form on the used branch: same fault, same shape, no path drops it.
example : useTotalBound true 18446744073709551615 1 = .error (.range "+" 64 18446744073709551615 1) := by
  decide

-- And the in-range run answers on both branches.
example : useTotalBound false 2 3 = .ok 0 := by decide
example : useTotalBound true 2 3 = .ok 5 := by decide

/-- The pyspec's `and` short-circuit (§4.3): the right operand's arithmetic
binds inside its own branch, so it is formed only when the pyspec forms it. -/
def bothGuard (a b : CLUint64) : Checked Bool := do
  if a < b then
    let gap ← b - a
    pure (gap < 100)
  else
    pure false

-- The pin that discriminates. With `a = max` and `b = 0` the guard is false,
-- so the pyspec never forms the `then` branch's `b - a`, which would fault
-- here. The incorrect form binds the subtraction above the branch
-- (`let gap ← b - a` before the `if`), and raises where the pyspec computes
-- nothing; this pin fails under it.
example : bothGuard 18446744073709551615 0 = .ok false := by decide

-- The taken branch's arithmetic does run: a small gap answers, a wide one
-- fails the guard's own test.
example : bothGuard 3 7 = .ok true := by decide
example : bothGuard 0 18446744073709551615 = .ok false := by decide

/-! ## The empty loop and the early return (§4.3) -/

/-- A `for` over the elements: the addition binds inside the loop body, so an
element that never comes forms no fault. -/
def sumAll (xs : List CLUint64) : Checked CLUint64 := do
  let mut total : CLUint64 := 0
  for x in xs do
    total ← total + x
  pure total

-- The pin that discriminates. An empty collection binds nothing and returns
-- the start value. The incorrect form hoists the loop's step arithmetic out of
-- the loop (`let step ← 18446744073709551615 + 1` before the `for`), which
-- faults on the empty path the pyspec never evaluates; this pin fails under
-- it.
example : sumAll [] = .ok 0 := by decide

-- The loop does form faults when elements exist: the second step overflows
-- even though the total of a plain sum would not be taken further.
example : sumAll [18446744073709551615, 1] = .error (.range "+" 64 18446744073709551615 1) := by
  decide

-- A run under the bound adds through.
example : sumAll [2, 3] = .ok 5 := by decide

/-- An early return skips the arithmetic after it: the growth step binds after
the cap branch, so a capped input never forms its fault. -/
def cappedGrowth (x cap : CLUint64) : Checked CLUint64 := do
  if x > cap then
    return cap
  let grown ← x + 18446744073709551615
  pure grown

-- The pin that discriminates. The capped path returns before the addition is
-- formed. The incorrect form binds `x + 18446744073709551615` above the `if`,
-- which faults for every `x > 0`; this pin fails under it.
example : cappedGrowth 5 3 = .ok 3 := by decide

-- The uncapped path really does run the faulting addition.
example : cappedGrowth 1 100 = .error (.range "+" 64 1 18446744073709551615) := by decide

-- The zero case stays in range: 0 + max is the last representable value.
example : cappedGrowth 0 100 = .ok 18446744073709551615 := by decide

/-! ## The store shape (§4.4's store row)

A toy fork-choice store over one checked field, the section header mirroring
`Fulu/ForkChoice.lean`: a `forkstruct` `Store`, a `state_preamble` + toy
container for the nested state machine's `State`, a `state_section` for the
nested actions, and a `fork_choice_section map` for the handlers. -/

/-- A local preset stand-in, as `PreambleSection` uses. -/
class Preset where
  dummy : Nat := 0

/-- A local config stand-in (`fork_choice_section` brings `[Config]` into
scope). -/
class Config where
  dummy : Nat := 0

@[reducible] def mini : Preset := {}

/-- The nested state machine's state: a one-field toy container. -/
forkcontainer ToyState where
  counter : CLUint64

state_preamble ToyState

-- The nested state actions, in their own section, as the real layout has them.
state_section

/-- A nested step that adds one to the counter, checked. -/
def nestedBump : StateTransition Unit := do
  let s ← get
  let cur := sszGet s counter
  let next ← cur + 1
  modifyState fun st => sszUpdate st with counter := next

/-- A nested step whose very first bind faults: the fault is formed before any
state change. -/
def nestedFaulting : StateTransition Unit := do
  let x ← (0 : CLUint64) - 1
  modifyState fun st => sszUpdate st with counter := x

end   -- closes the section opened by `state_section`

/-- The toy store: one checked field beside one map-backed one, so the section
`map` variable is the store's own backing, as the real `Store`'s is. -/
forkstruct Store (map : MapKind) where
  balance : CLUint64
  heights : map CLUint64 CLUint64

fork_choice_section map

/-- A store handler doing checked arithmetic over a store field: read, bind,
write back. -/
def addBalance (delta : CLUint64) : StoreTransition CLUint64 := do
  let store ← get
  let next ← store.balance + delta
  modify fun s => { s with balance := next }
  pure next

/-- The `on_block`-shaped composition: the store handler runs the nested state
machine on a pre-state through the one-way bridge. -/
def onNestedBlock (pre : State) : StoreTransition State :=
  runNestedStateTransition pre nestedBump

/-- The same composition over the faulting step. -/
def onNestedFault (pre : State) : StoreTransition State :=
  runNestedStateTransition pre nestedFaulting

end   -- closes the section opened by `fork_choice_section`

/-! ### The store pins -/

section StoreRun

open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Spec

local instance : Preset := mini
local instance : HasherTag := fastHasherTag

-- The pins' concrete store monad over the deterministic map. `@Store mini
-- treeMap` names the preset explicitly, so the section-variable handlers'
-- `MonadStateOf (Store …)` constraints unify with it directly.
abbrev PinM := StateT (@Store mini treeMap) (Except StoreTransitionError)

def store0 : @Store mini treeMap := { balance := 1, heights := FcMap.empty }

/-- The nested machine's pre-state, shared by the composition pins. -/
def boxPre : State := SSZ.CachedBox Sha256 ({ counter := 41 } : ToyState)

/-- Run a store action from `store0`, reporting the value or the reject. -/
def runStore (action : PinM CLUint64) : CLUint64 ⊕ StoreTransitionError :=
  match action.run store0 with
  | .ok (v, _)    => .inl v
  | .error e      => .inr e

/-- Run a nested-state store action from `store0`, reporting the post-state
counter or the reject. The nested machine's own pre-state rides inside the
action, the same hand `on_block` gets it by. -/
def runStoreState (action : PinM State) : CLUint64 ⊕ StoreTransitionError :=
  match action.run store0 with
  | .ok (post, _) => .inl (sszGet post counter)
  | .error e      => .inr e

-- The checked store arithmetic lands: 1 + 4 = 5. The `map` named argument
-- pins the section's `map` variable, so the handler's `MonadStateOf (Store …)`
-- constraint synthesizes against the concrete monad.
example : (runStore (addBalance (map := treeMap) 4) : CLUint64 ⊕ StoreTransitionError) = .inl 5 := by
  decide

-- An overflowing delta faults through the store channel, wrapped as the nested
-- state reject the store machine carries.
example : (runStore (addBalance (map := treeMap) 18446744073709551615) :
      CLUint64 ⊕ StoreTransitionError) = .inr (.transition (.arithmetic "+")) := by
  decide

-- The nested composition: the store handler ran the state step, and the
-- post-state carries the checked increment 41 → 42.
example : (runStoreState (onNestedBlock boxPre) : CLUint64 ⊕ StoreTransitionError) = .inl 42 := by
  native_decide

-- The faulting nested step surfaces as the wrapped arithmetic fault, and the
-- store handler cannot recover it.
example : (runStoreState (onNestedFault boxPre) : CLUint64 ⊕ StoreTransitionError)
  = .inr (.transition (.arithmetic "-")) := by native_decide

end StoreRun

end EthCLLib.Tests.CLAuthoring
