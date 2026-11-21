import EthCLSpecs.Fulu.Constants

/-!
# `EthCLSpecs.Tests.AuthoringShapes`: the state-function shape the fork bodies use

The state-function shape the fork bodies use (`SPEC_ARITHMETIC.md` §4.3,
§4.4's last row): a `forkdef` over the section pattern a real operation file
uses, reading a field, binding a checked sum under `←`, taking the
proved-total divisor route through Fulu's `Const.slotsPerEpochDiv` view,
running one `assert`, and writing back through `modifyState`.

The fork here is a toy: a one-field `forkcontainer`, its own `Preset` / `Config`
stand-ins, and a `state_preamble` + `state_section`, exactly the header layout
`Fulu/Time.lean` and its siblings use. What is real is the divisor: both pins
inject `EthCLSpecs.Fulu.Const.slotsPerEpochDiv` at a concrete Fulu preset, so
the toy body divides by the production view, at mainnet (32) and at minimal
(8). Nothing here touches a production fork body.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Tests.AuthoringShapes

fork AuthoringShapes

/-- The toy fork's preset stand-in. -/
class Preset where
  dummy : Nat := 0

/-- The toy fork's config stand-in. -/
class Config where
  dummy : Nat := 0

@[reducible] def mini : Preset := {}

/-- A one-field toy state container, `slot` in the checked width the fork
bodies use. -/
forkcontainer ToyState where
  slot : CLUint64

state_preamble ToyState

state_section

/-- `compute_epoch_at_slot` after a checked counter bump, the fork-body shape
in one `forkdef`: read the field, bind the checked sum immediately,
divide by the proved-total divisor view (no bind: the route is total), assert
the epoch fits a test bound, and write the new slot back. -/
forkdef bumpSlotEpoch (delta : CLUint64) (div : PositiveDivisor) :
    StateTransition CLUint64 := do
  let s ← get
  let cur := sszGet s slot
  let next ← cur + delta
  let epoch := next / div
  assert (epoch.toPlainNat < 1024)
  modifyState fun st => sszUpdate st with slot := next
  pure epoch

end   -- closes the section opened by `state_section`

/-! ## The pins -/

section Pins

open SizzLean.Cache
open SizzLean.Hasher

local instance : Preset := mini
local instance : HasherTag := fastHasherTag


/-- Fulu's divisor view at mainnet: 32. -/
def divMainnet : PositiveDivisor :=
  @EthCLSpecs.Fulu.Const.slotsPerEpochDiv EthCLSpecs.Fulu.mainnet

/-- Fulu's divisor view at minimal: 8. -/
def divMinimal : PositiveDivisor :=
  @EthCLSpecs.Fulu.Const.slotsPerEpochDiv EthCLSpecs.Fulu.minimal

/-- The pins' concrete machine monad over the toy state. -/
abbrev SM := EStateM StateTransitionError State

/-- Run `bumpSlotEpoch` from slot 40, reporting the returned epoch and the
post-state slot, or the reject. -/
def runBump (delta : CLUint64) (div : PositiveDivisor) :
    (CLUint64 × Nat) ⊕ StateTransitionError :=
  let box0 : State := SSZ.CachedBox Sha256 ({ slot := 40 } : ToyState)
  match (bumpSlotEpoch delta div : SM CLUint64).run box0 with
  | .ok v st  => .inl (v, (sszGet st slot).toPlainNat)
  | .error e _ => .inr e

-- The whole body lands at mainnet: 40 + 8 = 48, 48 // 32 = 1, and the write
-- put 48 back into the state.
example : (runBump 8 divMainnet : (CLUint64 × Nat) ⊕ StateTransitionError)
  = .inl (1, 48) := by decide

-- The same body at minimal reads the other preset through the same view:
-- 48 // 8 = 6. One body, both presets, the §7 inheritance rule.
example : (runBump 8 divMinimal : (CLUint64 × Nat) ⊕ StateTransitionError)
  = .inl (6, 48) := by decide

-- The checked sum faults through the machine channel: 40 + max leaves the
-- range, before the divisor route and the write.
example : (runBump 18446744073709551615 divMainnet :
      (CLUint64 × Nat) ⊕ StateTransitionError)
  = .inr (.arithmetic "+") := by decide

-- The assert fires on an epoch past the test bound (32968 // 32 = 1030), and
-- it rejects before the write runs. The descriptor is the condition's own
-- source text, parens included, diagnostic only.
example : (runBump 32928 divMainnet : (CLUint64 × Nat) ⊕ StateTransitionError)
  = .inr (.assert "(epoch.toPlainNat < 1024)") := by decide

end Pins

end EthCLSpecs.Tests.AuthoringShapes
