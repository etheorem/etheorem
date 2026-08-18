import EthCLLib.Spec.Forms

/-!
# `EthCLLib.Tests.ForkScoping`: nested-namespace capture keys and the new kinds

A synthetic two-fork chain that pins the three elaboration facts the per-fork
constant tiers rest on (`FRAMEWORK_ARCHITECTURE.md` §3.1). Each is a property of
Lean's elaborator rather than of our code, so it is asserted here instead of
being assumed:

1. **Composite-declId scoping.** A `forkabbrev` written inside `namespace Const`
   keys as `Const.<name>` under its *fork*, and replaying it as
   `abbrev Const.<name>` inside the child's namespace both lands the declaration
   at `Child.Const.<name>` and resolves its body's unqualified siblings inside
   `Child.Const`. Late binding therefore reaches into the sub-namespace.
2. **Section-variable auto-binding through `inherit`.** The replay runs
   `elabCommand` from inside a command elaborator; the surrounding
   `variable [Preset]` must still be picked up by the ordinary
   used-variable rule, so the child's constants bind to the child's `Preset`.
3. **Abbrev-ness survives replay.** An inherited `forkabbrev` stays
   `@[reducible]`, which is what instance synthesis and the symbolic-cap derive
   need. Demoting it to a `def` would break both silently, so the assertion is
   an `inferInstance` through the alias, which only reducible unfolding solves.

`forkinstance` replay rides along on the same chain.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.ForkScoping

/-- A marker class inhabited only at the literal `32`. Synthesising it at
`Const.limit` succeeds exactly when `Const.limit` is reducible, so it is the
observable difference between an `abbrev` and a `def`. -/
class Marker (n : Nat) where

instance : Marker 32 := ⟨⟩

/-- A fork-neutral class the two forks each register an instance of, at their own
`Const.limit`. Stands in for the real `ValidModulus` registrations. -/
class Tagged (n : Nat) where
  tag : Nat

/-! ## The base fork -/

namespace Base

fork Base

/-- The base fork's preset tier, one field wide. -/
class Preset where
  width : Nat

namespace Const
section
variable [Preset]

/-- A preset-backed constant: the body names the fork's own `Preset`. -/
forkabbrev width : Nat := Preset.width
/-- A flat constant, no binder. -/
forkabbrev limit : Nat := 16
/-- A flat constant the child leaves alone, the replay-reducibility probe. -/
forkabbrev cap : Nat := 32
/-- A constant whose body calls its sibling unqualified; the late-binding probe. -/
forkabbrev doubled : Nat := 2 * width

end
end Const

/-- Registered against `Const.limit`, so a replay in a fork that overrides
`limit` must retarget. -/
forkinstance taggedLimit : Tagged Const.limit := ⟨Const.limit + 1⟩

/-- A concrete preset, the base fork's `minimal`. -/
@[reducible] def minimal : Preset where
  width := 3

end Base

-- The base fork behaves as written: `doubled` is twice its own `width`, and the
-- instance carries the base's `limit`.
#guard @Base.Const.doubled Base.minimal = 6
#guard Base.taggedLimit.tag = 17

/-! ## The child fork -/

namespace Child

fork Child from Base

/-- The child's own preset tier. Nothing relates it to `Base.Preset`; the
inherited constant bodies bind to *this* class by name resolution alone. -/
class Preset where
  width : Nat

namespace Const

/-- The child's override of the flat constant. Written inside `namespace Const`,
so it keys as `Const.limit` under the fork `Child`, the same key the base used. -/
forkabbrev limit : Nat := 32

end Const

section
variable [Preset]

-- The `inherit` block sits at fork level, not inside `namespace Const`: the
-- names it spells are already fork-relative, and the surrounding `section
-- variable [Preset]` is what the replayed preset-backed bodies auto-bind to.
inherit Const.width Const.doubled

end

-- No binder on these, so they sit outside the section.
inherit Const.cap

-- `taggedLimit`'s body names `Const.limit`, which resolves to the child's
-- override on replay. Outside the section: it takes no preset.
inherit taggedLimit

/-- The child's `minimal`, a different width from the base's. -/
@[reducible] def minimal : Preset where
  width := 5

end Child

-- (1) + (2): the replayed `Const.doubled` landed in `Child.Const`, called the
-- replayed `Child.Const.width` rather than `Base.Const.width`, and bound to the
-- child's `Preset` through the section variable.
#guard @Child.Const.doubled Child.minimal = 10
#guard @Child.Const.width Child.minimal = 5

-- The replayed instance retargeted to the child's `Const.limit` (32), so its
-- tag is 33 rather than the base's 17.
#guard Child.taggedLimit.tag = 33

-- (3): synthesis through the inherited alias. `Marker` is inhabited only at the
-- literal `32`; instance search unfolds `Child.Const.cap` to reach it only
-- because the replay kept the alias reducible. A `def` would fail here.
example : Marker Child.Const.cap := inferInstance

end EthCLLib.Tests.ForkScoping
