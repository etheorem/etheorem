import EthCLLib.Spec.Tiers

/-!
# `EthCLLib.Tests.TierMerge`: lineage field merge and the downgrade bridge

A synthetic two-fork chain over `forkpreset` / `forkpresetvalues`, asserting the
three things the per-fork tier split needs (`FRAMEWORK_ARCHITECTURE.md` §4):

1. **The merge composes.** The child names only its diff, and the class it emits
   carries the parent's fields too, its own value overriding where the names
   collide.
2. **Proof fields ride along.** A well-formedness field replays into the child's
   class, and its `by decide` assignment re-proves against the *child's* value,
   so an overridden number gets a fresh proof with nothing restated.
3. **Symbolic cap defeq across the bridge.** This is the load-bearing one. With
   the preset still a variable, a vector width computed through the parent's
   class must be definitionally the width computed through the child's, or the
   fork upgrade (which copies parent-shaped fields into child-shaped ones before
   any preset is injected) would not elaborate.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.TierMerge

/-! ## The base fork -/

namespace Base

fork Base

forkpreset where
  /-- A width the child leaves alone. -/
  height : Nat
  /-- A width the child overrides. -/
  width : Nat
  /-- Well-formedness of `width`, the premise a modulo index into a
  length-`width` vector needs. -/
  widthPos : 0 < width

forkpresetvalues minimal where
  height := 2
  width := 4
  widthPos := by decide

namespace Const
section
variable [Preset]

forkabbrev width : Nat := Preset.width
forkabbrev height : Nat := Preset.height

end
end Const

end Base

/-! ## The child fork

Its `forkpreset` names two entries: one new field and one override of an
inherited value. `height`, `widthPos`, and the whole `Const` block arrive by
merge and by `inherit`. -/

namespace Child

fork Child from Base

forkpreset where
  /-- New in this fork. -/
  depth : Nat

forkpresetvalues minimal where
  width := 8
  depth := 3

section
variable [Preset]

inherit Const.width Const.height

end

end Child

-- (1) The merge composed: the child's class carries the parent's `height` beside
-- its own `depth`, and its `minimal` overrode `width` while inheriting `height`.
#guard @Child.Const.height Child.minimal = 2
#guard @Child.Const.width Child.minimal = 8
#guard @Child.Preset.depth Child.minimal = 3
#guard @Base.Const.width Base.minimal = 4

-- (2) The inherited `widthPos` proof field re-proved at the child's `width = 8`.
example : 0 < @Child.Const.width Child.minimal := @Child.Preset.widthPos Child.minimal

-- (3) The downgrade bridge, with the preset symbolic. `Base.Const.width` needs a
-- `Base.Preset`; instance search finds `Child.Downgrade.toBasePreset`, whose
-- structure literal projects straight back to the `Child.Preset` in scope. Both sides of
-- each `rfl` therefore reduce to the same variable projection, with no concrete
-- value anywhere, which is exactly the situation the fork upgrade elaborates in.
open scoped Child.Downgrade in
example [Child.Preset] : Base.Const.width = Child.Const.width := rfl

open scoped Child.Downgrade in
example [Child.Preset] : Vector Nat Base.Const.height = Vector Nat Child.Const.height := rfl

-- Both examples need their `open scoped Child.Downgrade`. Drop it and the
-- `Base.Preset` constraint has nothing to satisfy it. The extra namespace is what
-- buys that: `scoped` alone would leave the bridge active throughout `Child`,
-- since a fork's own files sit inside the fork's namespace.

end EthCLLib.Tests.TierMerge
