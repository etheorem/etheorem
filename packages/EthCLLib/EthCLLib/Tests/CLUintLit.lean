import EthCLLib.Spec.CLInt

/-!
# `EthCLLib.Tests.CLUintLit`: the kernel-checked literal gate

The `OfNat` instances of `CLUint64` and `CLUint8` carry a decidable bound
premise (`NeZero (2^64 - n)` / `NeZero (256 - n)`), so an out-of-range literal
fails instance synthesis wherever the expected type names the checked type
(`SPEC_ARITHMETIC.md` §4.5). This module pins the gate's reach, and it never
opens `EthCLLib.Spec`: every name is fully qualified, which pins the last §4.5
test context, a module with no authoring namespace in scope.

The negative pins were checked in a scratch module that fails to build; a
build cannot pin a failing module, so they live outside this file. The error
shapes, for the record:

- The out-of-range numeral `18446744073709551616` fails with
  `failed to synthesize instance of type class OfNat CLUint64
  18446744073709551616`, the same shape through a reducible alias (the
  alias's name stands in for the type).
- The power ascription `2 ^ 64` fails earlier, with
  `failed to synthesize instance of type class HPow CLUint64 Nat CLUint64`:
  no checked power route exists yet, so the out-of-range value cannot be
  written this way either.
- A non-reducible alias (a plain `def` of `CLUint64`) takes no literals at
  all, in range included, because instance search does not unfold a plain
  `def`: `failed to synthesize instance of type class OfNat SlowAlias 5`.
  That is an availability outcome, not a safety hole: no wrapping route
  survives the gate anywhere. The implication stands: the fork DSL keeps
  emitting reducible aliases (`forkabbrev`), or literals at the aliased type
  stop elaborating.
-/

set_option autoImplicit false

namespace EthCLLib.Tests.CLUintLit

/-! ## Direct `OfNat` use, in range -/

-- A direct `OfNat` application, no sugar.
example : EthCLLib.Spec.CLUint64 := @OfNat.ofNat _ 5 _
-- The numeral itself.
example : EthCLLib.Spec.CLUint64 := 5
example : EthCLLib.Spec.CLUint64 := 0
-- The maximum of each width builds.
example : EthCLLib.Spec.CLUint64 := 18446744073709551615
example : EthCLLib.Spec.CLUint8 := 255
-- The literal carries its value (the gate proved the range, so no wrap).
example : EthCLLib.Spec.CLUint64.toPlainNat (7 : EthCLLib.Spec.CLUint64) = 7 := rfl

/-! ## Reducible aliases -/

-- A reducible alias (the `forkabbrev` shape the fork DSL emits) takes the
-- gate with it: in range builds.
abbrev Gwei := EthCLLib.Spec.CLUint64

example : Gwei := 5
example : Gwei := 18446744073709551615

/-! ## Delayed expected types -/

-- The expected type arrives after the literal is elaborated.
def delayed : EthCLLib.Spec.CLUint64 := 7

example : EthCLLib.Spec.Checked EthCLLib.Spec.CLUint64 :=
  (6 : EthCLLib.Spec.CLUint64) * 7

example : EthCLLib.Spec.Checked EthCLLib.Spec.CLUint64 := do
  let x ← (2 : EthCLLib.Spec.CLUint64) + 3
  let y ← x * 2
  pure y

/-! ## The plain kind is unbounded -/

-- `CLInt` literals have no bound, the pyspec's plain `int` (`§3.1`).
example : EthCLLib.Spec.CLInt := 18446744073709551616
example : EthCLLib.Spec.CLInt := -7

end EthCLLib.Tests.CLUintLit
