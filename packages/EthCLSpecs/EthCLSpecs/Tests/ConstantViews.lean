import EthCLSpecs.Fulu.Constants
import EthCLSpecs.Gloas.Constants
import EthCLSpecs.Heze.Constants

/-!
# `EthCLSpecs.Tests.ConstantViews`: the derived constant views under tier inheritance

The pins for the two view kinds of `SPEC_ARITHMETIC.md` §4.5 and §4.2:

- the checked view (`…C`): a `CLUint64` built by proof-carrying construction
  over the preset's own `< 2 ^ 64` premise;
- the proved-total divisor view (`…Div`): a `PositiveDivisor` pairing the stored
  value with the preset's own positivity premise.

Each view body projects the original entry, so the numeral lives in the value
set alone. These pins lock the three properties the later stages rely on: the
views reduce at a concrete preset, the divisor view's positivity is the tier's
own proof field (no `decide` at the view), and tier inheritance carries both
through Fulu, Gloas, and Heze, with a child override getting a fresh proof from
the merged value set (`FRAMEWORK_ARCHITECTURE.md` §4).

The module also pins the `effectiveBalanceIncrement` twin settlement: the
pyspec declares `EFFECTIVE_BALANCE_INCREMENT` a `Gwei`, so the `…G` preset field
stores the value and the suffix-free `Nat` entry is a projection of it
(`SPEC_ARITHMETIC.md` §4.2, checked constants stay checked).

They live in `EthCLSpecsTests` rather than beside the views, for the reason
`FuluForkChoicePins.lean` records: a pin compiled into `EthCLSpecs` is shipped
weight, and `native_decide` compiled into a fork body is evaluation every
consumer of that body carries, for a check only the build gate reads.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

-- Load-bearing: the replayed `forkabbrev slotsPerEpochDiv` capture carries an
-- unqualified `PositiveDivisor` and re-elaborates in this file's scope, so the
-- child-fork section below needs the namespace open.
open EthCLLib.Spec

namespace EthCLSpecs.Tests.ConstantViews

/-! ### The symbolic laws

With the preset still a variable, the checked view round-trips through
`toPlainNat` to the original `Nat` entry, and the divisor view's positivity is
exactly its tier's proof field. Both hold by reduction, no concrete value
needed. -/

example [EthCLSpecs.Fulu.Preset] :
    EthCLSpecs.Fulu.Const.slotsPerEpochC.toPlainNat
      = EthCLSpecs.Fulu.Const.slotsPerEpoch :=
  CLUint64.ofNatLT_toPlainNat _ _

example [EthCLSpecs.Fulu.Preset] : 0 < EthCLSpecs.Fulu.Const.slotsPerEpochDiv.n :=
  EthCLSpecs.Fulu.Const.slotsPerEpochDiv.positive

example [EthCLSpecs.Fulu.Preset] :
    EthCLSpecs.Fulu.Const.effectiveBalanceIncrement
      = EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG.toNat := rfl

/-! ### Fulu pins

The views reduce at both injected presets. `@` supplies the instance the tier
binder asks for: `Preset` for the two preset views, `Config` for the config
view, whose body mentions the config class alone. -/

open EthCLSpecs.Fulu in
example : (@Const.slotsPerEpochDiv minimal).n = 8 := by native_decide

open EthCLSpecs.Fulu in
example : (@Const.slotsPerEpochDiv mainnet).n = 32 := by native_decide

open EthCLSpecs.Fulu in
example : (@Const.slotsPerEpochC minimal).toPlainNat = 8 := by native_decide

open EthCLSpecs.Fulu in
example : (@Const.slotsPerEpochC mainnet).toPlainNat = 32 := by native_decide

open EthCLSpecs.Fulu in
/-- The divisor view's positivity at a concrete preset comes from the preset's
own proof field; this test states no `decide` of its own. -/
example : 0 < (@Const.slotsPerEpochDiv minimal).n :=
  (@Const.slotsPerEpochDiv minimal).positive

open EthCLSpecs.Fulu in
/-- The twin settlement at both presets: the derived `Nat` view and the stored
`Gwei` field read the same value, so the numeral appears once per value set. -/
example : @Const.effectiveBalanceIncrement minimal
    = (@Const.effectiveBalanceIncrementG minimal).toNat := rfl

open EthCLSpecs.Fulu in
/-- The stored value pins at both presets, so a preset edit that silently moves
the increment fails here too. -/
example : @Const.effectiveBalanceIncrement minimal = 1000000000 := by
  native_decide

open EthCLSpecs.Fulu in
example : @Const.effectiveBalanceIncrement mainnet
    = (@Const.effectiveBalanceIncrementG mainnet).toNat := rfl

open EthCLSpecs.Fulu in
example : @Const.effectiveBalanceIncrement mainnet = 1000000000 := by
  native_decide

open EthCLSpecs.Fulu in
example : (@Const.churnLimitQuotientC minimalConfig).toPlainNat = 32 := by
  native_decide

open EthCLSpecs.Fulu in
example : (@Const.churnLimitQuotientC mainnetConfig).toPlainNat = 65536 := by
  native_decide

/-! ### Gloas and Heze pins

Both forks replay the views by `inherit`, so each copy binds to that fork's own
`Preset` and `Config`. The concrete numbers come from Fulu's merged value sets,
which is the point: the child forks added no value of their own, and the views
reduced anyway. -/

open EthCLSpecs.Gloas in
example : (@Const.slotsPerEpochDiv minimal).n = 8 := by native_decide

open EthCLSpecs.Gloas in
example : (@Const.slotsPerEpochC mainnet).toPlainNat = 32 := by native_decide

open EthCLSpecs.Gloas in
example : 0 < (@Const.slotsPerEpochDiv mainnet).n :=
  (@Const.slotsPerEpochDiv mainnet).positive

open EthCLSpecs.Gloas in
example : (@Const.churnLimitQuotientC minimalConfig).toPlainNat = 32 := by
  native_decide

open EthCLSpecs.Gloas in
/-- The inherited twin agreement, at the middle fork. -/
example : @Const.effectiveBalanceIncrement minimal
    = (@Const.effectiveBalanceIncrementG minimal).toNat := rfl

open EthCLSpecs.Heze in
example : (@Const.slotsPerEpochDiv minimal).n = 8 := by native_decide

open EthCLSpecs.Heze in
example : (@Const.slotsPerEpochC mainnet).toPlainNat = 32 := by native_decide

open EthCLSpecs.Heze in
example : 0 < (@Const.slotsPerEpochDiv minimal).n :=
  (@Const.slotsPerEpochDiv minimal).positive

open EthCLSpecs.Heze in
example : (@Const.churnLimitQuotientC mainnetConfig).toPlainNat = 65536 := by
  native_decide

open EthCLSpecs.Heze in
/-- The inherited twin agreement, at the newest fork. -/
example : @Const.effectiveBalanceIncrement mainnet
    = (@Const.effectiveBalanceIncrementG mainnet).toNat := rfl

/-! ### The child override

A synthetic fourth fork overrides `slotsPerEpoch` and nothing else. Its
`forkpresetvalues` names only the override; the merged value set re-runs Fulu's
`slotsPerEpochPos := by decide` against the child's number, so the proof is
fresh with nothing restated (`FRAMEWORK_ARCHITECTURE.md` §4): proof fields
merge like any other field and re-prove against the child's number. The
replayed views then read the child's number through the child's own `Preset`.

The fork sits in its own namespace directly under `EthCLSpecs`, the depth the
`fork … from` form resolves the parent at. A real fork body would also replay
its containers and transition; this test needs only the tier and the views, so
the capture stays that small. -/

end EthCLSpecs.Tests.ConstantViews

namespace EthCLSpecs.ConstViewChild

fork ConstViewChild from Heze

-- The type aliases the merged tier fields' types name. Each real fork declares
-- its own set in its `Types.lean`; a replayed tier class re-emits the raw field
-- types, so the child's namespace needs these four before `forkpreset`.
forkabbrev Slot := UInt64
forkabbrev Epoch := UInt64
forkabbrev Gwei := UInt64
forkabbrev Version := Vector UInt8 4

-- No new fields of its own; the forms materialize this fork's classes out of
-- the merged lineage.
forkpreset where
forkconfig where

forkpresetvalues minimal where
  slotsPerEpoch := 64

forkconfigvalues minimalConfig where

namespace Const
section
variable [Preset] [Config]

inherit slotsPerEpochC slotsPerEpochDiv churnLimitQuotientC

end
end Const

end EthCLSpecs.ConstViewChild

namespace EthCLSpecs.Tests.ConstantViews

/-! The override landed: both views read the child's number. -/

open EthCLSpecs.ConstViewChild in
example : (@Const.slotsPerEpochDiv minimal).n = 64 := by native_decide

open EthCLSpecs.ConstViewChild in
example : (@Const.slotsPerEpochC minimal).toPlainNat = 64 := by native_decide

/-! The tier's own proof field re-proved at the child's number: no `decide`
restated at the view, the value set, or this test (`FRAMEWORK_ARCHITECTURE.md`
§4). -/

open EthCLSpecs.ConstViewChild in
example : 0 < (@Const.slotsPerEpochDiv minimal).n :=
  (@Const.slotsPerEpochDiv minimal).positive

/-! The config tier was not overridden, and the inherited config view still
reduces through the child's own `Config` class. -/

open EthCLSpecs.ConstViewChild in
example : (@Const.churnLimitQuotientC minimalConfig).toPlainNat = 32 := by
  native_decide

end EthCLSpecs.Tests.ConstantViews
