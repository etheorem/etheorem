import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox
import SizzLean.Proofs.SSZListSet

/-!
# `EthCLSpecs.Proofs.Gloas.InitiateBuilderExit`: `initiateBuilderExit`'s effect on the builder registry

`initiateBuilderExit_run_eq` is the whole-transition contract: the run on the uncached
box of `preState` returns the uncached box of `{ preState with builders := … }`, the source-level
write on `builders`, as one value. The contract states the run at the box, in `.run`
form, because that is the shape the fork-choice bridge consumes. The readings state the
`runPure` form, which `runPure_of_run_ok` derives from the contract.
`initiateBuilderExit_run_inRange` reads it through `SizzLean.Proofs.SSZListSet` as the
per-index reads, and `initiateBuilderExit_run_outOfRange` reads it as the no-op it is:
for an out-of-range index the run returns `preState` itself.

Statements bind plain `BeaconState` values and never bind a boxed `State`, so no
theorem branches on the box flavour.

The out-of-range case is Lean-only behavior with no PySpec counterpart. The pinned
Gloas spec uses equivalent indexing syntax, yet the Python runtime rejects an
out-of-range index where Lean's `[i]!` write is a no-op. Python likewise rejects an
overflowing unsigned addition where Lean's `UInt64` addition wraps.

No-wrap for the withdrawability-delay sum is conditional for an arbitrary `[Config]`,
and unconditional for the two shipped Gloas preset/config pairs, with no epoch or slot
hypothesis from the caller.

Scope is Gloas's `initiateBuilderExit`. Heze inherits the function
(`Heze/Operations.lean:43`) at its own `State`; these theorems say nothing about that
instantiation. The sole current Gloas caller derives the index from a successful
`findIdx?`, so its calls are expected to be in range, and that caller-level fact is
left to `processBuilderExitRequest`'s own theorem.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag)
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok)
open EthCLSpecs.Gloas (Preset Config BuilderIndex Epoch BeaconState)
open EthCLSpecs.Gloas (minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Gloas (initiateBuilderExit currentEpochOf)
open SizzLean.Proofs (sszListSet!_size sszListSet!_getElem!_self sszListSet!_getElem!_ne
  sszListSet!_eq_of_size_le view_uncachedBox)

/-! ## The whole-transition equation

`initiateBuilderExit_run_eq` is the contract: the run returns `preState` with only
`builders[builderIndex.toNat]!` written. `initiateBuilderExit_run_inRange` and
`initiateBuilderExit_run_outOfRange` read that one equation through the `SSZList.set!`
lemmas, so the range split happens at the read. -/

/-- Exact whole-transition equation for `initiateBuilderExit`, at the box the pure
configuration runs: the step on `pureState preState` returns the uncached box of the original
value with only `builders[builderIndex.toNat]!` written through the source-level write.
Stated at the box level so the fork-choice bridge consumes it by application;
`runPure_of_run_ok` derives the `runPure` form. For an out-of-range index the underlying
list write is a no-op, so the whole result is the input value
(`initiateBuilderExit_run_outOfRange`). -/
@[characterizes EthCLSpecs.Gloas.initiateBuilderExit]
theorem initiateBuilderExit_run_eq [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run (pureState preState)
        = .ok ((), pureState
          { preState with builders :=
              (preState.builders.set! builderIndex.toNat
                { preState.builders[builderIndex.toNat]! with
                  withdrawableEpoch :=
                    currentEpochOf (pureState preState)
                      + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay }) }) := by
  intro preState builderIndex
  rfl

/-- **In range.** Running `initiateBuilderExit builderIndex` never rejects, and the
written builder reads back with `withdrawableEpoch` set to the pre-state's
`currentEpochOf` plus `MIN_BUILDER_WITHDRAWABILITY_DELAY`, while every other builder and
the registry's `.size` are unchanged. The index-level reading of
`initiateBuilderExit_run_eq` through `SSZList.set!`'s own lemmas. -/
theorem initiateBuilderExit_run_inRange [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!
            = { preState.builders[builderIndex.toNat]! with
                withdrawableEpoch :=
                  currentEpochOf (pureState preState)
                    + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay }
        ∧ (∀ j : Nat, j ≠ builderIndex.toNat →
              postState.builders[j]! = preState.builders[j]!)
        ∧ postState.builders.size = preState.builders.size := by
  intro preState builderIndex hidx
  refine ⟨_, runPure_of_run_ok (initiateBuilderExit_run_eq preState builderIndex), ?_, fun j hj => ?_, ?_⟩
  · exact sszListSet!_getElem!_self _ _ _ hidx
  · exact sszListSet!_getElem!_ne _ _ _ _ (Ne.symm hj)
  · exact sszListSet!_size _ _ _

/-- **Out of range.** Running `initiateBuilderExit builderIndex` still never rejects
(`[i]!` is total), and the write is a genuine no-op: the run returns the pre-state
value itself, so no read of any field can tell the two apart. -/
theorem initiateBuilderExit_run_outOfRange [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      ¬ builderIndex.toNat < preState.builders.size →
      runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
        = .ok ((), preState) := by
  intro preState builderIndex hidx
  rw [runPure_of_run_ok (initiateBuilderExit_run_eq preState builderIndex),
    sszListSet!_eq_of_size_le _ _ _ (Nat.le_of_not_lt hidx)]

/-! ## Generic conditional no-overflow

`Epoch` is an alias for `UInt64`, so `epoch + Const.minBuilderWithdrawabilityDelay` is
`UInt64` addition, mod `2 ^ 64`. No generic invariant relates the bounded `UInt64`
current epoch to the independently configurable withdrawal delay (a `[Config]` instance
is free to set `minBuilderWithdrawabilityDelay` arbitrarily), so the no-wrap fact is
necessarily **conditional**. Its condition is a hypothesis the caller must establish
elsewhere, say from a slot/epoch bound on `mainnet`, since the function itself carries
no run-time guard. -/

/-- Core's `UInt64.toNat_add` gives `(a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64`
unconditionally; under the stated bound, `Nat.mod_eq_of_lt` drops the `%` and the
`UInt64` sum's `.toNat` is exactly the `Nat` sum, with no wraparound. -/
private theorem epoch_add_minBuilderWithdrawabilityDelay_no_wrap [Config] {epoch : Epoch} :
    epoch.toNat + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64 →
      (epoch + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay).toNat
        = epoch.toNat + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  intro h
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- **Function-level corollary.** Chaining `initiateBuilderExit_run_inRange`'s
written-builder equation with `epoch_add_minBuilderWithdrawabilityDelay_no_wrap`: under
the epoch-bound hypothesis (read from the *pre*-state's `currentEpochOf`, as in the
unconditional in-range theorem), the post-state builder's `withdrawableEpoch.toNat` is
exactly the natural-number sum `currentEpochOf(pre-state).toNat +
MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat`, with no silent wrap through `2 ^ 64`. -/
theorem initiateBuilderExit_run_inRange_no_wrap [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      (currentEpochOf (pureState preState)).toNat
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64 →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toNat
            = (currentEpochOf (pureState preState)).toNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  intro preState builderIndex hidx hbound
  obtain ⟨postState, hrun, hview, -, -⟩ := initiateBuilderExit_run_inRange preState builderIndex hidx
  exact ⟨postState, hrun,
    by rw [hview]; exact epoch_add_minBuilderWithdrawabilityDelay_no_wrap hbound⟩

/-! ## Shipped preset/config pairs: unconditional

`initiateBuilderExit_run_inRange_no_wrap`'s `hbound` premise is conditional because a
`[Config]` instance is free, in general, to pick `minBuilderWithdrawabilityDelay` large
enough to make `currentEpochOf preState + minBuilderWithdrawabilityDelay` overflow
`2 ^ 64`. The two pairs the repository actually ships (the minimal and mainnet
preset/config pairs used by the shipped Gloas interfaces) don't: `slotsPerEpoch` bounds
`currentEpochOf preState` well below `2 ^ 64` for *any* `preState.slot : UInt64`, so the sum
with the concrete `minBuilderWithdrawabilityDelay` (`2` on minimal, `8192` on mainnet)
can never reach `2 ^ 64`.
Each corollary below discharges `hbound` from that arithmetic fact alone, with no epoch
or slot hypothesis from the caller, and reuses
`initiateBuilderExit_run_inRange_no_wrap` rather than re-deriving the state
transition. -/

/-- **Minimal preset/config (`minimal`, `minimalConfig`), unconditional.**
`slotsPerEpoch = 8`, `minBuilderWithdrawabilityDelay = 2`:
`currentEpochOf preState ≤ (2 ^ 64 - 1) / 8`, so the sum with `2` is nowhere near
`2 ^ 64`, for every `preState`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_minimal [HasherTag] :
    letI : Preset := minimal
    letI : Config := minimalConfig
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toNat
            = (currentEpochOf (pureState preState)).toNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  letI : Preset := minimal
  letI : Config := minimalConfig
  intro preState builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap minimal _ minimalConfig preState builderIndex hidx ?_
  have hslot := UInt64.toNat_lt preState.slot
  have hspe : (@Preset.slotsPerEpoch minimal : Nat) = 8 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay minimalConfig).toNat = 2 := rfl
  simp only [currentEpochOf, view_uncachedBox, EthCLSpecs.Gloas.computeEpochAtSlot,
    EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay, EthCLSpecs.Gloas.Const.slotsPerEpoch,
    UInt64.toNat_div, UInt64.toNat_ofNat', hspe, hdelay, Nat.reducePow, Nat.reduceMod]
  omega

/-- **Mainnet preset/config (`mainnet`, `mainnetConfig`), unconditional.**
`slotsPerEpoch = 32`, `minBuilderWithdrawabilityDelay = 8192`:
`currentEpochOf preState ≤ (2 ^ 64 - 1) / 32`, so the sum with `8192` is nowhere near
`2 ^ 64`, for every `preState`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_mainnet [HasherTag] :
    letI : Preset := mainnet
    letI : Config := mainnetConfig
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toNat
            = (currentEpochOf (pureState preState)).toNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  intro preState builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap mainnet _ mainnetConfig preState builderIndex hidx ?_
  have hslot := UInt64.toNat_lt preState.slot
  have hspe : (@Preset.slotsPerEpoch mainnet : Nat) = 32 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay mainnetConfig).toNat = 8192 := rfl
  simp only [currentEpochOf, view_uncachedBox, EthCLSpecs.Gloas.computeEpochAtSlot,
    EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay, EthCLSpecs.Gloas.Const.slotsPerEpoch,
    UInt64.toNat_div, UInt64.toNat_ofNat', hspe, hdelay, Nat.reducePow, Nat.reduceMod]
  omega

end EthCLSpecs.Proofs.Gloas
