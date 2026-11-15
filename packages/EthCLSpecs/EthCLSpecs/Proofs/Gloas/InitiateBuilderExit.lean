import EthCLSpecs.Gloas.Operations
import EthCLLib.Proofs.CLUint
import EthCLLib.Proofs.Run
import EthCLSpecs.Proofs.Gloas.Run
import SizzLean.Proofs.UncachedBox
import SizzLean.Proofs.SSZListSet

/-!
# `EthCLSpecs.Proofs.Gloas.InitiateBuilderExit`: `initiateBuilderExit`'s effect on the builder registry

`initiateBuilderExit_run_eq` is the whole-transition contract: the run on the uncached
box of `preState` dispatches on the checked `Epoch` sum
`currentEpochOf preState + MIN_BUILDER_WITHDRAWABILITY_DELAY` exactly as the body binds
it. The sum is a `Checked Epoch` bind since the `Epoch` unit flip: `Epoch` is `CLUint64`,
so the addition tests its result against `[0, 2^64)` and raises outside it. On a fault
the run rejects with the `.arithmetic` fault carrying the repr of the exact `ArithFault`,
and nothing is written. When the sum binds at `withdrawableAt`, the run returns the
uncached box of `{ preState with builders := … }`, the source-level write on `builders`,
as one value. The contract states the run at the box, in `.run` form, because that is
the shape the fork-choice bridge consumes. The readings state the `runPure` form under
the sum's `.ok` equation, which `runPure_of_run_ok` derives from the contract.
`initiateBuilderExit_run_inRange` reads it through `SizzLean.Proofs.SSZListSet` as the
per-index reads, and `initiateBuilderExit_run_outOfRange` reads it as the no-op it is:
for an out-of-range index, once the sum binds, the run returns `preState` itself.

Statements bind plain `BeaconState` values and never bind a boxed `State`, so no
theorem branches on the box flavour.

The out-of-range case is Lean-only behavior with no PySpec counterpart. The pinned
Gloas spec uses equivalent indexing syntax, yet the Python runtime rejects an
out-of-range index where Lean's `[i]!` write is a no-op. An overflowing unsigned
addition raises in both runtimes, so the old wrap discrepancy is gone.

No-wrap for the withdrawability-delay sum is conditional for an arbitrary `[Config]`,
and unconditional for the two shipped Gloas preset/config pairs, with no epoch or slot
hypothesis from the caller. The `.toPlainInt` reads in the no-wrap statements are the
pyspec's `int(x)`, the plain-`int` view the checked operators' success and value lemmas
(`EthCLLib.Proofs.CLUint`) are stated over.

Scope is Gloas's `initiateBuilderExit`. Heze inherits the function
(`Heze/Operations.lean:45`) at its own `State`; these theorems say nothing about that
instantiation. The sole current Gloas caller derives the index from a successful
`findIdx?`, so its calls are expected to be in range, and that caller-level fact is
left to `processBuilderExitRequest`'s own theorem.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError Checked ArithFault CLUint64)
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok run_bind run_pure
  except_bind_ok except_bind_error run_liftM_ok run_liftM_error
  add_ok_iff add_value)
open EthCLSpecs.Gloas (Preset Config BuilderIndex Epoch BeaconState)
open EthCLSpecs.Gloas (minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Gloas (initiateBuilderExit currentEpochOf computeEpochAtSlot modifyState)
open EthCLSpecs.Gloas.Const (slotsPerEpochDiv)
open SizzLean.Proofs (progressiveListSet!_size progressiveListSet!_getElem!_self
  progressiveListSet!_getElem!_ne progressiveListSet!_eq_of_size_le view_uncachedBox)

/-! ## The whole-transition equation

`initiateBuilderExit_run_eq` is the contract: the run dispatches on the checked
`Epoch` sum the body binds, and on `.ok` it returns `preState` with only
`builders[builderIndex.toNat]!` written. `initiateBuilderExit_run_inRange` and
`initiateBuilderExit_run_outOfRange` read that equation through the `ProgressiveList.set!`
lemmas under the sum's `.ok` equation, so the range split happens at the read. -/

/-- Exact whole-transition equation for `initiateBuilderExit`, at the box the pure
configuration runs: the step on `pureState preState` first runs the checked `Epoch`
sum `currentEpochOf preState + MIN_BUILDER_WITHDRAWABILITY_DELAY`, and its fault is
the run's fault. When the sum binds at `withdrawableAt`, the run returns the uncached
box of the original value with only `builders[builderIndex.toNat]!` written through
the source-level write. Stated at the box level so the fork-choice bridge consumes it
by application; `runPure_of_run_ok` derives the `runPure` form. For an out-of-range
index the underlying list write is a no-op, so the bound result is the input value
(`initiateBuilderExit_run_outOfRange`). -/
@[characterizes EthCLSpecs.Gloas.initiateBuilderExit]
theorem initiateBuilderExit_run_eq [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run (pureState preState)
        = match (currentEpochOf (pureState preState)
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch) with
          | .error e => .error (StateTransitionError.arithmetic (reprStr e))
          | .ok withdrawableAt => .ok ((), pureState
              { preState with builders :=
                  (preState.builders.set! builderIndex.toNat
                    { preState.builders[builderIndex.toNat]! with
                      withdrawableEpoch := withdrawableAt }) }) := by
  intro preState builderIndex
  -- Re-elaborate the source shape here: the checked sum lift, then the `builders` write.
  -- The `get` peels by definitional reduction at `pureState preState` (its state and
  -- value are the same box), so the shown shape binds no box of its own, and the sum
  -- reads `currentEpochOf (pureState preState)`, the value the get's continuation sees.
  show (do
      let withdrawableAt ←
        (currentEpochOf (pureState preState)
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay)
      modifyState fun state =>
        sszModify state builders[builderIndex.toNat]! as b => { b with withdrawableEpoch := withdrawableAt }
      : GloasRun Unit).run (pureState preState)
    = match (currentEpochOf (pureState preState)
        + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch) with
      | .error e => .error (StateTransitionError.arithmetic (reprStr e))
      | .ok withdrawableAt => .ok ((), pureState
          { preState with builders :=
              (preState.builders.set! builderIndex.toNat
                { preState.builders[builderIndex.toNat]! with
                  withdrawableEpoch := withdrawableAt }) })
  rw [run_bind]
  cases hsum : (currentEpochOf (pureState preState)
      + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch) with
  | error e =>
    rw [run_liftM_error, except_bind_error]
    rfl
  | ok withdrawableAt =>
    rw [run_liftM_ok, except_bind_ok]
    rfl

/-- **In range, sum bound.** Once the checked withdrawability sum binds at
`withdrawableAt`, running `initiateBuilderExit builderIndex` succeeds, and the written
builder reads back with `withdrawableEpoch` set to the bound sum, while every other
builder and the registry's `.size` are unchanged. The index-level reading of
`initiateBuilderExit_run_eq` through `ProgressiveList.set!`'s own lemmas; the sum's
`.ok` equation is a hypothesis, the same shape the contract's `.ok` arm commits to.
Without it the run may reject: `Epoch` is `CLUint64`, and the sum carries its own
range test. -/
theorem initiateBuilderExit_run_inRange [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex) (withdrawableAt : Epoch),
      builderIndex.toNat < preState.builders.size →
      (currentEpochOf (pureState preState)
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch)
        = .ok withdrawableAt →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!
            = { preState.builders[builderIndex.toNat]! with
                withdrawableEpoch := withdrawableAt }
        ∧ (∀ j : Nat, j ≠ builderIndex.toNat →
              postState.builders[j]! = preState.builders[j]!)
        ∧ postState.builders.size = preState.builders.size := by
  intro preState builderIndex withdrawableAt hidx hok
  have hrun := initiateBuilderExit_run_eq preState builderIndex
  simp only [hok] at hrun
  refine ⟨_, runPure_of_run_ok hrun, ?_, fun j hj => ?_, ?_⟩
  · exact progressiveListSet!_getElem!_self _ _ _ hidx
  · exact progressiveListSet!_getElem!_ne _ _ _ _ (Ne.symm hj)
  · exact progressiveListSet!_size _ _ _

/-- **Out of range, sum bound.** Once the checked withdrawability sum binds, running
`initiateBuilderExit builderIndex` succeeds even for an out-of-range index (the write
`[i]!` is total), and the write is a genuine no-op: the run returns the pre-state value
itself, so no read of any field can tell the two apart. Without the sum hypothesis the
run may reject, and no post-state exists to state. -/
theorem initiateBuilderExit_run_outOfRange [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex) (withdrawableAt : Epoch),
      ¬ builderIndex.toNat < preState.builders.size →
      (currentEpochOf (pureState preState)
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch)
        = .ok withdrawableAt →
      runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
        = .ok ((), preState) := by
  intro preState builderIndex withdrawableAt hidx hok
  have hrun := initiateBuilderExit_run_eq preState builderIndex
  simp only [hok] at hrun
  rw [runPure_of_run_ok hrun,
    progressiveListSet!_eq_of_size_le _ _ _ (Nat.le_of_not_lt hidx)]

/-! ## Generic conditional no-overflow

The withdrawability sum is a checked `CLUint64` add, so it raises exactly when the
plain-`int` sum reaches `2 ^ 64` (`add_ok_iff`). No generic invariant relates the bounded
current epoch to the independently configurable withdrawal delay: a `[Config]` instance
is free to set `minBuilderWithdrawabilityDelay` arbitrarily, so the no-wrap fact is
necessarily **conditional**. Its condition is a hypothesis the
caller must establish elsewhere, say from a slot/epoch bound on `mainnet`, since the
function itself carries no run-time guard. The `.toPlainInt` reads are the pyspec's
`int(x)`, the plain-`int` view `EthCLLib.Proofs.CLUint` states its lemmas over. -/

/-- **Function-level corollary.** Chaining `initiateBuilderExit_run_inRange` with the
checked add's own success and value facts (`add_ok_iff`, `add_value`): under the
epoch-bound hypothesis (read from the *pre*-state's `currentEpochOf`, as in the
in-range theorem), the sum binds, and the post-state builder's
`withdrawableEpoch.toPlainInt` is exactly the natural-number sum
`currentEpochOf(pre-state).toPlainInt + MIN_BUILDER_WITHDRAWABILITY_DELAY.toPlainInt`,
with no silent wrap through `2 ^ 64`. -/
theorem initiateBuilderExit_run_inRange_no_wrap [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      (currentEpochOf (pureState preState)).toPlainInt
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainInt < 2 ^ 64 →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toPlainInt
            = (currentEpochOf (pureState preState)).toPlainInt
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainInt := by
  intro preState builderIndex hidx hbound
  -- The bound is exactly `add`'s own success condition, and `add_value` reads the
  -- bound value back as the plain-`int` sum.
  obtain ⟨withdrawableAt, hok⟩ := (add_ok_iff _ _).mpr hbound
  obtain ⟨postState, hrun, hview, -, -⟩ :=
    initiateBuilderExit_run_inRange preState builderIndex withdrawableAt hidx hok
  exact ⟨postState, hrun, by rw [hview]; exact add_value _ _ _ hok⟩

/-! ## Shipped preset/config pairs: unconditional

`initiateBuilderExit_run_inRange_no_wrap`'s `hbound` premise is conditional because a
`[Config]` instance is free, in general, to pick `minBuilderWithdrawabilityDelay` large
enough to make `currentEpochOf preState + minBuilderWithdrawabilityDelay` overflow
`2 ^ 64`. The two pairs the repository actually ships (the minimal and mainnet
preset/config pairs used by the shipped Gloas interfaces) don't: `slotsPerEpoch` bounds
`currentEpochOf preState` well below `2 ^ 64` for *any* `preState.slot`, so the sum
with the concrete `minBuilderWithdrawabilityDelay` (`2` on minimal, `64` on mainnet)
can never reach `2 ^ 64`.
Each corollary below discharges `hbound` from that arithmetic fact alone, with no epoch
or slot hypothesis from the caller, and reuses
`initiateBuilderExit_run_inRange_no_wrap` rather than re-deriving the state
transition. -/

/-- **Minimal preset/config (`minimal`, `minimalConfig`), unconditional.**
`slotsPerEpoch = 8`, `minBuilderWithdrawabilityDelay = 2`:
`currentEpochOf preState = preState.slot.toPlainInt / 8`, so the sum with `2` is
nowhere near `2 ^ 64`, for every `preState`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_minimal [HasherTag] :
    letI : Preset := minimal
    letI : Config := minimalConfig
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toPlainInt
            = (currentEpochOf (pureState preState)).toPlainInt
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainInt := by
  letI : Preset := minimal
  letI : Config := minimalConfig
  intro preState builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap minimal _ minimalConfig preState builderIndex hidx ?_
  -- `toPlainInt` is `val.toNat` definitionally; the `have` names one atom for `omega`.
  have hslot : preState.slot.toPlainInt < 2 ^ 64 := preState.slot.val.toNat_lt
  have hdelay : EthCLLib.Spec.CLUint64.toPlainInt
      (@Config.minBuilderWithdrawabilityDelay minimalConfig) = 2 := rfl
  have hcep : (currentEpochOf (pureState preState)).toPlainInt
      = preState.slot.toPlainInt / 8 := by
    show CLUint64.toPlainInt (computeEpochAtSlot (sszGet (pureState preState) slot)) = _
    simp only [view_uncachedBox]
    show CLUint64.toPlainInt (preState.slot / slotsPerEpochDiv) = _
    show (UInt64.ofNat (preState.slot.toPlainInt / slotsPerEpochDiv.val)).toNat = _
    rw [UInt64.toNat_ofNat', show slotsPerEpochDiv.val = 8 from rfl]
    have hle : preState.slot.toPlainInt / 8 ≤ preState.slot.toPlainInt := Nat.div_le_self _ _
    exact Nat.mod_eq_of_lt (by omega)
  simp only [hdelay, hcep]
  omega

/-- **Mainnet preset/config (`mainnet`, `mainnetConfig`), unconditional.**
`slotsPerEpoch = 32`, `minBuilderWithdrawabilityDelay = 64`:
`currentEpochOf preState = preState.slot.toPlainInt / 32`, so the sum with `64` is
nowhere near `2 ^ 64`, for every `preState`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_mainnet [HasherTag] :
    letI : Preset := mainnet
    letI : Config := mainnetConfig
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toPlainInt
            = (currentEpochOf (pureState preState)).toPlainInt
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainInt := by
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  intro preState builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap mainnet _ mainnetConfig preState builderIndex hidx ?_
  -- `toPlainInt` is `val.toNat` definitionally; the `have` names one atom for `omega`.
  have hslot : preState.slot.toPlainInt < 2 ^ 64 := preState.slot.val.toNat_lt
  have hdelay : EthCLLib.Spec.CLUint64.toPlainInt
      (@Config.minBuilderWithdrawabilityDelay mainnetConfig) = 64 := rfl
  have hcep : (currentEpochOf (pureState preState)).toPlainInt
      = preState.slot.toPlainInt / 32 := by
    show CLUint64.toPlainInt (computeEpochAtSlot (sszGet (pureState preState) slot)) = _
    simp only [view_uncachedBox]
    show CLUint64.toPlainInt (preState.slot / slotsPerEpochDiv) = _
    show (UInt64.ofNat (preState.slot.toPlainInt / slotsPerEpochDiv.val)).toNat = _
    rw [UInt64.toNat_ofNat', show slotsPerEpochDiv.val = 32 from rfl]
    have hle : preState.slot.toPlainInt / 32 ≤ preState.slot.toPlainInt := Nat.div_le_self _ _
    exact Nat.mod_eq_of_lt (by omega)
  simp only [hdelay, hcep]
  omega

end EthCLSpecs.Proofs.Gloas
