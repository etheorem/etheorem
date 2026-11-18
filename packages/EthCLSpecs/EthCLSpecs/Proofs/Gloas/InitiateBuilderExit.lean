import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.GetPtc
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox
import SizzLean.Proofs.SSZListSet

/-!
# `EthCLSpecs.Proofs.Gloas.InitiateBuilderExit`: `initiateBuilderExit`'s effect on the builder registry

`initiateBuilderExit_run_eq` is the whole-transition contract: the run on the uncached
box of `preState` matches, in the pinned order, on the raising read
`state.builders[builder_index]` and then on the checked `current_epoch +
MIN_BUILDER_WITHDRAWABILITY_DELAY` sum. An out-of-range index rejects with the
`.outOfBounds` fault before the sum runs, the sum's arithmetic fault propagates as the
machine reject, and success writes the sum's value into `builders[builderIndex.toNat]!`.
The contract states the run at the box, in `.run` form, because that is
the shape the fork-choice bridge consumes. The readings state the `runPure` form, which
`runPure_of_run_ok` derives from the contract, under the no-overflow bound the checked
sum imposes. `initiateBuilderExit_run_inRange` reads the contract through
`SizzLean.Proofs.SSZListSet` as the per-index reads, and
`initiateBuilderExit_run_outOfRange` reads it as the raise it is: for an out-of-range
index the run rejects and produces no state.

Statements bind plain `BeaconState` values and never bind a boxed `State`, so no
theorem branches on the box flavour.

The out-of-range case rejects where the pinned Gloas spec rejects: Python's
`state.builders[builder_index]` raises `IndexError` there, and the body's `sszGetIdx`
read surfaces the same fault class as `.outOfBounds`.

No-wrap for the withdrawability-delay sum is conditional for an arbitrary `[Config]`,
and unconditional for the two shipped Gloas preset/config pairs, with no epoch or slot
hypothesis from the caller. The pre-migration body wrapped a raw `UInt64` sum; the
migrated body raises where the pinned Python raises, and the readings carry the
no-overflow bound instead.

Scope is Gloas's `initiateBuilderExit`. Heze inherits the function
(`Heze/Operations.lean:45`) at its own `State`; these theorems say nothing about that
instantiation. The sole current Gloas caller derives the index from a successful
`findIdx?`, so its calls are expected to be in range, and that caller-level fact is
left to `processBuilderExitRequest`'s own theorem.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag Checked StateTransitionError sszGetIdx IdxRead liftErr IndexError)
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok)
open EthCLLib.Proofs (add_ok_iff add_value run_bind run_pure except_bind_ok except_bind_error
  runPure_eq)
open EthCLSpecs.Gloas (Preset Config BuilderIndex Epoch BeaconState)
open EthCLSpecs.Gloas (minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Gloas (initiateBuilderExit currentEpochOf)
open SizzLean.Proofs (progressiveListSet!_size progressiveListSet!_getElem!_self
  progressiveListSet!_getElem!_ne progressiveListSet!_eq_of_size_le view_uncachedBox)

/-! ## The whole-transition equation

`initiateBuilderExit_run_eq` is the contract: the run matches, in the pinned order, on
the raising `builders[builderIndex]` read and then on the checked
`current_epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY` sum. An out-of-range index rejects
before the sum runs; in range, success returns `preState`
with only `builders[builderIndex.toNat]!` written.
`initiateBuilderExit_run_inRange` and `initiateBuilderExit_run_outOfRange` read that one
equation through the `ProgressiveList.set!` lemmas under the sum's no-overflow bound, so
the range split happens at the read. -/

/-- `sszGetIdx`'s in-range read is the identity action at the Gloas runner, so the body's
bind on it substitutes the element: the monad law `bind (pure v) k = k v` at the runner.
`rfl`: every layer is an instance projection, a definition, or a match on a constructor. -/
private theorem bind_liftErr_ok [Preset] [HasherTag] {α β : Type} (v : α) (k : α → GloasRun β) :
    bind (liftErr (Except.ok v : Except IndexError α)) k = k v :=
  rfl

/-- In range, the read's `[i]?` carries the same element as the total `[i]!` read. The
run equation matches on `[i]?`, and the in-range readings state their builders through
`[i]!`, so each in-range reading rewrites through this once. -/
private theorem progList_getElem?_eq_getElem! {α : Type} [Inhabited α]
    (xs : SizzLean.Repr.ProgressiveList α) (i : Nat) (h : i < xs.size) :
    xs.val[i]? = some xs[i]! := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.ProgressiveList α) i => i < xs.size)
    (h := h)]
  show xs.val[i]? = some (xs.val[i]'h)
  exact Array.getElem?_eq_getElem h

/-- Exact whole-transition equation for `initiateBuilderExit`, at the box the pure
configuration runs: the step on `pureState preState` matches on the raising read
`state.builders[builder_index]` first, then on the checked sum
`current_epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY`; past the registry's end the read
rejects with `.outOfBounds` (the `IndexError` the pinned Python read raises), the sum's
arithmetic fault propagates as the machine reject, and the success value lands in the
`withdrawableEpoch` of `builders[builderIndex.toNat]!` through the source-level write.
Stated at the box level so the fork-choice bridge consumes it by application;
`runPure_of_run_ok` derives the `runPure` form. -/
@[characterizes EthCLSpecs.Gloas.initiateBuilderExit]
theorem initiateBuilderExit_run_eq [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run (pureState preState)
        = match preState.builders.val[builderIndex.toNat]? with
          | none => .error (.outOfBounds builderIndex.toNat preState.builders.size)
          | some _builder =>
              match (currentEpochOf (pureState preState) +
                    EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch) with
              | .ok we =>
                  .ok ((), pureState
                    { preState with builders :=
                        (preState.builders.set! builderIndex.toNat
                          { preState.builders[builderIndex.toNat]! with
                            withdrawableEpoch := we }) })
              | .error f => .error (StateTransitionError.ofArithFault f) := by
  intro preState builderIndex
  unfold initiateBuilderExit sszGetIdx IdxRead.get? IdxRead.size
  rw [run_bind,
    show ((get : GloasRun (SizzLean.Cache.SSZ.Box HasherTag.H BeaconState)).run (pureState preState))
      = .ok (pureState preState, pureState preState) from rfl,
    except_bind_ok]
  simp only [view_uncachedBox]
  cases hx : preState.builders.val[builderIndex.toNat]? with
  | none =>
    simp
    rfl
  | some _builder =>
    rw [bind_liftErr_ok]
    cases hx2 : (currentEpochOf (pureState preState) +
        EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch) with
    | ok we =>
      rw [run_bind,
        show ((liftM (Except.ok we : Checked Epoch) : GloasRun Epoch).run (pureState preState))
          = .ok (we, pureState preState) from rfl,
        except_bind_ok]
      rfl
    | error f =>
      rw [run_bind,
        show ((liftM (Except.error f : Checked Epoch) : GloasRun Epoch).run (pureState preState))
          = .error (StateTransitionError.ofArithFault f) from rfl,
        except_bind_error]

/-- **In range.** Under the sum's no-overflow bound, running
`initiateBuilderExit builderIndex` never rejects, and the written builder reads back with
`withdrawableEpoch` set to the checked sum's value, which the law library reads back as
the plain `Nat` sum, while every other builder and the registry's `.size` are unchanged.
The index-level reading of `initiateBuilderExit_run_eq` through `ProgressiveList.set!`'s
own lemmas. -/
theorem initiateBuilderExit_run_inRange [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      (currentEpochOf (pureState preState)).toPlainNat
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat < UInt64.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ ∃ we : Epoch,
            (currentEpochOf (pureState preState) +
                EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch)
              = .ok we
            ∧ we.toPlainNat = (currentEpochOf (pureState preState)).toPlainNat
                + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat
            ∧ postState.builders[builderIndex.toNat]!
                = { preState.builders[builderIndex.toNat]! with withdrawableEpoch := we }
            ∧ (∀ j : Nat, j ≠ builderIndex.toNat →
                  postState.builders[j]! = preState.builders[j]!)
            ∧ postState.builders.size = preState.builders.size := by
  intro preState builderIndex hidx hbound
  have hex : ∃ we, (currentEpochOf (pureState preState) +
      EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay : Checked Epoch) = .ok we :=
    add_ok_iff _ _ |>.mpr hbound
  obtain ⟨we, hwe⟩ := hex
  refine ⟨({ preState with builders :=
      (preState.builders.set! builderIndex.toNat
        { preState.builders[builderIndex.toNat]! with withdrawableEpoch := we }) }),
    ?_, we, hwe, add_value _ _ _ hwe, ?_, fun j hj => ?_, ?_⟩
  · rw [runPure_eq, initiateBuilderExit_run_eq preState builderIndex,
      progList_getElem?_eq_getElem! preState.builders builderIndex.toNat hidx, hwe]
    simp only [Except.map, view_uncachedBox]
  · exact progressiveListSet!_getElem!_self _ _ _ hidx
  · exact progressiveListSet!_getElem!_ne _ _ _ _ (Ne.symm hj)
  · exact progressiveListSet!_size _ _ _

/-- **Out of range.** The raising read rejects before the withdrawability sum runs: past the
registry's end the run rejects with the `.outOfBounds` fault, the `IndexError` the pinned
Python read `state.builders[builder_index]` raises, and no state is produced. -/
theorem initiateBuilderExit_run_outOfRange [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      ¬ builderIndex.toNat < preState.builders.size →
      runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
        = .error (.outOfBounds builderIndex.toNat preState.builders.size) := by
  intro preState builderIndex hidx
  rw [runPure_eq, initiateBuilderExit_run_eq preState builderIndex]
  have hnone : preState.builders.val[builderIndex.toNat]? = none := by
    rw [Array.getElem?_eq_none_iff]
    exact Nat.le_of_not_lt hidx
  rw [hnone]
  rfl

/-! ## Generic conditional no-wrap

`Epoch` is the checked kind, so the withdrawability sum raises past `2 ^ 64 - 1` where
the pre-migration body wrapped. No generic invariant relates the bounded current epoch
to the independently configurable withdrawal delay (a `[Config]` instance is free to set
`minBuilderWithdrawabilityDelay` arbitrarily), so the no-wrap fact is necessarily
**conditional**. Its condition is the bound `initiateBuilderExit_run_inRange` carries,
a hypothesis the caller must establish elsewhere, say from a slot/epoch bound on
`mainnet`, since the function itself carries no run-time guard. -/

/-- **Function-level corollary.** Chaining `initiateBuilderExit_run_inRange` with the
law library's value lemma: under the epoch-bound hypothesis (read from the *pre*-state's
`currentEpochOf`, as in the unconditional in-range theorem), the post-state builder's
`withdrawableEpoch.toPlainNat` is exactly the natural-number sum
`currentEpochOf(pre-state).toPlainNat + MIN_BUILDER_WITHDRAWABILITY_DELAY.toPlainNat`,
with no silent wrap through `2 ^ 64`. -/
theorem initiateBuilderExit_run_inRange_no_wrap [Preset] [HasherTag] [Config] :
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      (currentEpochOf (pureState preState)).toPlainNat
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat < 2 ^ 64 →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toPlainNat
            = (currentEpochOf (pureState preState)).toPlainNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat := by
  intro preState builderIndex hidx hbound
  obtain ⟨postState, hrun, we, hwe, hwv, hview, -, -⟩ :=
    initiateBuilderExit_run_inRange preState builderIndex hidx
      (show (currentEpochOf (pureState preState)).toPlainNat
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat < UInt64.size
        from hbound)
  refine ⟨postState, hrun, ?_⟩
  have hwe' : postState.builders[builderIndex.toNat]!.withdrawableEpoch = we := by
    rw [hview]
  rw [hwe', hwv]

/-! ## Shipped preset/config pairs: unconditional

`initiateBuilderExit_run_inRange_no_wrap`'s `hbound` premise is conditional because a
`[Config]` instance is free, in general, to pick `minBuilderWithdrawabilityDelay` large
enough to make `currentEpochOf preState + minBuilderWithdrawabilityDelay` overflow
`2 ^ 64`. The two pairs the repository actually ships (the minimal and mainnet
preset/config pairs used by the shipped Gloas interfaces) don't: `slotsPerEpoch` bounds
`currentEpochOf preState` well below `2 ^ 64` for *any* `preState.slot : UInt64`, so the
sum with the concrete `minBuilderWithdrawabilityDelay` (`2` on minimal, `8192` on
mainnet) can never reach `2 ^ 64`.
Each corollary below discharges `hbound` from that arithmetic fact alone, with no epoch
or slot hypothesis from the caller, and reuses
`initiateBuilderExit_run_inRange_no_wrap` rather than re-deriving the state
transition. -/

/-- `currentEpochOf preState` is the slot's plain quotient by `SLOTS_PER_EPOCH`. The
one fact the preset corollaries need, stated at the checked kind through
`computeEpochAtSlot_toPlainNat`. -/
theorem currentEpochOf_toPlainNat [Preset] [HasherTag] (state : BeaconState) :
    (currentEpochOf (pureState state)).toPlainNat = state.slot.toPlainNat / Preset.slotsPerEpoch := by
  simp only [currentEpochOf, view_uncachedBox]
  exact computeEpochAtSlot_toPlainNat state.slot

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
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toPlainNat
            = (currentEpochOf (pureState preState)).toPlainNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat := by
  letI : Preset := minimal
  letI : Config := minimalConfig
  intro preState builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap minimal _ minimalConfig preState
    builderIndex hidx ?_
  -- `toPlainNat` is the underlying word's `toNat`, so the word lemma gives the bound.
  have hslot : preState.slot.toPlainNat < 18446744073709551616 :=
    UInt64.toNat_lt preState.slot.val
  have hspe : (@Preset.slotsPerEpoch minimal : Nat) = 8 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay minimalConfig).toPlainNat = 2 := rfl
  rw [currentEpochOf_toPlainNat, hspe, hdelay]
  show preState.slot.toPlainNat / 8 + 2 < 18446744073709551616
  omega

/-- **Mainnet preset/config (`mainnet`, `mainnetConfig`), unconditional.**
`slotsPerEpoch = 32`, `minBuilderWithdrawabilityDelay = 64`:
`currentEpochOf preState ≤ (2 ^ 64 - 1) / 32`, so the sum with `64` is nowhere near
`2 ^ 64`, for every `preState`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_mainnet [HasherTag] :
    letI : Preset := mainnet
    letI : Config := mainnetConfig
    ∀ (preState : BeaconState) (builderIndex : BuilderIndex),
      builderIndex.toNat < preState.builders.size →
      ∃ postState : BeaconState,
        runPure (initiateBuilderExit (StateTransition := GloasRun) builderIndex) preState
            = .ok ((), postState)
        ∧ postState.builders[builderIndex.toNat]!.withdrawableEpoch.toPlainNat
            = (currentEpochOf (pureState preState)).toPlainNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toPlainNat := by
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  intro preState builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap mainnet _ mainnetConfig preState
    builderIndex hidx ?_
  -- `toPlainNat` is the underlying word's `toNat`, so the word lemma gives the bound.
  have hslot : preState.slot.toPlainNat < 18446744073709551616 :=
    UInt64.toNat_lt preState.slot.val
  have hspe : (@Preset.slotsPerEpoch mainnet : Nat) = 32 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay mainnetConfig).toPlainNat = 64 := rfl
  rw [currentEpochOf_toPlainNat, hspe, hdelay]
  show preState.slot.toPlainNat / 32 + 64 < 18446744073709551616
  omega

end EthCLSpecs.Proofs.Gloas
