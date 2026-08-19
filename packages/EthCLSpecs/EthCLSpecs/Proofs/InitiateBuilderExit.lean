import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Run
import SizzLean.Proofs.SSZListSet

/-!
# `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit`'s effect on the builder registry

`initiateBuilderExit_run_eq` is the whole-transition equation (the run equals the
source-level `sszModify` on `builders`). `initiateBuilderExit_run_builders` projects it
onto the builder registry as a single `SSZList.set!`, and holds for every index. The
in-range and out-of-range theorems read that one equation through
`SizzLean.Proofs.SSZListSet`.

Postconditions on the registry are stated through `sszGet`, the *observable* read. The
cached (`TreeBacked`) and uncached flavours of `State` agree observationally while
differing structurally, so an out-of-range run has to be framed as agreement on
`sszGet builders` and cannot be claimed as `state' = state`.

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

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas (Preset Config BuilderIndex Epoch)
open EthCLSpecs.Gloas (minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Gloas (initiateBuilderExit State currentEpochOf)
open SizzLean.Proofs (sszListSet!_size sszListSet!_getElem!_self sszListSet!_getElem!_ne
  sszListSet!_eq_of_size_le)
open SizzLean.Repr
open SizzLean.Cache

/-! ## The concrete-run theorems

`initiateBuilderExit_run_eq` is the whole-transition equation: the run equals
`.ok ((), _)` of the source-level `sszModify` on `builders`. `initiateBuilderExit_run_builders`
projects that onto the registry, and the in-range / out-of-range theorems read the
projection through the `SSZList.set!` lemmas. -/

/-- Exact whole-transition equation for `initiateBuilderExit`. The returned state
is the original state with only `builders[builderIndex.toNat]!` updated through
`sszModify`; every other top-level field is carried through. For an out-of-range
index the underlying list write is a no-op, although the cached representation
need not be structurally identical to the pre-state. -/
@[characterizes EthCLSpecs.Gloas.initiateBuilderExit]
theorem initiateBuilderExit_run_eq [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state =
        .ok ((), sszModify state builders[builderIndex.toNat]! as b =>
          { b with withdrawableEpoch :=
              currentEpochOf state + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay }) := by
  intro state builderIndex
  rfl

/-- **The registry effect, at every index.** The post-state's `builders` is the
pre-state's with one `SSZList.set!` applied, writing `currentEpochOf` read from the
*pre*-state (the `do`-block's `← get` runs before the write) plus
`MIN_BUILDER_WITHDRAWABILITY_DELAY`. No range hypothesis: `set!` is total, and past
the end it is the identity. The two theorems below read this equation through
`SSZList.set!`'s own lemmas, so the range split happens once, at the read. This
characterizes no other top-level `BeaconState` field. -/
theorem initiateBuilderExit_run_builders [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state
            = .ok ((), state')
        ∧ sszGet state' builders
            = (sszGet state builders).set! builderIndex.toNat
                { sszGet state builders[builderIndex.toNat]! with
                  withdrawableEpoch :=
                    currentEpochOf state
                      + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay } := by
  intro state builderIndex
  refine ⟨_, initiateBuilderExit_run_eq state builderIndex, ?_⟩
  -- `State` is `SSZ.Box`'s two-constructor sum; both flavours' `.view` reduce the
  -- emitted write to the same `SSZList.set!`.
  rcases state with t | t <;> rfl

/-- **In range.** Running `initiateBuilderExit builderIndex` never rejects, and
`builders[builderIndex.toNat]!.withdrawableEpoch` becomes the pre-state's
`currentEpochOf` plus `MIN_BUILDER_WITHDRAWABILITY_DELAY`, with every other builder and
the registry's `.size` unchanged. The index-level convenience form of
`initiateBuilderExit_run_builders`. -/
theorem initiateBuilderExit_run_inRange [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state
            = .ok ((), state')
        ∧ sszGet state' builders[builderIndex.toNat]!
            = { sszGet state builders[builderIndex.toNat]! with
                withdrawableEpoch :=
                  currentEpochOf state + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay }
        ∧ (∀ j : Nat, j ≠ builderIndex.toNat →
              sszGet state' builders[j]! = sszGet state builders[j]!)
        ∧ (sszGet state' builders).size = (sszGet state builders).size := by
  intro state builderIndex hidx
  obtain ⟨state', hrun, hbuilders⟩ := initiateBuilderExit_run_builders state builderIndex
  refine ⟨state', hrun, ?_, fun j hj => ?_, ?_⟩
  · rw [hbuilders]; exact sszListSet!_getElem!_self _ _ _ hidx
  · rw [hbuilders]; exact sszListSet!_getElem!_ne _ _ _ _ (Ne.symm hj)
  · rw [hbuilders]; exact sszListSet!_size _ _ _

/-- **Out of range.** Running `initiateBuilderExit builderIndex` still never rejects
(`[i]!` is total), and the whole observable registry is carried through unchanged: the
write is a genuine no-op at the `SSZList` level, so no read at any index, nor `.size`,
can tell the two states' registries apart. Stated as `sszGet` agreement because
`state' = state` is false for the cached flavour; see the module docstring. -/
theorem initiateBuilderExit_run_outOfRange [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      ¬ builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state
            = .ok ((), state')
        ∧ sszGet state' builders = sszGet state builders := by
  intro state builderIndex hidx
  obtain ⟨state', hrun, hbuilders⟩ := initiateBuilderExit_run_builders state builderIndex
  refine ⟨state', hrun, ?_⟩
  rw [hbuilders]
  exact sszListSet!_eq_of_size_le _ _ _ (Nat.le_of_not_lt hidx)

/-! ## Generic conditional no-overflow

`Epoch` is an alias for `UInt64`, so `epoch + Const.minBuilderWithdrawabilityDelay` is
`UInt64` addition, mod `2 ^ 64`. No generic invariant relates the bounded `UInt64`
current epoch to the independently configurable withdrawal delay (a `[Config]` instance
is free to set `minBuilderWithdrawabilityDelay` arbitrarily), so the no-wrap fact is
necessarily **conditional**. Its condition is a hypothesis the caller must establish
elsewhere, say from a slot/epoch bound on `mainnet`, since the function itself carries
no run-time guard. -/

/-- Core Lean's `UInt64.toNat_add` gives `(a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64`
unconditionally; under the stated bound, `Nat.mod_eq_of_lt` drops the `%` and the
`UInt64` sum's `.toNat` is exactly the `Nat` sum, with no wraparound. -/
private theorem epoch_add_minBuilderWithdrawabilityDelay_no_wrap [Config] {epoch : Epoch} :
    epoch.toNat + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64 →
      (epoch + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay).toNat
        = epoch.toNat + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  intro h
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- **Function-level corollary.** Chaining `initiateBuilderExit_run_inRange`'s
written-field equation with `epoch_add_minBuilderWithdrawabilityDelay_no_wrap`: under
the epoch-bound hypothesis (read from the *pre*-state's `currentEpochOf`, as in the
unconditional in-range theorem), the post-state builder's `withdrawableEpoch.toNat` is
exactly the natural-number sum `currentEpochOf(pre-state).toNat +
MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat`, with no silent wrap through `2 ^ 64`. -/
theorem initiateBuilderExit_run_inRange_no_wrap [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      (currentEpochOf state).toNat
          + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64 →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state
            = .ok ((), state')
        ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
            = (currentEpochOf state).toNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  intro state builderIndex hidx hbound
  obtain ⟨state', hrun, hview, -, -⟩ := initiateBuilderExit_run_inRange state builderIndex hidx
  exact ⟨state', hrun,
    by rw [hview]; exact epoch_add_minBuilderWithdrawabilityDelay_no_wrap hbound⟩

/-! ## Shipped preset/config pairs: unconditional

`initiateBuilderExit_run_inRange_no_wrap`'s `hbound` premise is conditional because a
`[Config]` instance is free, in general, to pick `minBuilderWithdrawabilityDelay` large
enough to make `currentEpochOf state + minBuilderWithdrawabilityDelay` overflow
`2 ^ 64`. The two pairs the repository actually ships (the minimal and mainnet
preset/config pairs used by the shipped Gloas interfaces) don't: `slotsPerEpoch` bounds
`currentEpochOf state` well below `2 ^ 64` for *any* `state.slot : UInt64`, so the sum
with the concrete `minBuilderWithdrawabilityDelay` (`2` on minimal, `8192` on mainnet)
can never reach `2 ^ 64`.
Each corollary below discharges `hbound` from that arithmetic fact alone, with no epoch
or slot hypothesis from the caller, and reuses
`initiateBuilderExit_run_inRange_no_wrap` rather than re-deriving the state
transition. -/

/-- **Minimal preset/config (`minimal`, `minimalConfig`), unconditional.**
`slotsPerEpoch = 8`, `minBuilderWithdrawabilityDelay = 2`:
`currentEpochOf state ≤ (2 ^ 64 - 1) / 8`, so the sum with `2` is nowhere near
`2 ^ 64`, for every `state`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_minimal [HasherTag] :
    letI : Preset := minimal
    letI : Config := minimalConfig
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state
            = .ok ((), state')
        ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
            = (currentEpochOf state).toNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  letI : Preset := minimal
  letI : Config := minimalConfig
  intro state builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap minimal _ minimalConfig state builderIndex hidx ?_
  have hslot := UInt64.toNat_lt (sszGet state slot)
  have hspe : (@Preset.slotsPerEpoch minimal : Nat) = 8 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay minimalConfig).toNat = 2 := rfl
  simp only [currentEpochOf, EthCLSpecs.Gloas.computeEpochAtSlot,
    EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay, EthCLSpecs.Gloas.Const.slotsPerEpoch,
    UInt64.toNat_div, UInt64.toNat_ofNat', hspe, hdelay, Nat.reducePow, Nat.reduceMod]
  omega

/-- **Mainnet preset/config (`mainnet`, `mainnetConfig`), unconditional.**
`slotsPerEpoch = 32`, `minBuilderWithdrawabilityDelay = 8192`:
`currentEpochOf state ≤ (2 ^ 64 - 1) / 32`, so the sum with `8192` is nowhere near
`2 ^ 64`, for every `state`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_mainnet [HasherTag] :
    letI : Preset := mainnet
    letI : Config := mainnetConfig
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := GloasRun) builderIndex).run state
            = .ok ((), state')
        ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
            = (currentEpochOf state).toNat
              + EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay.toNat := by
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  intro state builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap mainnet _ mainnetConfig state builderIndex hidx ?_
  have hslot := UInt64.toNat_lt (sszGet state slot)
  have hspe : (@Preset.slotsPerEpoch mainnet : Nat) = 32 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay mainnetConfig).toNat = 8192 := rfl
  simp only [currentEpochOf, EthCLSpecs.Gloas.computeEpochAtSlot,
    EthCLSpecs.Gloas.Const.minBuilderWithdrawabilityDelay, EthCLSpecs.Gloas.Const.slotsPerEpoch,
    UInt64.toNat_div, UInt64.toNat_ofNat', hspe, hdelay, Nat.reducePow, Nat.reduceMod]
  omega

end EthCLSpecs.Proofs
