import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded PTC window's two regions

`EthCLSpecs.Gloas.initializePtcWindow` (`Gloas/Operations.lean`) builds the cached
`ptcWindow` the Fulu → Gloas upgrade seeds, as one `Vector.ofFn` over
`Fin (3 * SLOTS_PER_EPOCH)`, branching on whether the index falls in the empty first epoch
or the remaining two `SLOTS_PER_EPOCH` regions. `initializePtcWindow_run_eq` is the whole
contract, the complete `.run` equation over the window: the run rejects with the
`.arithmetic` fault exactly at `current_epoch = UINT64_MAX`, the one value where the spec's
checked `current_epoch + e` overflows, and on every other state it returns the window as one
pure value with the state unchanged. `initializePtcWindow_lt` / `initializePtcWindow_ge`
read the two regions off that equation's success branch under the no-overflow hypothesis,
`initializePtcWindow_getElem` joins them at the element level, and
`initializePtcWindow_lt_default` restates the first region as the ambient `default`.
`initializePtcWindow_run_eq` carries the `@[characterizes]` tag. No induction, no
`native_decide`, no mathlib.

At v1.7.0-beta.4 `upgrade_to_gloas` computes the window over the Gloas post-state with
Gloas's own `compute_ptc` (`completeUpgradeToGloas` runs it), so the subject is an ordinary
Gloas `forkdef` over a Gloas state; alpha.12 computed it over the Fulu pre-state, which made
this file boundary code naming both forks. Statements bind plain `Gloas.BeaconState` values;
the window's builder runs on `pureState state` at `GloasRun`, so the contract is stated at
the box in `.run` form, the shape the fork-choice bridge consumes.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError checkedAdd)
open EthCLSpecs.Gloas.Const (slotsPerEpochPos)
open EthCLSpecs.Gloas (Preset Config BeaconState ValidatorIndex initializePtcWindow computePtc
  computeStartSlotAtEpoch currentEpochOf)
open EthCLLib.Proofs (pureState run_bind run_pure except_bind_ok except_bind_error
  throwArithmetic_run)

/-- The unsigned carry test `checkedAdd` uses for `+ 1`: the sum wraps exactly at the top
of the range. Read at the `Nat` level underneath, since `UInt64`'s order is the `.toNat`
order and the `.toNat` of the sum is the sum mod `2 ^ 64`. -/
private theorem uint64_add_one_lt_iff_eq_max (a : UInt64) :
    a + 1 < a ↔ a = 0xffffffffffffffff := by
  have hmax : (0xffffffffffffffff : UInt64).toNat = 18446744073709551615 := rfl
  have hone : (1 : UInt64).toNat = 1 := rfl
  constructor
  · intro h
    have hbound : a.toNat < 18446744073709551616 := UInt64.toNat_lt_size (a := a)
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, hone] at h
    have hanat : a.toNat = 18446744073709551615 := by omega
    exact UInt64.toNat_inj.mp (by rw [hanat]; exact hmax.symm)
  · intro h
    rw [h, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, hone, hmax]
    omega

/-- **The window contract.** The complete `.run` equation of `initializePtcWindow`: the run
rejects with the `.arithmetic` fault exactly when the state's current epoch is `UINT64_MAX`,
where the spec's checked per-entry add `current_epoch + e` overflows (`e` is `1` for the
window's last `SLOTS_PER_EPOCH` entries), and on every other state it returns the window
over `pureState state` as one pure value with the state unchanged: the all-zero committee in
the first `SLOTS_PER_EPOCH` entries, and `compute_ptc` at the offset's slot in the remaining
`2 * SLOTS_PER_EPOCH`. Stated at the box in `.run` form, the shape the fork-choice bridge
consumes; the region theorems below read the success branch. -/
@[characterizes EthCLSpecs.Gloas.initializePtcWindow]
theorem initializePtcWindow_run_eq [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState),
      (initializePtcWindow (StateTransition := GloasRun) (pureState state)).run (pureState state) =
        if currentEpochOf (pureState state) = 0xffffffffffffffff then
          .error (.arithmetic "initialize_ptc_window: current_epoch + e")
        else
          .ok (Vector.ofFn fun i : Fin (3 * Gloas.Const.slotsPerEpoch) =>
            if i.val < Gloas.Const.slotsPerEpoch then Vector.replicate Gloas.Const.ptcSize 0
            else computePtc (pureState state)
              (computeStartSlotAtEpoch (currentEpochOf (pureState state) +
                  UInt64.ofNat ((i.val - Gloas.Const.slotsPerEpoch) /
                    Gloas.Const.slotsPerEpoch)) +
                UInt64.ofNat ((i.val - Gloas.Const.slotsPerEpoch) %
                  Gloas.Const.slotsPerEpoch)),
            pureState state) := by
  intro state
  simp only [← uint64_add_one_lt_iff_eq_max]
  unfold initializePtcWindow
  simp only [checkedAdd]
  -- `current_epoch + 0` cannot wrap, so the first checked add always takes its pure branch.
  by_cases hc0 : currentEpochOf (pureState state) + 0 < currentEpochOf (pureState state)
  · exact absurd hc0 (by simp)
  rw [ite_eq_right hc0, run_bind, run_pure, except_bind_ok]
  simp only []
  -- The second add is the delta-`1` sum; it wraps exactly at the top of the range.
  by_cases hwrap : currentEpochOf (pureState state) + 1 < currentEpochOf (pureState state)
  · rw [ite_eq_left hwrap, ite_eq_left hwrap, run_bind, throwArithmetic_run]
    exact except_bind_error _ _
  · rw [ite_eq_right hwrap, ite_eq_right hwrap, run_bind, run_pure, except_bind_ok, run_pure]
    simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
    refine Vector.ext fun j hj => ?_
    simp only [Vector.getElem_ofFn hj]
    split
    · simp
    · have hSPE : 0 < Gloas.Const.slotsPerEpoch := slotsPerEpochPos
      have hk : j - Gloas.Const.slotsPerEpoch < 2 * Gloas.Const.slotsPerEpoch := by omega
      have hd : (j - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch < 2 := by
        rw [Nat.div_lt_iff_lt_mul hSPE]
        omega
      rcases Nat.eq_zero_or_pos ((j - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch) with
        hzero | hpos
      · have hd0 : (j - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch = 0 := by omega
        simp [hd0]
      · have hd1 : (j - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch = 1 := by omega
        simp [hd1]

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous epoch", empty
because the pre-fork state carries no Gloas PTC) are the all-zero committee,
`initialize_ptc_window`'s `empty_previous_epoch`. The no-overflow hypothesis guards the run
as a whole; the region itself involves no arithmetic. -/
theorem initializePtcWindow_lt [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      currentEpochOf (pureState state) ≠ 0xffffffffffffffff →
      i.val < Gloas.Const.slotsPerEpoch →
      ((initializePtcWindow (StateTransition := GloasRun) (pureState state)).run
          (pureState state)).map (fun p => p.1[i])
        = .ok (Vector.replicate Gloas.Const.ptcSize 0) := by
  intro state i hmax h
  rw [initializePtcWindow_run_eq, ite_eq_right hmax]
  simp [Except.map, h]

/-- The window's remaining `2 * SLOTS_PER_EPOCH` entries (the current epoch and the one
after it) are `compute_ptc` evaluated at the slot `initialize_ptc_window` computes for that
offset: split the offset `k := i - SLOTS_PER_EPOCH` into an epoch delta
(`k / SLOTS_PER_EPOCH`) and an intra-epoch slot offset (`k % SLOTS_PER_EPOCH`), exactly as
the composed contract does. The no-overflow hypothesis is what keeps the delta-`1` add
inside the `uint64` range. -/
theorem initializePtcWindow_ge [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      currentEpochOf (pureState state) ≠ 0xffffffffffffffff →
      Gloas.Const.slotsPerEpoch ≤ i.val →
      ((initializePtcWindow (StateTransition := GloasRun) (pureState state)).run
          (pureState state)).map (fun p => p.1[i])
        = .ok (computePtc (pureState state)
            (computeStartSlotAtEpoch (currentEpochOf (pureState state) +
                UInt64.ofNat ((i.val - Gloas.Const.slotsPerEpoch) /
                  Gloas.Const.slotsPerEpoch)) +
              UInt64.ofNat ((i.val - Gloas.Const.slotsPerEpoch) %
                Gloas.Const.slotsPerEpoch))) := by
  intro state i hmax h
  rw [initializePtcWindow_run_eq, ite_eq_right hmax]
  simp [Except.map, Nat.not_lt.mpr h]

/-- The element-level join of the two regions: under the no-overflow hypothesis every entry
of the seeded window is the all-zero committee in the first `SLOTS_PER_EPOCH` entries and
`compute_ptc` at the offset's slot in the remaining `2 * SLOTS_PER_EPOCH`. The run equation
above is the whole contract, error branch included; this is its element reading. -/
theorem initializePtcWindow_getElem [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      currentEpochOf (pureState state) ≠ 0xffffffffffffffff →
      ((initializePtcWindow (StateTransition := GloasRun) (pureState state)).run
          (pureState state)).map (fun p => p.1[i])
        = .ok (if i.val < Gloas.Const.slotsPerEpoch then
            Vector.replicate Gloas.Const.ptcSize 0
          else computePtc (pureState state)
            (computeStartSlotAtEpoch (currentEpochOf (pureState state) +
                UInt64.ofNat ((i.val - Gloas.Const.slotsPerEpoch) /
                  Gloas.Const.slotsPerEpoch)) +
              UInt64.ofNat ((i.val - Gloas.Const.slotsPerEpoch) %
                Gloas.Const.slotsPerEpoch))) := by
  intro state i hmax
  rw [initializePtcWindow_run_eq, ite_eq_right hmax]
  by_cases hlt : i.val < Gloas.Const.slotsPerEpoch
  · simp [Except.map, hlt]
  · simp [Except.map, hlt]

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Gloas.Const.ptcSize` (`ValidatorIndex := UInt64`'s `default` is `0`,
and `Vector`'s `Inhabited` instance is pointwise), so callers that already reason in terms of
`default` don't need to unfold the window a second time to get there. -/
theorem initializePtcWindow_lt_default [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      currentEpochOf (pureState state) ≠ 0xffffffffffffffff →
      i.val < Gloas.Const.slotsPerEpoch →
      ((initializePtcWindow (StateTransition := GloasRun) (pureState state)).run
          (pureState state)).map (fun p => p.1[i])
        = .ok default := by
  intro state i hmax h
  rw [initializePtcWindow_lt state i hmax h]
  rfl

end EthCLSpecs.Proofs.Gloas
