import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Proofs.Support

/-!
# `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded PTC window's two regions

`EthCLSpecs.Gloas.initializePtcWindow` (`Gloas/Upgrade.lean`) builds the
Fulu → Gloas fork transition's cached `ptcWindow` as one `Vector.ofFnM` over
`Fin (3 * SLOTS_PER_EPOCH)`, branching on whether the index falls in the empty
first epoch or the remaining two SLOTS_PER_EPOCH regions. The build runs in
`Except`, because `compute_start_slot_at_epoch` multiplies through `checkedMul`.
`initializePtcWindow_eq_ok` collapses that layer to the pure `Vector.ofFn` once,
and the three region theorems read their `getElem` fact off it.

This file names **both** forks, the sanctioned exception to the one-fork rule for
proofs: its subject is boundary code, which converts a Fulu pre-state into a Gloas
window, so the statements mention `Fulu.State` and Fulu's committee helpers
alongside Gloas's constants. `open scoped EthCLSpecs.Gloas.Downgrade` supplies the
`Gloas.Preset → Fulu.Preset` bridge that lets a single `[Preset]` binder carry
both sides, the same bridge `Gloas/Upgrade.lean` itself opens.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError checkedMul)
open EthCLSpecs.Gloas (Preset initializePtcWindow computePtcFromFulu)
open EthCLSpecs.Fulu (computeStartSlotAtEpoch currentEpochOf)
open EthCLSpecs.Proofs.Support (ofFnM_eq_ok_ofFn)
open scoped EthCLSpecs.Gloas.Downgrade

/-- The window's largest epoch is `currentEpochOf state + 1`. The offset `k` stays below
`2 * SLOTS_PER_EPOCH` and contributes `k / SLOTS_PER_EPOCH`, which is `0` or `1`. The two
populated regions are the current epoch and the epoch after it. Under this bound the
`compute_start_slot_at_epoch` multiply cannot fault anywhere in the window.

The slot-derived call sites need no such bound. This one does. Its epoch comes from adding to a
state field, so the fault is reachable at an extreme `state.slot`. -/
abbrev PtcWindowInRange [Preset] [HasherTag] (state : Fulu.State) : Prop :=
  ((Fulu.currentEpochOf state).toNat + 1) * Gloas.Const.slotsPerEpoch < 2 ^ 64

/-- The epoch-start multiply succeeds at every epoch the window reaches. `k` is the epoch
delta, `0` or `1`, and the product stays below `2 ^ 64` under the window's range bound. -/
private theorem startSlot_eq_ok [Preset] [HasherTag] (state : Fulu.State)
    (h : PtcWindowInRange state) (k : Nat) (hk : k ≤ 1) :
    computeStartSlotAtEpoch (currentEpochOf state + UInt64.ofNat k)
      = (.ok ((currentEpochOf state + UInt64.ofNat k) *
          UInt64.ofNat Gloas.Const.slotsPerEpoch) : Except StateTransitionError UInt64) := by
  have hpos : 0 < Gloas.Const.slotsPerEpoch := Gloas.Const.slotsPerEpochPos
  have hlt : Gloas.Const.slotsPerEpoch < 2 ^ 64 := Gloas.Const.slotsPerEpochLt
  -- `omega` reasons over numerals, so give it `2 ^ 64` evaluated once.
  have hsize : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  -- The divisor's `toNat` is `SLOTS_PER_EPOCH` itself: `ofNat` only wraps above `2 ^ 64`.
  have hn : (UInt64.ofNat Gloas.Const.slotsPerEpoch).toNat = Gloas.Const.slotsPerEpoch := by
    simp [Nat.mod_eq_of_lt hlt]
  -- `currentEpochOf state + 1` is itself below `2 ^ 64`, so the epoch add cannot wrap.
  have hc : (currentEpochOf state).toNat + 1 < 18446744073709551616 := by
    have := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpos) h
    omega
  have hkn : (UInt64.ofNat k).toNat = k := by
    simp [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  have hek : (currentEpochOf state).toNat + k < 2 ^ 64 := by omega
  have he : (currentEpochOf state + UInt64.ofNat k).toNat = (currentEpochOf state).toNat + k := by
    simp [UInt64.toNat_add, hkn, Nat.mod_eq_of_lt hek]
  -- The product is bounded by the window's own bound, so the `uint64` multiply does not wrap.
  have hprod : ((currentEpochOf state).toNat + k) * Gloas.Const.slotsPerEpoch < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) h
  -- The guard is `a != 0 && a * b / a != b`. It is false either way: a zero epoch fails the
  -- first conjunct, and a non-zero one recovers the divisor exactly.
  have hguard :
      ((currentEpochOf state + UInt64.ofNat k) != 0 &&
        (currentEpochOf state + UInt64.ofNat k) * UInt64.ofNat Gloas.Const.slotsPerEpoch /
            (currentEpochOf state + UInt64.ofNat k) !=
          UInt64.ofNat Gloas.Const.slotsPerEpoch) = false := by
    rcases Nat.eq_zero_or_pos ((currentEpochOf state).toNat + k) with hz | hz
    · have hzero : currentEpochOf state + UInt64.ofNat k = 0 := by
        apply UInt64.toNat_inj.mp; simp [he, hz]
      simp [hzero]
    · have hrecover :
          (currentEpochOf state + UInt64.ofNat k) * UInt64.ofNat Gloas.Const.slotsPerEpoch /
              (currentEpochOf state + UInt64.ofNat k)
            = UInt64.ofNat Gloas.Const.slotsPerEpoch := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_div, UInt64.toNat_mul, he, hn, Nat.mod_eq_of_lt hprod]
        exact Nat.mul_div_cancel_left _ hz
      simp [hrecover]
  -- The two forks' `SLOTS_PER_EPOCH` are the same constant through the `Downgrade` bridge;
  -- the helper's body names Fulu's, the statement names Gloas's.
  have hspe : Fulu.Const.slotsPerEpoch = Gloas.Const.slotsPerEpoch := rfl
  simp only [computeStartSlotAtEpoch, checkedMul, hspe]
  rw [hguard]
  rfl

/-- Under the window's range bound, the whole build succeeds and agrees with the pure
`Vector.ofFn` of the same values. Every theorem below reads its `getElem` fact off this, so the
`Except` layer unfolds once instead of three times. -/
theorem initializePtcWindow_eq_ok [Preset] [HasherTag] (state : Fulu.State)
    (h : PtcWindowInRange state) :
    initializePtcWindow state = .ok (Vector.ofFn fun i : Fin (3 * Gloas.Const.slotsPerEpoch) =>
      if i.val < Gloas.Const.slotsPerEpoch then Vector.replicate Gloas.Const.ptcSize 0
      else
        let k := i.val - Gloas.Const.slotsPerEpoch
        computePtcFromFulu state
          ((currentEpochOf state + UInt64.ofNat (k / Gloas.Const.slotsPerEpoch)) *
              UInt64.ofNat Gloas.Const.slotsPerEpoch +
            UInt64.ofNat (k % Gloas.Const.slotsPerEpoch))) := by
  have hpos : 0 < Gloas.Const.slotsPerEpoch := Gloas.Const.slotsPerEpochPos
  unfold initializePtcWindow
  apply ofFnM_eq_ok_ofFn
  intro i
  by_cases hi : i.val < Gloas.Const.slotsPerEpoch
  · simp only [if_pos hi]
    rfl
  · -- The offset stays below `2 * SLOTS_PER_EPOCH`, so its epoch delta is `0` or `1`.
    have hk : (i.val - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch ≤ 1 := by
      have hi3 := i.isLt
      have hlt2 : i.val - Gloas.Const.slotsPerEpoch < Gloas.Const.slotsPerEpoch * 2 := by omega
      have := Nat.div_lt_of_lt_mul hlt2
      omega
    simp only [if_neg hi, startSlot_eq_ok state h _ hk]
    rfl

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous
epoch", empty because the pre-fork Fulu state carries no PTC) are the all-zero
committee, `initialize_ptc_window`'s `emptyCommittee`.

`PtcWindowInRange` rules out the `compute_start_slot_at_epoch` fault in the
window's populated regions, so the build succeeds and the entry exists. -/
theorem initializePtcWindow_lt [Preset] [HasherTag] :
    ∀ (state : Fulu.State) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      PtcWindowInRange state →
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow state).map (·[i]) = .ok (Vector.replicate Gloas.Const.ptcSize 0) := by
  intro state i hRange h
  simp [initializePtcWindow_eq_ok state hRange, Except.map, h]

/-- The window's remaining `2 * SLOTS_PER_EPOCH` entries (the current epoch and
the one after it) are `computePtcFromFulu` evaluated at the slot
`initialize_ptc_window` computes for that offset: split the offset
`k := i - SLOTS_PER_EPOCH` into an epoch delta (`k / SLOTS_PER_EPOCH`) and an
intra-epoch slot offset (`k % SLOTS_PER_EPOCH`), exactly as the definition
does, rather than the collapsed `startSlot(currentEpoch) + k` form (which
would need a `UInt64` no-overflow side condition this statement doesn't
carry).

`PtcWindowInRange` rules out the `compute_start_slot_at_epoch` fault at every
offset, so the build succeeds and the entry exists. -/
theorem initializePtcWindow_ge [Preset] [HasherTag] :
    ∀ (state : Fulu.State) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      PtcWindowInRange state →
      Gloas.Const.slotsPerEpoch ≤ i.val →
      (initializePtcWindow state).map (·[i]) = .ok (
        let k := i.val - Gloas.Const.slotsPerEpoch
        computePtcFromFulu state
          ((currentEpochOf state + UInt64.ofNat (k / Gloas.Const.slotsPerEpoch)) *
              UInt64.ofNat Gloas.Const.slotsPerEpoch +
            UInt64.ofNat (k % Gloas.Const.slotsPerEpoch))) := by
  intro state i hRange h
  simp [initializePtcWindow_eq_ok state hRange, Except.map, Nat.not_lt.mpr h]

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Gloas.Const.ptcSize` (`ValidatorIndex := UInt64`'s
`default` is `0`, and `Vector`'s `Inhabited` instance is pointwise), so callers
that already reason in terms of `default` don't need to unfold
`initializePtcWindow` a second time to get there.

It carries the same `PtcWindowInRange` bound as the theorem it reads from. -/
theorem initializePtcWindow_lt_default [Preset] [HasherTag] :
    ∀ (state : Fulu.State) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      PtcWindowInRange state →
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow state).map (·[i]) = .ok default := by
  intro state i hRange h
  exact initializePtcWindow_lt state i hRange h

end EthCLSpecs.Proofs.Gloas
