import EthCLSpecs.Fulu.Time
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Proofs.Fulu.Time`: the slot and epoch conversions

This module covers two spec functions, `compute_epoch_at_slot`
(`phase0/beacon-chain.md:908`) and `compute_start_slot_at_epoch` (`:918`), and the relation
between them.

`computeEpochAtSlot` divides. It cannot fault. `computeStartSlotAtEpoch` multiplies, and the
multiply can fault: remerkleable re-runs the bound check on the product and raises
`ValueError` above `2 ^ 64`.

The round trip needs a bound, and that bound depends on the preset. The theorem therefore takes
the bound as a hypothesis, and a corollary closes it at each shipped preset.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag StateTransitionError checkedMul)
open EthCLSpecs.Fulu (Preset computeEpochAtSlot computeStartSlotAtEpoch minimal mainnet)

/-- `compute_epoch_at_slot` never decreases as the slot grows. It divides a `uint64` by a
positive constant, so it is a total function and it is monotone in the dividend. The proof needs
no preset bound, only `slotsPerEpochPos` for the divisor. -/
theorem computeEpochAtSlot_monotone [Preset] :
    ∀ s₁ s₂ : UInt64, s₁ ≤ s₂ → computeEpochAtSlot s₁ ≤ computeEpochAtSlot s₂ := by
  intro s₁ s₂ h
  -- `UInt64.le_iff_toNat_le` is definitional, so the order goal moves to `Nat` by rewriting
  -- alone; `Nat.div_le_div_right` then takes the reflected hypothesis.
  simp only [computeEpochAtSlot, UInt64.le_iff_toNat_le, UInt64.toNat_div]
  exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp h)

/-- The divisor's `toNat` is `SLOTS_PER_EPOCH` itself. `UInt64.ofNat` only wraps above
`2 ^ 64`, and `slotsPerEpochLt` puts the constant below it at every preset. -/
private theorem toNat_ofNat_slotsPerEpoch [Preset] :
    (UInt64.ofNat Fulu.Const.slotsPerEpoch).toNat = Fulu.Const.slotsPerEpoch := by
  simp [Nat.mod_eq_of_lt Fulu.Const.slotsPerEpochLt]

/-- The multiply succeeds, and its result is the raw `uint64` product, whenever the `Nat`
product stays below `2 ^ 64`.

`checkedMul`'s guard is `a != 0 && a * b / a != b`. A zero epoch fails the first conjunct. A
non-zero one recovers the divisor exactly, because the product did not wrap. Both theorems
below reach `compute_start_slot_at_epoch` through this lemma; they differ only in where the
bound comes from. -/
private theorem computeStartSlotAtEpoch_eq_ok [Preset] (e : UInt64)
    (h : e.toNat * Fulu.Const.slotsPerEpoch < 2 ^ 64) :
    (computeStartSlotAtEpoch e : Except StateTransitionError UInt64)
      = .ok (e * UInt64.ofNat Fulu.Const.slotsPerEpoch) := by
  have hn := toNat_ofNat_slotsPerEpoch
  have hguard :
      (e != 0 && e * UInt64.ofNat Fulu.Const.slotsPerEpoch / e !=
        UInt64.ofNat Fulu.Const.slotsPerEpoch) = false := by
    rcases Nat.eq_zero_or_pos e.toNat with hz | hz
    · have hzero : e = 0 := UInt64.toNat_inj.mp (by simp [hz])
      simp [hzero]
    · have hrecover :
          e * UInt64.ofNat Fulu.Const.slotsPerEpoch / e
            = UInt64.ofNat Fulu.Const.slotsPerEpoch := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_div, UInt64.toNat_mul, hn, Nat.mod_eq_of_lt h]
        exact Nat.mul_div_cancel_left _ hz
      simp [hrecover]
  simp only [computeStartSlotAtEpoch, checkedMul]
  rw [hguard]
  rfl

/-- The same fact with a weaker hypothesis, so a bounded epoch is enough.

`compute_start_slot_at_epoch` cannot fault on any epoch at or below a `compute_epoch_at_slot`
result, because the product only grows with the epoch. The call sites use this form. It
subsumes `computeStartSlotAtEpoch_computeEpochAtSlot_isOk` below at `e = computeEpochAtSlot s`.

The `r ≤ s` conjunct is the bound that the `slot - epochFirstSlot` subtraction in
`onTickPerSlot` needs to rule out an underflow. -/
theorem computeStartSlotAtEpoch_isOk_of_le [Preset] :
    ∀ (e s : UInt64), e ≤ computeEpochAtSlot s →
      ∃ r : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok r ∧ r ≤ s := by
  intro e s h
  have hn := toNat_ofNat_slotsPerEpoch
  have he : e.toNat ≤ s.toNat / Fulu.Const.slotsPerEpoch := by
    have hle := UInt64.le_iff_toNat_le.mp h
    simpa [computeEpochAtSlot, UInt64.toNat_div, hn] using hle
  -- `(s / n) * n ≤ s` is the whole content: the product cannot leave the range the slot is in.
  have hbound : e.toNat * Fulu.Const.slotsPerEpoch ≤ s.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ he) (Nat.div_mul_le_self _ _)
  have hprod : e.toNat * Fulu.Const.slotsPerEpoch < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hbound (UInt64.toNat_lt s)
  refine ⟨e * UInt64.ofNat Fulu.Const.slotsPerEpoch, computeStartSlotAtEpoch_eq_ok e hprod, ?_⟩
  rw [UInt64.le_iff_toNat_le]
  simp only [UInt64.toNat_mul, hn, Nat.mod_eq_of_lt hprod]
  exact hbound

/-- `compute_start_slot_at_epoch` cannot fault on an epoch that `compute_epoch_at_slot` produced.

`(s / n) * n ≤ s < 2 ^ 64` for every `n`, so the product stays in range at any value of
`SLOTS_PER_EPOCH`. The statement quantifies over every slot, so it needs no bound hypothesis.

The `r ≤ s` conjunct is the bound that the `slot - epochFirstSlot` subtraction in
`onTickPerSlot` needs to rule out an underflow. -/
theorem computeStartSlotAtEpoch_computeEpochAtSlot_isOk [Preset] :
    ∀ s : UInt64, ∃ r : UInt64,
      (computeStartSlotAtEpoch (computeEpochAtSlot s) : Except StateTransitionError UInt64)
        = .ok r ∧ r ≤ s :=
  fun s => computeStartSlotAtEpoch_isOk_of_le _ s (Nat.le_refl _)

/-- `compute_epoch_at_slot ∘ compute_start_slot_at_epoch = id`, under the bound that keeps the
multiply in range.

The bound stays a hypothesis because `SLOTS_PER_EPOCH` is a `Preset` field
(`Fulu/Constants.lean`), and a `[Preset]` may carry any value. The two shipped presets
discharge it below. -/
@[characterizes computeStartSlotAtEpoch]
theorem computeEpochAtSlot_computeStartSlotAtEpoch [Preset] :
    ∀ e : UInt64, e.toNat * EthCLSpecs.Fulu.Const.slotsPerEpoch < 2 ^ 64 →
      ∃ s : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok s ∧
          computeEpochAtSlot s = e := by
  intro e h
  have hn := toNat_ofNat_slotsPerEpoch
  refine ⟨e * UInt64.ofNat Fulu.Const.slotsPerEpoch, computeStartSlotAtEpoch_eq_ok e h, ?_⟩
  -- The division recovers the epoch exactly: the product did not wrap, and the divisor is
  -- positive, so `Nat.mul_div_cancel` applies under `toNat`.
  apply UInt64.toNat_inj.mp
  simp only [computeEpochAtSlot, UInt64.toNat_div, UInt64.toNat_mul, hn, Nat.mod_eq_of_lt h]
  exact Nat.mul_div_cancel _ Fulu.Const.slotsPerEpochPos

/-- The round trip at the minimal preset. `SLOTS_PER_EPOCH` is `8` (`Fulu/Constants.lean`), so
every epoch below `2 ^ 61` round-trips. -/
theorem computeEpochAtSlot_computeStartSlotAtEpoch_minimal :
    letI : Preset := minimal
    ∀ e : UInt64, e.toNat < 2 ^ 61 →
      ∃ s : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok s ∧
          computeEpochAtSlot s = e := by
  letI : Preset := minimal
  intro e h
  refine @computeEpochAtSlot_computeStartSlotAtEpoch minimal e ?_
  have hspe : (@Fulu.Const.slotsPerEpoch minimal) = 8 := rfl
  rw [hspe]
  omega

/-- The round trip at the mainnet preset. `SLOTS_PER_EPOCH` is `32` (`Fulu/Constants.lean`), so
the ceiling is `2 ^ 59`. -/
theorem computeEpochAtSlot_computeStartSlotAtEpoch_mainnet :
    letI : Preset := mainnet
    ∀ e : UInt64, e.toNat < 2 ^ 59 →
      ∃ s : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok s ∧
          computeEpochAtSlot s = e := by
  letI : Preset := mainnet
  intro e h
  refine @computeEpochAtSlot_computeStartSlotAtEpoch mainnet e ?_
  have hspe : (@Fulu.Const.slotsPerEpoch mainnet) = 32 := rfl
  rw [hspe]
  omega

end EthCLSpecs.Proofs.Fulu
