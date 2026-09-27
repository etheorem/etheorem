import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Time

/-!
# `EthCLSpecs.Proofs.Heze.Time`: the slot and epoch conversions at Heze

Heze `inherit`s both conversions from Gloas. Each lands as a fresh constant that the Gloas
theorems do not describe.

The transfer chains one fork at a time. `Heze.Downgrade` reaches `Gloas.Preset` and stops
there, so Lean cannot synthesize `Fulu.Preset` for a Heze statement that cites a Fulu
theorem. Each theorem below takes the Gloas proof term.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (StateTransitionError)
open EthCLSpecs.Heze (Preset computeEpochAtSlot computeStartSlotAtEpoch)
open scoped EthCLSpecs.Heze.Downgrade

/-- `compute_epoch_at_slot` never decreases as the slot grows. -/
theorem computeEpochAtSlot_monotone [Preset] :
    ∀ s₁ s₂ : UInt64, s₁ ≤ s₂ → computeEpochAtSlot s₁ ≤ computeEpochAtSlot s₂ :=
  Gloas.computeEpochAtSlot_monotone

/-- `compute_start_slot_at_epoch` cannot fault on an epoch at or below a slot division, and
the slot it returns is at or below that slot. -/
theorem computeStartSlotAtEpoch_isOk_of_le [Preset] :
    ∀ (e s : UInt64), e ≤ computeEpochAtSlot s →
      ∃ r : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok r ∧ r ≤ s :=
  Gloas.computeStartSlotAtEpoch_isOk_of_le

/-- `compute_start_slot_at_epoch` cannot fault on an epoch that `compute_epoch_at_slot`
produced. The `r ≤ s` conjunct rules out the underflow in `onTickPerSlot`'s subtraction. -/
theorem computeStartSlotAtEpoch_computeEpochAtSlot_isOk [Preset] :
    ∀ s : UInt64, ∃ r : UInt64,
      (computeStartSlotAtEpoch (computeEpochAtSlot s) : Except StateTransitionError UInt64)
        = .ok r ∧ r ≤ s :=
  Gloas.computeStartSlotAtEpoch_computeEpochAtSlot_isOk

/-- `compute_epoch_at_slot ∘ compute_start_slot_at_epoch = id`, under the bound that keeps
the multiply in range. -/
@[characterizes computeStartSlotAtEpoch]
theorem computeEpochAtSlot_computeStartSlotAtEpoch [Preset] :
    ∀ e : UInt64, e.toNat * EthCLSpecs.Heze.Const.slotsPerEpoch < 2 ^ 64 →
      ∃ s : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok s ∧
          computeEpochAtSlot s = e :=
  Gloas.computeEpochAtSlot_computeStartSlotAtEpoch

end EthCLSpecs.Proofs.Heze
