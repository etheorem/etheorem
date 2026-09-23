import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Fulu.Time

/-!
# `EthCLSpecs.Proofs.Gloas.Time`: the slot and epoch conversions at Gloas

Gloas `inherit`s `computeEpochAtSlot` and `computeStartSlotAtEpoch`. Each lands as a fresh
constant that the Fulu theorems do not describe.

The two forks' bodies elaborate to the same term. Neither body calls a declaration Gloas
overrides, and the two `SLOTS_PER_EPOCH` are `rfl`-equal. The `Downgrade` bridge derives
the `Fulu.Preset` a Fulu statement needs from the ambient `Gloas.Preset`. Each theorem
below therefore takes the Fulu proof term unchanged.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (StateTransitionError)
open EthCLSpecs.Gloas (Preset computeEpochAtSlot computeStartSlotAtEpoch)
open scoped EthCLSpecs.Gloas.Downgrade

/-- `compute_epoch_at_slot` never decreases as the slot grows. -/
theorem computeEpochAtSlot_monotone [Preset] :
    ∀ s₁ s₂ : UInt64, s₁ ≤ s₂ → computeEpochAtSlot s₁ ≤ computeEpochAtSlot s₂ :=
  Fulu.computeEpochAtSlot_monotone

/-- `compute_start_slot_at_epoch` cannot fault on an epoch at or below a slot division, and
the slot it returns is at or below that slot. -/
theorem computeStartSlotAtEpoch_isOk_of_le [Preset] :
    ∀ (e s : UInt64), e ≤ computeEpochAtSlot s →
      ∃ r : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok r ∧ r ≤ s :=
  Fulu.computeStartSlotAtEpoch_isOk_of_le

/-- `compute_start_slot_at_epoch` cannot fault on an epoch that `compute_epoch_at_slot`
produced. The `r ≤ s` conjunct rules out the underflow in `onTickPerSlot`'s subtraction. -/
theorem computeStartSlotAtEpoch_computeEpochAtSlot_isOk [Preset] :
    ∀ s : UInt64, ∃ r : UInt64,
      (computeStartSlotAtEpoch (computeEpochAtSlot s) : Except StateTransitionError UInt64)
        = .ok r ∧ r ≤ s :=
  Fulu.computeStartSlotAtEpoch_computeEpochAtSlot_isOk

/-- `compute_epoch_at_slot ∘ compute_start_slot_at_epoch = id`, under the bound that keeps
the multiply in range. -/
@[characterizes computeStartSlotAtEpoch]
theorem computeEpochAtSlot_computeStartSlotAtEpoch [Preset] :
    ∀ e : UInt64, e.toNat * EthCLSpecs.Gloas.Const.slotsPerEpoch < 2 ^ 64 →
      ∃ s : UInt64,
        (computeStartSlotAtEpoch e : Except StateTransitionError UInt64) = .ok s ∧
          computeEpochAtSlot s = e :=
  Fulu.computeEpochAtSlot_computeStartSlotAtEpoch

end EthCLSpecs.Proofs.Gloas
