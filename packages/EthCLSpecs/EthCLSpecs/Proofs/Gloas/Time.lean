import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Fulu.Time

/-!
# `EthCLSpecs.Proofs.Gloas.Time`: the slot and epoch conversions at Gloas

Gloas `inherit`s `computeEpochAtSlot`, `computeStartSlotAtEpoch`, and
`computeActivationExitEpoch`. Each lands as a fresh constant that the Fulu theorems do not
describe.

The two forks' bodies elaborate to the same term. Neither body calls a declaration Gloas
overrides, and the two `SLOTS_PER_EPOCH` are `rfl`-equal. The `Downgrade` bridge derives
the `Fulu.Preset` a Fulu statement needs from the ambient `Gloas.Preset`. Each theorem
below therefore takes the Fulu proof term unchanged.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (StateTransitionError)
open EthCLSpecs.Gloas (Preset computeEpochAtSlot computeStartSlotAtEpoch
  computeActivationExitEpoch)
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

/-- **Exact equation** of `compute_activation_exit_epoch`: two carry tests, then the `uint64`
sum. -/
@[characterizes computeActivationExitEpoch]
theorem computeActivationExitEpoch_eq [Preset] :
    ∀ e : UInt64,
      (computeActivationExitEpoch e : Except StateTransitionError UInt64) =
        if e + 1 < e then .error (.arithmetic Fulu.activationExitDescr₁)
        else if e + 1 + EthCLSpecs.Gloas.Const.maxSeedLookahead < e + 1 then
          .error (.arithmetic Fulu.activationExitDescr₂)
        else .ok (e + 1 + EthCLSpecs.Gloas.Const.maxSeedLookahead) :=
  Fulu.computeActivationExitEpoch_eq

/-- Below the bound, the function succeeds with the exact sum. -/
theorem computeActivationExitEpoch_no_wrap [Preset] :
    ∀ e : UInt64, e.toNat + 1 + EthCLSpecs.Gloas.Const.maxSeedLookahead.toNat < 2 ^ 64 →
      ∃ r : UInt64,
        (computeActivationExitEpoch e : Except StateTransitionError UInt64) = .ok r ∧
          r.toNat = e.toNat + 1 + EthCLSpecs.Gloas.Const.maxSeedLookahead.toNat :=
  Fulu.computeActivationExitEpoch_no_wrap

/-- At or above the bound, the function rejects with the `.arithmetic` fault. -/
theorem computeActivationExitEpoch_overflow [Preset] :
    ∀ e : UInt64, 2 ^ 64 ≤ e.toNat + 1 + EthCLSpecs.Gloas.Const.maxSeedLookahead.toNat →
      ∃ d : String,
        (computeActivationExitEpoch e : Except StateTransitionError UInt64) = .error (.arithmetic d) :=
  Fulu.computeActivationExitEpoch_overflow

/-- The function cannot fault on an epoch that `compute_epoch_at_slot` produced, under the
preset bound. -/
theorem computeActivationExitEpoch_computeEpochAtSlot_isOk [Preset] :
    (2 ^ 64 - 1) / EthCLSpecs.Gloas.Const.slotsPerEpoch + 1
        + EthCLSpecs.Gloas.Const.maxSeedLookahead.toNat < 2 ^ 64 →
      ∀ s : UInt64, ∃ r : UInt64,
        (computeActivationExitEpoch (computeEpochAtSlot s) : Except StateTransitionError UInt64)
            = .ok r ∧
          r.toNat = (computeEpochAtSlot s).toNat + 1
            + EthCLSpecs.Gloas.Const.maxSeedLookahead.toNat :=
  Fulu.computeActivationExitEpoch_computeEpochAtSlot_isOk

end EthCLSpecs.Proofs.Gloas
