import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Time

/-!
# `EthCLSpecs.Proofs.Heze.Time`: the slot and epoch conversions at Heze

Heze `inherit`s both conversions and `computeActivationExitEpoch` from Gloas. Each lands as a fresh constant that the Gloas
theorems do not describe.

The transfer chains one fork at a time. `Heze.Downgrade` reaches `Gloas.Preset` and stops
there, so Lean cannot synthesize `Fulu.Preset` for a Heze statement that cites a Fulu
theorem. Each theorem below takes the Gloas proof term.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (StateTransitionError)
open EthCLSpecs.Heze (Preset computeEpochAtSlot computeStartSlotAtEpoch
  computeActivationExitEpoch)
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

/-- **Exact equation** of `compute_activation_exit_epoch`: two carry tests, then the `uint64`
sum. -/
@[characterizes computeActivationExitEpoch]
theorem computeActivationExitEpoch_eq [Preset] :
    ∀ e : UInt64,
      (computeActivationExitEpoch e : Except StateTransitionError UInt64) =
        if e + 1 < e then .error (.arithmetic Fulu.activationExitDescr₁)
        else if e + 1 + EthCLSpecs.Heze.Const.maxSeedLookahead < e + 1 then
          .error (.arithmetic Fulu.activationExitDescr₂)
        else .ok (e + 1 + EthCLSpecs.Heze.Const.maxSeedLookahead) :=
  Gloas.computeActivationExitEpoch_eq

/-- Below the bound, the function succeeds with the exact sum. -/
theorem computeActivationExitEpoch_no_wrap [Preset] :
    ∀ e : UInt64, e.toNat + 1 + EthCLSpecs.Heze.Const.maxSeedLookahead.toNat < 2 ^ 64 →
      ∃ r : UInt64,
        (computeActivationExitEpoch e : Except StateTransitionError UInt64) = .ok r ∧
          r.toNat = e.toNat + 1 + EthCLSpecs.Heze.Const.maxSeedLookahead.toNat :=
  Gloas.computeActivationExitEpoch_no_wrap

/-- At or above the bound, the function rejects with the `.arithmetic` fault. -/
theorem computeActivationExitEpoch_overflow [Preset] :
    ∀ e : UInt64, 2 ^ 64 ≤ e.toNat + 1 + EthCLSpecs.Heze.Const.maxSeedLookahead.toNat →
      ∃ d : String,
        (computeActivationExitEpoch e : Except StateTransitionError UInt64) = .error (.arithmetic d) :=
  Gloas.computeActivationExitEpoch_overflow

/-- The function cannot fault on an epoch that `compute_epoch_at_slot` produced, under the
preset bound. -/
theorem computeActivationExitEpoch_computeEpochAtSlot_isOk [Preset] :
    (2 ^ 64 - 1) / EthCLSpecs.Heze.Const.slotsPerEpoch + 1
        + EthCLSpecs.Heze.Const.maxSeedLookahead.toNat < 2 ^ 64 →
      ∀ s : UInt64, ∃ r : UInt64,
        (computeActivationExitEpoch (computeEpochAtSlot s) : Except StateTransitionError UInt64)
            = .ok r ∧
          r.toNat = (computeEpochAtSlot s).toNat + 1
            + EthCLSpecs.Heze.Const.maxSeedLookahead.toNat :=
  Gloas.computeActivationExitEpoch_computeEpochAtSlot_isOk

end EthCLSpecs.Proofs.Heze
