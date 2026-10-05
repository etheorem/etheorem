import EthCLSpecs.Proofs.Heze.PaymentFrame
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments

/-!
# `EthCLSpecs.Proofs.Heze.PaymentWriters`: the five writers of the payment window

`builderPendingPayments` holds `2 * SLOTS_PER_EPOCH` entries. The lower half holds the
previous epoch. The upper half holds the current epoch. `builderPaymentIndex slot current`
picks the entry of a slot. Five spec functions write the window:

| Writer | Index | Effect on the withdrawal |
| --- | --- | --- |
| `processExecutionPayloadBid` | the bid's slot, upper half | writes it when the value is `> 0` |
| `processAttestation` | the attested slot | keeps it, changes the weight |
| `processProposerSlashing` | the first header's slot | clears it when the proposer matches |
| `settleBuilderPayment` | its argument | clears it |
| `processBuilderPendingPayments` | every index | shifts the window down |

The index facts say when two slots share an index. In one half, two slots of one epoch
share an index only when they are equal (`builderPaymentIndex_inj`). The two halves never
share one. `vget_payments_write` states the window after a write at one index.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset State BeaconState Slot BuilderPendingPayment builderPaymentIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt)

section
variable [Preset]

/-- The index as a `Nat`: the offset of the half plus the slot modulo `SLOTS_PER_EPOCH`. -/
theorem builderPaymentIndex_eq (s : Slot) (c : Bool) :
    builderPaymentIndex s c = (if c then slotsPerEpoch else 0) + s.toNat % slotsPerEpoch := by
  have h : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt slotsPerEpochLt
  simp [builderPaymentIndex, umodIdx, UInt64.toNat_mod, h]

/-- Every index is inside the window. -/
theorem builderPaymentIndex_lt (s : Slot) (c : Bool) :
    builderPaymentIndex s c < 2 * slotsPerEpoch := by
  rw [builderPaymentIndex_eq]
  have := Nat.mod_lt s.toNat slotsPerEpochPos
  cases c <;> simp <;> omega

/-- In one half, two slots of one epoch with one index are equal. -/
theorem builderPaymentIndex_inj {s t : Slot} {c : Bool}
    (hidx : builderPaymentIndex s c = builderPaymentIndex t c)
    (hep : s.toNat / slotsPerEpoch = t.toNat / slotsPerEpoch) : s = t := by
  rw [builderPaymentIndex_eq, builderPaymentIndex_eq] at hidx
  have hmod : s.toNat % slotsPerEpoch = t.toNat % slotsPerEpoch := by omega
  apply UInt64.toNat_inj.mp
  rw [← Nat.div_add_mod s.toNat slotsPerEpoch, ← Nat.div_add_mod t.toNat slotsPerEpoch,
    hep, hmod]

/-- The upper and lower halves share no index. -/
theorem builderPaymentIndex_true_ne_false (s t : Slot) :
    builderPaymentIndex s true ≠ builderPaymentIndex t false := by
  rw [builderPaymentIndex_eq, builderPaymentIndex_eq]
  have := Nat.mod_lt s.toNat slotsPerEpochPos
  have := Nat.mod_lt t.toNat slotsPerEpochPos
  simp
  omega

/-- `computeEpochAtSlot` as a `Nat` division. -/
theorem computeEpochAtSlot_toNat (s : Slot) :
    (EthCLSpecs.Heze.computeEpochAtSlot s).toNat = s.toNat / slotsPerEpoch := by
  have h : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt slotsPerEpochLt
  simp [EthCLSpecs.Heze.computeEpochAtSlot, UInt64.toNat_div, h]

end

section
variable [Preset] [HasherTag]

/-- After a write of `x` at index `j` of the window, the entry at `j` is `x`. Every other
entry keeps its old value. -/
theorem vget_payments_write (st : BeaconState) (j : Nat) (hj : j < 2 * slotsPerEpoch)
    (x : BuilderPendingPayment) (i : Nat) :
    vget (sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
        builderPendingPayments) i
      = if i = j then x else vget (sszGet (pureState st) builderPendingPayments) i := by
  have hview : sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
      builderPendingPayments = (sszGet (pureState st) builderPendingPayments).set! j x := rfl
  rw [hview]
  unfold vget
  by_cases hij : i = j
  · subst hij
    simp [Vector.toArray_set!, hj]
  · simp [Vector.toArray_set!, hij, getElem!_def,
      Array.getElem?_setIfInBounds_ne (Ne.symm hij)]

end

end EthCLSpecs.Proofs.Heze
