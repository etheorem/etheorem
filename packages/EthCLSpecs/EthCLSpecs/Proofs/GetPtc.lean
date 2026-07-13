import EthCLLib.Spec.Arith
import EthCLSpecs.Fulu.Time

/-!
# `EthCLSpecs.Proofs.GetPtc`: the `get_ptc` else-branch offset bound

`EthCLSpecs.Gloas.getPtc` (`Gloas/Operations.lean:368-376`) reads the cached
Payload Timeliness Committee for a slot out of the `ptcWindow` ring buffer. Its
`if`-branch (a slot in the previous epoch) reads through `vmodGet`, already
proof-carrying and safe by construction. Its `else`-branch computes a raw
`UInt64` offset, `(epoch - stateEpoch + 1) * spe + slot % spe`, and reads
`ptcWindow` at it via the total `vget`, so an out-of-range offset would not
crash, it would silently return the vector's default element instead of the
cached committee. The docstring states this offset is in range only under the
caller's guarantee (`process_payload_attestation`'s `data.slot + 1 ==
state.slot`), never checked in `getPtc` itself. This file proves that claim.

`getPtcElseOffset_lt` states the bound at the `Nat` level (`hcaller` via
`.toNat`), not over the raw `UInt64` `slot + 1 == curSlot`: at `slot =
UInt64.max` that reading wraps to `0`, so the caller's guarantee could hold
vacuously while the bound itself fails. `.toNat` equality has no such
wraparound.

No mathlib needed; every step is a `UInt64`/`Nat` bridging lemma from Lean's
core `Init.Data.UInt` plus `omega`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (uint64ModOfNatToNatLt)
open EthCLSpecs.Fulu

/-- Names `getPtc`'s `else`-branch index into `ptcWindow`
(`Gloas/Operations.lean`'s `(epoch - stateEpoch + 1) * spe + slot % spe`), so
`getPtcElseOffset_lt` states the bound over one named quantity instead of
repeating the raw arithmetic. -/
def getPtcElseOffset [Preset] (slot curSlot : Slot) : Nat :=
  ((computeEpochAtSlot slot - computeEpochAtSlot curSlot + 1)
      * UInt64.ofNat Const.slotsPerEpoch
    + slot % UInt64.ofNat Const.slotsPerEpoch).toNat

/-- `getPtc`'s unchecked precondition: callers (`process_payload_attestation`)
guarantee `data.slot + 1 == state.slot` (`hcaller`, at the `Nat` level so
`slot`'s wraparound at `UInt64.max` cannot make the hypothesis hold
vacuously). `hbranch` is the `else`-branch's own guard, negated, the offset
formula's subtraction underflows if `getPtc` would have taken the `if`-branch
instead. Together the two force `computeEpochAtSlot slot = computeEpochAtSlot
curSlot`: `hcaller` gives `slot.toNat ≤ curSlot.toNat`, so `computeEpochAtSlot
slot ≤ computeEpochAtSlot curSlot` by division's monotonicity, and `hbranch`
gives the reverse `≤`. Equal epochs collapse the offset to `spe + slot % spe`,
comfortably under `3 * SLOTS_PER_EPOCH`. -/
theorem getPtcElseOffset_lt [Preset] {slot curSlot : Slot}
    (hcaller : slot.toNat + 1 = curSlot.toNat)
    (hbranch : ¬ computeEpochAtSlot slot < computeEpochAtSlot curSlot) :
    getPtcElseOffset slot curSlot < 3 * Const.slotsPerEpoch := by
  have hspe : (UInt64.ofNat Const.slotsPerEpoch).toNat = Const.slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt Const.slotsPerEpochLt
  unfold computeEpochAtSlot at hbranch
  rw [UInt64.not_lt, UInt64.le_iff_toNat_le, UInt64.toNat_div, UInt64.toNat_div, hspe] at hbranch
  have hmono : slot.toNat / Const.slotsPerEpoch ≤ curSlot.toNat / Const.slotsPerEpoch :=
    Nat.div_le_div_right (by omega)
  have hdiv : slot.toNat / Const.slotsPerEpoch = curSlot.toNat / Const.slotsPerEpoch :=
    Nat.le_antisymm hmono hbranch
  have heq : computeEpochAtSlot slot = computeEpochAtSlot curSlot := by
    unfold computeEpochAtSlot
    exact UInt64.toNat_inj.1 (by rw [UInt64.toNat_div, UInt64.toNat_div, hspe]; exact hdiv)
  have hmod := uint64ModOfNatToNatLt slot Const.slotsPerEpoch Const.slotsPerEpochPos
    Const.slotsPerEpochLt
  unfold getPtcElseOffset
  rw [heq, UInt64.sub_self, UInt64.zero_add, UInt64.one_mul, UInt64.toNat_add, hspe]
  omega

end EthCLSpecs.Proofs
