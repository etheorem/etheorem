import EthCLLib.Spec.Arith
import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Proofs.Gloas.GetPtc`: the `get_ptc` else-branch offset bound

`EthCLSpecs.Gloas.getPtc` (`Gloas/Operations.lean:539-565`) reads the cached
Payload Timeliness Committee for a slot out of the `ptcWindow` ring buffer. Its
`if`-branch (a slot in the previous epoch) reads through `vmodGet`, already
proof-carrying and safe by construction. Its `else`-branch computes a raw
`UInt64` offset, `(epoch - stateEpoch + 1) * spe + slot % spe`, and reads
`ptcWindow` at it via the total `vget`, so an out-of-range offset would not
correspond to the intended cached committee. Inside `getPtc` the branch's
`MIN_SEED_LOOKAHEAD` assert bounds the offset. This file proves the bound from the
slot relation of each of `getPtc`'s two guarded call sites, with no appeal to that
assert. The `GLOAS_FORK_EPOCH` assert that opens `getPtc` at v1.7.0-beta.4 does not
touch the offset, so neither bound changed.

`getPtcElseOffset_lt_next_slot` covers the slot-successor guard used by
`processPayloadAttestation`. `getPtcElseOffset_lt_same_slot` covers the
same-slot guard used by fork-choice replay paths. Calls without an established
relation between the queried slot and state slot are outside this module's
index-correctness scope.

`getPtcElseOffset_lt_next_slot` states its bound at the `Nat` level (`hcaller`
via `UInt64.toNat`), not over the raw `UInt64` `slot + 1 == curSlot`: at
`slot = UInt64.max` that reading wraps to `0`, so the caller's guarantee could
hold by wraparound while the bound itself fails. `Nat` equality has no such
wraparound.

The migrated `getPtc` computes the offset through the checked `Epoch` chain
(`diff ← epoch - stateEpoch`, `offset ← diff + 1`, `scaled ← offset *
SLOTS_PER_EPOCH`, `idx ← scaled + slot % SLOTS_PER_EPOCH`), so the index the
run passes to `vget` is that chain's plain value. `getPtcElseOffset` names the
plain value. The chain succeeds exactly when each step lands inside the checked
range; the bounds below imply that at the real presets (`SLOTS_PER_EPOCH` of 8
or 32 keeps `3 * SLOTS_PER_EPOCH` far below `2^64`), but the statements here are
the plain-`Nat` bounds only and do not claim fault-freedom for an arbitrary
preset whose `SLOTS_PER_EPOCH` approaches `2^63`.

No mathlib needed; every step is a `UInt64`/`Nat` bridging lemma from Lean's
core `Init.Data.UInt`, the proved-total divisor laws (`divPos_toPlainNat`), plus
`omega`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (CLUint64)
open EthCLSpecs.Gloas (Slot Preset computeEpochAtSlot)
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt)

/-- The plain reading of `computeEpochAtSlot`: the quotient of the slot by
`SLOTS_PER_EPOCH` through the proved-total divisor view. The lemma the two
bounds read the epoch comparisons through. -/
theorem computeEpochAtSlot_toPlainNat [Preset] (slot : Slot) :
    (computeEpochAtSlot slot).toPlainNat = slot.toPlainNat / slotsPerEpoch := by
  show (slot.divPos
    (⟨slotsPerEpoch, slotsPerEpochPos⟩ : EthCLLib.Spec.PositiveDivisor)).toPlainNat = _
  rw [CLUint64.divPos_toPlainNat]

/-- Names `getPtc`'s `else`-branch index into `ptcWindow`
(`Gloas/Operations.lean`'s checked chain `(epoch - stateEpoch + 1) * spe +
slot % spe`, read back as a `Nat`), so `getPtcElseOffset_lt_next_slot` states
the bound over one named quantity instead of repeating the raw arithmetic. -/
def getPtcElseOffset [Preset] (slot curSlot : Slot) : Nat :=
  ((computeEpochAtSlot slot).toPlainNat - (computeEpochAtSlot curSlot).toPlainNat + 1)
    * slotsPerEpoch + slot.toPlainNat % slotsPerEpoch

/-- `getPtc`'s unchecked precondition: callers (`process_payload_attestation`)
guarantee `data.slot + 1 == state.slot` (`hcaller`, at the `Nat` level so
`slot`'s wraparound at `UInt64.max` cannot vacuously satisfy it). `hbranch` is
the negated `else`-branch guard; without it, the epoch subtraction can
underflow when `getPtc` would have taken the `if`-branch. Together they force
the two epochs equal, collapsing the offset to `spe + slot % spe`, comfortably
under `3 * SLOTS_PER_EPOCH`. -/
theorem getPtcElseOffset_lt_next_slot [Preset] {slot curSlot : Slot}
    (hcaller : slot.toPlainNat + 1 = curSlot.toPlainNat)
    (hbranch : ¬ computeEpochAtSlot slot < computeEpochAtSlot curSlot) :
    getPtcElseOffset slot curSlot < 3 * slotsPerEpoch := by
  -- `LT` on `CLUint64` compares `val`, and `toPlainNat` is that `val` as a
  -- `Nat`, so the negated guard reads as the plain quotient inequality.
  have hple : (computeEpochAtSlot curSlot).toPlainNat ≤ (computeEpochAtSlot slot).toPlainNat := by
    have h : ¬ ((computeEpochAtSlot slot).val < (computeEpochAtSlot curSlot).val) := hbranch
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at h
    exact h
  rw [computeEpochAtSlot_toPlainNat] at hple
  have hmono : slot.toPlainNat / slotsPerEpoch ≤ curSlot.toPlainNat / slotsPerEpoch :=
    Nat.div_le_div_right (by omega)
  have hdiv : slot.toPlainNat / slotsPerEpoch = curSlot.toPlainNat / slotsPerEpoch :=
    Nat.le_antisymm hmono hple
  have hmod : slot.toPlainNat % slotsPerEpoch < slotsPerEpoch :=
    Nat.mod_lt _ slotsPerEpochPos
  unfold getPtcElseOffset
  simp only [computeEpochAtSlot_toPlainNat, hdiv, Nat.sub_self, Nat.zero_add, Nat.one_mul]
  omega

/-- Equality-guarded call sites query `getPtc` at the state's current slot.
Then the else-branch offset collapses to `slotsPerEpoch + slot % slotsPerEpoch`,
which is below the `3 * slotsPerEpoch` window bound. -/
theorem getPtcElseOffset_lt_same_slot [Preset] (slot : Slot) :
    getPtcElseOffset slot slot < 3 * slotsPerEpoch := by
  have hmod : slot.toPlainNat % slotsPerEpoch < slotsPerEpoch :=
    Nat.mod_lt _ slotsPerEpochPos
  unfold getPtcElseOffset
  simp only [computeEpochAtSlot_toPlainNat, Nat.sub_self, Nat.zero_add, Nat.one_mul]
  omega

end EthCLSpecs.Proofs.Gloas
