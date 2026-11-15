import EthCLLib.Proofs.CLUint
import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Proofs.Gloas.GetPtc`: the `get_ptc` else-branch offset bound

`EthCLSpecs.Gloas.getPtc` (`Gloas/Operations.lean:487-515`) reads the cached
Payload Timeliness Committee for a slot out of the `ptcWindow` ring buffer. Its
`if`-branch (a slot in the previous epoch) reads through `vmodGet`, already
proof-carrying and safe by construction. Its `else`-branch computes the offset as
a checked `Epoch` chain, `epoch - stateEpoch`, then `+ 1`, then `* spe`, then
`+ slot % SLOTS_PER_EPOCH`, and reads `ptcWindow` at the bound value's `.toPlainInt`, so a
faulting chain reads nothing and an out-of-range index would not correspond to
the intended cached committee. Inside `getPtc` the branch's `MIN_SEED_LOOKAHEAD`
assert bounds the offset. This file proves the bound from the slot relation of
each of `getPtc`'s two guarded call sites, with no appeal to that assert. The
`GLOAS_FORK_EPOCH` assert that opens `getPtc` at v1.7.0-beta.4 does not touch
the offset, so neither bound changed.

The unit flip made `Slot` the checked `CLUint64`, so the offset is the checked
chain the source binds, not a total `Nat` expression. Each theorem carries the
chain's `.ok` equation as a hypothesis and bounds the bound value's
`.toPlainInt`. The hypothesis is honest: the chain's final add can fault for a
preset whose `slotsPerEpoch` passes `2 ^ 63`, and a theorem may not claim a
value the chain never produced. For every preset the repository ships, the
call-site asserts force the chain to bind; the caller-level binding fact is the
run-level theorem's business, left to a future `getPtc` contract.

`getPtcElseOffset_lt_next_slot` covers the slot-successor guard used by
`processPayloadAttestation`. `getPtcElseOffset_lt_same_slot` covers the
same-slot guard used by fork-choice replay paths. Calls without an established
relation between the queried slot and state slot are outside this module's
index-correctness scope.

`getPtcElseOffset_lt_next_slot` states its caller guard at the `.toPlainInt`
level (`slot.toPlainInt + 1 = curSlot.toPlainInt`), not over the raw `UInt64`
`slot + 1 == curSlot`: at `slot = UInt64.max` that reading wraps to `0`, so the
caller's guarantee could hold by wraparound while the bound itself fails.
`.toPlainInt` has no such wraparound; it is the pyspec's `int(x)`, the
plain-`int` view `EthCLLib.Proofs.CLUint` states the checked operators' lemmas
over.

No mathlib needed; every step is a `UInt64`/`Nat` bridging lemma from Lean's
core `Init.Data.UInt`, a `CLUint` success or value lemma, and `omega`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (Checked CLUint64)
open EthCLLib.Proofs (bind_ok_iff sub_eq_ok add_eq_ok mul_eq_ok toPlainInt_inj)
open EthCLSpecs.Gloas (Preset Slot computeEpochAtSlot)
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt slotsPerEpochDiv)

/-- The plain-`int` reading of `computeEpochAtSlot`: the slot's plain `int`
divided by `SLOTS_PER_EPOCH`. The conversion the two call-site guards read
through, so the epoch-equality argument happens at the `Nat` level. -/
private theorem computeEpochAtSlot_toPlainInt [Preset] (s : Slot) :
    (computeEpochAtSlot s).toPlainInt = s.toPlainInt / slotsPerEpoch := by
  show CLUint64.toPlainInt (s / slotsPerEpochDiv) = _
  show (UInt64.ofNat (s.toPlainInt / slotsPerEpochDiv.val)).toNat = _
  rw [UInt64.toNat_ofNat', show slotsPerEpochDiv.val = slotsPerEpoch from rfl]
  have hle : s.toPlainInt / slotsPerEpoch ≤ s.toPlainInt := Nat.div_le_self _ _
  have hc : s.toPlainInt < 2 ^ 64 := s.val.toNat_lt
  exact Nat.mod_eq_of_lt (by omega)

/-- Names `getPtc`'s `else`-branch index chain
(`Gloas/Operations.lean`'s `offset ← epoch - stateEpoch`, then `+ 1`, then
`* spe`, then `+ slot % SLOTS_PER_EPOCH`), as one `Checked Slot` value spelled step for step
as the source binds it. The `spe` operand is the source's
`CLUint64.trustedOfUInt64 (UInt64.ofNat SLOTS_PER_EPOCH)`; the final `%` takes
the total `PositiveDivisor` route, so it is a plain `Slot` and only the four
`←` steps can fault. The `MIN_SEED_LOOKAHEAD` step above the chain feeds the
assert alone, not the index, so it is not part of this value. -/
def getPtcElseOffset [Preset] (slot curSlot : Slot) : Checked Slot :=
  (computeEpochAtSlot slot - computeEpochAtSlot curSlot).bind
    fun offset => (offset + (1 : Slot)).bind
      fun windowed =>
        (windowed * CLUint64.trustedOfUInt64 (UInt64.ofNat slotsPerEpoch)).bind
          fun scaled => (scaled + slot % slotsPerEpochDiv)

/-- The bound once the two epochs agree: the chain's value reads back as
`SLOTS_PER_EPOCH + slot.toPlainInt % SLOTS_PER_EPOCH`, which sits below the
`3 * slotsPerEpoch` window length. Both call-site theorems reduce to this
private step, which is where the chain's `.ok` equation is peeled one bind at a
time (`bind_ok_iff`) and each step's value is read back through its own
success-and-value lemma. -/
private theorem getPtcElseOffset_lt_of_epoch_eq [Preset] {slot curSlot : Slot}
    (heq : computeEpochAtSlot slot = computeEpochAtSlot curSlot)
    {idx : Slot} (hok : getPtcElseOffset slot curSlot = .ok idx) :
    idx.toPlainInt < 3 * slotsPerEpoch := by
  have hspe : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat slotsPerEpoch))
      = slotsPerEpoch := by
    show (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch
    exact UInt64.toNat_ofNat_of_lt slotsPerEpochLt
  unfold getPtcElseOffset at hok
  rw [bind_ok_iff] at hok
  obtain ⟨offset, hsub, hok⟩ := hok
  rw [bind_ok_iff] at hok
  obtain ⟨windowed, hadd, hok⟩ := hok
  rw [bind_ok_iff] at hok
  obtain ⟨scaled, hmul, hadd2⟩ := hok
  -- The subtraction binds by hypothesis; with the epochs equal, its value is `0`.
  obtain ⟨-, hsubVal⟩ := (sub_eq_ok _ _ offset).mp hsub
  rw [heq] at hsubVal
  have h0 : offset.toPlainInt = 0 := by rw [hsubVal]; omega
  -- The literal `1`'s `.toPlainInt` is the numeral `1`, but it is an atom for
  -- `omega` until this `rfl` names it.
  have hlit : CLUint64.toPlainInt (1 : Slot) = 1 := rfl
  obtain ⟨-, haddVal⟩ := (add_eq_ok offset (1 : Slot) windowed).mp hadd
  have h1 : windowed.toPlainInt = 1 := by rw [haddVal, h0, hlit]
  obtain ⟨-, hmulVal⟩ := (mul_eq_ok windowed _ scaled).mp hmul
  have hscaled : scaled.toPlainInt = slotsPerEpoch := by rw [hmulVal, h1, hspe]; omega
  obtain ⟨-, hidxVal⟩ :=
    (add_eq_ok scaled (slot % slotsPerEpochDiv) idx).mp hadd2
  have hmod : slot.toPlainInt % slotsPerEpoch < slotsPerEpoch :=
    Nat.mod_lt _ slotsPerEpochPos
  have hfinal : idx.toPlainInt = slotsPerEpoch + slot.toPlainInt % slotsPerEpoch := by
    rw [hidxVal, hscaled]
    show slotsPerEpoch + CLUint64.toPlainInt (slot % slotsPerEpochDiv) = _
    show slotsPerEpoch
      + (UInt64.ofNat (slot.toPlainInt % slotsPerEpochDiv.val)).toNat = _
    rw [UInt64.toNat_ofNat', show slotsPerEpochDiv.val = slotsPerEpoch from rfl]
    have hle : slot.toPlainInt % slotsPerEpoch < 2 ^ 64 := by
      have hlt := slotsPerEpochLt
      omega
    rw [Nat.mod_eq_of_lt hle]
  omega

/-- `getPtc`'s unchecked precondition: callers (`process_payload_attestation`)
guarantee `data.slot + 1 == state.slot` (`hcaller`, at the `.toPlainInt` level so
`slot`'s wraparound at `UInt64.max` cannot vacuously satisfy it). `hbranch` is
the negated `else`-branch guard; without it, the epoch subtraction can
underflow when `getPtc` would have taken the `if`-branch. Together they force
`computeEpochAtSlot slot = computeEpochAtSlot curSlot`, so the chain's value is
`spe + slot % spe`, comfortably under `3 * SLOTS_PER_EPOCH`. The chain's `.ok`
equation is a hypothesis, the shape the contract's `.ok` arm commits to: the
chain is checked, and the caller-level fact that the guards force it to bind
lives with a future `getPtc` contract. -/
theorem getPtcElseOffset_lt_next_slot [Preset] {slot curSlot : Slot}
    (hcaller : slot.toPlainInt + 1 = curSlot.toPlainInt)
    (hbranch : ¬ computeEpochAtSlot slot < computeEpochAtSlot curSlot)
    {idx : Slot} (hok : getPtcElseOffset slot curSlot = .ok idx) :
    idx.toPlainInt < 3 * slotsPerEpoch := by
  -- The negated guard is `¬(epoch < stateEpoch)` on the native width, so the
  -- curSlot epoch is at most the slot epoch; `.toPlainInt` is `val.toNat`
  -- definitionally, so the `have` carries it to the `Nat` spelling.
  have hb : (computeEpochAtSlot curSlot).toPlainInt
      ≤ (computeEpochAtSlot slot).toPlainInt := by
    have h'' : ¬ ((computeEpochAtSlot slot : Slot).val
        < (computeEpochAtSlot curSlot : Slot).val) := hbranch
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at h''
    exact h''
  have hdiv : slot.toPlainInt / slotsPerEpoch = curSlot.toPlainInt / slotsPerEpoch := by
    have h1 : curSlot.toPlainInt / slotsPerEpoch ≤ slot.toPlainInt / slotsPerEpoch := by
      rw [← computeEpochAtSlot_toPlainInt curSlot, ← computeEpochAtSlot_toPlainInt slot]
      exact hb
    have h2 : slot.toPlainInt / slotsPerEpoch ≤ curSlot.toPlainInt / slotsPerEpoch :=
      Nat.div_le_div_right (by omega)
    exact Nat.le_antisymm h2 h1
  have heq : computeEpochAtSlot slot = computeEpochAtSlot curSlot :=
    toPlainInt_inj (by rw [computeEpochAtSlot_toPlainInt, computeEpochAtSlot_toPlainInt]; exact hdiv)
  exact getPtcElseOffset_lt_of_epoch_eq heq hok

/-- Equality-guarded call sites query `getPtc` at the state's current slot, so
the two epochs agree by `rfl` and the chain's value reads back as
`slotsPerEpoch + slot.toPlainInt % slotsPerEpoch`, below the
`3 * slotsPerEpoch` window bound. The chain's `.ok` equation is a hypothesis,
the same shape `getPtcElseOffset_lt_next_slot` carries. -/
theorem getPtcElseOffset_lt_same_slot [Preset] (slot : Slot)
    {idx : Slot} (hok : getPtcElseOffset slot slot = .ok idx) :
    idx.toPlainInt < 3 * slotsPerEpoch :=
  getPtcElseOffset_lt_of_epoch_eq rfl hok

end EthCLSpecs.Proofs.Gloas
