import EthCLSpecs.Fulu

/-!
# `EthCLSpecs.Tests.ClockSamplingAuditPins`: the clock, sampling, and fork-choice audit pins

Pins for the manual audit of the Fulu clock, sampling, and fork-choice files (Stage 8.4a2).
The audit changed no behavior. These pins hold two of its proof justifications to the
pinned pyspec, so the build fails if a later edit breaks them. Every value comes from the
pinned pyspec (1.7.0b4).

1. `on_tick_per_slot` binds `compute_slots_since_epoch_start(current_slot)` above the
   branch where Python's `and` forms it. The audit accepts the eager bind because neither
   step can raise: the epoch-start slot is at most the slot. At `slot = UINT64_MAX` the
   start slot is `2^64 - 8` at minimal and `2^64 - 32` at mainnet, and the difference is
   `7` and `31`.
2. `compute_committee` iterates `range(start, end)` as the `Nat` difference
   `stop - start`. The audit accepts the truncated subtraction because `end ≥ start` for
   every `index`, so the difference is zero exactly where Python's range is empty. Two
   indices over four committees of two validators read the empty range, and the three
   committees of eight validators partition the shuffled registry.

The pins close by `native_decide`, as the other migration pins do: the committee pins hash
through the compiled `Sha256` seam.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.ClockSamplingAuditPins

open EthCLSpecs.Fulu

/-! ### 1. `compute_slots_since_epoch_start` at `UINT64_MAX` -/

/-- The epoch-start slot of `slot` and the slots since it, as `on_tick_per_slot` forms them.
`.none` when either checked step raises. -/
private def slotsSinceEpochStart [Preset] (slot : Slot) : Option (Nat × Nat) :=
  match (do
      let startSlot ← computeStartSlotAtEpoch (computeEpochAtSlot slot)
      let since ← slot - startSlot
      pure (startSlot, since) : Checked (Slot × Slot)) with
  | .ok (startSlot, since) => some (startSlot.toPlainNat, since.toPlainNat)
  | .error _ => none

/-- Minimal (`SLOTS_PER_EPOCH = 8`): start slot `2^64 - 8`, seven slots since it. -/
private def pinSinceEpochStartMaxMinimal : Bool :=
  letI : Preset := minimal
  slotsSinceEpochStart 18446744073709551615 == some (18446744073709551608, 7)
example : pinSinceEpochStartMaxMinimal = true := by native_decide

/-- Mainnet (`SLOTS_PER_EPOCH = 32`): start slot `2^64 - 32`, 31 slots since it. -/
private def pinSinceEpochStartMaxMainnet : Bool :=
  letI : Preset := mainnet
  slotsSinceEpochStart 18446744073709551615 == some (18446744073709551584, 31)
example : pinSinceEpochStartMaxMainnet = true := by native_decide

/-! ### 2. `compute_committee`: the `range(start, end)` length -/

/-- Runs `compute_committee` over the indices `0 … n - 1` and a zero seed, reading back the
committee's indices. -/
private def committeeOf (n : Nat) (index count : CLUint64) : Except ArithFault (List Nat) :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  (computeCommittee ((Array.range n).map fun i => ((CLUint64.ofNat? i).toOption.getD 0))
      (Vector.replicate 32 0) index count).map fun c => c.toList.map (·.toPlainNat)

/-- Two validators, four committees. Indices `0` and `2` give `start = end`, so the range is
empty. Indices `1` and `3` give one member each. -/
private def pinCommitteeEmptyRanges : Bool :=
  committeeOf 2 0 4 == .ok [] && committeeOf 2 1 4 == .ok [1]
    && committeeOf 2 2 4 == .ok [] && committeeOf 2 3 4 == .ok [0]
example : pinCommitteeEmptyRanges = true := by native_decide

/-- Eight validators, three committees: the bounds `0, 2, 5, 8` split the shuffled registry
`[4, 1, 0, 2, 6, 5, 3, 7]` into three consecutive slices. -/
private def pinCommitteePartition : Bool :=
  committeeOf 8 0 3 == .ok [4, 1] && committeeOf 8 1 3 == .ok [0, 2, 6]
    && committeeOf 8 2 3 == .ok [5, 3, 7]
example : pinCommitteePartition = true := by native_decide

end EthCLSpecs.Tests.ClockSamplingAuditPins
