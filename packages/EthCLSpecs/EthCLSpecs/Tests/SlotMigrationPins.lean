import EthCLSpecs.Fulu

/-!
# `EthCLSpecs.Tests.SlotMigrationPins`: the `Slot` boundary pins

Three Fulu behavior pins for the checked `Slot` kind; the Gloas
`process_slot` pin is `Tests/GloasSlotMigrationPins.lean`. Each pin pairs a
targeted failure case with a nearby success that reaches the same operation,
and the successes read back exact values.

1. `process_slots` at the top of the range: advancing from one slot below the
   maximum ends at exactly `UINT64_MAX`; a state already at the maximum slot
   rejects through the spec's entry assert. The entry assert and the loop bound
   keep the loop's `state.slot + 1` below `2^64`, so this pair pins the boundary
   and does not depend on the add being checked.
2. `compute_time_at_slot_ms`: `slot * SLOT_DURATION_MS` past `2^64 - 1`
   (`slot = 3074457345618259` overflows at the minimal preset's
   `SLOT_DURATION_MS = 6000`), beside slot `100`, whose exact product the pin
   reads back;
3. `get_block_root_at_slot`: the recency bound `slot + SLOTS_PER_HISTORICAL_ROOT`
   overflows at a slot `62` below the maximum, beside the ring wrap: with
   `state.slot = 128` (two full rings at the minimal preset's
   `SLOTS_PER_HISTORICAL_ROOT = 64`), reading slot `64` wraps the index to `0`
   and returns the marker root stored there.

The arithmetic rejects surface as the checked range fault: `.error (.arithmetic _)`
on the state machine at site 3, and the `Checked` result's `.range` cause at site 2,
where `compute_time_at_slot_ms` returns `Checked`. A wrapping form gives a different
outcome at both sites: at site 2 the wrapped product returns `.ok`, and at site 3 the
wrapped bound `1` fails the recency assert with `.error (.assert _)`. So those failure
pins fail under it. `Tests/ClockMigrationPins.lean` pins the clock's other sites. The pins
hash through the FFI `Sha256` (`fastHasherTag`), so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLSpecs.Fulu

namespace EthCLSpecs.Tests.SlotMigrationPins

/-! ### 1. `process_slots` at the maximum slot -/

/-- The state at `UINT64_MAX - 1`, then `process_slots UINT64_MAX`: the loop's
`state.slot + 1` produces exactly `UINT64_MAX`, and the store reads it back. -/
private def pinProcessSlotsToMaxSlotReadsMax : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st0 : @BeaconState minimal :=
    { (default : @BeaconState minimal) with slot := 18446744073709551614 }
  let action : EStateM StateTransitionError
      (@BeaconState minimal) Unit :=
    processSlots (18446744073709551615 : Slot)
  match action.run st0 with
  | .ok _ st => st.slot = 18446744073709551615
  | _ => false
example : pinProcessSlotsToMaxSlotReadsMax = true := by native_decide

/-- A state already at the maximum slot: the entry assert rejects (no slot
follows the maximum), so the loop and its add never run past the maximum. -/
private def pinProcessSlotsAtMaxSlotRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st0 : @BeaconState minimal :=
    { (default : @BeaconState minimal) with slot := 18446744073709551615 }
  let action : EStateM StateTransitionError
      (@BeaconState minimal) Unit :=
    processSlots (18446744073709551615 : Slot)
  match action.run st0 with
  | .error (.assert _) _ => true
  | _ => false
example : pinProcessSlotsAtMaxSlotRejects = true := by native_decide

/-! ### 2. `compute_time_at_slot_ms` -/

/-- Slot `3074457345618259`: `3074457345618259 * 6000` exceeds
`2^64 - 1`, so the checked multiply raises instead of wrapping. -/
private def pinTimeMsMultiplyOverflows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match (computeTimeAtSlotMs 0 (3074457345618259 : Slot) : Checked CLUint64) with
  | .error ⟨.range, _, _, _, _⟩ => true
  | _ => false
example : pinTimeMsMultiplyOverflows = true := by native_decide

/-- Slot `100` from genesis time `0`: exactly `100 * 6000 = 600000`. -/
private def pinTimeMsInRangeReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match (computeTimeAtSlotMs 0 (100 : Slot) : Checked CLUint64) with
  | .ok ms => ms.toPlainNat = 600000
  | _ => false
example : pinTimeMsInRangeReads = true := by native_decide

/-! ### 3. `get_block_root_at_slot`: the ring buffer -/

/-- The recency bound `slot + SLOTS_PER_HISTORICAL_ROOT` at a slot `62` below
the maximum: `(2^64 - 63) + 64` overflows the checked add. A wrapping add gives the
bound `1`, and the recency assert then rejects with `.assert` instead. -/
private def pinBlockRootRecencyBoundOverflows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : CryptoBackend := CryptoBackend.ffi
  let st0 : @BeaconState minimal :=
    { (default : @BeaconState minimal) with slot := 18446744073709551615 }
  let action : EStateM StateTransitionError
      (@BeaconState minimal) Root :=
    getBlockRootAtSlot st0 (18446744073709551553 : Slot)
  match action.run st0 with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinBlockRootRecencyBoundOverflows = true := by native_decide

/-- The ring wrap: `state.slot = 128` (two full rings at the minimal preset's
`SLOTS_PER_HISTORICAL_ROOT = 64`), reading slot `64` wraps the index to `0`
and returns the marker root stored there, and no other entry holds it. -/
private def pinBlockRootRingWrapReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : CryptoBackend := CryptoBackend.ffi
  let marker : Root := Vector.replicate 32 7
  let st0 : @BeaconState minimal :=
    { (default : @BeaconState minimal) with
      slot := 128
      blockRoots := Vector.ofFn (fun i => if i.val == 0 then marker else default) }
  let action : EStateM StateTransitionError
      (@BeaconState minimal) Root :=
    getBlockRootAtSlot st0 (64 : Slot)
  match action.run st0 with
  | .ok r _ => r = marker
  | _ => false
example : pinBlockRootRingWrapReads = true := by native_decide

end EthCLSpecs.Tests.SlotMigrationPins
