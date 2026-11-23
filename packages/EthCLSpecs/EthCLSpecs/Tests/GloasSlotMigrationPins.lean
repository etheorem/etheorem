import EthCLSpecs.Gloas.Transition

/-!
# `EthCLSpecs.Tests.GloasSlotMigrationPins`: the Gloas `process_slot` pin

Gloas `process_slot` (`gloas/minimal.py:2211-2225`) clears the next slot's payload
availability bit at `(state.slot + 1) % SLOTS_PER_HISTORICAL_ROOT`. The pyspec's
`state.slot + 1` is a checked `Slot` add, so at slot `UINT64_MAX` it raises. A wrapping
add returned `.ok` there and cleared bit `0`. The pin pairs that failure with the slot one
below the maximum, where the clear hits ring index `63` at the minimal preset, and reads
back both bits.

`process_slots` never calls `process_slot` at the maximum slot (its entry assert and loop
bound keep `state.slot` below `slot`), so no vector reaches the fault.

The second pair pins `process_ptc_window` (`gloas/minimal.py:7925-7936`). Its
`range(start_slot, start_slot + SLOTS_PER_EPOCH)` forms the checked range end once, before
any `compute_ptc`. At `start_slot = 2^64 - 8` that end raises; one epoch below, the fresh
entries read back exactly. The pins hash through the FFI `Sha256` (`fastHasherTag`), so
`native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasSlotMigrationPins

open EthCLSpecs.Gloas

/-- The pins' state-machine monad over the minimal preset and the FFI hasher. -/
private abbrev PinM := EStateM StateTransitionError (@State minimal fastHasherTag)

/-- A minimal Gloas state at slot `s` with the availability bits at ring indices `0` and
`63` set, so the pins can see which index the clear hits. -/
private def availabilityState (s : Slot) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
    slot := s
    executionPayloadAvailability := bitSet (bitSet default 0 true) 63 true }

/-- At slot `UINT64_MAX` the checked `state.slot + 1` raises the range fault. -/
private def pinProcessSlotAtMaxSlotRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processSlot : PinM Unit).run (availabilityState 18446744073709551615) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinProcessSlotAtMaxSlotRejects = true := by native_decide

/-- One slot below the maximum, the next slot is `UINT64_MAX`, ring index `63`: bit `63`
reads back cleared and bit `0` stays set. -/
private def pinProcessSlotBelowMaxClearsNextBit : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processSlot : PinM Unit).run (availabilityState 18446744073709551614) with
  | .ok _ st =>
    bitGet (sszGet st executionPayloadAvailability) 63 == false &&
      bitGet (sszGet st executionPayloadAvailability) 0 == true
  | _ => false
example : pinProcessSlotBelowMaxClearsNextBit = true := by native_decide

/-! ### `process_ptc_window`: the range end -/

/-- A minimal Gloas state at slot `s` with eight active validators at the maximum
effective balance, so every slot's PTC selection has a member and accepts at once. -/
private def ptcWindowState (s : Slot) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 2048000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
    slot := s
    validators := ⟨Array.replicate 8 v⟩
    balances := ⟨Array.replicate 8 2048000000000⟩ }

/-- Current epoch `2^61 - 3` at the minimal preset: `next_epoch = 2^61 - 1`, so
`start_slot = 2^64 - 8` and the range end `start_slot + SLOTS_PER_EPOCH` is `2^64`. The
pyspec raises there before any `compute_ptc`. -/
private def pinPtcWindowRangeEndFaults : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processPtcWindow : PinM Unit).run (ptcWindowState 18446744073709551592) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinPtcWindowRangeEndFaults = true := by native_decide

/-- One epoch below: `start_slot = 2^64 - 16` and the range end `2^64 - 8` fits. The fresh
last-epoch entries read back exactly `compute_ptc` at their first and last slots. -/
private def pinPtcWindowBelowRangeEndReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let state0 := ptcWindowState 18446744073709551584
  match (processPtcWindow : PinM Unit).run state0,
      computePtc state0 18446744073709551600, computePtc state0 18446744073709551607 with
  | .ok _ st, .ok first, .ok last =>
    vget (sszGet st ptcWindow) 16 == first && vget (sszGet st ptcWindow) 23 == last
  | _, _, _ => false
example : pinPtcWindowBelowRangeEndReads = true := by native_decide

end EthCLSpecs.Tests.GloasSlotMigrationPins
