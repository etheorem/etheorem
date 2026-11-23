import EthCLSpecs.Fulu.ForkChoice

/-!
# `EthCLSpecs.Tests.ClockMigrationPins`: the clock boundary pins

Fulu behavior pins for the clock. The clock values
(`time_ms`, `genesis_time_ms`, `genesis_time`, `SLOT_DURATION_MS`) are `Uint64` in the
pinned module, so every clock operation is the checked kind. Gloas and Heze inherit the
clock helpers from Fulu. Each pin pairs a targeted failure with a nearby success that
reaches the same operation, and the successes read back exact values. All values use the
minimal preset's `SLOT_DURATION_MS = 6000`.

1. `compute_time_at_slot_ms`: the sum `genesis_time_ms + slot * SLOT_DURATION_MS` past
   `2^64 - 1`. A wrapping add returns `.ok 0` instead of the range fault. The product
   overflow of the same function is site 2 of `Tests/SlotMigrationPins.lean`.
2. `compute_slot_at_time_ms`: a time before genesis. A wrapping subtraction returns
   `.ok 3074457345618258` (`(2^64 - 1) // 6000`) instead of the range fault.
3. `seconds_to_milliseconds`: the cap. One second past `UINT64_MAX // 1000` returns
   `UINT64_MAX`. A bare `UInt64` product with no guard wraps to `384` instead.
4. `compute_time_at_slot`: the cap feeds the checked sum. A genesis time past the cap
   gives `genesis_time_ms = UINT64_MAX`, so slot `1` raises. A bare product gives
   `genesis_time_ms = 384` and returns `.ok 6` instead.
5. The fork-choice store clock: `get_current_slot` on a store whose time is before
   genesis raises the range fault on the store machine, where a wrapping subtraction
   returns a slot. `on_tick` from genesis to `18001` ms catches up two slots and sets the
   store time to exactly `18001`.

The clock helpers return `Checked`, so sites 1 to 4 match on the fault's `.range` cause.
Site 5 runs on the store machine, where the lift wraps the fault as
`.transition (.arithmetic _)`. The pins close by `native_decide`, as the other migration
pins do: the minimal configuration is a large record, and site 5 runs the store through the
compiled `treeMap`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.ClockMigrationPins

open EthCLSpecs.Fulu

/-- `true` exactly when a checked result is the range fault. -/
private def isRangeFault {α : Type} : Checked α → Bool
  | .error ⟨.range, _, _, _, _⟩ => true
  | _ => false

/-! ### 1. `compute_time_at_slot_ms`: the checked sum -/

/-- `genesis_time_ms = 2^64 - 6000`, slot `1`: the product `6000` fits, and the sum is
`2^64`, so the checked add raises. -/
private def pinTimeMsSumOverflows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  isRangeFault (computeTimeAtSlotMs 18446744073709545616 (1 : Slot))
example : pinTimeMsSumOverflows = true := by native_decide

/-- `genesis_time_ms = 2^64 - 6001`, slot `1`: the sum is exactly `UINT64_MAX`. -/
private def pinTimeMsSumReachesMax : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match computeTimeAtSlotMs 18446744073709545615 (1 : Slot) with
  | .ok ms => ms.toPlainNat = 18446744073709551615
  | .error _ => false
example : pinTimeMsSumReachesMax = true := by native_decide

/-! ### 2. `compute_slot_at_time_ms`: a time before genesis -/

/-- `time_ms = 5999` before `genesis_time_ms = 6000`: the checked subtraction raises. -/
private def pinSlotAtTimeBeforeGenesis : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  isRangeFault (computeSlotAtTimeMs 6000 5999)
example : pinSlotAtTimeBeforeGenesis = true := by native_decide

/-- `time_ms = 23999` from `genesis_time_ms = 6000`: `17999 // 6000` floors to slot `2`.
At `time_ms = genesis_time_ms` the slot is `0`. -/
private def pinSlotAtTimeFloors : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match computeSlotAtTimeMs 6000 23999, computeSlotAtTimeMs 6000 6000 with
  | .ok s, .ok z => s.toPlainNat = 2 && z.toPlainNat = 0
  | _, _ => false
example : pinSlotAtTimeFloors = true := by native_decide

/-! ### 3. `seconds_to_milliseconds`: the cap -/

/-- One second past `UINT64_MAX // 1000 = 18446744073709551`: the guard returns
`UINT64_MAX`. -/
private def pinSecondsToMsCaps : Bool :=
  letI : Preset := minimal
  (secondsToMilliseconds 18446744073709552).toPlainNat = 18446744073709551615
example : pinSecondsToMsCaps = true := by native_decide

/-- At `UINT64_MAX // 1000` the guard passes and the product is exact. The inverse
`milliseconds_to_seconds` of `UINT64_MAX` floors back to the same second count. -/
private def pinSecondsToMsAtBound : Bool :=
  letI : Preset := minimal
  (secondsToMilliseconds 18446744073709551).toPlainNat = 18446744073709551000 &&
    (millisecondsToSeconds 18446744073709551615).toPlainNat = 18446744073709551
example : pinSecondsToMsAtBound = true := by native_decide

/-! ### 4. `compute_time_at_slot`: the cap feeds the checked sum -/

/-- A genesis time past the cap: `genesis_time_ms` is `UINT64_MAX`, so slot `1` adds
`6000` past the maximum and raises. -/
private def pinTimeAtSlotCappedGenesisOverflows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  isRangeFault (computeTimeAtSlot 18446744073709552 (1 : Slot))
example : pinTimeAtSlotCappedGenesisOverflows = true := by native_decide

/-- The same genesis time at slot `0`: the sum stays `UINT64_MAX`, and the seconds
floor to `UINT64_MAX // 1000`. -/
private def pinTimeAtSlotCappedGenesisSlotZero : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match computeTimeAtSlot 18446744073709552 (0 : Slot) with
  | .ok t => t.toPlainNat = 18446744073709551
  | .error _ => false
example : pinTimeAtSlotCappedGenesisSlotZero = true := by native_decide

/-! ### 5. The fork-choice store clock -/

/-- The pins' concrete fork-choice monad: the minimal preset over `treeMap`. -/
private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap)

/-- An empty Fulu `Store` at `genesis_time_ms = 6000` with the clock at `timeMs`. -/
private def clockStore (timeMs : CLUint64) : @Store minimal treeMap :=
  letI : Preset := minimal
  { timeMs := timeMs, genesisTimeMs := 6000
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty }

/-- `get_current_slot` with the store time `1` ms before genesis: the clock's checked
subtraction raises, and the lift lands it on the store machine as a nested range fault. -/
private def pinCurrentSlotBeforeGenesis : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let store := clockStore 5999
  match (getCurrentSlot (map := treeMap) store : PinM Slot).run store with
  | .error (.transition (.arithmetic _)) _ => true
  | _ => false
example : pinCurrentSlotBeforeGenesis = true := by native_decide

/-- `on_tick` from genesis to `18001` ms: the catch-up runs the slot starts `12000` and
`18000`, then the final tick sets the clock to exactly `18001`, in slot `2`. -/
private def pinOnTickCatchesUp : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let store := clockStore 6000
  let action : PinM Slot := do
    onTick (map := treeMap) 18001
    getCurrentSlot (← get)
  match action.run store with
  | .ok slot after => slot.toPlainNat = 2 && after.timeMs.toPlainNat = 18001
  | .error _ _ => false
example : pinOnTickCatchesUp = true := by native_decide

end EthCLSpecs.Tests.ClockMigrationPins
