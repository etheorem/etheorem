import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Tests.ConfigurationClockPins`: the clock at arbitrary configurations

Behavior pins for the clock at arbitrary configurations: the clock keeps the pinned
pyspec's answers for every accepted `SLOT_DURATION_MS`, the shipped `6000` and `12000` and
also `0`, `1`, `2^63`, and `UINT64_MAX`. `SLOT_DURATION_MS` is a configuration value, so it
carries no positivity proof, and the clock divides by it through the checked route
(`SPEC_ARITHMETIC.md` §4.2). A zero duration raises Python's `ZeroDivisionError`, which
`Checked` types as the `.zeroDivision` cause and the store machine lands as
`.transition (.zeroDivision _)`.

The divisions by configuration values:

| Site | Divisor | Route |
|---|---|---|
| `compute_slot_at_time_ms` | `SLOT_DURATION_MS` (config) | checked `//`, raises on zero |
| `get_slot_component_duration_ms` | `BASIS_POINTS` (the constant `10000`) | checked `//`, never zero |
| `get_balance_churn_limit` and the Gloas churn limits | `CHURN_LIMIT_QUOTIENT`, `CONSOLIDATION_CHURN_LIMIT_QUOTIENT` (config) | checked `//`, raises on zero |
| `process_inactivity_updates` penalty | `INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX` | checked product, then checked `//` |

This module pins the clock row. The other rows take the checked route, and
`Tests/ConstantAuditPins.lean` pins their constants. Every other clock divisor is the literal
`1000`, a `PositiveDivisor`.

Every expected value below is the answer of the pinned pyspec (`eth-consensus-specs`
1.7.0b4, the `minimal` module with `config.SLOT_DURATION_MS` replaced), read by running the
probes. Fulu, Gloas, and Heze gave the same answers. Each failure pin has a nearby success
that reaches the same operation.

1. Zero duration. `compute_slot_at_time_ms` and every store reader above it raise the zero
   divisor. A time before genesis raises the range fault first, because Python subtracts
   before it divides. `compute_time_at_slot_ms` and the slot deadlines multiply by zero, so
   they succeed. Duration `1` keeps the same calls on the success path.
2. Duration `2^63`. The product `slot * SLOT_DURATION_MS` raises at slot `2`, and the sum
   `genesis_time_ms + …` raises at genesis `2^63`. Slot `1` and genesis `2^63 - 1` succeed.
3. Duration `UINT64_MAX`. The clock still counts slot `1` at `UINT64_MAX` ms, and `on_tick`
   reaches it. The deadline product raises at basis points `2`, where `1` succeeds.
4. The shipped duration. The `seconds_to_milliseconds` cap feeds `compute_slot_at_time`.

The last section evaluates the unchecked forms on raw `UInt64` at the same inputs. Each
returns a value where the matching pin expects a fault. The pins close by `native_decide`, as
the other migration pins do: the minimal configuration is a large record, and the store runs
on the compiled `treeMap`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.ConfigurationClockPins

/-- What a clock call produced: the answer as a plain `Nat`, a range fault (Python's
`SSZValueError`), the zero divisor (Python's `ZeroDivisionError`), or another error. -/
private inductive Outcome where
  | answer (n : Nat)
  | rangeFault
  | zeroDivision
  | otherFault
  deriving DecidableEq

/-- Classify a `Checked` clock helper's result. -/
private def checkedOutcome : Checked CLUint64 → Outcome
  | .ok v => .answer v.toPlainNat
  | .error ⟨.range, _, _, _, _⟩ => .rangeFault
  | .error ⟨.zeroDivision, _, _, _, _⟩ => .zeroDivision

/-- Classify a store-machine error. The arithmetic lift lands a `Checked` fault one level
down, under `.transition`. -/
private def storeErrorOutcome : StoreTransitionError → Outcome
  | .transition (.arithmetic _) => .rangeFault
  | .transition (.zeroDivision _) => .zeroDivision
  | _ => .otherFault

/-- Classify a store run that returns a clock value. -/
private def storeOutcome {σ : Type} : EStateM.Result StoreTransitionError σ CLUint64 → Outcome
  | .ok v _ => .answer v.toPlainNat
  | .error e _ => storeErrorOutcome e

/-- `2^63`, the least duration whose product with slot `2` passes `2^64 - 1`. -/
private abbrev halfRange : CLUint64 := 9223372036854775808

/-- `UINT64_MAX`. -/
private abbrev u64Max : CLUint64 := 18446744073709551615

/-! ### Fulu: the clock helpers -/

section Fulu
open EthCLSpecs.Fulu

/-- The minimal configuration with `SLOT_DURATION_MS = d`. -/
@[instance_reducible]
private def durationConfig (d : CLUint64) : Config :=
  { minimalConfig with slotDurationMs := d }

/-- `compute_slot_at_time_ms(genesis_time_ms, time_ms)` at duration `d`. -/
private def slotAtTimeMs (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  checkedOutcome (computeSlotAtTimeMs genesisTimeMs timeMs)

/-- `compute_time_at_slot_ms(genesis_time_ms, slot)` at duration `d`. -/
private def timeAtSlotMs (d genesisTimeMs : CLUint64) (slot : Slot) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  checkedOutcome (computeTimeAtSlotMs genesisTimeMs slot)

/-- `compute_slot_at_time(genesis_time, time)`, in seconds, at duration `d`. -/
private def slotAtTime (d genesisTime time : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  checkedOutcome (computeSlotAtTime genesisTime time)

/-- `compute_time_at_slot(genesis_time, slot)`, in seconds, at duration `d`. -/
private def timeAtSlot (d genesisTime : CLUint64) (slot : Slot) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  checkedOutcome (computeTimeAtSlot genesisTime slot)

/-- `get_slot_component_duration_ms(basis_points)` at duration `d`. -/
private def deadlineMs (d bps : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  checkedOutcome (bpsDeadlineMs bps)

-- 1. Zero duration: the division raises, and the subtraction raises first before genesis.
example : slotAtTimeMs 0 6000 6000 = .zeroDivision := by native_decide
example : slotAtTimeMs 0 6000 5999 = .rangeFault := by native_decide
example : slotAtTime 0 6 6 = .zeroDivision := by native_decide
-- The products by zero succeed: the slot start is genesis, and the deadline is `0`.
example : timeAtSlotMs 0 6000 5 = .answer 6000 := by native_decide
example : timeAtSlot 0 6 5 = .answer 6 := by native_decide
example : deadlineMs 0 3333 = .answer 0 := by native_decide
-- Duration `1`, the least valid duration, at the same calls.
example : slotAtTimeMs 1 6000 6005 = .answer 5 := by native_decide
example : timeAtSlotMs 1 6000 5 = .answer 6005 := by native_decide
example : deadlineMs 1 3333 = .answer 0 := by native_decide

-- 2. Duration `2^63`: the product raises at slot `2`, the sum at genesis `2^63`.
example : timeAtSlotMs halfRange 0 1 = .answer 9223372036854775808 := by native_decide
example : timeAtSlotMs halfRange 0 2 = .rangeFault := by native_decide
example : timeAtSlotMs halfRange 9223372036854775807 1 = .answer 18446744073709551615 := by
  native_decide
example : timeAtSlotMs halfRange halfRange 1 = .rangeFault := by native_decide

-- 3. Duration `UINT64_MAX`: slot `1` starts at the last millisecond.
example : slotAtTimeMs u64Max 0 u64Max = .answer 1 := by native_decide
example : slotAtTimeMs u64Max 0 18446744073709551614 = .answer 0 := by native_decide
example : slotAtTimeMs u64Max 1 u64Max = .answer 0 := by native_decide
-- The deadline product fits at basis points `1` and raises at `2`.
example : deadlineMs u64Max 1 = .answer 1844674407370955 := by native_decide
example : deadlineMs u64Max 2 = .rangeFault := by native_decide

-- 4. The shipped duration: past `UINT64_MAX // 1000` seconds, the capped clock reads
-- `UINT64_MAX // 6000`.
example : slotAtTime 6000 0 18446744073709552 = .answer 3074457345618258 := by native_decide

end Fulu

/-! ### The store clock in each fork

Fulu defines `get_current_slot`, `get_time_into_slot_ms`, and `on_tick`. Gloas restates them,
and Heze inherits the Gloas declarations. Each fork elaborates its own constants, so each
fork has its own pins. A tick run reports the slot after the tick, or the fault, and the
store time after the run. A zero duration raises before `on_tick` writes the store, as in
Python.
-/

section Fulu
open EthCLSpecs.Fulu

/-- The Fulu pins' fork-choice monad. -/
private abbrev FuluPinM := EStateM StoreTransitionError (@Store minimal treeMap)

/-- An empty Fulu `Store` with the clock at `timeMs` and genesis at `genesisTimeMs`. -/
private def fuluStore (genesisTimeMs timeMs : CLUint64) : @Store minimal treeMap :=
  letI : Preset := minimal
  { timeMs := timeMs, genesisTimeMs := genesisTimeMs
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

/-- `get_current_slot` at duration `d`. -/
private def fuluCurrentSlot (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  let store := fuluStore genesisTimeMs timeMs
  storeOutcome ((getCurrentSlot (map := treeMap) store : FuluPinM Slot).run store)

/-- `get_time_into_slot_ms` at duration `d`. -/
private def fuluTimeIntoSlot (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  let store := fuluStore genesisTimeMs timeMs
  storeOutcome ((getTimeIntoSlotMs (map := treeMap) store : FuluPinM CLUint64).run store)

/-- `on_tick(store, to)` at duration `d`, then the current slot. -/
private def fuluTick (d genesisTimeMs timeMs to : CLUint64) : Outcome × Nat :=
  letI : Preset := minimal
  letI : Config := durationConfig d
  let action : FuluPinM Slot := do
    onTick (map := treeMap) to
    getCurrentSlot (← get)
  match action.run (fuluStore genesisTimeMs timeMs) with
  | .ok slot after => (.answer slot.toPlainNat, after.timeMs.toPlainNat)
  | .error e after => (storeErrorOutcome e, after.timeMs.toPlainNat)

example : fuluCurrentSlot 0 6000 6000 = .zeroDivision := by native_decide
example : fuluCurrentSlot 1 6000 6005 = .answer 5 := by native_decide
example : fuluTimeIntoSlot 0 6000 6000 = .zeroDivision := by native_decide
example : fuluTimeIntoSlot u64Max 0 u64Max = .answer 0 := by native_decide
example : fuluTick 0 6000 6000 12000 = (.zeroDivision, 6000) := by native_decide
example : fuluTick 1 6000 6000 6002 = (.answer 2, 6002) := by native_decide
example : fuluTick u64Max 0 0 u64Max = (.answer 1, 18446744073709551615) := by native_decide

end Fulu

section Gloas
open EthCLSpecs.Gloas

/-- The minimal Gloas configuration with `SLOT_DURATION_MS = d`. -/
@[instance_reducible]
private def gloasDurationConfig (d : CLUint64) : Config :=
  { minimalConfig with slotDurationMs := d }

/-- The Gloas pins' fork-choice monad. -/
private abbrev GloasPinM := EStateM StoreTransitionError (@Store minimal treeMap)

/-- An empty Gloas `Store` with the clock at `timeMs` and genesis at `genesisTimeMs`. -/
private def gloasStore (genesisTimeMs timeMs : CLUint64) :
    @Store minimal treeMap :=
  letI : Preset := minimal
  { timeMs := timeMs, genesisTimeMs := genesisTimeMs
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty }

/-- `get_current_slot` at duration `d`. -/
private def gloasCurrentSlot (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := gloasDurationConfig d
  let store := gloasStore genesisTimeMs timeMs
  storeOutcome ((getCurrentSlot (map := treeMap) store : GloasPinM Slot).run store)

/-- `get_time_into_slot_ms` at duration `d`. -/
private def gloasTimeIntoSlot (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := gloasDurationConfig d
  let store := gloasStore genesisTimeMs timeMs
  storeOutcome ((getTimeIntoSlotMs (map := treeMap) store : GloasPinM CLUint64).run store)

/-- `get_slot_component_duration_ms(basis_points)` (the Gloas restatement) at duration `d`. -/
private def gloasDeadlineMs (d bps : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := gloasDurationConfig d
  checkedOutcome (bpsDeadlineMs bps)

/-- `on_tick(store, to)` at duration `d`, then the current slot. -/
private def gloasTick (d genesisTimeMs timeMs to : CLUint64) : Outcome × Nat :=
  letI : Preset := minimal
  letI : Config := gloasDurationConfig d
  let action : GloasPinM Slot := do
    onTick (map := treeMap) to
    getCurrentSlot (← get)
  match action.run (gloasStore genesisTimeMs timeMs) with
  | .ok slot after => (.answer slot.toPlainNat, after.timeMs.toPlainNat)
  | .error e after => (storeErrorOutcome e, after.timeMs.toPlainNat)

example : gloasCurrentSlot 0 6000 6000 = .zeroDivision := by native_decide
example : gloasCurrentSlot 1 6000 6005 = .answer 5 := by native_decide
example : gloasTimeIntoSlot 0 6000 6000 = .zeroDivision := by native_decide
example : gloasTimeIntoSlot u64Max 0 u64Max = .answer 0 := by native_decide
example : gloasDeadlineMs 0 3333 = .answer 0 := by native_decide
example : gloasDeadlineMs u64Max 1 = .answer 1844674407370955 := by native_decide
example : gloasDeadlineMs u64Max 2 = .rangeFault := by native_decide
example : gloasTick 0 6000 6000 12000 = (.zeroDivision, 6000) := by native_decide
example : gloasTick 1 6000 6000 6002 = (.answer 2, 6002) := by native_decide
example : gloasTick u64Max 0 0 u64Max = (.answer 1, 18446744073709551615) := by native_decide

end Gloas

section Heze
open EthCLSpecs.Heze

/-- The minimal Heze configuration with `SLOT_DURATION_MS = d`. -/
@[instance_reducible]
private def hezeDurationConfig (d : CLUint64) : Config :=
  { minimalConfig with slotDurationMs := d }

/-- The Heze pins' fork-choice monad. -/
private abbrev HezePinM := EStateM StoreTransitionError (@Store minimal treeMap)

/-- An empty Heze `Store` with the clock at `timeMs` and genesis at `genesisTimeMs`. -/
private def hezeStore (genesisTimeMs timeMs : CLUint64) :
    @Store minimal treeMap :=
  letI : Preset := minimal
  { timeMs := timeMs, genesisTimeMs := genesisTimeMs
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction := FcMap.empty
    inclusionListStore := InclusionListStore.empty }

/-- `get_current_slot` at duration `d`. -/
private def hezeCurrentSlot (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := hezeDurationConfig d
  let store := hezeStore genesisTimeMs timeMs
  storeOutcome ((getCurrentSlot (map := treeMap) store : HezePinM Slot).run store)

/-- `get_time_into_slot_ms` at duration `d`. -/
private def hezeTimeIntoSlot (d genesisTimeMs timeMs : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := hezeDurationConfig d
  let store := hezeStore genesisTimeMs timeMs
  storeOutcome ((getTimeIntoSlotMs (map := treeMap) store : HezePinM CLUint64).run store)

/-- `on_tick(store, to)` at duration `d`, then the current slot. -/
private def hezeTick (d genesisTimeMs timeMs to : CLUint64) : Outcome × Nat :=
  letI : Preset := minimal
  letI : Config := hezeDurationConfig d
  let action : HezePinM Slot := do
    onTick (map := treeMap) to
    getCurrentSlot (← get)
  match action.run (hezeStore genesisTimeMs timeMs) with
  | .ok slot after => (.answer slot.toPlainNat, after.timeMs.toPlainNat)
  | .error e after => (storeErrorOutcome e, after.timeMs.toPlainNat)

example : hezeCurrentSlot 0 6000 6000 = .zeroDivision := by native_decide
example : hezeCurrentSlot 1 6000 6005 = .answer 5 := by native_decide
example : hezeTimeIntoSlot 0 6000 6000 = .zeroDivision := by native_decide
example : hezeTimeIntoSlot u64Max 0 u64Max = .answer 0 := by native_decide
example : hezeTick 0 6000 6000 12000 = (.zeroDivision, 6000) := by native_decide
example : hezeTick 1 6000 6000 6002 = (.answer 2, 6002) := by native_decide
example : hezeTick u64Max 0 0 u64Max = (.answer 1, 18446744073709551615) := by native_decide

end Heze

/-! ### The unchecked forms

An unchecked clock computes on raw `UInt64`, which wraps on overflow and answers `0` for a
division by zero. At each failure pin's inputs the raw form returns a value, so it would fail
the pin. -/

-- Zero duration: `(time_ms - genesis_time_ms) // 0` answers slot `0`, also before genesis.
#guard ((6000 : UInt64) - 6000) / 0 == 0
#guard ((5999 : UInt64) - 6000) / 0 == 0
-- Duration `2^63`: the product at slot `2` and the sum at genesis `2^63` both wrap to `0`.
#guard (2 : UInt64) * 9223372036854775808 == 0
#guard (9223372036854775808 : UInt64) + 1 * 9223372036854775808 == 0
-- Duration `UINT64_MAX`: the deadline product at basis points `2` wraps, and the quotient
-- repeats the answer for basis points `1`.
#guard (2 : UInt64) * 18446744073709551615 / 10000 == 1844674407370955
-- A bare seconds product with no cap wraps to `384`, so the slot reads `0`.
#guard (18446744073709552 : UInt64) * 1000 / 6000 == 0

end EthCLSpecs.Tests.ConfigurationClockPins
