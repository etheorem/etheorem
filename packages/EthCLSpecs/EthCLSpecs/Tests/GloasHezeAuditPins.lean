import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Tests.GloasHezeAuditPins`: the Gloas and Heze audit pins

Pins for the manual audit of the Gloas and Heze fork bodies (Stage 8.4a4). The audit fixed one
fault order. Every value comes from the pinned pyspec (1.7.0b4).

`is_previous_slot_payload_decision` and `should_extend_payload` (Gloas; Heze restates the second)
compare `store.blocks[root].slot + 1 == get_current_slot(store)`. Python evaluates the left
operand first, so the checked `Slot` add raises before the clock runs. The clock can raise a
different class: `compute_slot_at_time_ms` divides by the configuration value `SLOT_DURATION_MS`,
and a zero value raises `ZeroDivisionError`. The old bodies read the clock first, so a block at
`slot = UINT64_MAX` under a zero slot duration rejected with `.zeroDivision` where Python raises the
range fault (`ValueError`). The runner tells the two classes apart (`SPEC_ARITHMETIC.md` §1).

Each pin runs the body on a store whose one block sits at `UINT64_MAX`, under a configuration with
`SLOT_DURATION_MS = 0`, and expects the `.arithmetic` reject. A control pin puts the block at slot
`0`: the add succeeds, and the clock's `.zeroDivision` surfaces. The stores hash nothing, so
`#guard` evaluates the pins directly.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Cache

namespace EthCLSpecs.Tests.GloasHezeAuditPins

/-- Which reject class a run surfaced, or `answer` when it succeeded. Naming the class is the
point of these pins: the fix changes `.zeroDivision` into `.arithmetic`. -/
inductive Outcome where
  | answer
  | arithmetic
  | zeroDivision
  | other
  deriving DecidableEq

/-- Folds a store run's result into its `Outcome`. -/
def classify {α σ : Type} : EStateM.Result StoreTransitionError σ α → Outcome
  | .ok _ _ => .answer
  | .error (.transition (.arithmetic _)) _ => .arithmetic
  | .error (.transition (.zeroDivision _)) _ => .zeroDivision
  | .error _ _ => .other

private def pinRoot : EthCLSpecs.Gloas.Root := Vector.replicate 32 7

/-- `UINT64_MAX`, the slot whose `+ 1` raises. -/
private def maxSlot : CLUint64 := 18446744073709551615

namespace Gloas

open EthCLSpecs.Gloas

private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

/-- An empty Gloas store with one block at `slot`, keyed by `pinRoot`. -/
private def pinStore (slot : Slot) : @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { timeMs := 0, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.insert FcMap.empty pinRoot { (default : BeaconBlock) with slot := slot }
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty }

/-- `is_previous_slot_payload_decision` on a FULL node under `SLOT_DURATION_MS = 0`. -/
private def previousSlotDecision (slot : Slot) : Outcome :=
  letI : Preset := minimal
  letI : Config := { minimalConfig with slotDurationMs := 0 }
  letI : HasherTag := fastHasherTag
  let store := pinStore slot
  classify ((isPreviousSlotPayloadDecision (map := treeMap) store (.full pinRoot) :
    PinM Bool).run store)

/-- `should_extend_payload` under `SLOT_DURATION_MS = 0`. -/
private def extendPayload (slot : Slot) : Outcome :=
  letI : Preset := minimal
  letI : Config := { minimalConfig with slotDurationMs := 0 }
  letI : HasherTag := fastHasherTag
  let store := pinStore slot
  classify ((shouldExtendPayload (map := treeMap) store pinRoot : PinM Bool).run store)

-- The add raises first, as in Python.
#guard previousSlotDecision maxSlot = .arithmetic
#guard extendPayload maxSlot = .arithmetic
-- Control: with no overflow the clock's zero divisor surfaces.
#guard previousSlotDecision 0 = .zeroDivision
#guard extendPayload 0 = .zeroDivision

end Gloas

namespace Heze

open EthCLSpecs.Heze

private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

/-- An empty Heze store with one block at `slot`, keyed by `pinRoot`. -/
private def pinStore (slot : Slot) : @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { timeMs := 0, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.insert FcMap.empty pinRoot { (default : BeaconBlock) with slot := slot }
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

/-- Heze's `should_extend_payload` under `SLOT_DURATION_MS = 0`. -/
private def extendPayload (slot : Slot) : Outcome :=
  letI : Preset := minimal
  letI : Config := { minimalConfig with slotDurationMs := 0 }
  letI : HasherTag := fastHasherTag
  let store := pinStore slot
  classify ((shouldExtendPayload (map := treeMap) store pinRoot : PinM Bool).run store)

#guard extendPayload maxSlot = .arithmetic
#guard extendPayload 0 = .zeroDivision

end Heze

end EthCLSpecs.Tests.GloasHezeAuditPins
