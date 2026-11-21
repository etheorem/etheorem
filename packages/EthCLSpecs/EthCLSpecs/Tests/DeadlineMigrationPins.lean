import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Tests.DeadlineMigrationPins`: the slot deadline pins

Behavior pins for the slot deadlines. `get_slot_component_duration_ms`
computes `basis_points * SLOT_DURATION_MS // BASIS_POINTS`, and every operand is a `Uint64` in
the pinned module, so the product is the checked kind. `bpsDeadlineMs` models it, and the
callers bind its result where Python calls it. All values use the minimal preset's
`SLOT_DURATION_MS = 6000`, with the store's genesis at `0` and the clock in slot `0`, so the store
time is the time into the slot.

The minimal deadlines are `3333 → 1999` (Fulu attestation), `1667 → 1000` (reorg cutoff),
`2500 → 1500` (Gloas attestation), `7500 → 4500` (payload attestation), and `6667 → 4000`
(Heze inclusion list, pinned in `Tests/HezeForkChoicePins.lean`).

1. `bpsDeadlineMs`: the product past `2^64 - 1`. `B = 3074457345618259` is the least basis
   points whose product with `6000` passes the bound. A wrapping product gives `2384`, so a
   wrapping form returns `.ok 0` instead of the range fault. `B - 1` floors exactly.
2. Fulu `is_proposing_on_time`: `<=` against the cutoff, so `1000` ms is on time and `1001` is
   not. A strict `<` answers `false` at `1000`. A cutoff of `B` raises, where the wrapping
   product gives a cutoff of `0` and answers `true` at `0` ms.
3. Fulu `record_block_timeliness`: `<` against the attestation deadline, so `1998` ms is timely
   and `1999` is not. An attestation deadline of `B` raises, where the wrapping product files
   `false`.
4. Gloas `record_block_timeliness`: the two deadlines, each strict, at both edges. Both
   thresholds bind before the list forms, so a payload-attestation deadline of `B` raises
   even for a block outside the current slot. A wrapping form files `[false, false]` there.

The store machine lands a range fault as `.transition (.arithmetic _)`, so `outcomeOf` reads
the range cause one level down. The pins close by `native_decide`, as the other migration
pins do: the minimal configuration is a large record, and the store runs on the compiled
`treeMap`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.DeadlineMigrationPins

/-- What a store run produced: the answer, a range fault, or another error. -/
private inductive Outcome (α : Type) where
  | answer (a : α)
  | rangeFault
  | otherFault
  deriving DecidableEq

/-- Classify a store run. The lift lands a range fault as `.transition (.arithmetic _)`; a zero
divisor takes a separate constructor, so it counts as `.otherFault` here. -/
private def outcomeOf {α σ : Type} : EStateM.Result StoreTransitionError σ α → Outcome α
  | .ok a _ => .answer a
  | .error (.transition (.arithmetic _)) _ => .rangeFault
  | .error _ _ => .otherFault

/-- The least basis points whose product with the minimal `SLOT_DURATION_MS = 6000` passes
`2^64 - 1`: `6000 * B = 2^64 + 2384`. -/
private abbrev overflowBps : CLUint64 := 3074457345618259

/-! ### 1. `bpsDeadlineMs`: the checked product -/

section Fulu
open EthCLSpecs.Fulu

/-- The root under which the Fulu pins file their one block. -/
private def fuluRoot : Root := Vector.replicate 32 9

/-- `B` basis points: the product passes `2^64 - 1`, so the checked multiply raises before
the division. -/
private def pinDeadlineProductOverflows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match bpsDeadlineMs overflowBps with
  | .error ⟨.range, _, _, _, _⟩ => true
  | _ => false
example : pinDeadlineProductOverflows = true := by native_decide

/-- `B - 1` basis points: the product is `2^64 - 3616`, which fits, and the division by `10000`
floors it. The shipped Fulu constants floor to `1999` and `1000`. -/
private def pinDeadlineProductFits : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match bpsDeadlineMs 3074457345618258, bpsDeadlineMs Const.attestationDueBps,
      bpsDeadlineMs Const.proposerReorgCutoffBps with
  | .ok top, .ok attestation, .ok cutoff =>
    top.toPlainNat = 1844674407370954 && attestation.toPlainNat = 1999 &&
      cutoff.toPlainNat = 1000
  | _, _, _ => false
example : pinDeadlineProductFits = true := by native_decide

/-! ### 2. Fulu `is_proposing_on_time` -/

/-- The pins' Fulu fork-choice monad. -/
private abbrev FuluPinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

/-- A Fulu `Store` at genesis `0` with the clock at `timeMs`, holding one default block (slot
`0`, so in the current slot) at `fuluRoot`. -/
private def fuluStore (timeMs : CLUint64) : @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { timeMs := timeMs, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.insert FcMap.empty fuluRoot (default : @BeaconBlock minimal)
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty }

/-- `is_proposing_on_time` at `timeMs` into slot `0`, under `cfg`. -/
private def fuluOnTime (cfg : Config) (timeMs : CLUint64) : Outcome Bool :=
  letI : Preset := minimal
  letI : Config := cfg
  letI : HasherTag := fastHasherTag
  let store := fuluStore timeMs
  outcomeOf ((isProposingOnTime (map := treeMap) store : FuluPinM Bool).run store)

/-- The overflow cutoff config: `PROPOSER_REORG_CUTOFF_BPS = B`. -/
@[instance_reducible]
private def hugeCutoffConfig : Config :=
  { minimalConfig with proposerReorgCutoffBps := overflowBps }

-- The cutoff is inclusive: `1000 <= 1000`.
example : fuluOnTime minimalConfig 1000 = .answer true := by native_decide
example : fuluOnTime minimalConfig 1001 = .answer false := by native_decide
-- The cutoff's product raises, even at `0` ms into the slot.
example : fuluOnTime hugeCutoffConfig 0 = .rangeFault := by native_decide

/-! ### 3. Fulu `record_block_timeliness` -/

/-- `record_block_timeliness` for the block at `fuluRoot`, at `timeMs` into slot `0`, under
`cfg`. The answer is the filed timeliness bit. -/
private def fuluTimeliness (cfg : Config) (timeMs : CLUint64) : Outcome (Option Bool) :=
  letI : Preset := minimal
  letI : Config := cfg
  letI : HasherTag := fastHasherTag
  let store := fuluStore timeMs
  let action : FuluPinM (Option Bool) := do
    let after ← recordBlockTimeliness (map := treeMap) store fuluRoot
    pure (FcMap.lookup after.blockTimeliness fuluRoot)
  outcomeOf (action.run store)

/-- The overflow attestation config: `ATTESTATION_DUE_BPS = B`. -/
@[instance_reducible]
private def hugeAttestationConfig : Config :=
  { minimalConfig with attestationDueBps := overflowBps }

-- The deadline is strict: `1998 < 1999`, and `1999` is late.
example : fuluTimeliness minimalConfig 1998 = .answer (some true) := by native_decide
example : fuluTimeliness minimalConfig 1999 = .answer (some false) := by native_decide
example : fuluTimeliness hugeAttestationConfig 0 = .rangeFault := by native_decide

end Fulu

/-! ### 4. Gloas `record_block_timeliness` -/

section Gloas
open EthCLSpecs.Gloas

/-- The root under which the Gloas pins file their one block. -/
private def gloasRoot : Root := Vector.replicate 32 9

/-- The pins' Gloas fork-choice monad. -/
private abbrev GloasPinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

/-- A Gloas `Store` at genesis `0` with the clock at `timeMs`, holding one default block at
`blockSlot` under `gloasRoot`. -/
private def gloasStore (timeMs : CLUint64) (blockSlot : Slot) :
    @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { timeMs := timeMs, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.insert FcMap.empty gloasRoot
      { (default : @BeaconBlock minimal) with slot := blockSlot }
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty }

/-- `record_block_timeliness` for the block at `gloasRoot` (slot `blockSlot`), at `timeMs` into
slot `0`, under `cfg`. The answer is the filed `[attestation, payload attestation]` pair. -/
private def gloasTimeliness (cfg : Config) (timeMs : CLUint64) (blockSlot : Slot) :
    Outcome (Option (Array Bool)) :=
  letI : Preset := minimal
  letI : Config := cfg
  letI : HasherTag := fastHasherTag
  let store := gloasStore timeMs blockSlot
  let action : GloasPinM (Option (Array Bool)) := do
    let after ← recordBlockTimeliness (map := treeMap) store gloasRoot
    pure (FcMap.lookup after.blockTimeliness gloasRoot)
  outcomeOf (action.run store)

/-- The overflow payload-attestation config: `PAYLOAD_ATTESTATION_DUE_BPS = B`. -/
@[instance_reducible]
private def hugePtcConfig : Config :=
  { minimalConfig with payloadAttestationDueBps := overflowBps }

-- The attestation deadline is strict at `1500`.
example : gloasTimeliness minimalConfig 1499 0 = .answer (some #[true, true]) := by native_decide
example : gloasTimeliness minimalConfig 1500 0 = .answer (some #[false, true]) := by native_decide
-- The payload-attestation deadline is strict at `4500`.
example : gloasTimeliness minimalConfig 4499 0 = .answer (some #[false, true]) := by native_decide
example : gloasTimeliness minimalConfig 4500 0 = .answer (some #[false, false]) := by native_decide
-- A block outside the current slot files `[false, false]` under the shipped config, and the
-- overflowing threshold still raises there: Python binds it before the list forms.
example : gloasTimeliness minimalConfig 0 1 = .answer (some #[false, false]) := by native_decide
example : gloasTimeliness hugePtcConfig 0 1 = .rangeFault := by native_decide

end Gloas

end EthCLSpecs.Tests.DeadlineMigrationPins
