import EthCLSpecs.Fulu.State

/-!
# `EthCLSpecs.Fulu.Time`: slot / epoch accessors (load order row 20)

The time-domain helpers (`SPECS_ARCHITECTURE.md` §3.1 row 20). State-free
conversions are pure (`computeEpochAtSlot`, `computeStartSlotAtEpoch`,
`computeActivationExitEpoch`); accessors that read the threaded state come in two
shapes, the monadic `getCurrentEpoch` / `getPreviousEpoch` and the pure
`currentEpochOf` / `previousEpochOf` (functions of the boxed state, for the
`modifyState` / `Id.run` bodies the epoch substeps build), the state-free-pure /
state-reading-monadic split of §5. They are `forkdef`s so a later fork can
`inherit` them.

The clock helpers (`compute_time_at_slot` and its millisecond and slot-at-time
siblings) can fault on a `uint64` over- or underflow, so they return a bare
`Except StateTransitionError`. They take the genesis time, not the state, so the
block pipeline and the fork-choice store both reach the same declarations through
`liftErr`, and the clock lives in one place. At v1.7.0-beta.4 the store counts time in
milliseconds, so `seconds_to_milliseconds` / `milliseconds_to_seconds` (declared in
`phase0/fork-choice.md`) sit here beside the beacon-chain helpers that now call them.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `compute_epoch_at_slot(slot)` = `Epoch(slot // SLOTS_PER_EPOCH)`
(`fulu/mainnet.py:1364-1368`). Pure: the divisor is the preset's proved-positive
`slotsPerEpochDiv` view (`SPEC_ARITHMETIC.md` §4.2, "Total operations with a proof"), so the
quotient needs no range test, and the pyspec's `Epoch(...)` cast of a `Slot` value cannot
fault. -/
forkdef computeEpochAtSlot (slot : Slot) : Epoch :=
  slot / Const.slotsPerEpochDiv

/-- `compute_start_slot_at_epoch(epoch)` = `Slot(epoch) * SLOTS_PER_EPOCH`
(`fulu/mainnet.py:1371-1375`). The product is the pyspec's checked multiply, so it raises
past `2^64 - 1` and the function returns a `Checked` `Slot` (`SPEC_ARITHMETIC.md` §4.2);
the `Slot(...)` cast of an `Epoch` value cannot fault. -/
forkdef computeStartSlotAtEpoch (epoch : Epoch) : Checked Slot :=
  epoch * Const.slotsPerEpochC

/-- `compute_activation_exit_epoch(epoch)` = `epoch + 1 + MAX_SEED_LOOKAHEAD`
(`fulu/mainnet.py:1377-1380`). Two checked adds, tested per operation in Python's
left-to-right order, so each binds (`SPEC_ARITHMETIC.md` §4.3) and the function raises
where the pyspec raises. -/
forkdef computeActivationExitEpoch (e : Epoch) : Checked Epoch := do
  let next ← e + 1
  next + Const.maxSeedLookahead

/-- `seconds_to_milliseconds(seconds)` (`phase0/fork-choice.md:550-557`): convert seconds to
milliseconds, returning `UINT64_MAX` where the product would overflow. Total: the guard runs
before the multiply, so the `* 1000` cannot wrap. The cap is unreachable at realistic times
(`seconds` stays far below `UINT64_MAX // 1000`); it is modeled to mirror the pinned helper. -/
forkdef secondsToMilliseconds (seconds : UInt64) : UInt64 :=
  if seconds > (0xffffffffffffffff : UInt64) / 1000 then (0xffffffffffffffff : UInt64)
  else seconds * 1000

/-- `milliseconds_to_seconds(milliseconds)` (`phase0/fork-choice.md:563-568`): convert
milliseconds to seconds, discarding the remainder. Total. -/
forkdef millisecondsToSeconds (milliseconds : UInt64) : UInt64 := milliseconds / 1000

/-- `compute_time_at_slot_ms(genesis_time_ms, slot)` (`phase0/beacon-chain.md:1316-1321`,
`fulu/mainnet.py:1350-1354`): `genesis_time_ms + slot * SLOT_DURATION_MS`. Both `uint64` ops
raise on overflow in the pyspec (the outer `Uint64(...)` is a cast, not a wrap), so both are
checked, the product first as Python evaluates it.

TEMPORARY CROSSING (removed in Stage 7): `SLOT_DURATION_MS` and `genesis_time_ms` are still
raw `UInt64` words. Each enters the checked kind through the lossless wire iso, and the
result returns to the raw `UInt64` through the underlying-value projection. Stage 7 retypes
the clock values and deletes all three crossings. -/
forkdef computeTimeAtSlotMs (genesisTimeMs : UInt64) (slot : Slot) :
    Except StateTransitionError UInt64 := do
  let elapsedMs ← slot * CLUint64.trustedOfUInt64 Const.slotDurationMs
  let totalMs ← CLUint64.trustedOfUInt64 genesisTimeMs + elapsedMs
  pure totalMs.val

/-- `compute_slot_at_time_ms(genesis_time_ms, time_ms)` (`phase0/beacon-chain.md:1326-1331`,
`fulu/mainnet.py:1357-1361`): `(time_ms - genesis_time_ms) // SLOT_DURATION_MS`. The
subtraction raises on a time before genesis, so it is checked; the divide by the positive
config value cannot fault. The `Slot(...)` cast of the `uint64` quotient cannot fault.

TEMPORARY CROSSING (removed in Stage 7): the clock values are still raw `UInt64` words, so
the quotient enters the checked `Slot` through the lossless wire iso. Stage 7 retypes the
clock values, checks the subtraction on the checked surface, and audits the zero-duration
configuration (Lean's `UInt64` division by zero returns `0`, where the pyspec raises). -/
forkdef computeSlotAtTimeMs (genesisTimeMs timeMs : UInt64) : Except StateTransitionError Slot := do
  let elapsedMs ← checkedSub timeMs genesisTimeMs
    "compute_slot_at_time_ms: time_ms - genesis_time_ms"
  pure (CLUint64.trustedOfUInt64 (elapsedMs / Const.slotDurationMs))

/-- `compute_time_at_slot(genesis_time, slot)` (`phase0/beacon-chain.md:1292-1299`): the
Unix time in seconds at the start of `slot`, through the millisecond clock. The pinned spec
text flags the function as "unsafe with respect to overflows and underflows"; the faults
are `compute_time_at_slot_ms`'s, and `seconds_to_milliseconds` caps its own product at `UINT64_MAX`.

At v1.7.0-beta.4 the function takes `genesis_time` rather than the state, which is what lets
one declaration serve both callers: `process_execution_payload` on the state machine, and the
envelope timestamp assert in `verify_execution_payload_envelope` on the store machine, which
Gloas and Heze each reach by `inherit`. Each caller wraps it in `liftErr`. -/
forkdef computeTimeAtSlot (genesisTime : UInt64) (slot : Slot) :
    Except StateTransitionError UInt64 := do
  let genesisTimeMs := secondsToMilliseconds genesisTime
  let timeMs ← computeTimeAtSlotMs genesisTimeMs slot
  pure (millisecondsToSeconds timeMs)

/-- `compute_slot_at_time(genesis_time, time)` (`phase0/beacon-chain.md:1304-1311`): the
slot at Unix time `time` (seconds), through the millisecond clock. No modeled path calls
it; the spec's callers are validator duties. Kept as the beacon-chain surface. -/
forkdef computeSlotAtTime (genesisTime time : UInt64) : Except StateTransitionError Slot :=
  computeSlotAtTimeMs (secondsToMilliseconds genesisTime) (secondsToMilliseconds time)

/-- `get_current_epoch(state)`. Monadic: reads `state.slot`. -/
forkdef getCurrentEpoch : StateTransition Epoch := do
  let state ← get
  return computeEpochAtSlot (sszGet state slot)

/-- `get_previous_epoch(state)` (`phase0/beacon-chain.md:1428-1432`):
`saturating_sub(get_current_epoch(state), 1)`, the current epoch minus one, floored at
`GENESIS_EPOCH` (which is `0`). -/
forkdef getPreviousEpoch : StateTransition Epoch := do
  return (← getCurrentEpoch).saturatingSub 1

/-- `get_current_epoch(state)` as a pure function of the boxed state, for use in
the pure `modifyState` / `Id.run` bodies the epoch substeps build. -/
forkdef currentEpochOf (state : State) : Epoch := computeEpochAtSlot (sszGet state slot)

/-- `get_previous_epoch(state)`, pure: `saturating_sub(get_current_epoch(state), 1)`. -/
forkdef previousEpochOf (state : State) : Epoch := (currentEpochOf state).saturatingSub 1

