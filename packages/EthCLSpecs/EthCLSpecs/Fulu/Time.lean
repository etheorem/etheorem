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
siblings) can fault on a `uint64` over- or underflow or a zero `SLOT_DURATION_MS`, so they
return `Checked`. They take the genesis time, not the state, so the block pipeline and the
fork-choice store both bind the same declarations through the arithmetic lift, and the clock
lives in one place. At v1.7.0-beta.4 the store counts time in
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
(`fulu/mainnet.py:1378-1382`). Two checked adds, tested per operation in Python's
left-to-right order, so each binds (`SPEC_ARITHMETIC.md` §4.3) and the function raises
where the pyspec raises. -/
forkdef computeActivationExitEpoch (e : Epoch) : Checked Epoch := do
  let next ← e + 1
  next + Const.maxSeedLookahead

/-- `seconds_to_milliseconds(seconds)` (`phase0/fork-choice.md:550-557`): convert seconds to
milliseconds, returning `UINT64_MAX` where the product would overflow. Total
(`SPEC_ARITHMETIC.md` §4.4, a function proved total over its inputs returns `α` directly): the
guard runs before the multiply, so on the multiply branch `seconds ≤ UINT64_MAX // 1000` and
the product `seconds * 1000` is at most `UINT64_MAX`. The range proof builds the value through
`ofNatLT`. The guard's bound `18446744073709551` is `UINT64_MAX // 1000`, a quotient of two
in-range values (`UINT64_MAX` is a `Uint64` at the pin), so the literal gate checks it. The cap
is unreachable at realistic times; it is modeled to mirror the pinned helper. -/
forkdef secondsToMilliseconds (seconds : CLUint64) : CLUint64 :=
  if h : seconds > (18446744073709551 : CLUint64) then 18446744073709551615
  else
    CLUint64.ofNatLT (seconds.toPlainNat * 1000) (by
      -- `h` reads as `¬ (18446744073709551 < seconds.val)` on the native words; move it to
      -- `Nat` and the bound on the product is linear arithmetic.
      have hle : seconds.toPlainNat ≤ 18446744073709551 := by
        have h' : ¬ (18446744073709551 < seconds.val.toNat) := fun hlt =>
          h (UInt64.lt_iff_toNat_lt.mpr hlt)
        show seconds.val.toNat ≤ 18446744073709551
        omega
      show seconds.toPlainNat * 1000 < 18446744073709551616
      omega)

/-- `milliseconds_to_seconds(milliseconds)` (`phase0/fork-choice.md:563-568`): convert
milliseconds to seconds, discarding the remainder. Total: the divisor is the literal `1000`
for every configuration, so the division takes the proved-positive `PositiveDivisor` route
(`SPEC_ARITHMETIC.md` §4.2, "Total operations with a proof"). -/
forkdef millisecondsToSeconds (milliseconds : CLUint64) : CLUint64 :=
  milliseconds / (⟨1000, by decide⟩ : PositiveDivisor)

/-- `compute_time_at_slot_ms(genesis_time_ms, slot)` (`phase0/beacon-chain.md:1316-1321`,
`fulu/mainnet.py:1350-1354`): `genesis_time_ms + slot * SLOT_DURATION_MS`. Both `uint64` ops
raise on overflow in the pyspec, so both are checked binds, the product first as Python
evaluates it. The outer `Uint64(...)` is a cast of a value already in range, so it cannot
fault. -/
forkdef computeTimeAtSlotMs (genesisTimeMs : CLUint64) (slot : Slot) : Checked CLUint64 := do
  let elapsedMs ← slot * Const.slotDurationMs
  genesisTimeMs + elapsedMs

/-- `compute_slot_at_time_ms(genesis_time_ms, time_ms)` (`phase0/beacon-chain.md:1326-1331`,
`fulu/mainnet.py:1357-1361`): `(time_ms - genesis_time_ms) // SLOT_DURATION_MS`. The
subtraction raises on a time before genesis, and the division by the configuration value
`SLOT_DURATION_MS` raises on a zero divisor. A configuration value supplies no positivity
proof, so the division keeps the checked route (`SPEC_ARITHMETIC.md` §4.2). The `Slot(...)`
cast of the `uint64` quotient cannot fault. -/
forkdef computeSlotAtTimeMs (genesisTimeMs timeMs : CLUint64) : Checked Slot := do
  let elapsedMs ← timeMs - genesisTimeMs
  elapsedMs / Const.slotDurationMs

/-- `compute_time_at_slot(genesis_time, slot)` (`phase0/beacon-chain.md:1292-1299`): the
Unix time in seconds at the start of `slot`, through the millisecond clock. The pinned spec
text flags the function as "unsafe with respect to overflows and underflows"; the faults
are `compute_time_at_slot_ms`'s, and `seconds_to_milliseconds` caps its own product at
`UINT64_MAX`.

At v1.7.0-beta.4 the function takes `genesis_time` rather than the state, which is what lets
one declaration serve both callers: `process_execution_payload` on the state machine, and the
envelope timestamp assert in `verify_execution_payload_envelope` on the store machine, which
Gloas and Heze each reach by `inherit`. Each caller binds it with `←`, and the arithmetic lift
lands the fault on that caller's machine. -/
forkdef computeTimeAtSlot (genesisTime : CLUint64) (slot : Slot) : Checked CLUint64 := do
  let genesisTimeMs := secondsToMilliseconds genesisTime
  let timeMs ← computeTimeAtSlotMs genesisTimeMs slot
  pure (millisecondsToSeconds timeMs)

/-- `compute_slot_at_time(genesis_time, time)` (`phase0/beacon-chain.md:1304-1311`): the
slot at Unix time `time` (seconds), through the millisecond clock. No modeled path calls
it; the spec's callers are validator duties. Kept as the beacon-chain surface. -/
forkdef computeSlotAtTime (genesisTime time : CLUint64) : Checked Slot :=
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

