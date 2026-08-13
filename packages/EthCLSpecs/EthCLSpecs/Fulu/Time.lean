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

`computeTimeAtSlot` is the one helper here that can fault, so it returns an
`Except` over the state it is handed. The block pipeline and the fork-choice
store both reach it through `liftErr`, which keeps the clock in one declaration.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `compute_epoch_at_slot(slot)` = `slot // SLOTS_PER_EPOCH`. Pure. -/
forkdef computeEpochAtSlot (slot : Slot) : Epoch := slot / UInt64.ofNat Const.slotsPerEpoch

/-- `compute_start_slot_at_epoch(epoch)` = `epoch * SLOTS_PER_EPOCH`. Pure. -/
forkdef computeStartSlotAtEpoch (epoch : Epoch) : Slot := epoch * UInt64.ofNat Const.slotsPerEpoch

/-- `compute_activation_exit_epoch(epoch)`. Pure. -/
forkdef computeActivationExitEpoch (e : Epoch) : Epoch := e + 1 + Const.maxSeedLookahead

/-- `compute_time_at_slot(state, slot)` = `genesis_time + (slot - GENESIS_SLOT) *
SLOT_DURATION_MS // 1000` (`phase0/beacon-chain.md:900`). The pinned spec text flags the
function itself as "unsafe with respect to overflows and underflows", so all three ops are
checked.

The result is a bare `Except`, the shape `getForkchoiceStore` also returns. The body takes
the boxed state as an argument and reads no machine state, so it needs no monad of its own,
and each caller wraps it in `liftErr` to route the fault through `[ErrorConv …]` to whichever
machine is running. That is what lets one declaration serve both callers:
`process_execution_payload` on the state machine, and the envelope timestamp assert in
`verify_execution_payload_envelope` on the store machine, which Gloas and Heze each reach by
`inherit`.

`get_forkchoice_store` seeds the store clock from a different expression, `genesis_time +
SLOT_DURATION_MS * slot // 1000` (`phase0/fork-choice.md:223`), which agrees with this one
only because `GENESIS_SLOT` is 0. It stays inlined at its own site. -/
forkdef computeTimeAtSlot (state : State) (slot : Slot) : Except StateTransitionError UInt64 := do
  let slotsSinceGenesis ← checkedSub slot Const.genesisSlot
    "compute_time_at_slot: slot - GENESIS_SLOT"
  let elapsedMs ← checkedMul slotsSinceGenesis Const.slotDurationMs
    "compute_time_at_slot: (slot - GENESIS_SLOT) * SLOT_DURATION_MS"
  checkedAdd (sszGet state genesisTime) (elapsedMs / 1000)
    "compute_time_at_slot: genesis_time + (slot - GENESIS_SLOT) * SLOT_DURATION_MS // 1000"

/-- `get_current_epoch(state)`. Monadic: reads `state.slot`. -/
forkdef getCurrentEpoch : StateTransition Epoch := do
  let state ← get
  return computeEpochAtSlot (sszGet state slot)

/-- `get_previous_epoch(state)`: the current epoch minus one, floored at
`GENESIS_EPOCH`. -/
forkdef getPreviousEpoch : StateTransition Epoch := do
  let current ← getCurrentEpoch
  return if current == Const.genesisEpoch then Const.genesisEpoch else current - 1

/-- `get_current_epoch(state)` as a pure function of the boxed state, for use in
the pure `modifyState` / `Id.run` bodies the epoch substeps build. -/
forkdef currentEpochOf (state : State) : Epoch := computeEpochAtSlot (sszGet state slot)

/-- `get_previous_epoch(state)`, pure. -/
forkdef previousEpochOf (state : State) : Epoch :=
  let c := currentEpochOf state
  if c == Const.genesisEpoch then Const.genesisEpoch else c - 1

end

end EthCLSpecs.Fulu
