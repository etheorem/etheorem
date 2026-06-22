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
