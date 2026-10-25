import EthCLSpecs.Fulu.State

/-!
# `EthCLSpecs.Fulu.Time`: slot / epoch accessors (load order row 20)

The time-domain helpers (`SPECS_ARCHITECTURE.md` §3.1 row 20). `computeEpochAtSlot`
is state-free and pure. Accessors that read the
threaded state come in two shapes, the monadic `getCurrentEpoch` / `getPreviousEpoch`
and the pure `currentEpochOf` / `previousEpochOf` (functions of the boxed state, for
the `modifyState` / `Id.run` bodies the epoch substeps build), the state-free-pure /
state-reading-monadic split of §5. They are `forkdef`s so a later fork can
`inherit` them.

`computeStartSlotAtEpoch`, `computeActivationExitEpoch`, and `computeTimeAtSlot` are the
three helpers here that can fault, so each returns an `Except`. The first two are
state-free. The first faults on its multiply, and the second on its additions. The third
is handed the state. The block pipeline and the fork-choice store both reach
`computeTimeAtSlot` through `liftErr`, which keeps the clock in one declaration.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `compute_epoch_at_slot(slot)` = `slot // SLOTS_PER_EPOCH`. Pure. -/
forkdef computeEpochAtSlot (slot : Slot) : Epoch := slot / UInt64.ofNat Const.slotsPerEpoch

/-- `compute_start_slot_at_epoch(epoch)` = `epoch * SLOTS_PER_EPOCH`
(`phase0/beacon-chain.md:918`). The pyspec multiplies two bare `uint64` values. Remerkleable
re-runs its bound check on the product and raises `ValueError` above `2 ^ 64`. The runner does
not catch that fault. So the multiply is `checkedMul`, and the reject is `.arithmetic`.

Most callers pass an epoch that `computeEpochAtSlot` produced. The fault cannot occur there,
because `(s / n) * n ≤ s` for every `n`. `EthCLSpecs.Proofs.Fulu.Time` proves this. The other
callers pass a checkpoint epoch from a deserialized state. The spec does not bound that epoch.

The return type is a bare `Except`, which follows `computeTimeAtSlot` below. -/
forkdef computeStartSlotAtEpoch (epoch : Epoch) : Except StateTransitionError Slot :=
  checkedMul epoch (UInt64.ofNat Const.slotsPerEpoch)
    "compute_start_slot_at_epoch: epoch * SLOTS_PER_EPOCH"

/-- `compute_activation_exit_epoch(epoch)` = `epoch + 1 + MAX_SEED_LOOKAHEAD`
(`phase0/beacon-chain.md:928`). The pyspec adds on bare `uint64` values, and remerkleable
raises `ValueError` when a sum passes `2 ^ 64 - 1`. So each addition is `checkedAdd`, in the
spec's order, and the reject is `.arithmetic`.

Every caller passes the current epoch, which `computeEpochAtSlot` produced. That epoch is at
most `(2 ^ 64 - 1) / SLOTS_PER_EPOCH`, so the fault cannot occur there.
`EthCLSpecs.Proofs.Fulu.Time` proves this. -/
forkdef computeActivationExitEpoch (e : Epoch) : Except StateTransitionError Epoch := do
  let next ← checkedAdd e 1 "compute_activation_exit_epoch: epoch + 1"
  checkedAdd next Const.maxSeedLookahead
    "compute_activation_exit_epoch: epoch + 1 + MAX_SEED_LOOKAHEAD"

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
