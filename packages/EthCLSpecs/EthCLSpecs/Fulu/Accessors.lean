import EthCLSpecs.Fulu.Committees

/-!
# `EthCLSpecs.Fulu.Accessors`: the derived float-up accessors (load order row 26)

The read-only accessors whose callees straddle `Balances`, `Registry`, and
`Committees`, so they cannot sit in any one of those low files and float up here
(`SPECS_ARCHITECTURE.md` §3.1 row 26, §3.3): `get_total_active_balance` (reads the
active set and totals it), `get_unslashed_participating_indices`, the block-root
history reads, and `get_pending_balance_to_withdraw`. This is the specific set the
read/write seam forces above `Committees`; it is not a by-kind grab-bag of every
accessor.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_total_active_balance`. -/
forkdef getTotalActiveBalance (state : State) : Gwei :=
  getTotalBalance state (getActiveValidatorIndices state (computeEpochAtSlot (sszGet state slot)))

/-- `get_unslashed_participating_indices(state, flag_index, epoch)`. No committees. -/
forkdef getUnslashedParticipatingIndices (state : State) (flagIndex : Nat) (epoch : Epoch) :
    Array ValidatorIndex := Id.run do
  let isCurrent := epoch == computeEpochAtSlot (sszGet state slot)
  let part := if isCurrent then sszGet state currentEpochParticipation else sszGet state previousEpochParticipation
  let validators := sszGet state validators
  let mut out : Array ValidatorIndex := #[]

  for i in getActiveValidatorIndices state epoch do
    let idx := i.toNat
    if hasFlag (part[idx]!) flagIndex && !(validators[idx]!).slashed then out := out.push i
  return out

/-- `get_block_root_at_slot`. The pinned `assert slot < state.slot <= slot +
SLOTS_PER_HISTORICAL_ROOT` is a recency guard that raises for a stale or future
slot; throwing (`StateTransition`), so callers bind it. Unreachable in normal epoch
processing (`start_slot < state.slot` holds), fires only on degenerate epoch-boundary
near-zero-stake states (the path that makes `compute_pulled_up_tip`'s pjf reject
reachable). -/
forkdef getBlockRootAtSlot (state : State) (s : Slot) : StateTransition Root := do
  assert (s < (sszGet state slot) && (sszGet state slot) ≤ s + UInt64.ofNat Const.slotsPerHistoricalRoot)
  pure (vmodGet (sszGet state blockRoots) s Const.slotsPerHistoricalRoot)

/-- `get_block_root` (the epoch's first slot). -/
forkdef getBlockRoot (state : State) (epoch : Epoch) : StateTransition Root :=
  getBlockRootAtSlot state (epoch * UInt64.ofNat Const.slotsPerEpoch)

/-- `get_pending_balance_to_withdraw`. -/
forkdef getPendingBalanceToWithdraw (state : State) (vi : ValidatorIndex) : Gwei :=
  (sszGet state pendingPartialWithdrawals).foldl
    (fun acc w => if w.validatorIndex == vi then acc + w.amount else acc) 0

end

end EthCLSpecs.Fulu
