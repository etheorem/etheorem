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

/-- `get_total_active_balance`. The total folds the active set's
`effective_balance` values, a checked `sum` in the pyspec (`SPEC_ARITHMETIC.md`
§3.2), so the result carries the fold's fault, after the active set's checked casts and
the total's raising registry reads. -/
forkdef getTotalActiveBalance (state : State) : Except StateTransitionError Gwei := do
  let active ← getActiveValidatorIndices state (computeEpochAtSlot (sszGet state slot))
  getTotalBalance state active

/-- `get_unslashed_participating_indices(state, flag_index, epoch)`
(`fulu/minimal.py:4380-4396`). No committees. The pyspec reads `epoch_participation[index]`
for every active index first, then `state.validators[index].slashed` for each participating
one; both reads raise `IndexError` past the end, so they go through `getAt` in that order.
`has_flag`'s mask `ParticipationFlags(2**flag_index)` raises past flag index 7, so the
test binds after the read it evaluates beside (`SPEC_ARITHMETIC.md` §5.1). The pyspec's
leading `assert epoch in (previous, current)` has no Lean twin: every caller passes the
previous or the current epoch. -/
forkdef getUnslashedParticipatingIndices (state : State) (flagIndex : Nat) (epoch : Epoch) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let isCurrent := epoch == computeEpochAtSlot (sszGet state slot)
  let part := if isCurrent then sszGet state currentEpochParticipation else sszGet state previousEpochParticipation
  let validators := sszGet state validators
  let active ← getActiveValidatorIndices state epoch
  let mut participating : Array ValidatorIndex := #[]
  for i in active do
    if ← CLUint8.hasFlag (← liftErr (getAt part i)) flagIndex then participating := participating.push i
  let mut out : Array ValidatorIndex := #[]
  for i in participating do
    if !(← liftErr (getAt validators i)).slashed then out := out.push i
  return out

/-- `get_block_root_at_slot` (`fulu/mainnet.py:1447-1452`). The pinned
`assert slot < state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT` is a recency guard that raises
for a stale or future slot; throwing (`StateTransition`), so callers bind it. Unreachable in
normal epoch processing (`start_slot < state.slot` holds), fires only on degenerate
epoch-boundary near-zero-stake states (the path that makes `compute_pulled_up_tip`'s pjf
reject reachable). The `slot + SLOTS_PER_HISTORICAL_ROOT` sum adds two checked `Slot` values
(the pinned constant is `Slot(64)`, `fulu/minimal.py:189`), so it binds (`SPEC_ARITHMETIC.md`
§4.3). The ring read passes
the checked value's word to the proved-total `vmodGet` route, whose bound is the mod
itself. -/
forkdef getBlockRootAtSlot (state : State) (s : Slot) : StateTransition Root := do
  -- `assert slot < state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT`. Python's chained comparison
  -- short-circuits: `slot < state.slot` is checked first (a caught `AssertionError`), and only then
  -- is `slot + SPHR` formed. That `uint64` sum raises `ValueError` on overflow, an uncaught fault the
  -- runner does not catch, so it binds (the checked add) after the first assert.
  assert (s < sszGet state slot)
  let bound ← s + Const.slotsPerHistoricalRootC
  assert (sszGet state slot ≤ bound)
  pure (vmodGet (sszGet state blockRoots) s.val Const.slotsPerHistoricalRoot)

/-- `get_block_root` (`fulu/mainnet.py:1443-1445`): the epoch's first slot. The start slot
is `compute_start_slot_at_epoch`, so its checked product binds here. -/
forkdef getBlockRoot (state : State) (epoch : Epoch) : StateTransition Root := do
  getBlockRootAtSlot state (← computeStartSlotAtEpoch epoch)

/-- `get_pending_balance_to_withdraw`. The accumulator is a `Gwei` and each
`balance += withdrawal.amount` is a checked add (`SPEC_ARITHMETIC.md` §3.2, the
`sum` row), so the fold carries its fault. -/
forkdef getPendingBalanceToWithdraw (state : State) (vi : ValidatorIndex) : Checked Gwei :=
  (sszGet state pendingPartialWithdrawals).val.foldlM
    (fun acc w => if w.validatorIndex == vi then acc + w.amount else pure acc) (0 : Gwei)

end

end EthCLSpecs.Fulu
