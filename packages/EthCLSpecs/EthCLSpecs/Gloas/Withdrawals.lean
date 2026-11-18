import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Gloas.Withdrawals`: the EIP-7732 builder-aware withdrawal sweep

Gloas reshapes `process_withdrawals` (EIP-7732). It takes no payload, returns early
when the parent block carried no payload, and draws withdrawals from four sources in
order: the builder pending-withdrawal queue, the validator pending-partial queue, a
builder balance sweep, and the validator balance sweep. Each phase threads the
running list so the shared `MAX_WITHDRAWALS_PER_PAYLOAD` cap composes (the first
three reserve one slot for the validator sweep). The applied set is committed to
`payload_expected_withdrawals` for the later envelope check, and balances are
decremented on builders or validators per the index's builder flag.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

state_section

-- Withdrawal predicates (inherited; their credential / max-balance helpers bind to
-- the Gloas copies already in scope).
inherit isFullyWithdrawable
inherit isPartiallyWithdrawable
inherit isEligibleForPartialWithdrawals

/-- `addressOf` over `Gloas.Validator`: the 20-byte execution address in the validator's
withdrawal credentials. Fulu's version is a plain `def` bound to `Fulu.Validator`, so it
is restated here for the Gloas validator. -/
def addressOf (v : Validator) : ExecutionAddress :=
  Vector.ofFn (fun i : Fin 20 => vget v.withdrawalCredentials (12 + i.val))

/-- `get_balance_after_withdrawals` over `Gloas.State`: the balance net of any
already-queued withdrawals for `vi`. Fulu's version is a plain `def` bound to
`Fulu.State`, so it is restated here for the Gloas state.

Throwing (`StateTransition`), because the spec's `return state.balances[validator_index] -
withdrawn` (`capella/beacon-chain.md:421`) raises two ways, neither an explicit `assert`:
`state.balances[validator_index]` is a bare list index (`IndexError` out of range), so it goes
through `sszGetIdx` (→ `outOfBounds`); `- withdrawn` is a bare `uint64` subtraction whose
underflow raises `ValueError`, which the reference runner does NOT catch (`context.py:424-435`),
so it throws the uncaught `.arithmetic` reject rather than a caught `.assert`. Both are
unreachable on a well-formed state (`len(balances) == len(validators)`, and a validator's queued
withdrawals never exceed its balance), and the reads are modeled rather than clamped.

The `withdrawn` accumulator is a `Gwei` and the folded add is the checked `Gwei` `+`,
as in Fulu: pyspec's `sum(...)` accumulates in `Gwei` rather than widening to a Python
`int`, so it raises during the accumulation at the same point, and the final
`balances[i] - withdrawn` is the checked subtraction. See
`Fulu.balanceAfterWithdrawals`. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then acc + w.amount else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi
  bal - withdrawn

/-- `get_builder_withdrawals` (NEW, EIP-7732, `gloas/minimal.py:8003-8030`): drain
`builder_pending_withdrawals` into validator-flagged withdrawals, capped at
`MAX_WITHDRAWALS_PER_PAYLOAD - 1`. `withdrawal_index += 1` is the checked `WithdrawalIndex`
add, so it raises past `2^64 - 1`.

The four phases share three plain-integer conventions. `MAX_WITHDRAWALS_PER_PAYLOAD - 1` is
the checked `Uint64` subtraction, formed before the loop as Python does, so it raises for a
zero preset value. `len(all_withdrawals) >= withdrawals_limit` compares a plain length with
a checked limit, and `int(x)` carries the limit into the plain kind for the comparison.
Each phase's `processed_count` is a pinned `Uint64` counter kept as a structural `Nat`: it
counts entries of a list or a sweep window below `2^64`, so its checked `+= 1` cannot raise,
and its consumers (a slice start, and the builder cursor's mixed add) compute the same value
from the `Nat`. -/
forkdef getBuilderWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : StateTransition (Array Withdrawal × WithdrawalIndex × Nat) := do
  let state ← get
  let limit ← Const.maxWithdrawalsPerPayloadC - 1
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]

  for w in (sszGet state builderPendingWithdrawals) do
    if len (prior ++ ws) ≥ limit.toCLInt then break
    ws := ws.push
      { index := wi, validatorIndex := convertBuilderIndexToValidatorIndex w.builderIndex,
        address := w.feeRecipient, amount := w.amount }
    wi ← wi + 1
    count := count + 1
  return (ws, wi, count)

/-- `get_pending_partial_withdrawals` (Electra, threaded-prior form): the pending
partial queue, capped at `min(len(prior) + MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP,
MAX_WITHDRAWALS_PER_PAYLOAD - 1)`. An out-of-range `validator_index` rejects (the
spec's `IndexError`). -/
forkdef getPendingPartialWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : StateTransition (Array Withdrawal × WithdrawalIndex × Nat) := do
  let state ← get
  let epoch := currentEpochOf state
  -- `min(len(prior_withdrawals) + MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP,
  -- MAX_WITHDRAWALS_PER_PAYLOAD - 1)`: the plain length plus a checked constant is the mixed
  -- route, the subtraction is the checked one, and `min` picks an operand of one kind.
  let pendingCap ← len prior + Const.maxPendingPartialsPerWithdrawalsSweepC
  let payloadCap ← Const.maxWithdrawalsPerPayloadC - 1
  let limit := min pendingCap payloadCap
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]

  for w in (sszGet state pendingPartialWithdrawals) do
    let allW := prior ++ ws
    if !(w.withdrawableEpoch ≤ epoch) || len allW ≥ limit.toCLInt then break
    let vi := w.validatorIndex
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state vi allW
    if isEligibleForPartialWithdrawals validator bal then
      -- `withdrawal_amount = min(balance - MIN_ACTIVATION_BALANCE, withdrawal.amount)`:
      -- the checked subtraction, formed only in this branch.
      let excess ← bal - Const.minActivationBalance
      ws := ws.push
        { index := wi, validatorIndex := vi, address := addressOf validator,
          amount := min excess w.amount }
      wi ← wi + 1
    count := count + 1
  return (ws, wi, count)

/-- `get_builder_balance_after_withdrawals(state, builder_index, withdrawals)` (NEW at
v1.7.0-beta.4, `gloas/beacon-chain.md:1895-1906`): the builder's balance net of the
withdrawals already queued for it, floored at zero (`saturating_sub`). A builder withdrawal
carries the builder's flagged validator index, so the match is on
`convert_builder_index_to_validator_index`. The `withdrawn` sum is the checked `Gwei` fold:
pyspec's `sum(...)` accumulates in `Gwei` and raises on overflow. `state.builders[i]` is a bare
list index, so an out-of-range index rejects through `sszGetIdx`. -/
forkdef getBuilderBalanceAfterWithdrawals (state : State) (builderIndex : BuilderIndex)
    (ws : Array Withdrawal) : StateTransition Gwei := do
  let validatorIndex := convertBuilderIndexToValidatorIndex builderIndex
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == validatorIndex then acc + w.amount else pure acc
  let builder ← sszGetIdx (sszGet state builders) builderIndex
  pure (builder.balance.saturatingSub withdrawn)

/-- `get_builders_sweep_withdrawals` (NEW, EIP-7732, `gloas/beacon-chain.md:1912-1947`): sweep
up to `MAX_BUILDERS_PER_WITHDRAWALS_SWEEP` builders from `next_withdrawal_builder_index`,
withdrawing each withdrawable builder's balance net of the withdrawals already queued for it,
when that is non-zero. An out-of-range builder cursor rejects.

v1.7.0-beta.4 nets the queued withdrawals out (`get_builder_balance_after_withdrawals`), so a
builder with a pending withdrawal in the same payload is not paid twice; alpha.12 withdrew the
full balance. -/
forkdef getBuildersSweepWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : StateTransition (Array Withdrawal × WithdrawalIndex × Nat) := do
  let state ← get
  let epoch := currentEpochOf state
  let builderCount := len (sszGet state builders)
  -- `min(len(state.builders), MAX_BUILDERS_PER_WITHDRAWALS_SWEEP)` mixes a plain length and a
  -- `Uint64`; the result only bounds `range(...)`, which iterates the same positions for
  -- either kind, so the structural `Nat` minimum names the same loop.
  let buildersLimit := Nat.min (sszGet state builders).size Const.maxBuildersPerWithdrawalsSweep
  let limit ← Const.maxWithdrawalsPerPayloadC - 1
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  let mut builderIndex := sszGet state nextWithdrawalBuilderIndex

  for _ in [0:buildersLimit] do
    let allW := prior ++ ws
    if len allW ≥ limit.toCLInt then break
    let builder ← sszGetIdx (sszGet state builders) builderIndex
    let balance ← getBuilderBalanceAfterWithdrawals state builderIndex allW
    if builder.withdrawableEpoch ≤ epoch && balance > 0 then
      ws := ws.push
        { index := wi, validatorIndex := convertBuilderIndexToValidatorIndex builderIndex,
          address := builder.executionAddress, amount := balance }
      wi ← wi + 1
    -- `builder_index = (builder_index + 1) % len(state.builders)` (`gloas/minimal.py:8080`):
    -- the checked `BuilderIndex` add, then the modulo by the plain length, which raises
    -- `ZeroDivisionError` on an empty builder list. The loop runs only over a nonempty
    -- list whose read above proved the cursor in range, so neither fires here; both keep
    -- the pyspec's operators.
    let advanced ← builderIndex + 1
    builderIndex ← (advanced % builderCount : Checked _)
    count := count + 1
  return (ws, wi, count)

/-- `get_validators_sweep_withdrawals` (Electra): the validator balance sweep, the
only phase allowed up to the full `MAX_WITHDRAWALS_PER_PAYLOAD`. An out-of-range
validator cursor rejects. -/
forkdef getValidatorsSweepWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : StateTransition (Array Withdrawal × WithdrawalIndex × Nat) := do
  let state ← get
  let epoch := currentEpochOf state
  let nvals := len (sszGet state validators)
  -- The mixed `min(len(state.validators), MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)` only bounds
  -- `range(...)`, so the structural `Nat` minimum names the same loop.
  let validatorsLimit := Nat.min (sszGet state validators).size Const.maxValidatorsPerWithdrawalsSweep
  let limit := Const.maxWithdrawalsPerPayloadC
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  let mut vi := sszGet state nextWithdrawalValidatorIndex

  for _ in [0:validatorsLimit] do
    let allW := prior ++ ws
    if len allW ≥ limit.toCLInt then break
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state vi allW
    if isFullyWithdrawable validator bal epoch then
      ws := ws.push { index := wi, validatorIndex := vi, address := addressOf validator, amount := bal }
      wi ← wi + 1
    else if isPartiallyWithdrawable validator bal then
      -- `withdrawal_amount = balance - get_max_effective_balance(validator)`: the
      -- checked subtraction, formed only in this branch.
      let amount ← bal - getMaxEffectiveBalance validator
      ws := ws.push
        { index := wi, validatorIndex := vi, address := addressOf validator,
          amount := amount }
      wi ← wi + 1
    -- `validator_index = (validator_index + 1) % len(state.validators)`: the checked
    -- `ValidatorIndex` add, then the modulo by the plain length (`ZeroDivisionError` on an
    -- empty registry). The loop runs only over a nonempty registry whose read above proved
    -- the cursor in range, so neither fires; both keep the pyspec's operators.
    let advanced ← vi + 1
    vi ← (advanced % nvals : Checked _)
    count := count + 1
  return (ws, wi, count)

/-- `get_expected_withdrawals`: the four phases composed, threading the running list.
Returns the withdrawal set and the builder, partial, and builders-sweep processed
counts the `update_*` helpers consume. -/
forkdef getExpectedWithdrawals : StateTransition (Array Withdrawal × Nat × Nat × Nat) := do
  let firstIndex := sszGet (← get) nextWithdrawalIndex
  let (builderWs, idxAfterBuilder, builderCount) ← getBuilderWithdrawals firstIndex #[]
  let (partialWs, idxAfterPartial, partialCount) ← getPendingPartialWithdrawals idxAfterBuilder builderWs
  let priorAfterPartial := builderWs ++ partialWs
  let (sweepWs, idxAfterSweep, sweepCount) ← getBuildersSweepWithdrawals idxAfterPartial priorAfterPartial
  let priorAfterSweep := priorAfterPartial ++ sweepWs
  let (validatorWs, _, _) ← getValidatorsSweepWithdrawals idxAfterSweep priorAfterSweep
  return (priorAfterSweep ++ validatorWs, builderCount, partialCount, sweepCount)

/-- `apply_withdrawals` (MODIFIED, EIP-7732, `gloas/beacon-chain.md:1997-2006`): decrement a
builder's balance for a builder-flagged withdrawal, floored at zero (`saturating_sub`),
otherwise the validator's. An out-of-range builder index rejects. -/
forkdef applyWithdrawals (withdrawals : Array Withdrawal) : StateTransition Unit := do
  let mut stateAcc ← get
  for w in withdrawals do
    if isBuilderIndex w.validatorIndex then
      let builderIndex ← toBuilderIndex w.validatorIndex
      let b ← sszGetIdx (sszGet stateAcc builders) builderIndex
      -- `toPlainNat`: the raising read above proved `builderIndex` in range for this list.
      stateAcc := sszUpdate stateAcc with builders[builderIndex.toPlainNat]! := { b with balance := b.balance.saturatingSub w.amount }
    else
      stateAcc ← decreaseBalance stateAcc w.validatorIndex w.amount

  set stateAcc

/-- `process_withdrawals` (MODIFIED, EIP-7732): early-return on an empty parent block,
otherwise apply the expected withdrawals and run the six `update_*` bookkeeping steps
(including the new `payload_expected_withdrawals` commitment and the builder-queue /
builder-cursor advances). -/
forkdef processWithdrawals : StateTransition Unit := do
  let state ← get
  if (sszGet state latestBlockHash) != (sszGet state latestExecutionPayloadBid).blockHash then return

  let (expected, builderCount, partialCount, buildersSweepCount) ← getExpectedWithdrawals
  applyWithdrawals expected

  -- update_next_withdrawal_index (`gloas/minimal.py:6403-6407`): behind the
  -- `len(withdrawals) != 0` guard, `withdrawals[-1]` reads the last element through the plain
  -- negative index (§4.6), and `latest_withdrawal.index + 1` is the checked
  -- `WithdrawalIndex` add, so it raises past `2^64 - 1`.
  if len expected != 0 then
    let latestWithdrawal ← sszGetIdx expected (-1 : CLInt)
    let nextIndex ← latestWithdrawal.index + 1
    modifyState fun state => sszUpdate state with nextWithdrawalIndex := nextIndex

  -- update_payload_expected_withdrawals (NEW)
  modifyState fun state =>
    sszUpdate state with payloadExpectedWithdrawals := ⟨expected⟩

  -- update_builder_pending_withdrawals (NEW): drop the processed builder withdrawals
  modifyState fun state => sszUpdate state with builderPendingWithdrawals := sszDrop (sszGet state builderPendingWithdrawals) builderCount

  -- update_pending_partial_withdrawals: drop the processed pending partials
  modifyState fun state => sszUpdate state with pendingPartialWithdrawals := sszDrop (sszGet state pendingPartialWithdrawals) partialCount

  -- update_next_withdrawal_builder_index (NEW, `gloas/minimal.py:8100-8107`): behind the
  -- `len(state.builders) > 0` guard, the checked `BuilderIndex` add of the processed count,
  -- then the modulo by the plain length (`ZeroDivisionError` on an empty list, which the
  -- guard excludes).
  let state ← get
  let builderCount := len (sszGet state builders)
  if builderCount > 0 then
    -- `processed_builders_sweep_count` is the structural `Nat` counter (see
    -- `getBuilderWithdrawals`); the mixed add computes the pinned `Uint64` sum.
    let nextIndex ← sszGet state nextWithdrawalBuilderIndex + buildersSweepCount
    let nextBuilderIndex ← (nextIndex % builderCount : Checked _)
    modifyState fun state => sszUpdate state with nextWithdrawalBuilderIndex := nextBuilderIndex

  -- update_next_withdrawal_validator_index (`gloas/minimal.py:6410-6422`): a full payload
  -- resumes one past the last validator drained; a short one jumps a whole sweep window
  -- ahead. The plain `len(withdrawals)` meets the checked `MAX_WITHDRAWALS_PER_PAYLOAD` in a
  -- comparison. The full branch reads `withdrawals[-1]`, which raises `IndexError` on an
  -- empty list. Each branch forms the checked `ValidatorIndex` add, then the modulo by the
  -- plain `len(state.validators)`, which raises `ZeroDivisionError` on an empty registry.
  let state ← get
  let nvals := len (sszGet state validators)
  let nextCursor ←
    if len expected == Const.maxWithdrawalsPerPayloadC.toCLInt then do
      let latestWithdrawal ← sszGetIdx expected (-1 : CLInt)
      let advanced ← (latestWithdrawal.validatorIndex + 1 : Checked _)
      pure advanced
    else do
      let advanced ←
        (sszGet state nextWithdrawalValidatorIndex + Const.maxValidatorsPerWithdrawalsSweep : Checked _)
      pure advanced
  let nextValidatorIndex ← (nextCursor % nvals : Checked _)
  modifyState fun state => sszUpdate state with nextWithdrawalValidatorIndex := nextValidatorIndex

end

end EthCLSpecs.Gloas
