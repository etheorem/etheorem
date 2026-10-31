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

The `withdrawn` accumulator folds through `checkedAdd`, as in Fulu: pyspec's `sum(...)`
accumulates in `Gwei` rather than widening to a Python `int`, so it raises during the
accumulation at the same point. See `Fulu.balanceAfterWithdrawals`. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then
      checkedAdd acc w.amount "get_balance_after_withdrawals: sum(withdrawal.amount)"
    else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi.toNat
  checkedSub bal withdrawn "get_balance_after_withdrawals: balances[i] - withdrawn"

/-- `get_builder_withdrawals` (NEW, EIP-7732): drain `builder_pending_withdrawals`
into validator-flagged withdrawals, capped at `MAX_WITHDRAWALS_PER_PAYLOAD - 1`. -/
forkdef getBuilderWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : StateTransition (Array Withdrawal × WithdrawalIndex × Nat) := do
  let state ← get
  let limit := Const.maxWithdrawalsPerPayload - 1
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]

  for w in (sszGet state builderPendingWithdrawals) do
    if prior.size + ws.size ≥ limit then break
    ws := ws.push
      { index := wi, validatorIndex := convertBuilderIndexToValidatorIndex w.builderIndex,
        address := w.feeRecipient, amount := w.amount }
    wi := wi + 1
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
  let limit := Nat.min (prior.size + Const.maxPendingPartialsPerWithdrawalsSweep) (Const.maxWithdrawalsPerPayload - 1)
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]

  for w in (sszGet state pendingPartialWithdrawals) do
    let allW := prior ++ ws
    if !(w.withdrawableEpoch ≤ epoch) || allW.size ≥ limit then break
    let vi := w.validatorIndex
    let validator ← sszGetIdx (sszGet state validators) vi.toNat
    let bal ← balanceAfterWithdrawals state vi allW
    if isEligibleForPartialWithdrawals validator bal then
      ws := ws.push
        { index := wi, validatorIndex := vi, address := addressOf validator,
          amount := umin (bal - Const.minActivationBalance) w.amount }
      wi := wi + 1
    count := count + 1
  return (ws, wi, count)

/-- `get_builder_balance_after_withdrawals(state, builder_index, withdrawals)` (NEW at
v1.7.0-beta.4, `gloas/beacon-chain.md:1895-1906`): the builder's balance net of the
withdrawals already queued for it, floored at zero (`saturating_sub`). A builder withdrawal
carries the builder's flagged validator index, so the match is on
`convert_builder_index_to_validator_index`. The `withdrawn` sum folds through `checkedAdd`:
pyspec's `sum(...)` accumulates in `Gwei` and raises on overflow. `state.builders[i]` is a bare
list index, so an out-of-range index rejects through `sszGetIdx`. -/
forkdef getBuilderBalanceAfterWithdrawals (state : State) (builderIndex : BuilderIndex)
    (ws : Array Withdrawal) : StateTransition Gwei := do
  let validatorIndex := convertBuilderIndexToValidatorIndex builderIndex
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == validatorIndex then
      checkedAdd acc w.amount "get_builder_balance_after_withdrawals: sum(withdrawal.amount)"
    else pure acc
  let builder ← sszGetIdx (sszGet state builders) builderIndex.toNat
  pure (saturatingSub builder.balance withdrawn)

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
  let bs := (sszGet state builders).toArray
  let buildersLimit := Nat.min bs.size Const.maxBuildersPerWithdrawalsSweep
  let limit := Const.maxWithdrawalsPerPayload - 1
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  let mut builderIndex := (sszGet state nextWithdrawalBuilderIndex).toNat

  for _ in [0:buildersLimit] do
    let allW := prior ++ ws
    if allW.size ≥ limit then break
    let builder ← sszGetIdx (sszGet state builders) builderIndex
    let balance ← getBuilderBalanceAfterWithdrawals state (UInt64.ofNat builderIndex) allW
    if builder.withdrawableEpoch ≤ epoch && balance > 0 then
      ws := ws.push
        { index := wi, validatorIndex := convertBuilderIndexToValidatorIndex (UInt64.ofNat builderIndex),
          address := builder.executionAddress, amount := balance }
      wi := wi + 1
    builderIndex := modWrap (builderIndex + 1) bs.size
    count := count + 1
  return (ws, wi, count)

/-- `get_validators_sweep_withdrawals` (Electra): the validator balance sweep, the
only phase allowed up to the full `MAX_WITHDRAWALS_PER_PAYLOAD`. An out-of-range
validator cursor rejects. -/
forkdef getValidatorsSweepWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) : StateTransition (Array Withdrawal × WithdrawalIndex × Nat) := do
  let state ← get
  let epoch := currentEpochOf state
  let validators := (sszGet state validators).toArray
  let nvals := validators.size
  let validatorsLimit := Nat.min nvals Const.maxValidatorsPerWithdrawalsSweep
  let limit := Const.maxWithdrawalsPerPayload
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  let mut vi := (sszGet state nextWithdrawalValidatorIndex).toNat

  for _ in [0:validatorsLimit] do
    let allW := prior ++ ws
    if allW.size ≥ limit then break
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state (UInt64.ofNat vi) allW
    if isFullyWithdrawable validator bal epoch then
      ws := ws.push { index := wi, validatorIndex := UInt64.ofNat vi, address := addressOf validator, amount := bal }
      wi := wi + 1
    else if isPartiallyWithdrawable validator bal then
      ws := ws.push
        { index := wi, validatorIndex := UInt64.ofNat vi, address := addressOf validator,
          amount := bal - getMaxEffectiveBalance validator }
      wi := wi + 1
    vi := modWrap (vi + 1) nvals
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
      let builderIndex := toBuilderIndex w.validatorIndex
      let b ← sszGetIdx (sszGet stateAcc builders) builderIndex.toNat
      stateAcc := sszUpdate stateAcc with builders[builderIndex.toNat]! := { b with balance := saturatingSub b.balance w.amount }
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

  -- update_next_withdrawal_index
  if expected.size != 0 then
    modifyState fun state => sszUpdate state with nextWithdrawalIndex := (expected[expected.size - 1]!).index + 1

  -- update_payload_expected_withdrawals (NEW)
  modifyState fun state =>
    sszUpdate state with payloadExpectedWithdrawals := ⟨expected⟩

  -- update_builder_pending_withdrawals (NEW): drop the processed builder withdrawals
  modifyState fun state => sszUpdate state with builderPendingWithdrawals := sszDrop (sszGet state builderPendingWithdrawals) builderCount

  -- update_pending_partial_withdrawals: drop the processed pending partials
  modifyState fun state => sszUpdate state with pendingPartialWithdrawals := sszDrop (sszGet state pendingPartialWithdrawals) partialCount

  -- update_next_withdrawal_builder_index (NEW)
  modifyState fun state =>
    let n := (sszGet state builders).size
    if n > 0 then sszUpdate state with nextWithdrawalBuilderIndex := UInt64.ofNat (((sszGet state nextWithdrawalBuilderIndex).toNat + buildersSweepCount) % n)
    else state

  -- update_next_withdrawal_validator_index: a full payload resumes one past the
  -- last validator drained; a short one jumps a whole sweep window ahead. Both
  -- wrap modulo the registry size (0 when empty).
  modifyState fun state =>
    let nvals := (sszGet state validators).size
    let sweptFullPayload := expected.size == Const.maxWithdrawalsPerPayload
    let nextCursor :=
      if sweptFullPayload then (expected[expected.size - 1]!).validatorIndex.toNat + 1
      else (sszGet state nextWithdrawalValidatorIndex).toNat + Const.maxValidatorsPerWithdrawalsSweep
    sszUpdate state with nextWithdrawalValidatorIndex := UInt64.ofNat (modWrap nextCursor nvals)

end

end EthCLSpecs.Gloas
