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

The `withdrawn` accumulator folds through the checked `+`, as in Fulu: pyspec's `sum(...)`
accumulates in `Gwei` rather than widening to a Python `int`, so it raises during the
accumulation at the same point. See `Fulu.balanceAfterWithdrawals`. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then acc + w.amount else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi
  bal - withdrawn

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
    let allW := prior ++ ws
    -- `len(all_withdrawals)` is a plain `int`, so the cap comparison reads through `CLInt`.
    if CLInt.len allW ≥ limit then break
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

  -- `len(all_withdrawals)` is a plain `int`, so the cap comparison reads through `CLInt`.
  for w in (sszGet state pendingPartialWithdrawals) do
    let allW := prior ++ ws
    if !(w.withdrawableEpoch ≤ epoch) || CLInt.len allW ≥ limit then break
    let vi := w.validatorIndex
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state vi allW
    if isEligibleForPartialWithdrawals validator bal then
      ws := ws.push
        { index := wi, validatorIndex := vi, address := addressOf validator,
          amount := min (← bal - Const.minActivationBalance) w.amount }
      wi := wi + 1
    count := count + 1
  return (ws, wi, count)

/-- `get_builder_balance_after_withdrawals(state, builder_index, withdrawals)` (NEW at
v1.7.0-beta.4, `gloas/beacon-chain.md:1895-1906`): the builder's balance net of the
withdrawals already queued for it, floored at zero (`saturating_sub`). A builder withdrawal
carries the builder's flagged validator index, so the match is on
`convert_builder_index_to_validator_index`. The `withdrawn` sum folds through the checked `+`:
pyspec's `sum(...)` accumulates in `Gwei` and raises on overflow, and its outer `Gwei(sum(...))`
cast adds no raise point (an empty sum casts a plain `0`; a nonempty one is already a checked
`Gwei`). `state.builders[i]` is a bare
list index, so an out-of-range index rejects through `sszGetIdx`. -/
forkdef getBuilderBalanceAfterWithdrawals (state : State) (builderIndex : BuilderIndex)
    (ws : Array Withdrawal) : StateTransition Gwei := do
  let validatorIndex := convertBuilderIndexToValidatorIndex builderIndex
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == validatorIndex then acc + w.amount else pure acc
  let builder ← sszGetIdx (sszGet state builders) builderIndex.toNat
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
  let bs := (sszGet state builders).toArray
  let buildersLimit := Nat.min bs.size Const.maxBuildersPerWithdrawalsSweep
  let limit := Const.maxWithdrawalsPerPayload - 1
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  -- `builder_index` is the sweep cursor, the raw `BuilderIndex` the state field holds.
  -- `len(all_withdrawals)` is a plain `int`, so the cap comparison reads through `CLInt`.
  let mut builderIndex := sszGet state nextWithdrawalBuilderIndex

  for _ in [0:buildersLimit] do
    let allW := prior ++ ws
    if CLInt.len allW ≥ limit then break
    let builder ← sszGetIdx (sszGet state builders) builderIndex.toNat
    let balance ← getBuilderBalanceAfterWithdrawals state builderIndex allW
    if builder.withdrawableEpoch ≤ epoch && balance > 0 then
      ws := ws.push
        { index := wi, validatorIndex := convertBuilderIndexToValidatorIndex builderIndex,
          address := builder.executionAddress, amount := balance }
      wi := wi + 1
    -- `(builder_index + 1) % len(state.builders)`: the `int(x)` read through the trusted
    -- route into `CLInt` (the field holds a decoded `uint64`), the total `CLInt` `+ 1`, the
    -- `%` that raises on a zero divisor, then `toUint64?` narrowing and the iso `.val` read
    -- back into the raw cursor. The pyspec's checked `+ 1` raise is unreachable, the same
    -- iteration's `state.builders[builder_index]` read rejects an out-of-range cursor
    -- first. The empty-registry `%` raise is unreachable here (the loop bound is
    -- `min(len(builders), …)`); the update site guards the empty registry itself.
    let advanced ← (CLUint64.toInt (CLUint64.trustedOfUInt64 builderIndex) + 1) % CLInt.len bs
    builderIndex := (← advanced.toUint64?).val
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
  let validatorsLimit := Nat.min validators.size Const.maxValidatorsPerWithdrawalsSweep
  let limit := Const.maxWithdrawalsPerPayload
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  -- `vi` is the sweep cursor, the checked `ValidatorIndex` the state field holds, and each
  -- advance is the pyspec's `(validator_index + 1) % len(state.validators)`: the `+` is a
  -- total `CLInt` sum (the checked `+ 1` raise is unreachable, the same iteration's
  -- `state.validators[validator_index]` read rejects an out-of-range cursor first), the
  -- `%` is a `CLInt` modulo that raises on a zero divisor, and `toUint64?` is the
  -- `Uint64(n)` narrowing into the cursor. The empty-registry raise is unreachable here
  -- (the loop bound is `min(len(validators), …)`), reachable at the update site in
  -- `processWithdrawals`.
  let mut vi := sszGet state nextWithdrawalValidatorIndex

  for _ in [0:validatorsLimit] do
    let allW := prior ++ ws
    -- `len(all_withdrawals)` is a plain `int`, so the cap comparison reads through `CLInt`.
    if CLInt.len allW ≥ limit then break
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state vi allW
    if isFullyWithdrawable validator bal epoch then
      ws := ws.push { index := wi, validatorIndex := vi, address := addressOf validator, amount := bal }
      wi := wi + 1
    else if isPartiallyWithdrawable validator bal then
      ws := ws.push
        { index := wi, validatorIndex := vi, address := addressOf validator,
          amount := (← bal - getMaxEffectiveBalance validator) }
      wi := wi + 1
    let advanced ← (vi.toInt + 1) % CLInt.len validators
    vi := ← advanced.toUint64?
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
      stateAcc := sszUpdate stateAcc with builders[builderIndex.toNat]! := { b with balance := b.balance.saturatingSub w.amount }
    else
      stateAcc ← decreaseBalance stateAcc w.validatorIndex w.amount

  set stateAcc

/-- `process_withdrawals` (MODIFIED, EIP-7732): early-return on an empty parent block,
otherwise apply the expected withdrawals and run the six `update_*` bookkeeping steps
(including the new `payload_expected_withdrawals` commitment and the builder-queue /
builder-cursor advances).

Throwing beyond the apply step: the two `withdrawals[-1]` reads are the plain negative
literal index, counted from the end (§3.7), through the raising `⟦·⟧` route. The builder
cursor's `% len(state.builders)` raise is unreachable, the `len(builders) > 0` guard skips
it. The validator cursor's `% len(state.validators)` raises on an empty registry, the one
empty-registry path the sweep body itself cannot reach. -/
forkdef processWithdrawals : StateTransition Unit := do
  let state ← get
  if (sszGet state latestBlockHash) != (sszGet state latestExecutionPayloadBid).blockHash then return

  let (expected, builderCount, partialCount, buildersSweepCount) ← getExpectedWithdrawals
  applyWithdrawals expected

  -- update_next_withdrawal_index: `latest_withdrawal = withdrawals[-1]`, counted from the
  -- end. `WithdrawalIndex` is still the raw `UInt64`, so the `+ 1` wraps at the maximum
  -- where the pyspec's checked add raises. A known gap (IMPLEMENTATION_NOTES.md, "Fulu
  -- state transition"); the `WithdrawalIndex` migration closes it, and the `wi + 1` sites
  -- in the four phase helpers share it.
  if expected.size != 0 then
    let last ← expected⟦(-1 : CLInt)⟧
    modifyState fun state => sszUpdate state with nextWithdrawalIndex := last.index + 1

  -- update_payload_expected_withdrawals (NEW)
  modifyState fun state =>
    sszUpdate state with payloadExpectedWithdrawals := ⟨expected⟩

  -- update_builder_pending_withdrawals (NEW): drop the processed builder withdrawals
  modifyState fun state => sszUpdate state with builderPendingWithdrawals := sszDrop (sszGet state builderPendingWithdrawals) builderCount

  -- update_pending_partial_withdrawals: drop the processed pending partials
  modifyState fun state => sszUpdate state with pendingPartialWithdrawals := sszDrop (sszGet state pendingPartialWithdrawals) partialCount

  -- update_next_withdrawal_builder_index (NEW): resume the sweep at the first builder
  -- this window did not examine,
  -- `(next_withdrawal_builder_index + builders_sweep_count) % len(state.builders)`. The
  -- `+` is the checked `uint64` add, entered through the trusted read of the raw field,
  -- and the `%` is the `CLInt` modulo; the empty-registry raise is unreachable, the
  -- `len(builders) > 0` guard skips it.
  let builders := (sszGet state builders).toArray
  if builders.size > 0 then
    let sum ← (CLUint64.trustedOfUInt64 (sszGet state nextWithdrawalBuilderIndex)) + buildersSweepCount
    let next ← sum % CLInt.len builders
    modifyState fun state => sszUpdate state with nextWithdrawalBuilderIndex := next.val

  -- update_next_withdrawal_validator_index: a full payload resumes one past the last
  -- validator drained, `(withdrawals[-1].validator_index + 1) % len(state.validators)`:
  -- the negative read, the total `CLInt` `+ 1`, the `%` that raises on an empty registry,
  -- then `toUint64?` into the cursor. A short payload jumps a whole sweep window ahead,
  -- `uint64 + uint64` checked, then the same `%`.
  let nvals := CLInt.len (sszGet state validators).toArray
  if expected.size == Const.maxWithdrawalsPerPayload then
    let last ← expected⟦(-1 : CLInt)⟧
    let nextV ← (last.validatorIndex.toInt + 1) % nvals
    let nextCursor ← nextV.toUint64?
    modifyState fun state => sszUpdate state with nextWithdrawalValidatorIndex := nextCursor
  else
    let nextIndex ← (sszGet state nextWithdrawalValidatorIndex) + Const.maxValidatorsPerWithdrawalsSweep
    let nextCursor ← nextIndex % nvals
    modifyState fun state => sszUpdate state with nextWithdrawalValidatorIndex := nextCursor

end

end EthCLSpecs.Gloas
