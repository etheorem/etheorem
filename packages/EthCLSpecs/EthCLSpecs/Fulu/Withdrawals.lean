import EthCLSpecs.Fulu.Deposits
import EthCLSpecs.Fulu.Blocks

/-!
# `EthCLSpecs.Fulu.Withdrawals`: the withdrawal sweep and `process_withdrawals`

`get_expected_withdrawals` (the Electra pending-partial queue followed by the
validator balance sweep) and `process_withdrawals` (assert the payload's
withdrawals match the expected set, apply them, advance the sweep bookkeeping).
The withdrawal predicates (`is_fully_withdrawable_validator`,
`is_partially_withdrawable_validator`, `is_eligible_for_partial_withdrawals`) are
pure functions of a validator and its post-sweep balance.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-! ## Withdrawal predicates -/

/-- The 20-byte execution address held in a validator's withdrawal credentials
(`withdrawal_credentials[12:]`). -/
def addressOf (v : Validator) : ExecutionAddress :=
  Vector.ofFn (fun i : Fin 20 => vget v.withdrawalCredentials (12 + i.val))

/-- `is_fully_withdrawable_validator`. -/
forkdef isFullyWithdrawable (v : Validator) (balance : Gwei) (epoch : Epoch) : Bool :=
  hasExecutionWithdrawalCredential v && v.withdrawableEpoch ≤ epoch && balance > 0

/-- `is_partially_withdrawable_validator`. -/
forkdef isPartiallyWithdrawable (v : Validator) (balance : Gwei) : Bool :=
  let maxEff := getMaxEffectiveBalance v
  hasExecutionWithdrawalCredential v && v.effectiveBalance == maxEff && balance > maxEff

/-- `is_eligible_for_partial_withdrawals`. -/
forkdef isEligibleForPartialWithdrawals (v : Validator) (balance : Gwei) : Bool :=
  hasNotInitiatedExit v && v.effectiveBalance ≥ Const.minActivationBalance
    && balance > Const.minActivationBalance

/-! ## Expected withdrawals -/

/-- `get_balance_after_withdrawals` (`capella/beacon-chain.md:411-421`): the balance net of any
already-queued withdrawals for that validator. Throwing (`StateTransition`). The spec's
`state.balances[validator_index]` is a bare list index, so a read past the end rejects with
`outOfBounds` through `sszGetIdx`, the class of Python's `IndexError`.

The `withdrawn` accumulator is a `Gwei`, and the folded add is the checked `Gwei` `+`
(`SPEC_ARITHMETIC.md` §3.2, the `sum` row), so a running sum past `2^64 - 1` raises during
the accumulation. The final `balances[i] - withdrawn` is the checked subtraction. Its
underflow raises Python `ValueError`, which `expect_assertion_error` does not catch
(`context.py:451-462` catches only `AssertionError` and `IndexError`), so the body throws the
uncaught `.arithmetic` reject. A well-formed state reaches none of these faults, and the
body still models each one. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then acc + w.amount else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi
  bal - withdrawn

/-- `get_expected_withdrawals`: the pending-partial queue then the validator sweep.
Throwing: the two `validators[i]` reads are bare list indices (`IndexError`, via
`sszGetIdx` → `outOfBounds`, the same faithful class as the balance read); `balanceAfterWithdrawals`
raises on the balance read / underflow. Both unreachable on a well-formed state. -/
forkdef getExpectedWithdrawals (state : State) : StateTransition (Array Withdrawal × Nat) := do
  let epoch := currentEpochOf state
  let nvals := len (sszGet state validators)
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := sszGet state nextWithdrawalIndex
  -- `processed_count` is a pinned `Uint64` counter. It stays a structural `Nat`: it counts
  -- entries of the pending-partials list, whose cap is below `2^64`, so its checked
  -- `+= 1` cannot raise, and `update_pending_partial_withdrawals` reads it as a slice start.
  let mut processedPartial := 0

  -- Pending partial withdrawals (EIP-7251). `withdrawals_limit = min(len(prior_withdrawals)
  -- + MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP, MAX_WITHDRAWALS_PER_PAYLOAD - 1)`
  -- (`fulu/minimal.py:6177-6180`), with `prior_withdrawals` the still-empty list. Both
  -- operands are `Uint64`: the plain length plus a checked constant is the mixed route, and
  -- `MAX_WITHDRAWALS_PER_PAYLOAD - 1` is the checked subtraction, which raises for a zero
  -- preset value. `min` picks an operand.
  let pendingCap ← len withdrawals + Const.maxPendingPartialsPerWithdrawalsSweepC
  let payloadCap ← Const.maxWithdrawalsPerPayloadC - 1
  let partialLimit := min pendingCap payloadCap
  for w in (sszGet state pendingPartialWithdrawals) do
    -- `len(all_withdrawals) >= withdrawals_limit`: the plain length against the checked
    -- limit, a comparison that never raises; `int(x)` carries the limit into the plain kind.
    if !(w.withdrawableEpoch ≤ epoch) || len withdrawals ≥ partialLimit.toCLInt then break
    let vi := w.validatorIndex
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state vi withdrawals
    if isEligibleForPartialWithdrawals validator bal then
      -- `withdrawal_amount = min(balance - MIN_ACTIVATION_BALANCE, withdrawal.amount)`
      -- (`fulu/mainnet.py:6204`, in `get_pending_partial_withdrawals`): the excess is the checked subtraction, formed only in
      -- this branch, and `min` then picks an operand.
      let excess ← bal - Const.minActivationBalance
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := vi, address := addressOf validator,
          amount := min excess w.amount }
      withdrawalIndex ← withdrawalIndex + 1
    processedPartial := processedPartial + 1

  -- Validator sweep (Capella). `min(len(state.validators), MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)`
  -- mixes a plain length and a `Uint64`, so Python's result kind is whichever operand wins.
  -- The result only bounds `range(...)`, which iterates the same positions for either kind,
  -- so the structural `Nat` minimum names the same loop.
  let validatorsLimit := Nat.min (sszGet state validators).size Const.maxValidatorsPerWithdrawalsSweep
  let mut validatorIndex := sszGet state nextWithdrawalValidatorIndex
  for _ in [0:validatorsLimit] do
    -- `len(all_withdrawals) >= MAX_WITHDRAWALS_PER_PAYLOAD`: a comparison, which never raises.
    if len withdrawals ≥ Const.maxWithdrawalsPerPayloadC.toCLInt then break
    let validator ← sszGetIdx (sszGet state validators) validatorIndex
    let bal ← balanceAfterWithdrawals state validatorIndex withdrawals
    if isFullyWithdrawable validator bal epoch then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := validatorIndex, address := addressOf validator, amount := bal }
      withdrawalIndex ← withdrawalIndex + 1
    else if isPartiallyWithdrawable validator bal then
      -- `withdrawal_amount = balance - get_max_effective_balance(validator)`: the checked
      -- subtraction, formed only in this branch.
      let amount ← bal - getMaxEffectiveBalance validator
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := validatorIndex, address := addressOf validator,
          amount := amount }
      withdrawalIndex ← withdrawalIndex + 1
    -- `validator_index = (validator_index + 1) % len(state.validators)`
    -- (`fulu/minimal.py:5675`): the checked `ValidatorIndex` add, then the modulo by the
    -- plain length, which raises `ZeroDivisionError` on an empty registry. The loop runs
    -- only when the registry is nonempty, and the read above already proved the cursor in
    -- range, so neither fires here; both keep the pyspec's operators.
    let advanced ← validatorIndex + 1
    validatorIndex ← (advanced % nvals : Checked _)
  return (withdrawals, processedPartial)

/-! ## process_withdrawals -/

/-- `process_withdrawals`: the payload's withdrawals must equal the expected set;
apply them, then advance `next_withdrawal_index`, drop the consumed pending
partials, and advance the sweep cursor. -/
forkdef processWithdrawals (payload : ExecutionPayload) : StateTransition Unit := do
  let state ← get
  let (expected, processedPartial) ← getExpectedWithdrawals state
  -- `payload.withdrawals == expected.withdrawals`: remerkleable's `View.__eq__` coerces the
  -- Python list through the `List` constructor, which raises on too many elements, then
  -- compares roots.
  let expectedList : SSZList Withdrawal Const.maxWithdrawalsPerPayload ←
    sszOfArrayM "withdrawals" expected
  assert (htr expectedList == htr payload.withdrawals)

  let nvals := len (sszGet state validators)
  let mut stateAcc := state
  for w in expected do
    stateAcc ← decreaseBalance stateAcc w.validatorIndex w.amount

  -- `update_next_withdrawal_index` (`fulu/minimal.py:5711-5715`): behind the
  -- `len(withdrawals) != 0` guard, `withdrawals[-1]` reads the last element through the
  -- plain negative index (§4.6), and `latest_withdrawal.index + 1` is the checked
  -- `WithdrawalIndex` add, so it raises past `2^64 - 1`.
  if len expected != 0 then
    let latestWithdrawal ← sszGetIdx expected (-1 : CLInt)
    let nextIndex ← latestWithdrawal.index + 1
    stateAcc := sszUpdate stateAcc with nextWithdrawalIndex := nextIndex
  stateAcc := sszUpdate stateAcc with pendingPartialWithdrawals := sszDrop (sszGet stateAcc pendingPartialWithdrawals) processedPartial
  -- `update_next_withdrawal_validator_index` (`fulu/minimal.py:5718-5730`): the plain
  -- `len(withdrawals)` against the checked `MAX_WITHDRAWALS_PER_PAYLOAD`, a comparison. Each
  -- branch forms the checked `ValidatorIndex` add, then the modulo by the plain
  -- `len(state.validators)`, which raises `ZeroDivisionError` on an empty registry. The full
  -- branch reads `withdrawals[-1]`, which raises `IndexError` on an empty list.
  if len expected == Const.maxWithdrawalsPerPayloadC.toCLInt then
    let latestWithdrawal ← sszGetIdx expected (-1 : CLInt)
    let advanced ← latestWithdrawal.validatorIndex + 1
    let nextV ← (advanced % nvals : Checked _)
    stateAcc := sszUpdate stateAcc with nextWithdrawalValidatorIndex := nextV
  else
    let nextIndex ← sszGet stateAcc nextWithdrawalValidatorIndex + Const.maxValidatorsPerWithdrawalsSweep
    let nextV ← (nextIndex % nvals : Checked _)
    stateAcc := sszUpdate stateAcc with nextWithdrawalValidatorIndex := nextV
  set stateAcc

end

end EthCLSpecs.Fulu
