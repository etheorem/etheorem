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
already-queued withdrawals for that validator. Throwing (`StateTransition`): the spec's
`state.balances[validator_index]` is a bare list index (`IndexError`, via `sszGetIdx` →
`outOfBounds`), and `- withdrawn` is a bare `uint64` subtraction whose underflow raises Python
`ValueError`, which the reference runner does NOT catch (`context.py:424-435` catches only
`AssertionError` / `IndexError`), so it throws the uncaught `.arithmetic` reject rather than a
caught `.assert`. Both reads are unreachable on a well-formed state and modeled rather than
clamped.

The `withdrawn` accumulator is a `Gwei`, and the folded add is the checked `Gwei` `+`
(`SPEC_ARITHMETIC.md` §3.2, the `sum` row), so a running sum past `2^64` raises during the
accumulation, and the final `balances[i] - withdrawn` is the checked subtraction, whose
underflow raises Python `ValueError` the reference runner does not catch (`context.py:424-435`
catches only `AssertionError` / `IndexError`). Both reads are unreachable on a well-formed
state and modeled rather than clamped. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then acc + w.amount else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi.toNat
  bal - withdrawn

/-- `get_expected_withdrawals`: the pending-partial queue then the validator sweep.
Throwing: the two `validators[i]` reads are bare list indices (`IndexError`, via
`sszGetIdx` → `outOfBounds`, the same faithful class as the balance read); `balanceAfterWithdrawals`
raises on the balance read / underflow. Both unreachable on a well-formed state. -/
forkdef getExpectedWithdrawals (state : State) : StateTransition (Array Withdrawal × Nat) := do
  let epoch := currentEpochOf state
  let nvals := (sszGet state validators).size
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := sszGet state nextWithdrawalIndex
  let mut processedPartial := 0

  -- Pending partial withdrawals (EIP-7251).
  let partialLimit := Nat.min Const.maxPendingPartialsPerWithdrawalsSweep (Const.maxWithdrawalsPerPayload - 1)
  for w in (sszGet state pendingPartialWithdrawals) do
    if !(w.withdrawableEpoch ≤ epoch) || withdrawals.size ≥ partialLimit then break
    let vi := w.validatorIndex
    let validator ← sszGetIdx (sszGet state validators) vi.toNat
    let bal ← balanceAfterWithdrawals state vi withdrawals
    if isEligibleForPartialWithdrawals validator bal then
      -- `withdrawal_amount = min(balance - MIN_ACTIVATION_BALANCE, withdrawal.amount)`
      -- (`fulu/mainnet.py:6204`, in `get_pending_partial_withdrawals`): the excess is the checked subtraction, formed only in
      -- this branch, and `min` then picks an operand.
      let excess ← bal - Const.minActivationBalance
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := vi, address := addressOf validator,
          amount := min excess w.amount }
      withdrawalIndex := withdrawalIndex + 1
    processedPartial := processedPartial + 1

  -- Validator sweep (Capella).
  let validatorsLimit := Nat.min nvals Const.maxValidatorsPerWithdrawalsSweep
  let mut vIdx := (sszGet state nextWithdrawalValidatorIndex).toNat
  for _ in [0:validatorsLimit] do
    if withdrawals.size ≥ Const.maxWithdrawalsPerPayload then break
    let validator ← sszGetIdx (sszGet state validators) vIdx
    let bal ← balanceAfterWithdrawals state (UInt64.ofNat vIdx) withdrawals
    if isFullyWithdrawable validator bal epoch then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := UInt64.ofNat vIdx, address := addressOf validator, amount := bal }
      withdrawalIndex := withdrawalIndex + 1
    else if isPartiallyWithdrawable validator bal then
      -- `withdrawal_amount = balance - get_max_effective_balance(validator)`: the checked
      -- subtraction, formed only in this branch.
      let amount ← bal - getMaxEffectiveBalance validator
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := UInt64.ofNat vIdx, address := addressOf validator,
          amount := amount }
      withdrawalIndex := withdrawalIndex + 1
    vIdx := modWrap (vIdx + 1) nvals
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

  let nvals := (sszGet state validators).size
  let mut stateAcc := state
  for w in expected do
    stateAcc ← decreaseBalance stateAcc w.validatorIndex w.amount

  if expected.size != 0 then
    stateAcc := sszUpdate stateAcc with nextWithdrawalIndex := (expected[expected.size - 1]!).index + 1
  stateAcc := sszUpdate stateAcc with pendingPartialWithdrawals := sszDrop (sszGet stateAcc pendingPartialWithdrawals) processedPartial
  if expected.size == Const.maxWithdrawalsPerPayload then
    let nextV := modWrap ((expected[expected.size - 1]!).validatorIndex.toNat + 1) nvals
    stateAcc := sszUpdate stateAcc with nextWithdrawalValidatorIndex := UInt64.ofNat nextV
  else
    let nextV := modWrap ((sszGet stateAcc nextWithdrawalValidatorIndex).toNat + Const.maxValidatorsPerWithdrawalsSweep) nvals
    stateAcc := sszUpdate stateAcc with nextWithdrawalValidatorIndex := UInt64.ofNat nextV
  set stateAcc

end

end EthCLSpecs.Fulu
