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

/-- `get_balance_after_withdrawals`: the balance net of any already-queued
withdrawals for that validator (the sweep reads draining balances). -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) : Gwei :=
  let withdrawn := ws.foldl (fun acc w => if w.validatorIndex == vi then acc + w.amount else acc) 0
  let bal := sszGet state balances[vi.toNat]!
  if withdrawn > bal then 0 else bal - withdrawn

/-- `get_expected_withdrawals`: the pending-partial queue (bounded) then the
validator sweep (bounded), returning the withdrawal list and the count of pending
partials consumed. -/
forkdef getExpectedWithdrawals (state : State) : Array Withdrawal × Nat := Id.run do
  let epoch := currentEpochOf state
  let validators := (sszGet state validators).toArray
  let nvals := validators.size
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := sszGet state nextWithdrawalIndex
  let mut processedPartial := 0
  -- Pending partial withdrawals (EIP-7251).
  let partialLimit := Nat.min Const.maxPendingPartialsPerWithdrawalsSweep (Const.maxWithdrawalsPerPayload - 1)
  for w in (sszGet state pendingPartialWithdrawals) do
    if !(w.withdrawableEpoch ≤ epoch) || withdrawals.size ≥ partialLimit then break
    let vi := w.validatorIndex
    let validator := validators[vi.toNat]?.getD default
    let bal := balanceAfterWithdrawals state vi withdrawals
    if isEligibleForPartialWithdrawals validator bal then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := vi, address := addressOf validator,
          amount := umin (bal - Const.minActivationBalance) w.amount }
      withdrawalIndex := withdrawalIndex + 1
    processedPartial := processedPartial + 1
  -- Validator sweep (Capella).
  let validatorsLimit := Nat.min nvals Const.maxValidatorsPerWithdrawalsSweep
  let mut vIdx := (sszGet state nextWithdrawalValidatorIndex).toNat
  for _ in [0:validatorsLimit] do
    if withdrawals.size ≥ Const.maxWithdrawalsPerPayload then break
    let validator := validators[vIdx]?.getD default
    let bal := balanceAfterWithdrawals state (UInt64.ofNat vIdx) withdrawals
    if isFullyWithdrawable validator bal epoch then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := UInt64.ofNat vIdx, address := addressOf validator, amount := bal }
      withdrawalIndex := withdrawalIndex + 1
    else if isPartiallyWithdrawable validator bal then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := UInt64.ofNat vIdx, address := addressOf validator,
          amount := bal - getMaxEffectiveBalance validator }
      withdrawalIndex := withdrawalIndex + 1
    vIdx := modWrap (vIdx + 1) nvals
  return (withdrawals, processedPartial)

/-! ## process_withdrawals -/

/-- `process_withdrawals`: the payload's withdrawals must equal the expected set;
apply them, then advance `next_withdrawal_index`, drop the consumed pending
partials, and advance the sweep cursor. -/
forkdef processWithdrawals (payload : ExecutionPayload) : StateTransition Unit := do
  let state ← get
  let (expected, processedPartial) := getExpectedWithdrawals state
  let expectedList : SSZList Withdrawal Const.maxWithdrawalsPerPayload := sszOfArray expected
  assert (htr expectedList == htr payload.withdrawals)
  let nvals := (sszGet state validators).size
  let mut stateAcc := state
  for w in expected do
    stateAcc := decreaseBalance stateAcc w.validatorIndex w.amount
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
