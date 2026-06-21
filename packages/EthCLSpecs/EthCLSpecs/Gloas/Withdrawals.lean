import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Fulu.Withdrawals

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
open EthCLSpecs.Fulu

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
`Fulu.State`, so it is restated here for the Gloas state. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) : Gwei :=
  let withdrawn := ws.foldl (fun acc w => if w.validatorIndex == vi then acc + w.amount else acc) 0
  let bal := sszGet state balances[vi.toNat]!
  if withdrawn > bal then 0 else bal - withdrawn

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
  let validators := (sszGet state validators).toArray
  let mut wi := withdrawalIndex
  let mut count := 0
  let mut ws : Array Withdrawal := #[]
  for w in (sszGet state pendingPartialWithdrawals) do
    let allW := prior ++ ws
    if !(w.withdrawableEpoch ≤ epoch) || allW.size ≥ limit then break
    let vi := w.validatorIndex
    let hb ← assertH (vi.toNat < validators.size)
    let validator := validators[vi.toNat]'hb.down
    let bal := balanceAfterWithdrawals state vi allW
    if isEligibleForPartialWithdrawals validator bal then
      ws := ws.push
        { index := wi, validatorIndex := vi, address := addressOf validator,
          amount := umin (bal - Const.minActivationBalance) w.amount }
      wi := wi + 1
    count := count + 1
  return (ws, wi, count)

/-- `get_builders_sweep_withdrawals` (NEW, EIP-7732): sweep up to
`MAX_BUILDERS_PER_WITHDRAWALS_SWEEP` builders from `next_withdrawal_builder_index`,
withdrawing the full balance of each withdrawable, non-empty builder. An out-of-range
builder cursor rejects. -/
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
    if prior.size + ws.size ≥ limit then break
    let hb ← assertH (builderIndex < bs.size)
    let builder := bs[builderIndex]'hb.down
    if builder.withdrawableEpoch ≤ epoch && builder.balance > 0 then
      ws := ws.push
        { index := wi, validatorIndex := convertBuilderIndexToValidatorIndex (UInt64.ofNat builderIndex),
          address := builder.executionAddress, amount := builder.balance }
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
    assert (vi < nvals)
    let validator := validators[vi]?.getD default
    let bal := balanceAfterWithdrawals state (UInt64.ofNat vi) allW
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
Returns the withdrawal set and the (builder, partial, builders-sweep) processed
counts the `update_*` helpers consume. -/
forkdef getExpectedWithdrawals : StateTransition (Array Withdrawal × Nat × Nat × Nat) := do
  let wi0 := sszGet (← get) nextWithdrawalIndex
  let (bw, wi1, bc) ← getBuilderWithdrawals wi0 #[]
  let (pw, wi2, pc) ← getPendingPartialWithdrawals wi1 bw
  let prior2 := bw ++ pw
  let (sw, wi3, sc) ← getBuildersSweepWithdrawals wi2 prior2
  let prior3 := prior2 ++ sw
  let (vw, _, _) ← getValidatorsSweepWithdrawals wi3 prior3
  return (prior3 ++ vw, bc, pc, sc)

/-- `apply_withdrawals` (MODIFIED, EIP-7732): decrement a builder's balance for a
builder-flagged withdrawal, otherwise the validator's. An out-of-range builder index
rejects. -/
forkdef applyWithdrawals (withdrawals : Array Withdrawal) : StateTransition Unit := do
  let mut stateAcc ← get
  for w in withdrawals do
    if isBuilderIndex w.validatorIndex then
      let builderIndex := toBuilderIndex w.validatorIndex
      let hb ← assertH (builderIndex.toNat < (sszGet stateAcc builders).size)
      let b := (sszGet stateAcc builders)[builderIndex.toNat]'hb.down
      stateAcc := sszUpdate stateAcc with builders[builderIndex.toNat]! := { b with balance := b.balance - umin w.amount b.balance }
    else
      stateAcc := decreaseBalance stateAcc w.validatorIndex w.amount
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
  modifyState fun state => sszUpdate state with payloadExpectedWithdrawals := sszOfArray expected
  -- update_builder_pending_withdrawals (NEW): drop the processed builder withdrawals
  modifyState fun state => sszUpdate state with builderPendingWithdrawals := sszDrop (sszGet state builderPendingWithdrawals) builderCount
  -- update_pending_partial_withdrawals: drop the processed pending partials
  modifyState fun state => sszUpdate state with pendingPartialWithdrawals := sszDrop (sszGet state pendingPartialWithdrawals) partialCount
  -- update_next_withdrawal_builder_index (NEW)
  modifyState fun state =>
    let n := (sszGet state builders).size
    if n > 0 then sszUpdate state with nextWithdrawalBuilderIndex := UInt64.ofNat (((sszGet state nextWithdrawalBuilderIndex).toNat + buildersSweepCount) % n)
    else state
  -- update_next_withdrawal_validator_index
  modifyState fun state =>
    let nvals := (sszGet state validators).size
    if expected.size == Const.maxWithdrawalsPerPayload then
      sszUpdate state with nextWithdrawalValidatorIndex :=
        UInt64.ofNat (modWrap ((expected[expected.size - 1]!).validatorIndex.toNat + 1) nvals)
    else
      sszUpdate state with nextWithdrawalValidatorIndex :=
        UInt64.ofNat (modWrap ((sszGet state nextWithdrawalValidatorIndex).toNat + Const.maxValidatorsPerWithdrawalsSweep) nvals)

end

end EthCLSpecs.Gloas
