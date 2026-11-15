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

The `withdrawn` accumulator folds through `checkedAdd`, which is where pyspec faults too.
`sum(...)` looks like it widens to a Python `int`, but `Gwei` subclasses `int` and defines
`__radd__`, so Python's reflected-operand rule makes the accumulator a `Gwei` from the first
element on, and every add re-runs the bound check in `uint.__new__`
(`remerkleable/basic.py:88-107`). A running sum past `2^64` therefore raises `ValueError`
during the accumulation, not at the later subtraction. Verified against the pinned
remerkleable. -/
def balanceAfterWithdrawals (state : State) (vi : ValidatorIndex) (ws : Array Withdrawal) :
    StateTransition Gwei := do
  let withdrawn ← ws.foldlM (init := (0 : Gwei)) fun acc w =>
    if w.validatorIndex == vi then acc + w.amount else pure acc
  let bal ← sszGetIdx (sszGet state balances) vi
  bal - withdrawn

/-- `get_expected_withdrawals`: the pending-partial queue then the validator sweep.
Throwing: the two `validators[i]` reads are bare list indices (`IndexError`, via
`sszGetIdx` → `outOfBounds`, the same faithful class as the balance read), and
`balanceAfterWithdrawals` raises on the balance read / underflow; both need a well-formed
state. The sweep cursor's `% len(state.validators)` raise is unreachable on every state,
because the sweep's bound is `min(len(validators), …)` and a zero bound skips the loop
body; the empty-registry raise is reachable at the update site in `processWithdrawals`
below. -/
forkdef getExpectedWithdrawals (state : State) : StateTransition (Array Withdrawal × Nat) := do
  let epoch := currentEpochOf state
  let validators := (sszGet state validators).toArray
  let mut withdrawals : Array Withdrawal := #[]
  let mut withdrawalIndex := sszGet state nextWithdrawalIndex
  let mut processedPartial := 0

  -- Pending partial withdrawals (EIP-7251). `len(withdrawals)` is a plain `int`, so the
  -- cap comparison reads through `CLInt`. The pinned limit is
  -- `min(len(prior) + MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP, MAX_WITHDRAWALS_PER_PAYLOAD - 1)`;
  -- `get_expected_withdrawals` calls this phase with an empty prior list, so the
  -- `len(prior)` term drops.
  let partialLimit := Nat.min Const.maxPendingPartialsPerWithdrawalsSweep (Const.maxWithdrawalsPerPayload - 1)
  for w in (sszGet state pendingPartialWithdrawals) do
    if !(w.withdrawableEpoch ≤ epoch) || CLInt.len withdrawals ≥ partialLimit then break
    let vi := w.validatorIndex
    let validator ← sszGetIdx (sszGet state validators) vi
    let bal ← balanceAfterWithdrawals state vi withdrawals
    if isEligibleForPartialWithdrawals validator bal then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := vi, address := addressOf validator,
          amount := min (← bal - Const.minActivationBalance) w.amount }
      withdrawalIndex := withdrawalIndex + 1
    processedPartial := processedPartial + 1

  -- Validator sweep (Capella). `vIdx` is the sweep cursor, the checked `ValidatorIndex`
  -- the state field holds, and each advance is the pyspec's
  -- `(validator_index + 1) % len(state.validators)`: the `+` is a total `CLInt` sum, the
  -- `%` is a `CLInt` modulo that raises on a zero divisor, and `toUint64?` is the
  -- `Uint64(n)` narrowing into the cursor. The empty-registry raise is unreachable here
  -- (the loop bound is `min(len(validators), …)`), reachable at the update site below.
  let validatorsLimit := Nat.min validators.size Const.maxValidatorsPerWithdrawalsSweep
  let mut vIdx := sszGet state nextWithdrawalValidatorIndex
  for _ in [0:validatorsLimit] do
    if CLInt.len withdrawals ≥ Const.maxWithdrawalsPerPayload then break
    let validator ← sszGetIdx (sszGet state validators) vIdx
    let bal ← balanceAfterWithdrawals state vIdx withdrawals
    if isFullyWithdrawable validator bal epoch then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := vIdx, address := addressOf validator, amount := bal }
      withdrawalIndex := withdrawalIndex + 1
    else if isPartiallyWithdrawable validator bal then
      withdrawals := withdrawals.push
        { index := withdrawalIndex, validatorIndex := vIdx, address := addressOf validator,
          amount := (← bal - getMaxEffectiveBalance validator) }
      withdrawalIndex := withdrawalIndex + 1
    let advanced ← (vIdx.toInt + 1) % CLInt.len validators
    vIdx := ← advanced.toUint64?
  return (withdrawals, processedPartial)

/-! ## process_withdrawals -/

/-- `process_withdrawals`: the payload's withdrawals must equal the expected set;
apply them, then advance `next_withdrawal_index`, drop the consumed pending
partials, and advance the sweep cursor.

Throwing beyond the expected-set assert: `withdrawals[-1]` is the plain negative literal
index, counted from the end (§3.7), so both reads go through the raising `⟦·⟧` route, and
the sweep cursor's `% len(state.validators)` raises on an empty registry (the one
empty-registry path the sweep body itself cannot reach). -/
forkdef processWithdrawals (payload : ExecutionPayload) : StateTransition Unit := do
  let state ← get
  let (expected, processedPartial) ← getExpectedWithdrawals state
  -- `payload.withdrawals == expected.withdrawals`: remerkleable's `View.__eq__` coerces the
  -- Python list through the `List` constructor, which raises on too many elements, then
  -- compares roots.
  let expectedList : SSZList Withdrawal Const.maxWithdrawalsPerPayload ←
    sszOfArrayM "withdrawals" expected
  assert (htr expectedList == htr payload.withdrawals)

  let nvals := CLInt.len (sszGet state validators).toArray
  let mut stateAcc := state
  for w in expected do
    stateAcc ← decreaseBalance stateAcc w.validatorIndex w.amount

  -- update_next_withdrawal_index: `latest_withdrawal = withdrawals[-1]`, counted from the
  -- end. `WithdrawalIndex` is still the raw `UInt64`, so the `+ 1` wraps at the maximum
  -- where the pyspec's checked add raises. A known gap (IMPLEMENTATION_NOTES.md, "Fulu
  -- state transition"); the `WithdrawalIndex` migration closes it, and the three
  -- `withdrawalIndex + 1` sites in `getExpectedWithdrawals` share it.
  if expected.size != 0 then
    let last ← expected⟦(-1 : CLInt)⟧
    stateAcc := sszUpdate stateAcc with nextWithdrawalIndex := last.index + 1
  stateAcc := sszUpdate stateAcc with pendingPartialWithdrawals := sszDrop (sszGet stateAcc pendingPartialWithdrawals) processedPartial
  -- update_next_withdrawal_validator_index: a full payload resumes one past the last
  -- validator drained, `(withdrawals[-1].validator_index + 1) % len(state.validators)`:
  -- the negative read, the total `CLInt` `+ 1`, the `%` that raises on an empty registry,
  -- then `toUint64?` into the cursor. A short payload jumps a whole sweep window ahead,
  -- `uint64 + uint64` checked, then the same `%`.
  if expected.size == Const.maxWithdrawalsPerPayload then
    let last ← expected⟦(-1 : CLInt)⟧
    let nextV ← (last.validatorIndex.toInt + 1) % nvals
    let nextCursor ← nextV.toUint64?
    stateAcc := sszUpdate stateAcc with nextWithdrawalValidatorIndex := nextCursor
  else
    let nextIndex ← (sszGet stateAcc nextWithdrawalValidatorIndex) + Const.maxValidatorsPerWithdrawalsSweep
    let nextCursor ← nextIndex % nvals
    stateAcc := sszUpdate stateAcc with nextWithdrawalValidatorIndex := nextCursor
  set stateAcc

end

end EthCLSpecs.Fulu
