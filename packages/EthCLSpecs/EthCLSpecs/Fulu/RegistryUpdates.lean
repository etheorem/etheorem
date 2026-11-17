import EthCLSpecs.Fulu.Accessors

/-!
# `EthCLSpecs.Fulu.RegistryUpdates`: registry mutators, churn, lifecycle (load order rows 27–28)

The write side of the registry concern: the Electra churn reservations
(`get_balance_churn_limit` and friends, `compute_exit_epoch_and_update_churn`),
the validator-lifecycle mutators (`initiate_validator_exit`, `slash_validator`),
and the consolidation / compounding mutators (`SPECS_ARCHITECTURE.md` §3.1 rows
27–28). These float **above** `Committees` because `slashValidator` calls
`getBeaconProposerIndex`; the read-only registry accessors stayed low in
`Registry` (the §3.3 seam).

The state-reading activation predicate `is_eligible_for_activation` (a one-line
predicate, the tiny row-27 concern) is merged here rather than into its own file,
the registry-update stratum it belongs to (§3.2 allows a tiny concern to merge
with an adjacent one). The churn helpers read config-tier constants, so the
section carries `[Config]`; Lean attaches it only where used.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- Modify validator `i` via the infallible `[i]!` element write: total (fits the
pure `State → State` shape), and the cached single-leaf update for the composite
`Validator` element. -/
forkdef modValidator (state : State) (i : ValidatorIndex) (f : Validator → Validator) : State :=
  sszModify state validators[i.toNat]! := f

/-- `is_eligible_for_activation`: reads the finalized checkpoint, so it is a
state-operation predicate, not pure on the `Validator` (those live in
`Containers/Validator`). -/
forkdef isEligibleForActivation (state : State) (validator : Validator) : Bool :=
  validator.activationEligibilityEpoch ≤ (sszGet state finalizedCheckpoint).epoch && validator.activationEpoch == Const.farFutureEpoch

/-! ## Electra churn limits -/

/-- `get_balance_churn_limit` (`fulu/mainnet.py:5970-5977`): `churn =
max(MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA, get_total_active_balance(state) //
config.CHURN_LIMIT_QUOTIENT)`, then `churn - churn % EFFECTIVE_BALANCE_INCREMENT`.
Every operand is `Gwei`, so the division, modulo, and subtraction are the
checked `Gwei` operators, each bound as the pyspec assigns it
(`SPEC_ARITHMETIC.md` §4.3). The divisor is the checked config view; a
configuration value keeps checked division (`SPEC_ARITHMETIC.md` §4.2). -/
forkdef getBalanceChurnLimit (state : State) : Checked Gwei := do
  let totalActiveBalance ← getTotalActiveBalance state
  let scaled ← totalActiveBalance / Const.churnLimitQuotientC
  let churn := max Const.minPerEpochChurnLimitElectra scaled
  let rounded ← churn % Const.effectiveBalanceIncrementG
  churn - rounded

/-- `get_activation_exit_churn_limit` (`fulu/mainnet.py:5980-5985`):
`min(config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT, get_balance_churn_limit(state))`.
The churn limit binds first, the comparison picks an operand. -/
forkdef getActivationExitChurnLimit (state : State) : Checked Gwei := do
  let churn ← getBalanceChurnLimit state
  return min Const.maxPerEpochActivationExitChurnLimit churn

/-- `get_consolidation_churn_limit` (`fulu/mainnet.py:5988-5990`): the balance
churn limit minus the activation/exit one, both bound before the checked
subtraction. -/
forkdef getConsolidationChurnLimit (state : State) : Checked Gwei := do
  let total ← getBalanceChurnLimit state
  let exit ← getActivationExitChurnLimit state
  total - exit

/-! ## Churn reservation -/

/-- The Electra churn-reservation arithmetic core shared by
`compute_exit_epoch_and_update_churn` and `compute_consolidation_epoch_and_update_churn`
(`fulu/mainnet.py:6034-6042`): given the `balance` to reserve, the churn already
`consume`d this epoch, and the `perEpoch` churn limit, return the assigned `Epoch`
and the new consumed total. When `balance` fits in the remaining budget
(`balance ≤ consume`) the epoch and consumption are unchanged; otherwise the leftover is
spread forward by the ceiling-division `(balanceToProcess - 1) / perEpoch + 1`, the
`-1 … +1` rounding the quotient up. Every step is the pyspec's checked arithmetic, so the
core returns a `Checked` pair and each branch binds its own arithmetic.

TEMPORARY CROSSING (removed in Stage 5): `earliest` arrives as the still-raw
`Epoch`. The checked addition forms on the value through the wire route, and
the in-range result adapts back to the raw `Epoch` with the underlying-value
projection. Stage 5 moves `Epoch` onto the checked surface and deletes the
crossing. -/
forkdef reserveChurn (balance consume perEpoch : Gwei) (earliest : Epoch) :
    Checked (Epoch × Gwei) := do
  if balance > consume then
    let balanceToProcess ← balance - consume
    let additional ← (balanceToProcess - 1) / perEpoch + 1
    -- TEMPORARY CROSSING (removed in Stage 5): the pyspec's
    -- `earliest_exit_epoch += Epoch(additional_epochs)`; `earliest` is the raw
    -- `Epoch` until Stage 5.
    let sum ← CLUint64.trustedOfUInt64 earliest + additional
    let consumed ← consume + additional * perEpoch
    return (UInt64.ofNat sum.toPlainNat, consumed)
  else return (earliest, consume)

/-- `compute_exit_epoch_and_update_churn` (`fulu/mainnet.py:6026-6049`): reserve
exit churn, returning the assigned exit epoch and advancing the bookkeeping.
The per-epoch churn limit and the reservation arithmetic are checked `Gwei`
chains, so each binds where the pyspec assigns it. -/
forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  let earliest := umax (sszGet state earliestExitEpoch) (computeActivationExitEpoch currentEpoch)
  let perEpochChurn ← getActivationExitChurnLimit state
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)

  let (ee, ebtc) ← reserveChurn exitBalance consume perEpochChurn earliest
  let remaining ← ebtc - exitBalance
  modifyState fun state =>
    sszUpdate state with exitBalanceToConsume := remaining, earliestExitEpoch := ee
  return ee

/-- `compute_consolidation_epoch_and_update_churn`
(`fulu/mainnet.py:6051-6077`): the consolidation analogue of
`compute_exit_epoch_and_update_churn`, reserving consolidation churn. -/
forkdef computeConsolidationEpochAndUpdateChurn (consolidationBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let earliest := umax (sszGet state earliestConsolidationEpoch)
    (computeActivationExitEpoch (currentEpochOf state))
  let perEpoch ← getConsolidationChurnLimit state
  let consume := if (sszGet state earliestConsolidationEpoch) < earliest then perEpoch
                 else (sszGet state consolidationBalanceToConsume)

  let (ee, cbtc) ← reserveChurn consolidationBalance consume perEpoch earliest
  let remaining ← cbtc - consolidationBalance
  modifyState fun state =>
    sszUpdate state with consolidationBalanceToConsume := remaining,
                     earliestConsolidationEpoch := ee
  return ee

/-! ## Validator-lifecycle mutators -/

/-- `initiate_validator_exit`. The `withdrawable_epoch = exit_epoch +
MIN_VALIDATOR_WITHDRAWABILITY_DELAY` sum is a bare `uint64` addition in the pyspec, so an
overflow raises `ValueError` there. `checkedAdd` models the addition and reports the
`.arithmetic` uncaught fault. `test_invalid_large_withdrawable_epoch` catches that raise in its
own `except ValueError` and scores it as the expected outcome
(`RunnerCaughtSet.valueError`). -/
forkdef initiateValidatorExit (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  if !hasNotInitiatedExit validator then pure ()
  else
    let exitEpoch ← computeExitEpochAndUpdateChurn validator.effectiveBalance
    let withdrawableEpoch ← checkedAdd exitEpoch Const.minValidatorWithdrawabilityDelay
      "initiate_validator_exit: exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY"
    modifyState fun state => modValidator state i fun validator =>
      { validator with exitEpoch := exitEpoch, withdrawableEpoch := withdrawableEpoch }

/-- `slash_validator` (whistleblower = proposer; `fulu/mainnet.py:1631-1661`).
The `slashings` ring store and the penalty / reward chain are the checked
`Gwei` surface: the ring `+=` reads, adds, and stores
(`fulu/mainnet.py:1644`), the penalty divides by
`MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA`, and the whistleblower reward splits by
`PROPOSER_WEIGHT // WEIGHT_DENOMINATOR`, each step a checked `Gwei` operation
bound where the pyspec forms it. The `withdrawableEpoch` and `epoch` parts run
in the raw `Epoch` until Stage 5. -/
forkdef slashValidator (i : ValidatorIndex) : StateTransition Unit := do
  let epoch := computeEpochAtSlot (sszGet (← get) slot)
  initiateValidatorExit i
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  let slashIdx := umodIdx epoch Const.epochsPerSlashingsVector

  -- Mark slashed, extend withdrawability, record the effective balance in the
  -- slashings ring buffer, and apply the slashing penalty.
  let state := modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := umax validator.withdrawableEpoch (epoch + UInt64.ofNat Const.epochsPerSlashingsVector) }
  let ringTotal ← vget (sszGet state slashings) slashIdx + validator.effectiveBalance
  let state := sszUpdate state with
    slashings[slashIdx]! := ringTotal
  let slashingPenalty ← validator.effectiveBalance / Const.minSlashingPenaltyQuotientElectra
  let state ← decreaseBalance state i slashingPenalty
  set state

  -- Pay the proposer its share of the whistleblower reward, then the remainder.
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward ← validator.effectiveBalance / Const.whistleblowerRewardQuotientElectra
  let proposerReward ← whistleblowerReward * Const.proposerWeight / Const.weightDenominator
  let state ← increaseBalance state proposerIdx proposerReward
  let remainder ← whistleblowerReward - proposerReward
  set (← increaseBalance state proposerIdx remainder)

/-! ## Compounding / consolidation balance moves -/

/-- `queue_excess_active_balance` (`fulu/mainnet.py`): move a validator's balance above
`MIN_ACTIVATION_BALANCE` into a pending deposit (the infinity-signature, genesis-slot
marker form). The excess is the checked `balance - MIN_ACTIVATION_BALANCE` difference,
formed and bound inside the branch, where the pyspec computes it. -/
forkdef queueExcessActiveBalance (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let balance ← sszGetIdx (sszGet state balances) i.toNat
  if balance > Const.minActivationBalance then
    let excess ← balance - Const.minActivationBalance
    let validator ← sszGetIdx (sszGet state validators) i.toNat
    let pendingDeposit : PendingDeposit :=
      { pubkey := validator.pubkey, withdrawalCredentials := validator.withdrawalCredentials, amount := excess,
        signature := Const.g2PointAtInfinity, slot := Const.genesisSlot }
    modifyState fun state => modBalance state i (fun _ => Const.minActivationBalance)
    appendState pendingDeposits pendingDeposit

/-- `switch_to_compounding_validator`: flip the credential prefix to compounding and
queue any excess active balance. -/
forkdef switchToCompoundingValidator (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  let newWc : Bytes32 := validator.withdrawalCredentials.set 0 Const.compoundingWithdrawalPrefix
  modifyState fun state => modValidator state i (fun validator => { validator with withdrawalCredentials := newWc })
  queueExcessActiveBalance i

end

end EthCLSpecs.Fulu
