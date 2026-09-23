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

/-- `get_balance_churn_limit`. -/
forkdef getBalanceChurnLimit (state : State) : Gwei :=
  let churn := umax Const.minPerEpochChurnLimitElectra
    ((getTotalActiveBalance state) / Const.churnLimitQuotient)
  churn - churn % Const.effectiveBalanceIncrementG

/-- `get_activation_exit_churn_limit`. -/
forkdef getActivationExitChurnLimit (state : State) : Gwei :=
  umin Const.maxPerEpochActivationExitChurnLimit (getBalanceChurnLimit state)

/-- `get_consolidation_churn_limit`. -/
forkdef getConsolidationChurnLimit (state : State) : Gwei :=
  getBalanceChurnLimit state - getActivationExitChurnLimit state

/-! ## Churn reservation -/

/-- The Electra churn-reservation arithmetic that `compute_exit_epoch_and_update_churn` and
`compute_consolidation_epoch_and_update_churn` share. The inputs are the `balance` to reserve,
the churn already `consume`d this epoch, the `perEpoch` churn limit, and the `earliest`
candidate epoch. The result is the assigned epoch and the new consumed total.

When `balance ≤ consume`, the balance fits in the remaining budget, and both values stay
unchanged. Otherwise the ceiling division `(balanceToProcess - 1) / perEpoch + 1` spreads the
rest over later epochs. The `- 1 … + 1` rounds the quotient up.

`Epoch` and `Gwei` are both `UInt64`, so the same arithmetic serves the Fulu exit churn, the
consolidation churn, and the Gloas override. The callers read the per-fork state and write it.

The pyspec runs every step on remerkleable `uint64` values, so each step can raise. Four steps
can fault, and the body checks each one in the spec's order:

1. `// per_epoch_churn` raises `ZeroDivisionError` on a zero limit.
2. `earliest_epoch += additional_epochs` raises `ValueError` past `2 ^ 64 - 1`.
3. `additional_epochs * per_epoch_churn` raises `ValueError` past `2 ^ 64 - 1`.
4. `balance_to_consume += …` raises `ValueError` past `2 ^ 64 - 1`.

Each fault is `.arithmetic`. The other steps stay raw, because they cannot fault. The guard
`balance > consume` makes `balance - consume` at least `1`, so the `- 1` cannot underflow. The
quotient is at most `2 ^ 64 - 2`, so the `+ 1` cannot overflow. -/
forkdef reserveChurn (balance consume perEpoch earliest : Gwei) :
    Except StateTransitionError (Epoch × Gwei) := do
  if balance > consume then
    let balanceToProcess := balance - consume
    if perEpoch == 0 then
      throwArithmetic "reserve_churn: (balance_to_process - 1) // per_epoch_churn"
    let additional := (balanceToProcess - 1) / perEpoch + 1
    let epoch ← checkedAdd earliest additional "reserve_churn: earliest_epoch += additional_epochs"
    let added ← checkedMul additional perEpoch
      "reserve_churn: additional_epochs * per_epoch_churn"
    let consumed ← checkedAdd consume added
      "reserve_churn: balance_to_consume += additional_epochs * per_epoch_churn"
    pure (epoch, consumed)
  else pure (earliest, consume)

/-- `compute_exit_epoch_and_update_churn`: reserve exit churn, returning the
assigned exit epoch and advancing the bookkeeping. -/
forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  let activationExitEpoch ← liftErr (computeActivationExitEpoch currentEpoch)
  let earliest := umax (sszGet state earliestExitEpoch) activationExitEpoch
  let perEpochChurn := getActivationExitChurnLimit state
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)

  let (ee, ebtc) ← liftErr (reserveChurn exitBalance consume perEpochChurn earliest)
  let remaining ← checkedSub ebtc exitBalance
    "compute_exit_epoch_and_update_churn: exit_balance_to_consume - exit_balance"
  modifyState fun state =>
    sszUpdate state with exitBalanceToConsume := remaining, earliestExitEpoch := ee
  return ee

/-- `compute_consolidation_epoch_and_update_churn`: the consolidation analogue of
`compute_exit_epoch_and_update_churn`, reserving consolidation churn. -/
forkdef computeConsolidationEpochAndUpdateChurn (consolidationBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let activationExitEpoch ← liftErr (computeActivationExitEpoch (currentEpochOf state))
  let earliest := umax (sszGet state earliestConsolidationEpoch) activationExitEpoch
  let perEpoch := getConsolidationChurnLimit state
  let consume := if (sszGet state earliestConsolidationEpoch) < earliest then perEpoch
                 else (sszGet state consolidationBalanceToConsume)

  let (ee, cbtc) ← liftErr (reserveChurn consolidationBalance consume perEpoch earliest)
  let remaining ← checkedSub cbtc consolidationBalance
    "compute_consolidation_epoch_and_update_churn: consolidation_balance_to_consume - consolidation_balance"
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

/-- `slash_validator` (whistleblower = proposer). -/
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
  let state := sszUpdate state with
    slashings[slashIdx]! := (vget (sszGet state slashings) slashIdx + validator.effectiveBalance)
  let state ← decreaseBalance state i (validator.effectiveBalance / UInt64.ofNat Const.minSlashingPenaltyQuotientElectra)
  set state

  -- Pay the proposer its share of the whistleblower reward, then the remainder.
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward := validator.effectiveBalance / UInt64.ofNat Const.whistleblowerRewardQuotientElectra
  let proposerReward := whistleblowerReward * UInt64.ofNat Const.proposerWeight / UInt64.ofNat Const.weightDenominator
  let state ← increaseBalance state proposerIdx proposerReward
  set (← increaseBalance state proposerIdx (whistleblowerReward - proposerReward))

/-! ## Compounding / consolidation balance moves -/

/-- `queue_excess_active_balance`: move a validator's balance above
`MIN_ACTIVATION_BALANCE` into a pending deposit (the infinity-signature, genesis-slot
marker form). -/
forkdef queueExcessActiveBalance (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let balance ← sszGetIdx (sszGet state balances) i.toNat
  if balance > Const.minActivationBalance then
    let excess := balance - Const.minActivationBalance
    let validator ← sszGetIdx (sszGet state validators) i.toNat
    let pendingDeposit : PendingDeposit :=
      { pubkey := validator.pubkey, withdrawalCredentials := validator.withdrawalCredentials, amount := excess,
        signature := Const.g2PointAtInfinity, slot := Const.genesisSlot }
    modifyState fun state =>
      let state := modBalance state i (fun _ => Const.minActivationBalance)
      sszAppend state pendingDeposits pendingDeposit

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
