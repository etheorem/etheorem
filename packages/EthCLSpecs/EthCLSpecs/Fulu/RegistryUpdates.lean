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

/-- The Electra churn-reservation arithmetic core shared by
`compute_exit_epoch_and_update_churn` and `compute_consolidation_epoch_and_update_churn`:
given the `balance` to reserve, the churn already `consume`d this epoch, the `perEpoch` churn
limit, and the `earliest` candidate epoch, return the assigned epoch and the new consumed total.
When `balance` fits in the remaining budget (`balance ≤ consume`) the epoch and consumption are
unchanged; otherwise the leftover is spread forward by the ceiling-division
`(balanceToProcess - 1) / perEpoch + 1`, the `-1 … +1` rounding the quotient up. Pure on
`UInt64` (`Epoch`/`Gwei` are both `UInt64`), so the same byte arithmetic runs for Fulu's
exit/consolidation churn and Gloas's overrides; the per-fork state reads and the `state` write
stay in the callers. -/
def reserveChurn (balance consume perEpoch earliest : Gwei) : Epoch × Gwei :=
  if balance > consume then
    let balanceToProcess := balance - consume
    let additional := (balanceToProcess - 1) / perEpoch + 1
    (earliest + additional, consume + additional * perEpoch)
  else (earliest, consume)

/-- `compute_exit_epoch_and_update_churn`: reserve exit churn, returning the
assigned exit epoch and advancing the bookkeeping. -/
forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  let earliest := umax (sszGet state earliestExitEpoch) (computeActivationExitEpoch currentEpoch)
  let perEpochChurn := getActivationExitChurnLimit state
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)
  let (ee, ebtc) := reserveChurn exitBalance consume perEpochChurn earliest
  modifyState fun state =>
    sszUpdate state with exitBalanceToConsume := ebtc - exitBalance, earliestExitEpoch := ee
  return ee

/-- `compute_consolidation_epoch_and_update_churn`: the consolidation analogue of
`compute_exit_epoch_and_update_churn`, reserving consolidation churn. -/
forkdef computeConsolidationEpochAndUpdateChurn (consolidationBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let earliest := umax (sszGet state earliestConsolidationEpoch)
    (computeActivationExitEpoch (currentEpochOf state))
  let perEpoch := getConsolidationChurnLimit state
  let consume := if (sszGet state earliestConsolidationEpoch) < earliest then perEpoch
                 else (sszGet state consolidationBalanceToConsume)
  let (ee, cbtc) := reserveChurn consolidationBalance consume perEpoch earliest
  modifyState fun state =>
    sszUpdate state with consolidationBalanceToConsume := cbtc - consolidationBalance,
                     earliestConsolidationEpoch := ee
  return ee

/-! ## Validator-lifecycle mutators -/

/-- `initiate_validator_exit`. The `withdrawable_epoch = exit_epoch +
MIN_VALIDATOR_WITHDRAWABILITY_DELAY` sum is checked against the `uint64` bound:
the pyspec raises (and the case is invalid) when it overflows, where Lean's
`UInt64` would wrap silently, so the bound is asserted explicitly. -/
forkdef initiateValidatorExit (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  if !hasNotInitiatedExit validator then pure ()
  else
    let exitEpoch ← computeExitEpochAndUpdateChurn validator.effectiveBalance
    assert (exitEpoch.toNat + Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64)
    modifyState fun state => modValidator state i fun validator =>
      { validator with
          exitEpoch := exitEpoch,
          withdrawableEpoch := exitEpoch + UInt64.ofNat (Const.minValidatorWithdrawabilityDelay.toNat) }

/-- `slash_validator` (whistleblower = proposer). -/
forkdef slashValidator (i : ValidatorIndex) : StateTransition Unit := do
  let epoch := computeEpochAtSlot (sszGet (← get) slot)
  initiateValidatorExit i
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  let slashIdx := umodIdx epoch Const.epochsPerSlashingsVector
  let state := modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := umax validator.withdrawableEpoch (epoch + UInt64.ofNat Const.epochsPerSlashingsVector) }
  let state := sszUpdate state with
    slashings[slashIdx]! := (vget (sszGet state slashings) slashIdx + validator.effectiveBalance)
  let state := decreaseBalance state i (validator.effectiveBalance / UInt64.ofNat Const.minSlashingPenaltyQuotientElectra)
  set state
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward := validator.effectiveBalance / UInt64.ofNat Const.whistleblowerRewardQuotientElectra
  let proposerReward := whistleblowerReward * UInt64.ofNat Const.proposerWeight / UInt64.ofNat Const.weightDenominator
  modifyState fun state => increaseBalance state proposerIdx proposerReward
  modifyState fun state => increaseBalance state proposerIdx (whistleblowerReward - proposerReward)

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
