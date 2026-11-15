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
  -- `toPlainInt` reason: index-only. The `sszModify` path spells the write
  -- position as a plain `Nat` for the view's `set!`; the pyspec writes
  -- `validators[index]` and this is that position, nothing more.
  sszModify state validators[i.toPlainInt]! := f

/-- `is_eligible_for_activation`: reads the finalized checkpoint, so it is a
state-operation predicate, not pure on the `Validator` (those live in
`Containers/Validator`). -/
forkdef isEligibleForActivation (state : State) (validator : Validator) : Bool :=
  validator.activationEligibilityEpoch ≤ (sszGet state finalizedCheckpoint).epoch && validator.activationEpoch == Const.farFutureEpoch

/-! ## Electra churn limits -/

/-- `get_balance_churn_limit`. -/
forkdef getBalanceChurnLimit (state : State) : Checked Gwei := do
  let churn := max Const.minPerEpochChurnLimitElectra
    (← getTotalActiveBalance state / Const.churnLimitQuotient.toNat)
  churn - churn % Const.effectiveBalanceIncrementG

/-- `get_activation_exit_churn_limit`. -/
forkdef getActivationExitChurnLimit (state : State) : Checked Gwei := do
  return min Const.maxPerEpochActivationExitChurnLimit (← getBalanceChurnLimit state)

/-- `get_consolidation_churn_limit`. -/
forkdef getConsolidationChurnLimit (state : State) : Checked Gwei :=
  getBalanceChurnLimit state - getActivationExitChurnLimit state

/-! ## Churn reservation -/

/-- The Electra churn-reservation arithmetic core shared by
`compute_exit_epoch_and_update_churn` and `compute_consolidation_epoch_and_update_churn`:
given the `balance` to reserve, the churn already `consume`d this epoch, the `perEpoch` churn
limit, and the `earliest` candidate epoch, return the assigned epoch and the new consumed total.
When `balance` fits in the remaining budget (`balance ≤ consume`) the epoch and consumption are
unchanged; otherwise the leftover is spread forward by the ceiling-division
`(balanceToProcess - 1) / perEpoch + 1`, the `-1 … +1` rounding the quotient up. `Epoch` and
`Gwei` are both checked `CLUint64` now, so the same byte arithmetic runs for Fulu's
exit/consolidation churn and Gloas's overrides; the per-fork state reads and the `state` write
stay in the callers. -/
forkdef reserveChurn (balance consume perEpoch : Gwei) (earliest : Epoch) :
    Checked (Epoch × Gwei) := do
  if balance > consume then
    let balanceToProcess ← balance - consume
    let additional ← (balanceToProcess - 1) / perEpoch + 1
    -- `earliest_exit_epoch += Epoch(additional_epochs)`: the checked `Epoch` sum itself.
    let epoch ← earliest + additional
    return (epoch, ← consume + additional * perEpoch)
  else return (earliest, consume)

/-- `compute_exit_epoch_and_update_churn`: reserve exit churn, returning the
assigned exit epoch and advancing the bookkeeping. -/
forkdef computeExitEpochAndUpdateChurn (exitBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  let currentEpoch := computeEpochAtSlot (sszGet state slot)
  -- `fulu/mainnet.py:6027-6029`: `max(earliest_exit_epoch, compute_activation_exit_epoch(...))`.
  let exitCandidate ← computeActivationExitEpoch currentEpoch
  let earliest := max (sszGet state earliestExitEpoch) exitCandidate
  let perEpochChurn ← getActivationExitChurnLimit state
  let consume := if (sszGet state earliestExitEpoch) < earliest then perEpochChurn else (sszGet state exitBalanceToConsume)

  let (ee, ebtc) ← reserveChurn exitBalance consume perEpochChurn earliest
  let remaining ← ebtc - exitBalance
  modifyState fun state =>
    sszUpdate state with exitBalanceToConsume := remaining, earliestExitEpoch := ee
  return ee

/-- `compute_consolidation_epoch_and_update_churn`: the consolidation analogue of
`compute_exit_epoch_and_update_churn`, reserving consolidation churn. -/
forkdef computeConsolidationEpochAndUpdateChurn (consolidationBalance : Gwei) : StateTransition Epoch := do
  let state ← get
  -- `fulu/mainnet.py:6054-6056`, the consolidation twin of the exit max.
  let exitCandidate ← computeActivationExitEpoch (currentEpochOf state)
  let earliest := max (sszGet state earliestConsolidationEpoch) exitCandidate
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

/-- `initiate_validator_exit` (`fulu/mainnet.py:1614-1628`). The
`withdrawable_epoch = exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` sum is a checked
`uint64` addition in the pyspec, so an overflow raises `ValueError` there; `Epoch` and the
constant are both `Epoch` now, so the body takes the checked operator directly.
`test_invalid_large_withdrawable_epoch` catches that raise in its own `except ValueError` and
scores it as the expected outcome (`RunnerCaughtSet.valueError`). -/
forkdef initiateValidatorExit (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i
  if !hasNotInitiatedExit validator then pure ()
  else
    let exitEpoch ← computeExitEpochAndUpdateChurn validator.effectiveBalance
    let withdrawableEpoch ← exitEpoch + Const.minValidatorWithdrawabilityDelay
    modifyState fun state => modValidator state i fun validator =>
      { validator with exitEpoch := exitEpoch, withdrawableEpoch := withdrawableEpoch }

/-- `slash_validator` (whistleblower = proposer) (`fulu/mainnet.py:1631-1659`). -/
forkdef slashValidator (i : ValidatorIndex) : StateTransition Unit := do
  let epoch := computeEpochAtSlot (sszGet (← get) slot)
  initiateValidatorExit i
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i
  -- `epoch % EPOCHS_PER_SLASHINGS_VECTOR`, the total ring index (positive preset divisor).
  let slashIdx := (epoch % Const.epochsPerSlashingsVectorDiv).toPlainInt

  -- Mark slashed, extend withdrawability, record the effective balance in the
  -- slashings ring buffer, and apply the slashing penalty. The withdrawability sum is the
  -- checked `epoch + EPOCHS_PER_SLASHINGS_VECTOR`, bound where the pyspec's assignment forms it.
  let withdrawableAt ← epoch + Const.epochsPerSlashingsVector
  let state := modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := max validator.withdrawableEpoch withdrawableAt }
  let slashed ← vget (sszGet state slashings) slashIdx + validator.effectiveBalance
  let state := sszUpdate state with slashings[slashIdx]! := slashed
  let state ← decreaseBalance state i (← validator.effectiveBalance / Const.minSlashingPenaltyQuotientElectra)
  set state

  -- Pay the proposer its share of the whistleblower reward, then the remainder.
  let proposerIdx := getBeaconProposerIndex (← get)
  let whistleblowerReward ← validator.effectiveBalance / Const.whistleblowerRewardQuotientElectra
  let proposerReward ← whistleblowerReward * Const.proposerWeight / Const.weightDenominator
  let state ← increaseBalance state proposerIdx proposerReward
  set (← increaseBalance state proposerIdx (← whistleblowerReward - proposerReward))

/-! ## Compounding / consolidation balance moves -/

/-- `queue_excess_active_balance`: move a validator's balance above
`MIN_ACTIVATION_BALANCE` into a pending deposit (the infinity-signature, genesis-slot
marker form). -/
forkdef queueExcessActiveBalance (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let balance ← sszGetIdx (sszGet state balances) i
  if balance > Const.minActivationBalance then
    let excess ← balance - Const.minActivationBalance
    let validator ← sszGetIdx (sszGet state validators) i
    let pendingDeposit : PendingDeposit :=
      { pubkey := validator.pubkey, withdrawalCredentials := validator.withdrawalCredentials, amount := excess,
        signature := Const.g2PointAtInfinity, slot := Const.genesisSlot }
    modifyState fun state => modBalance state i (fun _ => Const.minActivationBalance)
    appendState pendingDeposits pendingDeposit

/-- `switch_to_compounding_validator`: flip the credential prefix to compounding and
queue any excess active balance. -/
forkdef switchToCompoundingValidator (i : ValidatorIndex) : StateTransition Unit := do
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i
  let newWc : Bytes32 := validator.withdrawalCredentials.set 0 Const.compoundingWithdrawalPrefix
  modifyState fun state => modValidator state i (fun validator => { validator with withdrawalCredentials := newWc })
  queueExcessActiveBalance i

end

end EthCLSpecs.Fulu
