import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Fulu.Churn
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Proofs.Gloas.Churn`: the churn reservation at Gloas

Gloas `inherit`s `reserveChurn`, so it has its own constant. Its body reads no preset or
config value, so each `reserveChurn` theorem below takes the Fulu proof term unchanged.

The two callers need their own proofs, because they run over the Gloas `State`. Gloas
overrides `computeExitEpochAndUpdateChurn` (`Gloas/EpochProcessing.lean`) to read
`get_exit_churn_limit`. It inherits `computeConsolidationEpochAndUpdateChurn`, which then
reads the Gloas `getConsolidationChurnLimit`. That limit has no `MIN` floor, so it can be zero.
`reserveChurn` rejects a zero limit, as the pyspec's `ZeroDivisionError` does.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError checkedSub umax liftErr)
open EthCLSpecs.Gloas (Preset Config State reserveChurn computeExitEpochAndUpdateChurn
  computeConsolidationEpochAndUpdateChurn computeActivationExitEpoch computeEpochAtSlot
  currentEpochOf getExitChurnLimit getConsolidationChurnLimit)
open EthCLSpecs.Proofs.Fulu (churnEpochs churnDescrDiv)
open SizzLean.Repr
open SizzLean.Cache

/-- **Fits.** When the balance fits in the remaining budget, the reservation changes nothing
and cannot fault. -/
theorem reserveChurn_fits :
    ∀ (balance consume perEpoch earliest : UInt64), balance ≤ consume →
      (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
        = .ok (earliest, consume) :=
  Fulu.reserveChurn_fits

/-- **Zero limit.** The reservation rejects, as the pyspec's `ZeroDivisionError` does. -/
theorem reserveChurn_zero :
    ∀ (balance consume earliest : UInt64), consume < balance →
      (reserveChurn balance consume 0 earliest : Except StateTransitionError _)
        = .error (.arithmetic churnDescrDiv) :=
  Fulu.reserveChurn_zero

/-- **Below every bound.** The reservation succeeds with the exact epoch and consumed total. -/
@[characterizes reserveChurn]
theorem reserveChurn_ok :
    ∀ (balance consume perEpoch earliest : UInt64),
      consume < balance → 0 < perEpoch.toNat →
      earliest.toNat + churnEpochs balance consume perEpoch < 2 ^ 64 →
      churnEpochs balance consume perEpoch * perEpoch.toNat < 2 ^ 64 →
      consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat < 2 ^ 64 →
      ∃ epoch consumed : UInt64,
        (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
            = .ok (epoch, consumed) ∧
          epoch.toNat = earliest.toNat + churnEpochs balance consume perEpoch ∧
          consumed.toNat = consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat :=
  Fulu.reserveChurn_ok

/-- **At a bound.** The reservation rejects with `.arithmetic`. -/
theorem reserveChurn_overflow :
    ∀ (balance consume perEpoch earliest : UInt64),
      consume < balance → 0 < perEpoch.toNat →
      (2 ^ 64 ≤ earliest.toNat + churnEpochs balance consume perEpoch ∨
        2 ^ 64 ≤ churnEpochs balance consume perEpoch * perEpoch.toNat ∨
        2 ^ 64 ≤ consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat) →
      ∃ d : String,
        (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
          = .error (.arithmetic d) :=
  Fulu.reserveChurn_overflow

/-- **Coverage.** A successful reservation returns a consumed total at least as large as the
balance. -/
theorem reserveChurn_covers :
    ∀ (balance consume perEpoch earliest epoch consumed : UInt64),
      (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
          = .ok (epoch, consumed) →
        balance ≤ consumed :=
  Fulu.reserveChurn_covers

/-- **Exit churn, success.** When the activation-exit epoch and the reservation both succeed,
the run succeeds. It writes the consumed total minus the exit balance and the reserved epoch.
The subtraction cannot fault. The Gloas override reads `get_exit_churn_limit`. -/
@[characterizes computeExitEpochAndUpdateChurn]
theorem computeExitEpochAndUpdateChurn_run_ok [Preset] [HasherTag] [Config] :
    ∀ (state : State) (exitBalance activation epoch consumed : UInt64),
      (computeActivationExitEpoch (computeEpochAtSlot (sszGet state slot))
          : Except StateTransitionError UInt64) = .ok activation →
      (reserveChurn exitBalance
          (if sszGet state earliestExitEpoch < umax (sszGet state earliestExitEpoch) activation
            then getExitChurnLimit state else sszGet state exitBalanceToConsume)
          (getExitChurnLimit state)
          (umax (sszGet state earliestExitEpoch) activation)
          : Except StateTransitionError _) = .ok (epoch, consumed) →
      (computeExitEpochAndUpdateChurn (StateTransition := GloasRun) exitBalance).run state =
        .ok (epoch, sszUpdate state with exitBalanceToConsume := consumed - exitBalance,
          earliestExitEpoch := epoch) := by
  intro state exitBalance activation epoch consumed hact hres
  have hcov := reserveChurn_covers _ _ _ _ _ _ hres
  have hnot : ¬ exitBalance > consumed := Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hcov)
  simp [computeExitEpochAndUpdateChurn, hact, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept, checkedSub, hnot]
  rfl

/-- **Exit churn, activation fault.** The run rejects with the activation-epoch fault. -/
theorem computeExitEpochAndUpdateChurn_run_activation_error [Preset] [HasherTag] [Config] :
    ∀ (state : State) (exitBalance : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (computeEpochAtSlot (sszGet state slot))
          : Except StateTransitionError UInt64) = .error err →
      (computeExitEpochAndUpdateChurn (StateTransition := GloasRun) exitBalance).run state
        = .error err := by
  intro state exitBalance err hact
  simp [computeExitEpochAndUpdateChurn, hact, liftErr, Except.mapError, MonadExcept.ofExcept]
  rfl

/-- **Exit churn, reservation fault.** The run rejects with the reservation's fault. -/
theorem computeExitEpochAndUpdateChurn_run_reserve_error [Preset] [HasherTag] [Config] :
    ∀ (state : State) (exitBalance activation : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (computeEpochAtSlot (sszGet state slot))
          : Except StateTransitionError UInt64) = .ok activation →
      (reserveChurn exitBalance
          (if sszGet state earliestExitEpoch < umax (sszGet state earliestExitEpoch) activation
            then getExitChurnLimit state else sszGet state exitBalanceToConsume)
          (getExitChurnLimit state)
          (umax (sszGet state earliestExitEpoch) activation)
          : Except StateTransitionError _) = .error err →
      (computeExitEpochAndUpdateChurn (StateTransition := GloasRun) exitBalance).run state
        = .error err := by
  intro state exitBalance activation err hact hres
  simp [computeExitEpochAndUpdateChurn, hact, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Consolidation churn, success.** The consolidation analogue, over the Gloas
consolidation churn limit. -/
@[characterizes computeConsolidationEpochAndUpdateChurn]
theorem computeConsolidationEpochAndUpdateChurn_run_ok [Preset] [HasherTag] [Config] :
    ∀ (state : State) (balance activation epoch consumed : UInt64),
      (computeActivationExitEpoch (currentEpochOf state)
          : Except StateTransitionError UInt64) = .ok activation →
      (reserveChurn balance
          (if sszGet state earliestConsolidationEpoch
                < umax (sszGet state earliestConsolidationEpoch) activation
            then getConsolidationChurnLimit state else sszGet state consolidationBalanceToConsume)
          (getConsolidationChurnLimit state)
          (umax (sszGet state earliestConsolidationEpoch) activation)
          : Except StateTransitionError _) = .ok (epoch, consumed) →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := GloasRun) balance).run state =
        .ok (epoch, sszUpdate state with consolidationBalanceToConsume := consumed - balance,
          earliestConsolidationEpoch := epoch) := by
  intro state balance activation epoch consumed hact hres
  have hcov := reserveChurn_covers _ _ _ _ _ _ hres
  have hnot : ¬ balance > consumed := Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hcov)
  simp [computeConsolidationEpochAndUpdateChurn, hact, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept, checkedSub, hnot]
  rfl

/-- **Consolidation churn, activation fault.** The run rejects with the activation-epoch
fault. -/
theorem computeConsolidationEpochAndUpdateChurn_run_activation_error
    [Preset] [HasherTag] [Config] :
    ∀ (state : State) (balance : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (currentEpochOf state)
          : Except StateTransitionError UInt64) = .error err →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := GloasRun) balance).run state
        = .error err := by
  intro state balance err hact
  simp [computeConsolidationEpochAndUpdateChurn, hact, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Consolidation churn, reservation fault.** The run rejects with the reservation's
fault. -/
theorem computeConsolidationEpochAndUpdateChurn_run_reserve_error
    [Preset] [HasherTag] [Config] :
    ∀ (state : State) (balance activation : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (currentEpochOf state)
          : Except StateTransitionError UInt64) = .ok activation →
      (reserveChurn balance
          (if sszGet state earliestConsolidationEpoch
                < umax (sszGet state earliestConsolidationEpoch) activation
            then getConsolidationChurnLimit state else sszGet state consolidationBalanceToConsume)
          (getConsolidationChurnLimit state)
          (umax (sszGet state earliestConsolidationEpoch) activation)
          : Except StateTransitionError _) = .error err →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := GloasRun) balance).run state
        = .error err := by
  intro state balance activation err hact hres
  simp [computeConsolidationEpochAndUpdateChurn, hact, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

end EthCLSpecs.Proofs.Gloas
