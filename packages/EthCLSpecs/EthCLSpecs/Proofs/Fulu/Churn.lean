import EthCLSpecs.Fulu.RegistryUpdates
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Checked
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Fulu.Churn`: where the churn reservation faults, and what it covers

`reserveChurn` (`Fulu/RegistryUpdates.lean`) is the arithmetic that
`compute_exit_epoch_and_update_churn` and `compute_consolidation_epoch_and_update_churn`
share (`electra/beacon-chain.md:770`, `:798`). The pyspec runs it on `uint64` values, so four
steps can raise: the division on a zero limit, and the epoch add, the multiply, and the
consumed add past `2 ^ 64 - 1`. `reserveChurn` rejects at each of those four points with
`.arithmetic`.

A successful reservation covers the balance: the new consumed total is at least the balance.
So the callers' `balance_to_consume - balance` never underflows, and its `checkedSub` never
faults. The run theorems at the end state this for both Fulu callers.

The caller theorems bind plain `BeaconState` values. Each one runs its caller on
`pureState state`, and a successful run returns `pureState` of the updated record.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag StateTransitionError checkedAdd checkedMul checkedSub
  throwArithmetic)
open EthCLLib.Proofs (mulGuard_iff)
open EthCLSpecs.Fulu (Preset Config BeaconState reserveChurn computeExitEpochAndUpdateChurn
  computeConsolidationEpochAndUpdateChurn computeActivationExitEpoch computeEpochAtSlot
  currentEpochOf getActivationExitChurnLimit getConsolidationChurnLimit)

/-- The descriptor of the zero-limit reject. -/
abbrev churnDescrDiv : String := "reserve_churn: (balance_to_process - 1) // per_epoch_churn"

/-- The descriptor of the epoch addition. -/
abbrev churnDescrEpoch : String := "reserve_churn: earliest_epoch += additional_epochs"

/-- The descriptor of the multiply. -/
abbrev churnDescrMul : String := "reserve_churn: additional_epochs * per_epoch_churn"

/-- The descriptor of the consumed addition. -/
abbrev churnDescrConsume : String :=
  "reserve_churn: balance_to_consume += additional_epochs * per_epoch_churn"

/-- The additional epochs as a `Nat`: the ceiling of `(balance - consume) / perEpoch`, in the
spec's `(x - 1) // p + 1` form. -/
abbrev churnEpochs (balance consume perEpoch : UInt64) : Nat :=
  (balance.toNat - consume.toNat - 1) / perEpoch.toNat + 1

/-- The raw `uint64` steps before the checked ones cannot wrap. `balance > consume` makes the
difference at least `1`, and the quotient is at most `2 ^ 64 - 2`, so the `+ 1` stays in
range. The `UInt64` value therefore equals `churnEpochs`. -/
private theorem additional_toNat (balance consume perEpoch : UInt64) (h : consume < balance) :
    ((balance - consume - 1) / perEpoch + 1).toNat = churnEpochs balance consume perEpoch := by
  have hlt := UInt64.lt_iff_toNat_lt.mp h
  have hb := UInt64.toNat_lt balance
  have hsub : (balance - consume).toNat = balance.toNat - consume.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)
  have hone : (1 : UInt64) ≤ balance - consume := by
    rw [UInt64.le_iff_toNat_le, hsub, UInt64.toNat_one]
    omega
  have hsub1 : (balance - consume - 1).toNat = balance.toNat - consume.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ hone, hsub, UInt64.toNat_one]
  have hq : (balance.toNat - consume.toNat - 1) / perEpoch.toNat ≤
      balance.toNat - consume.toNat - 1 := Nat.div_le_self _ _
  rw [UInt64.toNat_add, UInt64.toNat_div, hsub1, UInt64.toNat_one,
    Nat.mod_eq_of_lt (by omega)]

/-- **Fits.** When the balance fits in the remaining budget, the reservation changes nothing
and cannot fault. -/
theorem reserveChurn_fits :
    ∀ (balance consume perEpoch earliest : UInt64), balance ≤ consume →
      (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
        = .ok (earliest, consume) := by
  intro balance consume perEpoch earliest h
  have hng : ¬ balance > consume := Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp h)
  simp [reserveChurn, hng]
  rfl

/-- **Zero limit.** When the balance does not fit and the limit is zero, the reservation
rejects. The pyspec raises `ZeroDivisionError` at the same point. -/
theorem reserveChurn_zero :
    ∀ (balance consume earliest : UInt64), consume < balance →
      (reserveChurn balance consume 0 earliest : Except StateTransitionError _)
        = .error (.arithmetic churnDescrDiv) := by
  intro balance consume earliest h
  simp [reserveChurn, h, throwArithmetic, EthCLLib.Spec.liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Below every bound.** When the balance does not fit, the limit is positive, and all three
checked results stay below `2 ^ 64`, the reservation succeeds. The epoch grows by
`churnEpochs`, and the consumed total grows by `churnEpochs * perEpoch`, both exactly. -/
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
          consumed.toNat = consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat := by
  intro balance consume perEpoch earliest h hp hE hM hC
  have ha := additional_toNat balance consume perEpoch h
  have hp0 : perEpoch ≠ 0 := fun hz => by simp [hz] at hp
  -- Name the `UInt64` value of the additional epochs once, with its `Nat` reading.
  generalize hadd : (balance - consume - 1) / perEpoch + 1 = a at ha
  have hEpoch : (earliest + a).toNat = earliest.toNat + churnEpochs balance consume perEpoch := by
    rw [UInt64.toNat_add, ha, Nat.mod_eq_of_lt hE]
  have hMul : (a * perEpoch).toNat = churnEpochs balance consume perEpoch * perEpoch.toNat := by
    rw [UInt64.toNat_mul, ha, Nat.mod_eq_of_lt hM]
  have hCons : (consume + a * perEpoch).toNat
      = consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat := by
    rw [UInt64.toNat_add, hMul, Nat.mod_eq_of_lt hC]
  have hc₁ : ¬ earliest + a < earliest := by
    rw [UInt64.lt_iff_toNat_lt, hEpoch]
    omega
  -- The product stays below `2 ^ 64`, so the division recovers the limit, and `checkedMul`'s
  -- guard is false.
  have hrec : a * perEpoch / a = perEpoch := by
    have hapos : 0 < a.toNat := by rw [ha]; exact Nat.succ_pos _
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, UInt64.toNat_mul, ha, Nat.mod_eq_of_lt hM, ← ha]
    exact Nat.mul_div_cancel_left _ hapos
  have hc₃ : ¬ consume + a * perEpoch < consume := by
    rw [UInt64.lt_iff_toNat_lt, hCons]
    omega
  refine ⟨earliest + a, consume + a * perEpoch, ?_, hEpoch, hCons⟩
  simp [reserveChurn, h, hp0, hadd, checkedAdd, checkedMul, hc₁, hrec, hc₃]
  rfl

/-- **At a bound.** When the balance does not fit, the limit is positive, and any of the three
checked results reaches `2 ^ 64`, the reservation rejects with `.arithmetic`. The pyspec raises
`ValueError` at the same point. -/
theorem reserveChurn_overflow :
    ∀ (balance consume perEpoch earliest : UInt64),
      consume < balance → 0 < perEpoch.toNat →
      (2 ^ 64 ≤ earliest.toNat + churnEpochs balance consume perEpoch ∨
        2 ^ 64 ≤ churnEpochs balance consume perEpoch * perEpoch.toNat ∨
        2 ^ 64 ≤ consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat) →
      ∃ d : String,
        (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
          = .error (.arithmetic d) := by
  intro balance consume perEpoch earliest h hp hbound
  have ha := additional_toNat balance consume perEpoch h
  have hp0 : perEpoch ≠ 0 := fun hz => by simp [hz] at hp
  have he := UInt64.toNat_lt earliest
  have hcn := UInt64.toNat_lt consume
  generalize hadd : (balance - consume - 1) / perEpoch + 1 = a at ha
  have hane : a.toNat ≠ 0 := by rw [ha]; exact Nat.succ_ne_zero _
  have ha0 : a ≠ 0 := fun hz => hane (by simp [hz])
  have hat := UInt64.toNat_lt a
  -- The three checks run in order. The first one that fires names the fault.
  by_cases hc₁ : earliest + a < earliest
  · refine ⟨churnDescrEpoch, ?_⟩
    simp [reserveChurn, h, hp0, hadd, checkedAdd, hc₁, throwArithmetic, EthCLLib.Spec.liftErr,
      Except.mapError, MonadExcept.ofExcept]
    rfl
  · have hEpoch : earliest.toNat + a.toNat < 2 ^ 64 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hc₁
      omega
    by_cases hM : 2 ^ 64 ≤ a.toNat * perEpoch.toNat
    · -- `simp` reads `checkedMul`'s `Bool` guard as two `Prop` facts, so pass it those.
      have hg := (mulGuard_iff a perEpoch hane).mpr hM
      have hne : a * perEpoch / a ≠ perEpoch := by
        intro heq
        simp [heq] at hg
      refine ⟨churnDescrMul, ?_⟩
      simp [reserveChurn, h, hp0, hadd, checkedAdd, checkedMul, hc₁, ha0, hne, throwArithmetic,
        EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl
    · have hMlt : a.toNat * perEpoch.toNat < 2 ^ 64 := Nat.lt_of_not_le hM
      have hrec : a * perEpoch / a = perEpoch := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt hMlt]
        exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hane)
      have hc₃ : consume + a * perEpoch < consume := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt hMlt]
        rw [ha] at hEpoch hMlt
        rcases hbound with hb | hb | hb
        · omega
        · omega
        · rw [ha]
          omega
      refine ⟨churnDescrConsume, ?_⟩
      simp [reserveChurn, h, hp0, hadd, checkedAdd, checkedMul, hc₁, hrec, hc₃, throwArithmetic,
        EthCLLib.Spec.liftErr, Except.mapError, MonadExcept.ofExcept]
      rfl

/-- **Coverage.** A successful reservation returns a consumed total at least as large as the
balance. So `balance_to_consume - balance` in every caller never underflows.

The fits case returns `consume ≥ balance`. Otherwise the consumed total is
`consume + ceil((balance - consume) / perEpoch) * perEpoch`, and the ceiling times the limit is
at least `balance - consume`. -/
theorem reserveChurn_covers :
    ∀ (balance consume perEpoch earliest epoch consumed : UInt64),
      (reserveChurn balance consume perEpoch earliest : Except StateTransitionError _)
          = .ok (epoch, consumed) →
        balance ≤ consumed := by
  intro balance consume perEpoch earliest epoch consumed hok
  by_cases hfit : balance ≤ consume
  · rw [reserveChurn_fits _ _ _ _ hfit] at hok
    cases hok
    exact hfit
  · have h : consume < balance := UInt64.lt_iff_toNat_lt.mpr
      (Nat.lt_of_not_le (fun hle => hfit (UInt64.le_iff_toNat_le.mpr hle)))
    by_cases hp : perEpoch.toNat = 0
    · have hz : perEpoch = 0 := UInt64.toNat_inj.mp (by simp [hp])
      rw [hz, reserveChurn_zero _ _ _ h] at hok
      cases hok
    · have hppos : 0 < perEpoch.toNat := Nat.pos_of_ne_zero hp
      have hE := UInt64.toNat_lt earliest
      by_cases hall :
          earliest.toNat + churnEpochs balance consume perEpoch < 2 ^ 64 ∧
          churnEpochs balance consume perEpoch * perEpoch.toNat < 2 ^ 64 ∧
          consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat < 2 ^ 64
      · obtain ⟨e', c', hres, -, hc'⟩ :=
          reserveChurn_ok _ _ _ _ h hppos hall.1 hall.2.1 hall.2.2
        rw [hres] at hok
        cases hok
        -- `x - 1 < p * ((x - 1) / p + 1)` is `Nat.lt_mul_div_succ`, so the ceiling covers `x`.
        have hceil := Nat.lt_mul_div_succ (balance.toNat - consume.toNat - 1) hppos
        have hlt := UInt64.lt_iff_toNat_lt.mp h
        rw [UInt64.le_iff_toNat_le, hc']
        simp only [churnEpochs]
        rw [Nat.mul_comm]
        omega
      · have hbound :
            2 ^ 64 ≤ earliest.toNat + churnEpochs balance consume perEpoch ∨
            2 ^ 64 ≤ churnEpochs balance consume perEpoch * perEpoch.toNat ∨
            2 ^ 64 ≤ consume.toNat + churnEpochs balance consume perEpoch * perEpoch.toNat := by
          omega
        obtain ⟨d, hd⟩ := reserveChurn_overflow _ _ _ _ h hppos hbound
        rw [hd] at hok
        cases hok

/-! ## The two Fulu callers

Each caller reads the state, computes the activation-exit epoch, reads the churn limit,
reserves churn, and writes the two churn fields. The theorems per caller split on those three
steps, in that order. When all three succeed, the run succeeds, because `reserveChurn_covers`
rules out the subtraction fault. When one of them faults, the run rejects with that same
fault. The churn limit faults only where `get_total_active_balance` does. -/

section Callers

open EthCLLib.Spec (umax liftErr)
open EthCLLib.Proofs (pureState)

/-- **Exit churn, success.** When the activation-exit epoch, the churn limit and the
reservation all succeed, the run succeeds. It returns the reserved epoch, and it writes the
consumed total minus the exit balance and the reserved epoch. The subtraction cannot fault. -/
@[characterizes computeExitEpochAndUpdateChurn]
theorem computeExitEpochAndUpdateChurn_run_ok [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (exitBalance activation churn epoch consumed : UInt64),
      (computeActivationExitEpoch (computeEpochAtSlot state.slot)
          : Except StateTransitionError UInt64) = .ok activation →
      getActivationExitChurnLimit (pureState state) = .ok churn →
      (reserveChurn exitBalance
          (if state.earliestExitEpoch < umax (state.earliestExitEpoch) activation
            then churn else state.exitBalanceToConsume)
          churn
          (umax (state.earliestExitEpoch) activation)
          : Except StateTransitionError _) = .ok (epoch, consumed) →
      (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) exitBalance).run (pureState state) =
        .ok (epoch, pureState
          { state with
              exitBalanceToConsume := consumed - exitBalance
              earliestExitEpoch := epoch }) := by
  intro state exitBalance activation churn epoch consumed hact hchurn hres
  have hcov := reserveChurn_covers _ _ _ _ _ _ hres
  have hnot : ¬ exitBalance > consumed := Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hcov)
  simp [computeExitEpochAndUpdateChurn, hact, hchurn, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept, checkedSub, hnot]
  rfl

/-- **Exit churn, churn-limit fault.** When the activation-exit epoch succeeds and the churn
limit faults, the run rejects with that fault. -/
theorem computeExitEpochAndUpdateChurn_run_churn_error [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (exitBalance activation : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (computeEpochAtSlot state.slot)
          : Except StateTransitionError UInt64) = .ok activation →
      getActivationExitChurnLimit (pureState state) = .error err →
      (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) exitBalance).run (pureState state)
        = .error err := by
  intro state exitBalance activation err hact hchurn
  simp [computeExitEpochAndUpdateChurn, hact, hchurn, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Exit churn, activation fault.** When the activation-exit epoch faults, the run rejects
with that fault. -/
theorem computeExitEpochAndUpdateChurn_run_activation_error [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (exitBalance : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (computeEpochAtSlot state.slot)
          : Except StateTransitionError UInt64) = .error err →
      (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) exitBalance).run (pureState state)
        = .error err := by
  intro state exitBalance err hact
  simp [computeExitEpochAndUpdateChurn, hact, liftErr, Except.mapError, MonadExcept.ofExcept]
  rfl

/-- **Exit churn, reservation fault.** When the activation-exit epoch and the churn limit
succeed and the reservation faults, the run rejects with the reservation's fault. -/
theorem computeExitEpochAndUpdateChurn_run_reserve_error [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (exitBalance activation churn : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (computeEpochAtSlot state.slot)
          : Except StateTransitionError UInt64) = .ok activation →
      getActivationExitChurnLimit (pureState state) = .ok churn →
      (reserveChurn exitBalance
          (if state.earliestExitEpoch < umax (state.earliestExitEpoch) activation
            then churn else state.exitBalanceToConsume)
          churn
          (umax (state.earliestExitEpoch) activation)
          : Except StateTransitionError _) = .error err →
      (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) exitBalance).run (pureState state)
        = .error err := by
  intro state exitBalance activation churn err hact hchurn hres
  simp [computeExitEpochAndUpdateChurn, hact, hchurn, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Consolidation churn, success.** The consolidation analogue of
`computeExitEpochAndUpdateChurn_run_ok`, over the consolidation fields and the consolidation
churn limit. -/
@[characterizes computeConsolidationEpochAndUpdateChurn]
theorem computeConsolidationEpochAndUpdateChurn_run_ok [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (balance activation churn epoch consumed : UInt64),
      (computeActivationExitEpoch (currentEpochOf (pureState state))
          : Except StateTransitionError UInt64) = .ok activation →
      getConsolidationChurnLimit (pureState state) = .ok churn →
      (reserveChurn balance
          (if state.earliestConsolidationEpoch
                < umax (state.earliestConsolidationEpoch) activation
            then churn else state.consolidationBalanceToConsume)
          churn
          (umax (state.earliestConsolidationEpoch) activation)
          : Except StateTransitionError _) = .ok (epoch, consumed) →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun) balance).run (pureState state) =
        .ok (epoch, pureState
          { state with
              consolidationBalanceToConsume := consumed - balance
              earliestConsolidationEpoch := epoch }) := by
  intro state balance activation churn epoch consumed hact hchurn hres
  have hcov := reserveChurn_covers _ _ _ _ _ _ hres
  have hnot : ¬ balance > consumed := Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hcov)
  simp [computeConsolidationEpochAndUpdateChurn, hact, hchurn, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept, checkedSub, hnot]
  rfl

/-- **Consolidation churn, churn-limit fault.** When the activation-exit epoch succeeds and
the consolidation churn limit faults, the run rejects with that fault. -/
theorem computeConsolidationEpochAndUpdateChurn_run_churn_error [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (balance activation : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (currentEpochOf (pureState state))
          : Except StateTransitionError UInt64) = .ok activation →
      getConsolidationChurnLimit (pureState state) = .error err →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun) balance).run (pureState state)
        = .error err := by
  intro state balance activation err hact hchurn
  simp [computeConsolidationEpochAndUpdateChurn, hact, hchurn, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Consolidation churn, activation fault.** When the activation-exit epoch faults, the run
rejects with that fault. -/
theorem computeConsolidationEpochAndUpdateChurn_run_activation_error
    [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (balance : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (currentEpochOf (pureState state))
          : Except StateTransitionError UInt64) = .error err →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun) balance).run (pureState state)
        = .error err := by
  intro state balance err hact
  simp [computeConsolidationEpochAndUpdateChurn, hact, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Consolidation churn, reservation fault.** When the activation-exit epoch and the churn
limit succeed and the reservation faults, the run rejects with the reservation's fault. -/
theorem computeConsolidationEpochAndUpdateChurn_run_reserve_error
    [Preset] [HasherTag] [Config] :
    ∀ (state : BeaconState) (balance activation churn : UInt64) (err : StateTransitionError),
      (computeActivationExitEpoch (currentEpochOf (pureState state))
          : Except StateTransitionError UInt64) = .ok activation →
      getConsolidationChurnLimit (pureState state) = .ok churn →
      (reserveChurn balance
          (if state.earliestConsolidationEpoch
                < umax (state.earliestConsolidationEpoch) activation
            then churn else state.consolidationBalanceToConsume)
          churn
          (umax (state.earliestConsolidationEpoch) activation)
          : Except StateTransitionError _) = .error err →
      (computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun) balance).run (pureState state)
        = .error err := by
  intro state balance activation churn err hact hchurn hres
  simp [computeConsolidationEpochAndUpdateChurn, hact, hchurn, hres, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

end Callers

end EthCLSpecs.Proofs.Fulu
