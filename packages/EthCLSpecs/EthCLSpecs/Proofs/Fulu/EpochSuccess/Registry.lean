import EthCLSpecs.Proofs.Fulu.EpochSuccess.FieldSteps

/-!
# `EthCLSpecs.Proofs.Fulu.EpochSuccess.Registry`: the registry updates eject within the budget

An ejection reserves exit churn for a validator whose effective balance is at most
`EJECTION_BALANCE`. The per-epoch exit churn is at least `exitChurnFloor` under `ConfigValid`, so
`reserve_churn` moves the earliest exit epoch by at most `ejectionStep`, and the exit epoch plus
`MIN_VALIDATOR_WITHDRAWABILITY_DELAY` fits in a `uint64` while `EpochSafe.exitRoom` lasts.

Exits and activations scheduled at epoch `E` land at or past `E + 1 + MAX_SEED_LOOKAHEAD`, after
both sampled epochs, so they leave every validator's activity there unchanged. The loop body has
two join points; `hJ2` and `hJ1` prove each once.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub umin umax)
open EthCLSpecs.Fulu

/-- `umin` in `Nat`. -/
theorem umin_toNat (a b : UInt64) : (umin a b).toNat = min a.toNat b.toNat := by
  unfold umin
  split
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega

/-- `umax` in `Nat`. -/
theorem umax_toNat (a b : UInt64) : (umax a b).toNat = max a.toNat b.toNat := by
  unfold umax
  split
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega

/-- Rounding a `UInt64` down to a multiple of `d`, in `Nat`. -/
theorem uint64_sub_mod_toNat (c d : UInt64) : (c - c % d).toNat = c.toNat - c.toNat % d.toNat := by
  have hle : c % d ≤ c := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; exact Nat.mod_le _ _
  rw [UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_mod]

/-- Rounding down to a multiple of `d` is monotone. -/
theorem sub_mod_mono {a b d : Nat} (h : a ≤ b) : a - a % d ≤ b - b % d := by
  have ha := Nat.div_add_mod a d
  have hb := Nat.div_add_mod b d
  have hdiv : a / d ≤ b / d := Nat.div_le_div_right h
  have : d * (a / d) ≤ d * (b / d) := Nat.mul_le_mul_left _ hdiv
  omega

/-- `reserve_churn` moves the earliest epoch by `⌈balance / per_epoch⌉` at most, without a `uint64`
wrap when that fits. -/
theorem reserveChurn_fst_bound [Preset] (bal consume perEpoch earl : Gwei)
    (hroom : earl.toNat + ((bal.toNat - 1) / perEpoch.toNat + 1) < 2 ^ 64) :
    earl.toNat ≤ (reserveChurn bal consume perEpoch earl).1.toNat ∧
      (reserveChurn bal consume perEpoch earl).1.toNat ≤
        earl.toNat + ((bal.toNat - 1) / perEpoch.toNat + 1) := by
  unfold reserveChurn
  split
  · rename_i hgt
    rw [GT.gt, UInt64.lt_iff_toNat_lt] at hgt
    have hsub : (bal - consume).toNat = bal.toNat - consume.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    have hsub1 : (bal - consume - 1).toNat = bal.toNat - consume.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsub]; simp; omega)), hsub]
      rfl
    have hdiv : ((bal - consume - 1) / perEpoch).toNat = (bal.toNat - consume.toNat - 1) / perEpoch.toNat := by
      rw [UInt64.toNat_div, hsub1]
    have hdle : (bal.toNat - consume.toNat - 1) / perEpoch.toNat ≤ (bal.toNat - 1) / perEpoch.toNat :=
      Nat.div_le_div_right (by omega)
    have hlt1 : (bal.toNat - consume.toNat - 1) / perEpoch.toNat + 1 < 2 ^ 64 := by omega
    have hadd : ((bal - consume - 1) / perEpoch + 1).toNat =
        (bal.toNat - consume.toNat - 1) / perEpoch.toNat + 1 := by
      rw [UInt64.toNat_add, hdiv, UInt64.toNat_one, Nat.mod_eq_of_lt hlt1]
    dsimp only
    rw [UInt64.toNat_add, hadd, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

section

variable [Preset] [Config] [HasherTag]

omit [Config] [HasherTag] in
/-- The two sampled epochs lie before `E + 1 + MAX_SEED_LOOKAHEAD`, the earliest epoch an exit or
activation scheduled at `E` can take. -/
theorem liveEpoch_lt [PresetValid] {E e : Epoch}
    (hslot : E.toNat + 1 + Const.maxSeedLookahead.toNat < 2 ^ 64)
    (he : e = E + 1 ∨ e = E + Const.minSeedLookahead + 1) :
    e.toNat < E.toNat + 1 + Const.maxSeedLookahead.toNat := by
  have hlt := PresetValid.minSeedLookaheadLtMaxSeedLookahead (self := ‹_›)
  rw [UInt64.lt_iff_toNat_lt] at hlt
  rcases he with rfl | rfl
  · rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

omit [HasherTag] in
/-- A `Stage` state after an exit write at `i`: the validator's exit epoch becomes `ee`, the churn
bookkeeping moves to `ee`, and `ee` lies between `E + 1 + MAX_SEED_LOOKAHEAD` and one ejection step
past the old start. -/
theorem Stage.setExit [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w)
    (hslot : (computeEpochAtSlot v.slot).toNat + 1 + Const.maxSeedLookahead.toNat < 2 ^ 64)
    (i : Nat) (ee we ebtc : UInt64)
    (hee1 : (computeEpochAtSlot w.slot).toNat + 1 + Const.maxSeedLookahead.toNat ≤ ee.toNat)
    (hee2 : ee.toNat ≤ exitStart w + ejectionStep) :
    Stage b v { caps with exit := caps.exit + ejectionStep }
      { w with
          validators := w.validators.set! i { w.validators[i]! with exitEpoch := ee, withdrawableEpoch := we },
          exitBalanceToConsume := ebtc, earliestExitEpoch := ee } := by
  have hslotw := hw.slot
  -- First the bookkeeping write, which moves `exitStart` to `ee`.
  have hbook : Stage b v { caps with exit := caps.exit + ejectionStep }
      { w with exitBalanceToConsume := ebtc, earliestExitEpoch := ee } := by
    refine ⟨hw.slot, hw.registrySizes, hw.vGrows, hw.potential, hw.consolidationIdx,
      hw.consolidationCount, hw.effCap, hw.depositCap, ?_, hw.historyBound, hw.balanceBound, hw.live⟩
    have := hw.exitBound
    unfold exitStart at this hee2 ⊢
    dsimp only
    simp only [hslotw] at this hee1 hee2 ⊢
    omega
  -- Then the validator write, which keeps the effective balance and moves the exit epoch past
  -- the sampled epochs.
  refine hbook.setValidator i _ ?_ ?_
  · show UInt64.toNat (w.validators[i]!).effectiveBalance ≤ _
    by_cases hi : i < w.validators.val.size
    · exact hw.effCap _ (sszList_getElem!_mem _ hi)
    · rw [getElem!_neg (dom := fun (xs : SizzLean.Repr.SSZList Validator Const.validatorRegistryLimit) i =>
        i < xs.size) w.validators i hi]
      exact Nat.zero_le _
  · intro hj e he ha
    have hlt := liveEpoch_lt hslot he
    rw [hslotw] at hee1
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
    refine ⟨?_, ?_⟩
    · rw [sszList_getElem!_eq _ hj]; exact ha.1
    · rw [UInt64.lt_iff_toNat_lt]; omega

/-- The per-epoch exit churn is at least `exitChurnFloor`, at a valid preset and config. -/
theorem exitChurnFloor_le [PresetValid] [ConfigValid] (s : BeaconState) :
    exitChurnFloor ≤ (getActivationExitChurnLimit (pureState s)).toNat ∧ 1 ≤ exitChurnFloor := by
  have hebi := PresetValid.effectiveBalanceIncrementPos (self := ‹_›)
  have htwin := PresetValid.effectiveBalanceIncrementTwin (self := ‹_›)
  have hfloor := ConfigValid.exitChurnFloorPos (self := ‹_›)
  rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le, htwin] at hfloor
  unfold getActivationExitChurnLimit getBalanceChurnLimit exitChurnFloor
  dsimp only
  rw [umin_toNat, uint64_sub_mod_toNat, umax_toNat, htwin]
  have hebi_self : Const.effectiveBalanceIncrement - Const.effectiveBalanceIncrement %
      Const.effectiveBalanceIncrement = Const.effectiveBalanceIncrement := by
    rw [Nat.mod_self]; rfl
  have h1 := sub_mod_mono (d := Const.effectiveBalanceIncrement) hfloor.1
  rw [hebi_self] at h1
  have h2 := sub_mod_mono (d := Const.effectiveBalanceIncrement)
    (Nat.le_max_left (UInt64.toNat Const.minPerEpochChurnLimitElectra)
      (UInt64.toNat (getTotalActiveBalance (pureState s) / Const.churnLimitQuotient)))
  constructor <;> omega

theorem computeExitEpochAndUpdateChurn_succeeds [PresetValid] [ConfigValid] (s : BeaconState)
    (bal : Gwei) (hbal : bal.toNat ≤ Const.ejectionBalanceG.toNat)
    (hroom : exitStart s + ejectionStep < 2 ^ 64) :
    RunSucceeds s (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) bal)
      (fun ee s' => ∃ ebtc, s' = { s with exitBalanceToConsume := ebtc, earliestExitEpoch := ee } ∧
        (computeEpochAtSlot s.slot).toNat + 1 + Const.maxSeedLookahead.toNat ≤ ee.toNat ∧
        ee.toNat ≤ exitStart s + ejectionStep) := by
  have hrun : (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) bal).run (pureState s) =
      .ok ((reserveChurn bal
          (if s.earliestExitEpoch < umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot))
            then getActivationExitChurnLimit (pureState s) else s.exitBalanceToConsume)
          (getActivationExitChurnLimit (pureState s))
          (umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot)))).1,
        pureState { s with
          exitBalanceToConsume := (reserveChurn bal
            (if s.earliestExitEpoch < umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot))
              then getActivationExitChurnLimit (pureState s) else s.exitBalanceToConsume)
            (getActivationExitChurnLimit (pureState s))
            (umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot)))).2 - bal,
          earliestExitEpoch := (reserveChurn bal
            (if s.earliestExitEpoch < umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot))
              then getActivationExitChurnLimit (pureState s) else s.exitBalanceToConsume)
            (getActivationExitChurnLimit (pureState s))
            (umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot)))).1 }) := rfl
  refine ⟨_, _, hrun, _, rfl, ?_⟩
  have hstart : (computeEpochAtSlot s.slot).toNat + 1 + Const.maxSeedLookahead.toNat ≤ exitStart s :=
    Nat.le_max_right _ _
  have hcae : (computeActivationExitEpoch (computeEpochAtSlot s.slot)).toNat =
      (computeEpochAtSlot s.slot).toNat + 1 + Const.maxSeedLookahead.toNat := by
    unfold computeActivationExitEpoch
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hearl : (umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot))).toNat =
      exitStart s := by
    rw [umax_toNat, hcae]; rfl
  obtain ⟨hfloorP, hfloor1⟩ := exitChurnFloor_le s
  -- One ejection's reservation moves the epoch by at most `ejectionStep`.
  have hstep : (bal.toNat - 1) / (getActivationExitChurnLimit (pureState s)).toNat + 1 ≤ ejectionStep := by
    unfold ejectionStep
    have h1 : (bal.toNat - 1) / (getActivationExitChurnLimit (pureState s)).toNat ≤
        (bal.toNat - 1) / exitChurnFloor := Nat.div_le_div_left hfloorP hfloor1
    have h2 : (bal.toNat - 1) / exitChurnFloor ≤ (Const.ejectionBalanceG.toNat - 1) / exitChurnFloor :=
      Nat.div_le_div_right (by omega)
    omega
  have hbound := reserveChurn_fst_bound bal
    (if s.earliestExitEpoch < umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot))
      then getActivationExitChurnLimit (pureState s) else s.exitBalanceToConsume)
    (getActivationExitChurnLimit (pureState s))
    (umax s.earliestExitEpoch (computeActivationExitEpoch (computeEpochAtSlot s.slot)))
    (by rw [hearl]; omega)
  rw [hearl] at hbound
  constructor <;> omega

/-- An exit write keeps the registry length and every activation epoch. -/
def ExitFrame [Preset] (s s' : BeaconState) : Prop :=
  s'.validators.val.size = s.validators.val.size ∧
    ∀ j (hj : j < s.validators.val.size) (hj' : j < s'.validators.val.size),
      (s'.validators.val[j]).activationEpoch = (s.validators.val[j]).activationEpoch

theorem initiateValidatorExit_succeeds [PresetValid] [ConfigValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {s : BeaconState} (hs : Stage b v caps s)
    (hslot : (computeEpochAtSlot v.slot).toNat + 1 + Const.maxSeedLookahead.toNat < 2 ^ 64)
    (i : ValidatorIndex) (hi : i.toNat < s.validators.val.size)
    (heff : (s.validators[i.toNat]!).effectiveBalance.toNat ≤ Const.ejectionBalanceG.toNat)
    (hroom : exitStart s + ejectionStep + Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64) :
    RunSucceeds s (initiateValidatorExit (StateTransition := FuluRun) i)
      (fun _ s' => Stage b v { caps with exit := caps.exit + ejectionStep } s' ∧ ExitFrame s s') := by
  unfold initiateValidatorExit
  run_succeeds
  · exact ⟨_, sszList_get?_eq _ _ hi⟩
  · exact ⟨hs.mono (Nat.le_refl _) (Nat.le_add_right _ _) (Nat.le_refl _), rfl, fun _ _ _ => rfl⟩
  · rename_i y hy _
    have hyEq : y = s.validators[i.toNat]! := Option.some.inj (hy.symm.trans (sszList_get?_eq _ _ hi))
    subst hyEq
    refine (computeExitEpochAndUpdateChurn_succeeds s _ heff (by omega)).weaken (fun ee s1 h => ?_)
    obtain ⟨ebtc, hs1, h1, h2⟩ := h
    subst hs1
    have hsize : UInt64.size = 2 ^ 64 := rfl
    run_succeeds
    · exact uint64_not_add_lt_of_toNat (by omega)
    · refine ⟨hs.setExit hslot i.toNat ee _ ebtc h1 h2, ?_, ?_⟩
      · simp [box_reduce]
      · intro j hj hj'
        simp only [box_reduce, Array.set!_eq_setIfInBounds]
        rw [Array.getElem_setIfInBounds hj]
        split
        · rename_i hij
          subst hij
          show (s.validators[i.toNat]!).activationEpoch = _
          rw [sszList_getElem!_eq _ hj]
        · rfl

theorem processRegistryUpdates_succeeds [PresetValid] [ConfigValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hslot : (computeEpochAtSlot v.slot).toNat + 1 + Const.maxSeedLookahead.toNat < 2 ^ 64)
    (hroom : exitStart v + caps.exit + w.validators.val.size * ejectionStep +
      Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64) :
    RunSucceeds w (processRegistryUpdates (StateTransition := FuluRun))
      (fun _ w' => Stage b v { caps with exit := caps.exit + w.validators.val.size * ejectionStep } w') := by
  unfold processRegistryUpdates
  run_succeeds
  refine (runSucceeds_forIn_range _
    (fun i _ s => Stage b v { caps with exit := caps.exit + i * ejectionStep } s ∧
      s.validators.val.size = w.validators.val.size)
    (fun _ s => Stage b v { caps with exit := caps.exit + w.validators.val.size * ejectionStep } s)
    (fun idx _ s hidx hI => ?_) (fun _ s hI => hI.1) _ ⟨by simpa using hw, rfl⟩).weaken ?_
  · obtain ⟨hst, hsz⟩ := hI
    refine runSucceeds_get_bind ?_
    dsimp only
    have hidxs : idx < s.validators.val.size := by rw [hsz]; exact hidx
    have hidxn := toNat_ofNat_registry hidxs
    have hx0 : (pureState s).view.validators[idx]! = s.validators.val[idx] := sszList_getElem!_eq _ hidxs
    have hcapnext : caps.exit + idx * ejectionStep + ejectionStep = caps.exit + (idx + 1) * ejectionStep := by
      rw [Nat.succ_mul]; omega
    have hslotv : s.slot = v.slot := hst.slot
    -- The activation write: it runs only on a validator not yet activated, which is active at no
    -- sampled epoch, so it keeps liveness.
    have hJ2 : ∀ (Post : ForInStep PUnit → BeaconState → Prop) (s2 : BeaconState),
        Stage b v { caps with exit := caps.exit + (idx + 1) * ejectionStep } s2 →
        s2.validators.val.size = w.validators.val.size →
        (∀ j (h : j < s2.validators.val.size), j = idx →
          (s2.validators.val[j]).activationEpoch = (s.validators.val[idx]).activationEpoch) →
        (∀ s3, Stage b v { caps with exit := caps.exit + (idx + 1) * ejectionStep } s3 →
          s3.validators.val.size = w.validators.val.size → Post (.yield ⟨⟩) s3) →
        RunSucceeds s2
          ((if isEligibleForActivation (pureState s) (pureState s).view.validators[idx]! = true then do
              modifyState fun state =>
                  modValidator state (UInt64.ofNat idx) fun validator =>
                    { pubkey := validator.pubkey, withdrawalCredentials := validator.withdrawalCredentials,
                      effectiveBalance := validator.effectiveBalance, slashed := validator.slashed,
                      activationEligibilityEpoch := validator.activationEligibilityEpoch,
                      activationEpoch := computeActivationExitEpoch (currentEpochOf (pureState w)),
                      exitEpoch := validator.exitEpoch, withdrawableEpoch := validator.withdrawableEpoch }
              pure (ForInStep.yield PUnit.unit)
            else pure (ForInStep.yield PUnit.unit)) : FuluRun (ForInStep PUnit)) Post := by
      intro Post s2 hs2 hsz2 hact2 hpost
      run_succeeds
      · rename_i helig
        apply hpost
        · refine hs2.setValidator _ _ ?_ ?_
          · show UInt64.toNat (s2.validators[(UInt64.ofNat idx).toNat]!).effectiveBalance ≤ _
            rw [hidxn]
            exact hs2.effCap _ (sszList_getElem!_mem _ (by show idx < s2.validators.val.size; rw [hsz2]; exact hidx))
          · intro hj e he ha
            exfalso
            have hlt := liveEpoch_lt hslot he
            simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at helig
            rw [hx0] at helig
            have hfar := (hact2 _ hj hidxn).trans helig.2
            simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at ha
            have h1 := ha.1
            rw [hfar, UInt64.le_iff_toNat_le] at h1
            have : Const.farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
            omega
        · simp [box_reduce, hsz2]
      · exact hpost s2 hs2 hsz2
    -- The ejection: an exit write, which moves the exit start by one step and keeps every
    -- activation epoch.
    have hJ1 : ∀ (Post : ForInStep PUnit → BeaconState → Prop) (s1 : BeaconState),
        Stage b v { caps with exit := caps.exit + idx * ejectionStep } s1 →
        s1.validators.val.size = w.validators.val.size →
        (∀ j (h : j < s1.validators.val.size), j = idx →
          (s1.validators.val[j]).activationEpoch = (s.validators.val[idx]).activationEpoch) →
        (∀ j (h : j < s1.validators.val.size), j = idx →
          (s1.validators.val[j]).effectiveBalance = (s.validators.val[idx]).effectiveBalance) →
        (∀ s3, Stage b v { caps with exit := caps.exit + (idx + 1) * ejectionStep } s3 →
          s3.validators.val.size = w.validators.val.size → Post (.yield ⟨⟩) s3) →
        RunSucceeds s1
          ((if (isActiveValidator (pureState s).view.validators[idx]! (currentEpochOf (pureState w)) &&
                decide ((pureState s).view.validators[idx]!.effectiveBalance ≤ Const.ejectionBalanceG)) =
              true then
            do
            initiateValidatorExit (UInt64.ofNat idx)
            ((if isEligibleForActivation (pureState s) (pureState s).view.validators[idx]! = true then do
              modifyState fun state =>
                  modValidator state (UInt64.ofNat idx) fun validator =>
                    { pubkey := validator.pubkey, withdrawalCredentials := validator.withdrawalCredentials,
                      effectiveBalance := validator.effectiveBalance, slashed := validator.slashed,
                      activationEligibilityEpoch := validator.activationEligibilityEpoch,
                      activationEpoch := computeActivationExitEpoch (currentEpochOf (pureState w)),
                      exitEpoch := validator.exitEpoch, withdrawableEpoch := validator.withdrawableEpoch }
              pure (ForInStep.yield PUnit.unit)
            else pure (ForInStep.yield PUnit.unit)) : FuluRun (ForInStep PUnit))
          else ((if isEligibleForActivation (pureState s) (pureState s).view.validators[idx]! = true then do
              modifyState fun state =>
                  modValidator state (UInt64.ofNat idx) fun validator =>
                    { pubkey := validator.pubkey, withdrawalCredentials := validator.withdrawalCredentials,
                      effectiveBalance := validator.effectiveBalance, slashed := validator.slashed,
                      activationEligibilityEpoch := validator.activationEligibilityEpoch,
                      activationEpoch := computeActivationExitEpoch (currentEpochOf (pureState w)),
                      exitEpoch := validator.exitEpoch, withdrawableEpoch := validator.withdrawableEpoch }
              pure (ForInStep.yield PUnit.unit)
            else pure (ForInStep.yield PUnit.unit)) : FuluRun (ForInStep PUnit))) : FuluRun (ForInStep PUnit)) Post := by
      intro Post s1 hs1 hsz1 hact1 heff1 hpost
      have hidx1 : (UInt64.ofNat idx).toNat < s1.validators.val.size := by rw [hidxn, hsz1]; exact hidx
      have hmono : Stage b v { caps with exit := caps.exit + (idx + 1) * ejectionStep } s1 :=
        hs1.mono (Nat.le_refl _) (by dsimp only; omega) (Nat.le_refl _)
      split
      · rename_i hej
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hej
        have heff : (s1.validators[(UInt64.ofNat idx).toNat]!).effectiveBalance.toNat ≤
            Const.ejectionBalanceG.toNat := by
          rw [sszList_getElem!_eq _ hidx1, heff1 _ hidx1 hidxn, ← hx0]
          exact UInt64.le_iff_toNat_le.mp hej.2
        have hmul : idx * ejectionStep + ejectionStep ≤ w.validators.val.size * ejectionStep := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hidx
        have hstart := hs1.exitBound
        dsimp only at hstart
        refine runSucceeds_bind (RunSucceeds.weaken
          (initiateValidatorExit_succeeds hs1 hslot _ hidx1 heff (by omega)) (fun _ s2 h => ?_))
        obtain ⟨hs2, hsz2, hact2⟩ := h
        exact hJ2 Post s2 (hs2.mono (Nat.le_refl _) (by dsimp only; omega) (Nat.le_refl _))
          (hsz2.trans hsz1)
          (fun j hj hji => by
            rw [hact2 j (by rw [← hsz2]; exact hj) hj]
            exact hact1 j (by rw [← hsz2]; exact hj) hji)
          hpost
      · exact hJ2 Post s1 hmono hsz1 hact1 hpost
    have hpost : ∀ s3, Stage b v { caps with exit := caps.exit + (idx + 1) * ejectionStep } s3 →
        s3.validators.val.size = w.validators.val.size →
        loopStepPost (fun (_ : PUnit) s' =>
          Stage b v { caps with exit := caps.exit + (idx + 1) * ejectionStep } s' ∧
            s'.validators.val.size = w.validators.val.size)
          (fun (_ : PUnit) s' =>
            Stage b v { caps with exit := caps.exit + w.validators.val.size * ejectionStep } s')
          (ForInStep.yield PUnit.unit) s3 :=
      fun s3 h1 h2 => by simp only [loopStepPost_yield]; exact ⟨h1, h2⟩
    split
    · -- The eligibility write keeps the activation and exit epochs and the effective balance.
      refine runSucceeds_bind (runSucceeds_modifyThe_view rfl ?_)
      refine hJ1 _ _ (hst.setValidator _ _ ?_ ?_) (by simp [box_reduce, hsz]) ?_ ?_ hpost
      · show UInt64.toNat (s.validators[(UInt64.ofNat idx).toNat]!).effectiveBalance ≤ _
        rw [hidxn]; exact hst.effCap _ (sszList_getElem!_mem _ hidxs)
      · intro hj e _ ha
        simp only [isActiveValidator] at ha ⊢
        have hX : (pureState s).view.validators[(UInt64.ofNat idx).toNat]! =
            s.validators.val[(UInt64.ofNat idx).toNat] := sszList_getElem!_eq _ hj
        rw [hX]
        exact ha
      · intro j hj hji
        simp only [box_reduce, Array.set!_eq_setIfInBounds]
        rw [Array.getElem_setIfInBounds (by simpa [box_reduce] using hj), ite_eq_left (hidxn.trans hji.symm)]
        show (s.validators[(UInt64.ofNat idx).toNat]!).activationEpoch = _
        rw [hidxn, sszList_getElem!_eq _ hidxs]
      · intro j hj hji
        simp only [box_reduce, Array.set!_eq_setIfInBounds]
        rw [Array.getElem_setIfInBounds (by simpa [box_reduce] using hj), ite_eq_left (hidxn.trans hji.symm)]
        show (s.validators[(UInt64.ofNat idx).toNat]!).effectiveBalance = _
        rw [hidxn, sszList_getElem!_eq _ hidxs]
    · exact hJ1 _ s hst hsz (fun j _ hji => by subst hji; rfl) (fun j _ hji => by subst hji; rfl) hpost
  · intro _ s hs
    run_succeeds
    exact hs

end

end EthCLSpecs.Proofs.Fulu
