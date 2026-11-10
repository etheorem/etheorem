import EthCLSpecs.Proofs.Fulu.EpochSuccess.Balances

/-!
# `EthCLSpecs.Proofs.Fulu.EpochSuccess.FieldSteps`: three substeps that write one field group

The effective-balance update rewrites effective balances, capped by `get_max_effective_balance`,
so `effCap` holds after it, and the activation and exit epochs stay put, so liveness does. The
historical-summaries update appends once when the list has room. The participation rotation
rebuilds both lists at the registry's length. `Live.set!` and `Stage.setValidator` carry the stage
across a validator write that keeps every sampled epoch's activity.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Fulu

/-- Liveness carries to a registry that keeps every old validator active where it was active. -/
theorem Live.mono [Preset] {w w' : BeaconState} {e : Epoch} (h : Live w e)
    (hsize : w.validators.val.size ≤ w'.validators.val.size)
    (hact : ∀ i (hi : i < w.validators.val.size) (hi' : i < w'.validators.val.size),
      isActiveValidator w.validators.val[i] e = true → isActiveValidator w'.validators.val[i] e = true) :
    Live w' e := by
  obtain ⟨i, hi, ha⟩ := h
  exact ⟨i, by omega, hact i hi (by omega) ha⟩

/-- A `set!` into the registry keeps liveness when the written validator is active wherever the
old one was. -/
theorem Live.set! [Preset] {w : BeaconState} {e : Epoch} (h : Live w e) (j : Nat) (y : Validator)
    (hy : ∀ (hj : j < w.validators.val.size), isActiveValidator w.validators.val[j] e = true →
      isActiveValidator y e = true) :
    Live { w with validators := w.validators.set! j y } e := by
  refine h.mono (by simp) (fun i hi hi' ha => ?_)
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hi]
  split
  · rename_i hji
    subst hji
    exact hy hi ha
  · exact ha

section

variable [Preset] [Config]

/-- A `Stage` state with one validator overwritten by one whose effective balance is capped and
which is active at the two sampled epochs wherever the old one was. -/
theorem Stage.setValidator {b : EpochBudget} {v : BeaconState} {caps : StageCaps} {w : BeaconState}
    (hw : Stage b v caps w) (j : Nat) (y : Validator)
    (heff : y.effectiveBalance.toNat ≤ Const.maxEffectiveBalanceElectra)
    (hact : ∀ (hj : j < w.validators.val.size) (e : Epoch),
      (e = computeEpochAtSlot v.slot + 1 ∨ e = computeEpochAtSlot v.slot + Const.minSeedLookahead + 1) →
      isActiveValidator w.validators.val[j] e = true → isActiveValidator y e = true) :
    Stage b v caps { w with validators := w.validators.set! j y } := by
  have hsz : (w.validators.set! j y).val.size = w.validators.val.size := by
    simp
  obtain ⟨hb1, hi, hp, hq⟩ := hw.registrySizes
  refine ⟨hw.slot, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hw.consolidationCount, ?_, hw.depositCap,
    hw.exitBound, hw.historyBound, hw.balanceBound,
    ⟨hw.live.1.set! j y (fun hj => hact hj _ (Or.inl rfl)),
     hw.live.2.set! j y (fun hj => hact hj _ (Or.inr rfl))⟩⟩
  all_goals simp only [SizzLean.Repr.SSZList.size] at hb1 hi hp hq ⊢
  · rw [hsz]; exact hb1
  · rw [hsz]; exact hi
  · rw [hsz]; exact hp
  · rw [hsz]; exact hq
  · rw [hsz]; exact hw.vGrows
  · unfold registryPotential; rw [hsz]; exact hw.potential
  · intro pc hpc; rw [hsz]; exact hw.consolidationIdx pc hpc
  · intro x hx
    simp only [Array.set!_eq_setIfInBounds] at hx
    rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
    · exact hw.effCap x hx
    · exact heff

omit [Config] in
/-- `get_max_effective_balance` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`, at a valid preset. -/
theorem getMaxEffectiveBalance_le [PresetValid] (x : Validator) :
    (getMaxEffectiveBalance x).toNat ≤ Const.maxEffectiveBalanceElectra := by
  have htwin := PresetValid.maxEffectiveBalanceElectraTwin (self := ‹_›)
  have hmin := PresetValid.minActivationBalanceLe (self := ‹_›)
  unfold getMaxEffectiveBalance
  split
  · exact Nat.le_of_eq htwin
  · exact hmin

omit [Preset] [Config] in
/-- `umin a b` is at most `b`. -/
theorem umin_toNat_le_right (a b : UInt64) : (EthCLLib.Spec.umin a b).toNat ≤ b.toNat := by
  unfold EthCLLib.Spec.umin
  split
  · rename_i h
    exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h)
  · exact Nat.le_refl _

omit [Preset] [Config] in
/-- An in-range total read of an SSZ list is the checked read. -/
theorem sszList_getElem!_eq {α : Type} [Inhabited α] {cap : Nat} (xs : SizzLean.Repr.SSZList α cap)
    {i : Nat} (h : i < xs.val.size) : xs[i]! = xs.val[i] := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := h)]
  rfl

/-- A `Stage` state with one more historical summary, under a history cap one higher. -/
theorem Stage.setHistory {b : EpochBudget} {v : BeaconState} {caps : StageCaps} {w : BeaconState}
    (hw : Stage b v caps w) (l : SizzLean.Repr.SSZList HistoricalSummary Const.historicalRootsLimit)
    (hl : l.val.size = w.historicalSummaries.val.size + 1) :
    Stage b v { caps with history := caps.history + 1 } { w with historicalSummaries := l } :=
  ⟨hw.slot, hw.registrySizes, hw.vGrows, hw.potential, hw.consolidationIdx, hw.consolidationCount,
    hw.effCap, hw.depositCap, hw.exitBound, by have := hw.historyBound; simp only at this ⊢; omega,
    hw.balanceBound, hw.live⟩

variable [HasherTag]

theorem processEffectiveBalanceUpdates_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processEffectiveBalanceUpdates (StateTransition := FuluRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processEffectiveBalanceUpdates
  refine runSucceeds_modifyThe (pureState_forIn_range_inv (fun s => Stage b v caps s)
    (by
      intro i s hs
      dsimp only
      split
      · refine ⟨_, rfl, hs.setValidator _ _ ?_ ?_⟩
        · exact Nat.le_trans (umin_toNat_le_right _ _) (getMaxEffectiveBalance_le _)
        · intro hj e _ ha
          simp only [box_reduce]
          rw [sszList_getElem!_eq _ hj]
          exact ha
      · exact ⟨_, rfl, hs⟩) _ _ hw)

theorem processHistoricalSummariesUpdate_succeeds {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hroom : w.historicalSummaries.val.size < Const.historicalRootsLimit) :
    RunSucceeds w (processHistoricalSummariesUpdate (StateTransition := FuluRun))
      (fun _ w' => Stage b v { caps with history := caps.history + 1 } w') := by
  unfold processHistoricalSummariesUpdate
  run_succeeds
  ro_call getCurrentEpoch_succeeds _
  run_succeeds
  · split
    · rename_i s' heq
      obtain ⟨l, hpush, rfl⟩ := Option.map_eq_some_iff.mp heq
      have hval := SizzLean.Proofs.sszListPush?_eq_some hpush
      run_succeeds
      -- The walk names the new state by the written box's view, the record update by `rfl`.
      exact hw.setHistory l (by rw [hval, Array.size_push]; rfl)
    · rename_i heq
      exfalso
      rw [Option.map_eq_none_iff,
        SizzLean.Proofs.sszListPush?_of_lt (pureState w).view.historicalSummaries _ hroom] at heq
      exact Option.some_ne_none _ heq
  · exact hw.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_succ _)

theorem processParticipationFlagUpdates_succeeds {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processParticipationFlagUpdates (StateTransition := FuluRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processParticipationFlagUpdates
  run_succeeds
  · rw [Array.size_replicate]
    exact w.validators.property
  · rename_i l hl
    -- Both participation lists keep the registry's length, so the stage fields are unchanged.
    obtain ⟨_, _, hp, hq⟩ := hw.registrySizes
    refine hw.of_frame ?_
    simp only [SizzLean.Repr.SSZList.size] at hp hq
    have hls : l.size = w.validators.val.size := by
      show l.val.size = _
      rw [hl, Array.size_replicate]
      rfl
    simp [stageFields, listSizes, box_reduce, hls, hp, hq]

end

end EthCLSpecs.Proofs.Fulu
