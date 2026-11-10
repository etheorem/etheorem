import EthCLSpecs.Proofs.Gloas.EpochSuccess.Balances
import EthCLSpecs.Proofs.Gloas.EpochSuccess.Lists

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.FieldSteps`: three substeps that write one field group

The Gloas counterpart of the Fulu module of the same name, over Gloas's progressive lists.

The effective-balance update rewrites effective balances, capped by `get_max_effective_balance`,
so `effCap` holds after it, and the activation and exit epochs stay put, so liveness does. The
historical-summaries update appends once when the list has room. The participation rotation
rebuilds both lists at the registry's length. `Live.set!` and `Stage.setValidator` carry the stage
across a validator write that keeps every sampled epoch's activity.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Gloas

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
  refine h.mono (Nat.le_of_eq (plist_set!_size _ _ _).symm) (fun i hi hi' ha => ?_)
  simp only [plist_set!_val]
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
      isActiveValidator w.validators.val[j] e = true → isActiveValidator y e = true)
    (hsl : ∀ (hj : j < w.validators.val.size), y.slashed = w.validators.val[j].slashed) :
    Stage b v caps { w with validators := w.validators.set! j y } := by
  have hsz : (w.validators.set! j y).val.size = w.validators.val.size := plist_set!_size _ _ _
  obtain ⟨hb1, hi, hp, hq⟩ := hw.registrySizes
  refine ⟨hw.slot, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hw.consolidationCount, ?_, hw.depositCap,
    hw.exitBound, hw.historyBound, hw.balanceBound,
    ⟨hw.live.1.set! j y (fun hj => hact hj _ (Or.inl rfl)),
     hw.live.2.set! j y (fun hj => hact hj _ (Or.inr rfl))⟩, ?_, ?_⟩
  all_goals simp only [SizzLean.Repr.ProgressiveList.size] at hb1 hi hp hq ⊢
  · rw [hsz]; exact hb1
  · rw [hsz]; exact hi
  · rw [hsz]; exact hp
  · rw [hsz]; exact hq
  · rw [hsz]; exact hw.vGrows
  · unfold registryPotential; rw [hsz]; exact hw.potential
  · intro pc hpc; rw [hsz]; exact hw.consolidationIdx pc hpc
  · intro x hx
    rw [plist_set!_val] at hx
    rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
    · exact hw.effCap x hx
    · exact heff
  · -- The unslashed active validator stays unslashed and active.
    obtain ⟨i, hi, ha, hs⟩ := hw.liveUnslashed
    refine ⟨i, by rw [hsz]; exact hi, ?_⟩
    simp only [plist_set!_val]
    rw [Array.getElem_setIfInBounds hi]
    split
    · rename_i hji
      subst hji
      exact ⟨hact hi _ (Or.inr rfl) ha, (hsl hi).trans hs⟩
    · exact ⟨ha, hs⟩
  · -- Every active validator stays active, so the count does not drop.
    refine Nat.le_trans hw.liveCount (EthCLLib.Proofs.indicesWhere_size_mono (Nat.le_of_eq hsz.symm)
      (fun i hi ha => ?_))
    rw [getElem!_pos _ i hi] at ha
    rw [getElem!_pos _ i (by rw [hsz]; exact hi)]
    simp only [plist_set!_val]
    rw [Array.getElem_setIfInBounds hi]
    split
    · rename_i hji
      subst hji
      exact hact hi _ (Or.inr rfl) ha
    · exact ha

omit [Config] in
/-- `get_max_effective_balance` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`, at a valid preset. -/
theorem getMaxEffectiveBalance_le [PresetValid] (x : Validator) :
    (getMaxEffectiveBalance x).toNat ≤ Const.maxEffectiveBalanceElectra := by
  have htwin : Const.maxEffectiveBalanceElectraG.toNat = Const.maxEffectiveBalanceElectra :=
    (PresetValid.toFulu (self := ‹_›)).maxEffectiveBalanceElectraTwin
  have hmin : Const.minActivationBalance.toNat ≤ Const.maxEffectiveBalanceElectra :=
    (PresetValid.toFulu (self := ‹_›)).minActivationBalanceLe
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

/-- A `Stage` state with one more historical summary, under a history cap one higher. -/
theorem Stage.setHistory {b : EpochBudget} {v : BeaconState} {caps : StageCaps} {w : BeaconState}
    (hw : Stage b v caps w) (l : SizzLean.Repr.SSZList HistoricalSummary Const.historicalRootsLimit)
    (hl : l.val.size = w.historicalSummaries.val.size + 1) :
    Stage b v { caps with history := caps.history + 1 } { w with historicalSummaries := l } :=
  ⟨hw.slot, hw.registrySizes, hw.vGrows, hw.potential, hw.consolidationIdx, hw.consolidationCount,
    hw.effCap, hw.depositCap, hw.exitBound, by have := hw.historyBound; simp only at this ⊢; omega,
    hw.balanceBound, hw.live, hw.liveUnslashed, hw.liveCount⟩

variable [HasherTag]

theorem processEffectiveBalanceUpdates_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processEffectiveBalanceUpdates (StateTransition := GloasRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processEffectiveBalanceUpdates
  refine runSucceeds_modifyThe (pureState_forIn_range_inv (fun s => Stage b v caps s)
    (by
      intro i s hs
      dsimp only
      split
      · refine ⟨_, rfl, hs.setValidator _ _ ?_ ?_ ?_⟩
        · exact Nat.le_trans (umin_toNat_le_right _ _) (getMaxEffectiveBalance_le _)
        · intro hj e _ ha
          simp only [box_reduce]
          rw [plist_getElem!_eq _ hj]
          exact ha
        · intro hj
          simp only [box_reduce]
          rw [plist_getElem!_eq _ hj]
      · exact ⟨_, rfl, hs⟩) _ _ hw)

theorem processHistoricalSummariesUpdate_succeeds {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hroom : w.historicalSummaries.val.size < Const.historicalRootsLimit) :
    RunSucceeds w (processHistoricalSummariesUpdate (StateTransition := GloasRun))
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
    RunSucceeds w (processParticipationFlagUpdates (StateTransition := GloasRun))
      (fun _ w' => Stage b v caps w') := by
  unfold processParticipationFlagUpdates
  run_succeeds
  -- Both participation lists keep the registry's length, so the stage fields are unchanged.
  obtain ⟨_, _, hp, hq⟩ := hw.registrySizes
  refine hw.of_frame ?_
  simp only [SizzLean.Repr.ProgressiveList.size] at hp hq
  simp [stageFields, listSizes, box_reduce, hp, hq, SizzLean.Repr.ProgressiveList.size]

end

end EthCLSpecs.Proofs.Gloas
