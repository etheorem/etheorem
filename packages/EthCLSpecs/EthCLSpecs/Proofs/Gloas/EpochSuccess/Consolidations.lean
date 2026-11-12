import EthCLSpecs.Proofs.Gloas.EpochSuccess.FieldSteps
import EthCLSpecs.Proofs.Gloas.EpochSuccess.Lists

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Consolidations`: the consolidation queue drains

The Gloas counterpart of the Fulu module of the same name, over Gloas's progressive lists.

The scan reads each queued source and target in the registry (`Stage.consolidationIdx`) and
moves at most the source's effective balance, at most `MAX_EFFECTIVE_BALANCE_ELECTRA`, into the
target. The target's balance then grows by at most one cap per queued entry, which the budget
covers. The scan's fuel never runs out before its `npc ≥ size` guard ends it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Gloas

/-- An element of an array's suffix is an element of the array. -/
theorem mem_of_mem_extract_suffix {α : Type} {xs : Array α} {k : Nat} {x : α}
    (h : x ∈ xs.extract k xs.size) : x ∈ xs := by
  rw [Array.mem_iff_getElem] at h ⊢
  obtain ⟨i, hi, rfl⟩ := h
  simp only [Array.size_extract] at hi
  exact ⟨k + i, by omega, by simp [Array.getElem_extract]⟩

section

variable [Preset] [Config] [HasherTag]

omit [HasherTag] in
/-- A `Stage` state whose consolidation queue is replaced by a suffix of itself. -/
theorem Stage.dropConsolidations {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) (k : Nat) :
    Stage b v caps { w with pendingConsolidations := EthCLLib.Spec.sszDrop w.pendingConsolidations k } :=
  ⟨hw.slot, hw.registrySizes, hw.vGrows, hw.potential,
    fun pc hpc => hw.consolidationIdx pc (mem_of_mem_extract_suffix hpc),
    Nat.le_trans (by show (w.pendingConsolidations.val.extract k _).size ≤ _; simp)
      hw.consolidationCount,
    hw.effCap, hw.depositCap, hw.exitBound, hw.historyBound, hw.balanceBound, hw.live,
    hw.liveUnslashed, hw.liveCount⟩

theorem pcLoop_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w)
    (hroom : caps.balance + b.consolidations * Const.maxEffectiveBalanceElectra < 2 ^ 64)
    (nextEpoch : Epoch) :
    RunSucceeds w (pcLoop (StateTransition := GloasRun) w.pendingConsolidations.val nextEpoch)
      (fun npc w' => npc ≤ w.pendingConsolidations.val.size ∧
        w'.pendingConsolidations = w.pendingConsolidations ∧
        Stage b v { caps with balance := caps.balance + npc * Const.maxEffectiveBalanceElectra } w') := by
  unfold pcLoop
  -- The fuel left plus the next index is the queue length plus one, so the fuel never runs out
  -- before the `npc ≥ size` guard ends the scan.
  refine runSucceeds_fuelLoop (fun fuel npc s => npc + fuel = w.pendingConsolidations.val.size + 1 ∧
      npc ≤ w.pendingConsolidations.val.size ∧ s.pendingConsolidations = w.pendingConsolidations ∧
      Stage b v { caps with balance := caps.balance + npc * Const.maxEffectiveBalanceElectra } s)
    _ (fun fuel npc s hs => ?_) (fun _ _ h => absurd h.1 (by have := h.2.1; omega)) _ _ _
    ⟨by omega, Nat.zero_le _, rfl, by simpa using hw⟩
  obtain ⟨hfuel, hnpc, hpc, hs⟩ := hs
  -- The queued entry at `npc` names validators in the registry.
  have hidx : npc < w.pendingConsolidations.val.size →
      (w.pendingConsolidations.val[npc]!.sourceIndex.toNat < s.validators.val.size ∧
        w.pendingConsolidations.val[npc]!.targetIndex.toNat < s.validators.val.size) := by
    intro hlt
    refine hs.consolidationIdx _ ?_
    rw [hpc, getElem!_pos w.pendingConsolidations.val npc hlt]
    exact Array.getElem_mem _
  have hbal := hs.registrySizes.1
  simp only [SizzLean.Repr.ProgressiveList.size] at hbal
  run_succeeds
  · exact ⟨hnpc, hpc, hs⟩
  · exact ⟨_, plist_get?_eq _ _ (hidx (by omega)).1⟩
  · refine ⟨by omega, by omega, hpc, hs.mono ?_ (Nat.le_refl _) (Nat.le_refl _)⟩
    simp only [Nat.succ_mul]
    omega
  · exact ⟨hnpc, hpc, hs⟩
  · exact ⟨_, plist_get?_eq _ _ (by rw [SizzLean.Repr.ProgressiveList.size, hbal]; exact (hidx (by omega)).1)⟩
  · rename_i src hsrc _ _ srcBal _
    have hlt : npc < w.pendingConsolidations.val.size := by omega
    obtain ⟨hsi, hti⟩ := hidx hlt
    have hcount : w.pendingConsolidations.val.size ≤ b.consolidations := by
      have := hs.consolidationCount; rw [hpc] at this; exact this
    -- The moved amount is at most the source's effective balance, so at most the cap.
    have hsrcEq : src = s.validators[w.pendingConsolidations.val[npc]!.sourceIndex.toNat]! :=
      Option.some.inj (hsrc.symm.trans (plist_get?_eq _ _ hsi))
    have hamt : (EthCLLib.Spec.umin srcBal src.effectiveBalance).toNat ≤
        Const.maxEffectiveBalanceElectra :=
      Nat.le_trans (umin_toNat_le_right _ _) (hs.effCap _ (by rw [hsrcEq]; exact plist_getElem!_mem _ hsi))
    have hib : w.pendingConsolidations.val[npc]!.sourceIndex.toNat < s.balances.size := by
      show _ < s.balances.val.size; rw [hbal]; exact hsi
    refine (decreaseBalance_succeeds s s _ _ hib).weaken (fun _ _ h => ?_)
    obtain ⟨hw', hb'⟩ := h
    subst hb'
    replace hw' := hw'.symm
    subst hw'
    -- After the source's floored decrease, every balance is still under the cap.
    have hb1 := plist_set!_bound (j := w.pendingConsolidations.val[npc]!.sourceIndex.toNat)
      hs.balanceBound (y := saturatingSub s.balances[w.pendingConsolidations.val[npc]!.sourceIndex.toNat]!
        (EthCLLib.Spec.umin srcBal src.effectiveBalance)) (by
          rw [EthCLLib.Proofs.saturatingSub_toNat]
          exact Nat.le_trans (Nat.sub_le _ _) (hs.balanceBound _ (plist_getElem!_mem _ hib)))
    have hs1 := hs.setBalances _ (SizzLean.Proofs.progressiveListSet!_size _ _ _) hb1
    have hit : w.pendingConsolidations.val[npc]!.targetIndex.toNat <
        (s.balances.set! (w.pendingConsolidations.val[npc]!.sourceIndex.toNat) (saturatingSub
          s.balances[w.pendingConsolidations.val[npc]!.sourceIndex.toNat]!
          (EthCLLib.Spec.umin srcBal src.effectiveBalance))).size := by
      rw [SizzLean.Proofs.progressiveListSet!_size]; show _ < s.balances.val.size; rw [hbal]; exact hti
    have hold := hb1 _ (plist_getElem!_mem _ hit)
    dsimp only at hold
    have hno : (s.balances.set! (w.pendingConsolidations.val[npc]!.sourceIndex.toNat) (saturatingSub
          s.balances[w.pendingConsolidations.val[npc]!.sourceIndex.toNat]!
          (EthCLLib.Spec.umin srcBal src.effectiveBalance)))[
            w.pendingConsolidations.val[npc]!.targetIndex.toNat]!.toNat +
        (EthCLLib.Spec.umin srcBal src.effectiveBalance).toNat < 2 ^ 64 := by
      have : (npc + 1) * Const.maxEffectiveBalanceElectra ≤
          b.consolidations * Const.maxEffectiveBalanceElectra :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [Nat.succ_mul] at this
      omega
    run_succeeds
    -- The goal fixes the written state; the two premises follow.
    refine RunSucceeds.weaken (increaseBalance_succeeds _ _ _ _ ?_ ?_) (fun _ _ h => ?_)
    · exact hit
    · exact hno
    obtain ⟨hw', hb'⟩ := h
    subst hb'
    replace hw' := hw'.symm
    subst hw'
    run_succeeds
    refine ⟨by omega, by omega, hpc, ?_⟩
    refine hs1.setBalances _ (SizzLean.Proofs.progressiveListSet!_size _ _ _)
      (plist_set!_bound (fun x hx => Nat.le_trans (hb1 x hx) ?_) ?_)
    · simp only [Nat.succ_mul]; omega
    · rw [UInt64.toNat_add, Nat.mod_eq_of_lt hno]
      simp only [Nat.succ_mul]
      omega

theorem processPendingConsolidations_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w)
    (hroom : caps.balance + b.consolidations * Const.maxEffectiveBalanceElectra < 2 ^ 64) :
    RunSucceeds w (processPendingConsolidations (StateTransition := GloasRun))
      (fun _ w' => Stage b v
        { caps with balance := caps.balance + b.consolidations * Const.maxEffectiveBalanceElectra } w') := by
  unfold processPendingConsolidations
  run_succeeds
  refine (pcLoop_succeeds hw hroom _).weaken (fun npc w' h => ?_)
  obtain ⟨hnpc, hpc, hs⟩ := h
  run_succeeds
  have hcount := hw.consolidationCount
  have hle : npc * Const.maxEffectiveBalanceElectra ≤ b.consolidations * Const.maxEffectiveBalanceElectra :=
    Nat.mul_le_mul_right _ (by omega)
  have := (hs.dropConsolidations npc).mono (caps' := { caps with
    balance := caps.balance + b.consolidations * Const.maxEffectiveBalanceElectra })
    (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _)
  -- The step drops from the queue it read before the scan, which the scan left unchanged.
  rw [hpc] at this
  exact this

end

end EthCLSpecs.Proofs.Gloas
