import EthCLSpecs.Proofs.Fulu.EpochSuccess.FrameSteps
import EthCLSpecs.Proofs.Fulu.Balances

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag]

omit [Preset] [HasherTag] in
/-- In range, the spec's checked read of an SSZ list returns the total read's element. -/
theorem sszList_get?_eq {α : Type} [Inhabited α] {cap : Nat} (xs : SizzLean.Repr.SSZList α cap)
    (i : Nat) (h : i < xs.size) : EthCLLib.Spec.IdxRead.get? xs i = some xs[i]! := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := h)]
  show xs.val[i]? = some (xs.val[i]'h)
  exact Array.getElem?_eq_getElem h

theorem increaseBalance_succeeds (s u : BeaconState) (i : ValidatorIndex) (d : Gwei)
    (hi : i.toNat < s.balances.size) (hno : s.balances[i.toNat]!.toNat + d.toNat < 2 ^ 64) :
    RunSucceeds u (increaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b u' => u' = u ∧
        b = pureState { s with balances := s.balances.set! i.toNat (s.balances[i.toNat]! + d) }) := by
  unfold increaseBalance
  run_succeeds
  · exact ⟨_, sszList_get?_eq _ _ hi⟩
  · rename_i y hy
    rw [show y = s.balances[i.toNat]! from Option.some.inj (hy.symm.trans (sszList_get?_eq _ _ hi))]
    exact uint64_not_add_lt_of_toNat hno
  · rename_i y hy
    rw [show y = s.balances[i.toNat]! from Option.some.inj (hy.symm.trans (sszList_get?_eq _ _ hi))]
    exact ⟨trivial, modBalance_pureState _ _ _⟩

theorem decreaseBalance_succeeds (s u : BeaconState) (i : ValidatorIndex) (d : Gwei)
    (hi : i.toNat < s.balances.size) :
    RunSucceeds u (decreaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b u' => u' = u ∧ b = pureState
        { s with balances := s.balances.set! i.toNat (saturatingSub s.balances[i.toNat]! d) }) := by
  unfold decreaseBalance
  run_succeeds
  · exact ⟨_, sszList_get?_eq _ _ hi⟩
  · rename_i y hy
    rw [show y = s.balances[i.toNat]! from Option.some.inj (hy.symm.trans (sszList_get?_eq _ _ hi))]
    exact ⟨trivial, modBalance_pureState _ _ _⟩

omit [HasherTag] in
omit [Preset] in
/-- A bound on every element survives a `set!` of a value under the bound. -/
theorem sszList_set!_bound {cap : Nat} {xs : SizzLean.Repr.SSZList Gwei cap} {j : Nat} {y : Gwei}
    {c : Nat} (hxs : ∀ x ∈ xs.val, x.toNat ≤ c) (hy : y.toNat ≤ c) :
    ∀ x ∈ (xs.set! j y).val, x.toNat ≤ c := by
  intro x hx
  simp only [Array.set!_eq_setIfInBounds] at hx
  rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | rfl
  · exact hxs x hx
  · exact hy

variable [Config]

omit [HasherTag] [Config] in
/-- A registry index below the registry size survives the round trip through `uint64`. -/
theorem toNat_ofNat_registry [PresetValid] {i : Nat} {w : BeaconState}
    (hi : i < w.validators.val.size) : (UInt64.ofNat i).toNat = i := by
  have hcap := w.validators.property
  have hlim := (PresetValid.committeeBounds (self := ‹_›)).2.1
  have hsize : UInt64.size = 2 ^ 64 := rfl
  exact UInt64.toNat_ofNat_of_lt' (by omega)

omit [HasherTag] [Config] in
omit [Preset] in
/-- An in-range element of an SSZ list is one of its elements. -/
theorem sszList_getElem!_mem {α : Type} [Inhabited α] {cap : Nat} (xs : SizzLean.Repr.SSZList α cap)
    {i : Nat} (h : i < xs.size) : xs[i]! ∈ xs.val := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := h)]
  exact Array.getElem_mem _

omit [HasherTag] in
/-- A `Stage` state with its balances replaced by a list of the same length under a new cap. -/
theorem Stage.setBalances {b : EpochBudget} {v : BeaconState} {caps : StageCaps} {w : BeaconState}
    (hw : Stage b v caps w) (bs : SizzLean.Repr.SSZList Gwei Const.validatorRegistryLimit)
    (hsize : bs.size = w.balances.size) {cap : Nat} (hb : ∀ x ∈ bs.val, x.toNat ≤ cap) :
    Stage b v { caps with balance := cap } { w with balances := bs } := by
  obtain ⟨hb1, hi, hp, hq⟩ := hw.registrySizes
  exact ⟨hw.slot, ⟨hsize.trans hb1, hi, hp, hq⟩, hw.vGrows, hw.potential, hw.consolidationIdx,
    hw.consolidationCount, hw.effCap, hw.depositCap, hw.exitBound, hw.historyBound, hb, hw.live⟩

theorem processSlashings_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) :
    RunSucceeds w (processSlashings (StateTransition := FuluRun)) (fun _ w' => Stage b v caps w') := by
  unfold processSlashings
  run_succeeds
  -- The loop carries a box; only its balances change, and only downward.
  refine (runSucceeds_forIn_range_box (fun _ s => Stage b v caps s ∧ s.validators = w.validators)
    _ (fun i s u hi hs => ?_) w w ⟨hw, rfl⟩).weaken ?_
  · have hiv : i < s.validators.val.size := by rw [hs.2]; exact hi
    have hidx := toNat_ofNat_registry hiv
    have hib : (UInt64.ofNat i).toNat < s.balances.size := by
      rw [hidx, hs.1.registrySizes.1]; exact hiv
    run_succeeds
    · refine (decreaseBalance_succeeds s u _ _ hib).weaken (fun _ _ h => ?_)
      obtain ⟨rfl, rfl⟩ := h
      run_succeeds
      refine ⟨rfl, _, rfl, ?_, hs.2⟩
      have hy : ∀ d : Gwei, (saturatingSub s.balances[(UInt64.ofNat i).toNat]! d).toNat ≤ caps.balance := by
        intro d
        rw [EthCLLib.Proofs.saturatingSub_toNat]
        exact Nat.le_trans (Nat.sub_le _ _) (hs.1.balanceBound _ (sszList_getElem!_mem _ hib))
      exact hs.1.setBalances _ (SizzLean.Proofs.sszListSet!_size _ _ _)
        (sszList_set!_bound hs.1.balanceBound (hy _))
    · exact ⟨rfl, _, rfl, hs⟩
  · intro _ w' ⟨hw', s', ha, hs'⟩
    subst hw' ha
    run_succeeds
    exact hs'.1

end

end EthCLSpecs.Proofs.Fulu
