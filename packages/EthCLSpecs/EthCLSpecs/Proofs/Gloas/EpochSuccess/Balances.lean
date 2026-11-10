import EthCLSpecs.Proofs.Gloas.EpochSuccess.FrameSteps
import EthCLSpecs.Proofs.Gloas.EpochSuccess.Lists

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Balances`: the balance writes and the slashings substep

`increaseBalance` succeeds in range and under the overflow bound, and `decreaseBalance` in range;
both write one entry of the uncached box they are handed. `Stage.setBalances` keeps a stage across
a balance write under a new cap. The slashings substep only lowers balances, so it keeps the stage
as it is.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Gloas

section

variable [Preset] [HasherTag]

/-- `modBalance` at the uncached box is one plain record update. -/
theorem modBalance_pureState (state : BeaconState) (i : ValidatorIndex) (f : Gwei → Gwei) :
    modBalance (pureState state) i f =
      pureState { state with balances := state.balances.set! i.toNat (f state.balances[i.toNat]!) } :=
  rfl

theorem increaseBalance_succeeds (s u : BeaconState) (i : ValidatorIndex) (d : Gwei)
    (hi : i.toNat < s.balances.size) (hno : s.balances[i.toNat]!.toNat + d.toNat < 2 ^ 64) :
    RunSucceeds u (increaseBalance (StateTransition := GloasRun) (pureState s) i d)
      (fun b u' => u' = u ∧
        b = pureState { s with balances := s.balances.set! i.toNat (s.balances[i.toNat]! + d) }) := by
  unfold increaseBalance
  run_succeeds
  · exact ⟨_, plist_get?_eq _ _ hi⟩
  · rename_i y hy
    rw [show y = s.balances[i.toNat]! from Option.some.inj (hy.symm.trans (plist_get?_eq _ _ hi))]
    exact uint64_not_add_lt_of_toNat hno
  · rename_i y hy
    rw [show y = s.balances[i.toNat]! from Option.some.inj (hy.symm.trans (plist_get?_eq _ _ hi))]
    exact ⟨trivial, modBalance_pureState _ _ _⟩

theorem decreaseBalance_succeeds (s u : BeaconState) (i : ValidatorIndex) (d : Gwei)
    (hi : i.toNat < s.balances.size) :
    RunSucceeds u (decreaseBalance (StateTransition := GloasRun) (pureState s) i d)
      (fun b u' => u' = u ∧ b = pureState
        { s with balances := s.balances.set! i.toNat (saturatingSub s.balances[i.toNat]! d) }) := by
  unfold decreaseBalance
  run_succeeds
  · exact ⟨_, plist_get?_eq _ _ hi⟩
  · rename_i y hy
    rw [show y = s.balances[i.toNat]! from Option.some.inj (hy.symm.trans (plist_get?_eq _ _ hi))]
    exact ⟨trivial, modBalance_pureState _ _ _⟩

variable [Config]

omit [Preset] [HasherTag] [Config] in
/-- An index below `2^64` survives the round trip through `uint64`. Gloas's registry has no cap,
so the bound comes from `EpochSafe.registryRoom`. -/
theorem toNat_ofNat_registry {i : Nat} (hi : i < 2 ^ 64) : (UInt64.ofNat i).toNat = i :=
  UInt64.toNat_ofNat_of_lt' hi

omit [HasherTag] in
/-- A `Stage` state with its balances replaced by a list of the same length under a new cap. -/
theorem Stage.setBalances {b : EpochBudget} {v : BeaconState} {caps : StageCaps} {w : BeaconState}
    (hw : Stage b v caps w) (bs : SizzLean.Repr.ProgressiveList Gwei)
    (hsize : bs.size = w.balances.size) {cap : Nat} (hb : ∀ x ∈ bs.val, x.toNat ≤ cap) :
    Stage b v { caps with balance := cap } { w with balances := bs } := by
  obtain ⟨hb1, hi, hp, hq⟩ := hw.registrySizes
  exact ⟨hw.slot, ⟨hsize.trans hb1, hi, hp, hq⟩, hw.vGrows, hw.potential, hw.consolidationIdx,
    hw.consolidationCount, hw.effCap, hw.depositCap, hw.exitBound, hw.historyBound, hb, hw.live,
    hw.liveUnslashed, hw.liveCount⟩

theorem processSlashings_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {w : BeaconState} (hw : Stage b v caps w) (hV : w.validators.val.size < 2 ^ 64) :
    RunSucceeds w (processSlashings (StateTransition := GloasRun)) (fun _ w' => Stage b v caps w') := by
  unfold processSlashings
  run_succeeds
  -- The loop carries a box; only its balances change, and only downward.
  refine (runSucceeds_forIn_range_box (fun _ s => Stage b v caps s ∧ s.validators = w.validators)
    _ (fun i s u hi hs => ?_) w w ⟨hw, rfl⟩).weaken ?_
  · have hiv : i < s.validators.val.size := by rw [hs.2]; exact hi
    have hidx := toNat_ofNat_registry (i := i) (by rw [hs.2] at hiv; omega)
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
        exact Nat.le_trans (Nat.sub_le _ _) (hs.1.balanceBound _ (plist_getElem!_mem _ hib))
      exact hs.1.setBalances _ (SizzLean.Proofs.progressiveListSet!_size _ _ _)
        (plist_set!_bound hs.1.balanceBound (hy _))
    · exact ⟨rfl, _, rfl, hs⟩
  · intro _ w' ⟨hw', s', ha, hs'⟩
    subst hw' ha
    run_succeeds
    exact hs'.1

end

end EthCLSpecs.Proofs.Gloas
