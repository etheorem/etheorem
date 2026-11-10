import EthCLSpecs.Proofs.Fulu.EpochSuccess.FieldSteps

/-!
# `EthCLSpecs.Proofs.Fulu.EpochSuccess.Rewards`: the rewards and penalties substep

`getFlagIndexDeltas` succeeds on every registry index, and each reward it returns is at most the
`flagReward` formula. `applyDeltas` keeps an invariant on the index: entries the loop has passed
are under the raised cap, and entries it has not reached are still under the old one, so each
increase has room. Three flag passes raise the cap by `3 * R`; the inactivity pass pays no reward.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag]

/-- In range, `getBaseReward` returns the formula `flagReward` uses. -/
theorem getBaseReward_eq (w : BeaconState) (vi : ValidatorIndex)
    (hi : vi.toNat < w.validators.size) :
    getBaseReward (pureState w) vi = .ok ((w.validators.val[vi.toNat]!).effectiveBalance.toNat /
      Const.effectiveBalanceIncrement * getBaseRewardPerIncrement (pureState w)) := by
  unfold getBaseReward
  show (EthCLLib.Spec.sszGetIdx (m := Except SizzLean.Cache.IndexError) w.validators vi.toNat >>= _) = _
  unfold EthCLLib.Spec.sszGetIdx EthCLLib.Spec.liftErr
  rw [sszList_get?_eq _ _ hi]
  rw [show w.validators[vi.toNat]! = w.validators.val[vi.toNat]! from by
    rw [sszList_getElem!_eq _ hi, getElem!_pos w.validators.val _ hi]]
  rfl

omit [Preset] [HasherTag] in
/-- A bound on every total read of an array survives a `set!` of a value under the bound. -/
theorem array_set!_getElem!_le {xs : Array Gwei} {R : Nat} (hxs : ∀ j : Nat, UInt64.toNat (xs[j]!) ≤ R)
    (i : Nat) {y : Gwei} (hy : y.toNat ≤ R) : ∀ j : Nat, UInt64.toNat ((xs.set! i y)[j]!) ≤ R := by
  intro j
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < xs.size
  · rw [getElem!_pos (xs.setIfInBounds i y) j (by simpa using hj), Array.getElem_setIfInBounds hj]
    split
    · exact hy
    · have := hxs j
      rwa [getElem!_pos xs j hj] at this
  · rw [getElem!_neg (xs.setIfInBounds i y) j (by simpa using hj)]
    exact Nat.zero_le _

theorem getFlagIndexDeltas_ok [PresetValid] {R : Nat} (w : BeaconState) (f : Nat)
    (hR : ∀ i < w.validators.val.size, flagReward w f (UInt64.ofNat i) ≤ R) :
    ∃ r, getFlagIndexDeltas (pureState w) f = .ok r ∧ ∀ i : Nat, UInt64.toNat (r.1[i]!) ≤ R := by
  unfold getFlagIndexDeltas
  dsimp only
  refine except_array_forIn_bind_ok
    (fun (p : Array Gwei × Array Gwei) => ∀ i : Nat, UInt64.toNat (p.1[i]!) ≤ R) ?_ ?_ ?_
  · intro vi hvi p hp
    unfold getEligibleValidatorIndices at hvi
    obtain ⟨j, hj, rfl, _⟩ := EthCLLib.Proofs.mem_indicesWhere hvi
    have hjv : j < w.validators.val.size := hj
    have hjn := toNat_ofNat_registry hjv
    rw [getBaseReward_eq w _ (by show _ < w.validators.val.size; rw [hjn]; exact hjv)]
    simp only [bind, Except.bind]
    split
    · split
      · refine ⟨_, rfl, array_set!_getElem!_le hp _ ?_⟩
        have hb := hR j hjv
        unfold flagReward at hb
        exact Nat.le_trans UInt64.toNat_ofNat_le hb
      · exact ⟨_, rfl, hp⟩
    · split <;> exact ⟨_, rfl, hp⟩
  · intro i
    show UInt64.toNat ((Array.replicate _ (0 : Gwei))[i]!) ≤ R
    by_cases hi : i < (Array.replicate (pureState w).view.validators.size (0 : Gwei)).size
    · rw [getElem!_pos _ i hi, Array.getElem_replicate]
      exact Nat.zero_le _
    · rw [getElem!_neg _ i hi]
      exact Nat.zero_le _
  · intro p hp
    exact ⟨_, rfl, hp⟩

omit [Preset] [HasherTag] in
/-- A `set!` at `i` leaves every other in-range entry alone. -/
theorem sszList_set!_getElem!_of_ne {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) {i j : Nat} (y : α) (hj : j < xs.val.size) (hne : i ≠ j) :
    (xs.set! i y)[j]! = xs[j]! := by
  rw [sszList_getElem!_eq _ (by simpa using hj), sszList_getElem!_eq _ hj]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hj, ite_eq_right hne]

variable [Config]

theorem applyDeltas_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState} {caps : StageCaps}
    {s u : BeaconState} (rewards penalties : Array Gwei) {R : Nat} (hs : Stage b v caps s)
    (hR : ∀ i : Nat, UInt64.toNat (rewards[i]!) ≤ R) (hroom : caps.balance + R < 2 ^ 64) :
    RunSucceeds u (applyDeltas (StateTransition := FuluRun) rewards penalties (pureState s))
      (fun bx u' => u' = u ∧ ∃ s', bx = pureState s' ∧
        Stage b v { caps with balance := caps.balance + R } s') := by
  unfold applyDeltas
  run_succeeds
  -- Before step `i`, every balance is under the raised cap, and the balances at `i` and past it,
  -- which no step has touched yet, are still under the old one.
  refine (runSucceeds_forIn_range_box (fun i s' => Stage b v { caps with balance := caps.balance + R } s' ∧
      s'.validators = s.validators ∧
      ∀ j, j < s'.balances.val.size → i ≤ j → (s'.balances[j]!).toNat ≤ caps.balance)
    _ (fun i s' u' hi hs' => ?_) s u ⟨hs.mono (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _),
      rfl, fun j hj _ => hs.balanceBound _ (sszList_getElem!_mem _ hj)⟩).weaken ?_
  · obtain ⟨hst, hval, hun⟩ := hs'
    have hiv : i < s'.validators.val.size := by rw [hval]; exact hi
    have hidx := toNat_ofNat_registry hiv
    have hbal := hst.registrySizes.1
    simp only [SizzLean.Repr.SSZList.size] at hbal
    have hib : (UInt64.ofNat i).toNat < s'.balances.size := by
      show _ < s'.balances.val.size; rw [hidx, hbal]; exact hiv
    have hold := hun i (by rw [hbal]; exact hiv) (Nat.le_refl _)
    have hno : (s'.balances[(UInt64.ofNat i).toNat]!).toNat + UInt64.toNat (rewards[i]!) < 2 ^ 64 := by
      rw [hidx]; have := hR i; omega
    run_succeeds
    refine RunSucceeds.weaken (increaseBalance_succeeds _ _ _ _ ?_ ?_) (fun _ _ h => ?_)
    · exact hib
    · exact hno
    obtain ⟨hw', hb'⟩ := h
    subst hb'
    replace hw' := hw'.symm
    subst hw'
    run_succeeds
    refine RunSucceeds.weaken (decreaseBalance_succeeds _ _ _ _ ?_) (fun _ _ h => ?_)
    · rw [SizzLean.Proofs.sszListSet!_size]; exact hib
    obtain ⟨hw', hb'⟩ := h
    subst hb'
    replace hw' := hw'.symm
    subst hw'
    run_succeeds
    -- The increased entry is under the raised cap, so both writes keep the stage.
    have hinc : (s'.balances[(UInt64.ofNat i).toNat]! + rewards[i]!).toNat ≤ caps.balance + R := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hno, hidx]; have := hR i; omega
    have hs1 := hst.setBalances _ (SizzLean.Proofs.sszListSet!_size _ (UInt64.ofNat i).toNat _)
      (sszList_set!_bound (j := (UInt64.ofNat i).toNat) hst.balanceBound hinc)
    refine ⟨rfl, _, rfl, hs1.setBalances _ (SizzLean.Proofs.sszListSet!_size _ _ _)
      (sszList_set!_bound hs1.balanceBound ?_), hval, ?_⟩
    · rw [EthCLLib.Proofs.saturatingSub_toNat]
      exact Nat.le_trans (Nat.sub_le _ _)
        (hs1.balanceBound _ (sszList_getElem!_mem _ (by rw [SizzLean.Proofs.sszListSet!_size]; exact hib)))
    · intro j hj hij
      simp only [SizzLean.Repr.SSZList.set!, Array.size_set!] at hj
      have hne : (UInt64.ofNat i).toNat ≠ j := by rw [hidx]; omega
      rw [sszList_set!_getElem!_of_ne _ _ (by simpa using hj) hne,
        sszList_set!_getElem!_of_ne _ _ hj hne]
      exact hun j hj (by omega)
  · intro bx u'' ⟨hu, s'', hb, hs''⟩
    subst hu hb
    run_succeeds
    exact ⟨trivial, s'', rfl, hs''.1⟩

theorem processRewardsAndPenalties_succeeds [PresetValid] {b : EpochBudget} {v : BeaconState}
    {caps : StageCaps} {w : BeaconState} (hw : Stage b v caps w) {R : Nat} (hR : RewardsWithin R w)
    (hroom : caps.balance + 3 * R < 2 ^ 64) :
    RunSucceeds w (processRewardsAndPenalties (StateTransition := FuluRun))
      (fun _ w' => Stage b v { caps with balance := caps.balance + 3 * R } w') := by
  -- The three flag computations succeed, and every reward they return is at most `R`.
  obtain ⟨deltas, hdeltas, hlen, hbound⟩ := EthCLLib.Proofs.except_list_mapM_ok
    (P := fun (y : Array Gwei × Array Gwei) => ∀ i : Nat, UInt64.toNat (y.1[i]!) ≤ R)
    (List.range 3) (fun f hf => getFlagIndexDeltas_ok w f (hR f (List.mem_range.mp hf)))
  unfold processRewardsAndPenalties
  run_succeeds
  · exact hw.mono (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _)
  · exact ⟨_, hdeltas⟩
  · rename_i ds hds
    rw [hdeltas] at hds
    cases hds
    have hlen3 : deltas.length = 3 := by rw [hlen, List.length_range]
    -- Each flag pass raises the balance cap by `R`; `k` counts the passes done.
    refine (runSucceeds_forIn_list
      (fun rest _ w' => (∀ y ∈ rest, ∀ i : Nat, UInt64.toNat (y.1[i]!) ≤ R) ∧
        ∃ k, k + rest.length ≤ 3 ∧ Stage b v { caps with balance := caps.balance + k * R } w')
      (fun _ w' => ∃ k, k ≤ 3 ∧ Stage b v { caps with balance := caps.balance + k * R } w')
      (fun x rest _ w' hI => ?_) (fun _ w' hI => ?_) deltas _ w
      ⟨hbound, 0, by omega, by simpa using hw⟩).weaken ?_
    · obtain ⟨hall, k, hk, hs'⟩ := hI
      obtain ⟨r, p⟩ := x
      have hr := hall (r, p) List.mem_cons_self
      have hk1 : k + 1 ≤ 3 := by simp only [List.length_cons] at hk; omega
      have hkR : k * R + R ≤ 3 * R := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk1
      run_succeeds
      refine (applyDeltas_succeeds r p hs' hr (by dsimp only; omega)).weaken (fun _ _ h => ?_)
      obtain ⟨hu, s'', hb, hs''⟩ := h
      subst hu hb
      run_succeeds
      refine ⟨fun y hy => hall y (List.mem_cons_of_mem _ hy), k + 1, by simp only [List.length_cons] at hk; omega, ?_⟩
      have := hs''
      simp only [Nat.succ_mul, Nat.add_assoc] at this ⊢
      exact this
    · obtain ⟨_, k, hk, hs'⟩ := hI
      exact ⟨k, by simpa using hk, hs'⟩
    · intro _ w' ⟨k, hk, hs'⟩
      have hkR : k * R ≤ 3 * R := Nat.mul_le_mul_right _ hk
      run_succeeds
      refine (applyDeltas_succeeds (R := 0) _ _ hs' (fun i => ?_) (by dsimp only; omega)).weaken
        (fun _ _ h => ?_)
      · by_cases hi : i < (Array.replicate (pureState w).view.validators.size (0 : Gwei)).size
        · rw [getElem!_pos _ i hi, Array.getElem_replicate]; exact Nat.zero_le _
        · rw [getElem!_neg _ i hi]; exact Nat.zero_le _
      obtain ⟨hu, s'', hb, hs''⟩ := h
      subst hu hb
      run_succeeds
      exact hs''.mono (by dsimp only; omega) (Nat.le_refl _) (Nat.le_refl _)

end

end EthCLSpecs.Proofs.Fulu
