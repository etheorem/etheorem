import EthCLSpecs.Proofs.Heze.StakeFrame
import EthCLSpecs.Proofs.Heze.FinalizationProgress

/-!
# `EthCLSpecs.Proofs.Heze.StakeRun`: the target test along a chain inside one epoch

Take a state `s` whose honest validators pass the target test of the previous epoch `e₀`: each
one that the test can count has its target flag, and they hold two thirds of the total active
balance. A chain run from `s` that stays in the epoch of `s` keeps that test passing, when no
state of the run marks an honest validator slashed.

- Inside one epoch, a run keeps the effective balances (`ebView`) and the activity of each
  validator at the current and the previous epoch (`comView`): `ChainRun.views_of_epoch`. So
  it keeps the list of honest validators that the test counts, their stake, and the total
  active balance (`honestList_eq_of_views`, `honestStake_eq_of_views`, `totBal_eq_of_views`).
- A target flag lasts to the end of the next epoch (`ChainRun.targetFlag_carry`).

So the end state of the run passes the target test of `e₀` (`jp_along`). The run can hold any
blocks. The slashed premise is the one thing a block could break: a slashing removes a
validator from the counted set.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Epoch ValidatorIndex currentEpochOf
  previousEpochOf isActiveValidator)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The views along a run -/

/-- A slot step that does not end an epoch keeps `comView` of each epoch: it keeps the
registry, the RANDAO mixes, and the epoch. -/
theorem SlotStep.comView_of_not_boundary {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch ≠ 0) (e : Epoch) :
    comView e (pureState u') = comView e (pureState u) := by
  have hs := h.slot hlt
  have hv := h.validators_of_not_boundary hlt hb
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := processSlot_run_eq h1
  subst e1
  split at h2
  · rename_i htest
    exact absurd ((epochTest_iff (slotWrite u).slot hlt).mp htest) hb
  subst h2
  have hr : u'.randaoMixes = u.randaoMixes := congrArg (fun s : State => s.view.randaoMixes) hst'
  have hep := (epochs_eq_of_toNat (a := u') (b := u)
    (by rw [hs]; exact epoch_succ_of_not_boundary hb)).1
  simp only [comView, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · exact decide_eq_decide.mpr (by
      unfold CommitteeWindow
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ u'.validators.val.size < 2 ^ 64 ↔ _
      rw [hep, hv]
      try exact Iff.rfl)
  · show u'.validators.val.map _ = u.validators.val.map _
    rw [hv]
  · show vmodGet u'.randaoMixes _ _ = vmodGet u.randaoMixes _ _
    rw [hr]

/-- **A run inside one epoch keeps the stake views.** It keeps the effective balances, and a
`comView` of an epoch of the window. -/
theorem ChainRun.views_of_epoch {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w)
    (he : u.slot.toNat / slotsPerEpoch = w.slot.toNat / slotsPerEpoch) {e : Epoch}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32} (hc : comView e (pureState u) = (true, c)) :
    ebView (pureState w) = ebView (pureState u) ∧ comView e (pureState w) = (true, c) := by
  revert he hc
  induction h with
  | nil => intro _ hc; exact ⟨rfl, hc⟩
  | @slot _ st st1 _ hlt hstep hrest ih =>
    intro he hc
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    have hle := hrest.epoch_le hhi
    by_cases hb : (st.slot.toNat + 1) % slotsPerEpoch = 0
    · exfalso
      have := succ_div_of_mod_eq hb
      rw [← hs] at this
      omega
    · have hep := epoch_succ_of_not_boundary hb
      rw [← hs] at hep
      have hv := hstep.validators_of_not_boundary (by omega) hb
      have hc1 : comView e (pureState st1) = (true, c) :=
        (hstep.comView_of_not_boundary (by omega) hb e).trans hc
      obtain ⟨k1, k2⟩ := ih (by omega) hc1
      refine ⟨k1.trans ?_, k2⟩
      show st1.validators.val.map _ = st.validators.val.map _
      rw [hv]
  | block sb v hstep _ ih =>
    intro he hc
    obtain ⟨hs, -⟩ := hstep.slot
    obtain ⟨k1, k2⟩ := ih (by rw [hs]; exact he) (processBlock_frame_com hstep.2.1 hc)
    exact ⟨k1.trans (processBlock_frame_eb hstep.2.1), k2⟩

/-- A `comView` of `true` holds the activity of each validator at its epoch. -/
theorem act_of_comView {e : Epoch} {a b : BeaconState} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (ha : comView e (pureState a) = (true, c)) (hb : comView e (pureState b) = (true, c)) :
    b.validators.val.map (isActiveValidator · e) = a.validators.val.map (isActiveValidator · e) := by
  have h1 := congrArg (fun x => x.2.1) ha
  have h2 := congrArg (fun x => x.2.1) hb
  simp only [comView] at h1 h2
  exact h2.trans h1.symm

/-- Two registries with one effective balance list have one effective balance at each
index. -/
theorem eb_of_ebView {a b : BeaconState} (h : ebView (pureState b) = ebView (pureState a))
    {i : Nat} (hb : i < b.validators.val.size) (ha : i < a.validators.val.size) :
    b.validators.val[i].effectiveBalance = a.validators.val[i].effectiveBalance := by
  have e := congrArg (fun x : Array EthCLSpecs.Heze.Gwei => x[i]?) h
  simp only [ebView] at e
  change (b.validators.val.map (·.effectiveBalance))[i]? =
    (a.validators.val.map (·.effectiveBalance))[i]? at e
  rw [Array.getElem?_map, Array.getElem?_map, getElem?_pos b.validators.val i hb,
    getElem?_pos a.validators.val i ha] at e
  exact Option.some.inj e

/-! ## The stake and the total -/

/-- Two registries with one activity at `e`, where no honest validator is slashed, have one
list of honest validators for the test of `e`. -/
theorem honestList_eq_of_views {a b : BeaconState} {honestOf : ValidatorIndex → Bool} {e : Epoch}
    (hm : b.validators.val.map (isActiveValidator · e) =
      a.validators.val.map (isActiveValidator · e))
    (ha : ∀ j < a.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (a.validators.val[j]!).slashed = false)
    (hb : ∀ j < b.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (b.validators.val[j]!).slashed = false) :
    honestList b honestOf e = honestList a honestOf e := by
  have hsz : b.validators.val.size = a.validators.val.size := by
    simpa using congrArg Array.size hm
  unfold honestList
  rw [hsz]
  congr 1
  refine List.filter_congr fun j hj => ?_
  have hj' := List.mem_range.mp hj
  have hjb : j < b.validators.val.size := by omega
  by_cases hh : honestOf (UInt64.ofNat j) = true
  · rw [ha j hj' hh, hb j hjb hh, hh]
    have e1 := congrArg (fun x : Array Bool => x[j]?) hm
    simp only at e1
    rw [Array.getElem?_map, Array.getElem?_map, getElem?_pos b.validators.val j hjb,
      getElem?_pos a.validators.val j hj'] at e1
    have e2 : isActiveValidator b.validators.val[j] e = isActiveValidator a.validators.val[j] e :=
      Option.some.inj e1
    rw [getElem!_pos b.validators.val j hjb, getElem!_pos a.validators.val j hj', e2]
  · simp [hh]

/-- Two registries as in `honestList_eq_of_views`, with one effective balance list, have one
honest stake for the test of `e`. -/
theorem honestStake_eq_of_views {a b : BeaconState} {honestOf : ValidatorIndex → Bool} {e : Epoch}
    (hm : b.validators.val.map (isActiveValidator · e) =
      a.validators.val.map (isActiveValidator · e))
    (heb : ebView (pureState b) = ebView (pureState a))
    (h64 : a.validators.val.size < 2 ^ 64)
    (ha : ∀ j < a.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (a.validators.val[j]!).slashed = false)
    (hb : ∀ j < b.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (b.validators.val[j]!).slashed = false) :
    honestStake b honestOf e = honestStake a honestOf e := by
  have hsz : b.validators.val.size = a.validators.val.size := by
    simpa using congrArg Array.size hm
  unfold honestStake
  rw [honestList_eq_of_views hm ha hb]
  congr 1
  refine List.map_congr_left fun x hx => ?_
  have hlt := (mem_honestList h64 hx).1
  rw [getElem!_pos b.validators.val x.toNat (by omega), getElem!_pos a.validators.val x.toNat hlt,
    eb_of_ebView heb (by omega) hlt]

/-- **Two states in one epoch with one activity at that epoch and one effective balance list
have one total active balance.** The proof follows `totalActive_congr`: the active indices
agree, and each balance read at an active index returns one effective balance. -/
theorem totBal_eq_of_views {a b : BeaconState}
    (hep : currentEpochOf (pureState b) = currentEpochOf (pureState a))
    (hm : b.validators.val.map (isActiveValidator · (currentEpochOf (pureState a))) =
      a.validators.val.map (isActiveValidator · (currentEpochOf (pureState a))))
    (heb : ebView (pureState b) = ebView (pureState a))
    (h64 : a.validators.val.size < 2 ^ 64) : totBal b = totBal a := by
  have hsz : b.validators.val.size = a.validators.val.size := by
    simpa using congrArg Array.size hm
  have hidx : EthCLSpecs.Heze.activeValidatorIndicesOf (pureState b)
        (currentEpochOf (pureState b)) =
      EthCLSpecs.Heze.activeValidatorIndicesOf (pureState a) (currentEpochOf (pureState a)) := by
    rw [hep]
    exact activeValidatorIndicesOf_eq_of_map hm
  have h64a : a.validators.val.size ≤ 2 ^ 64 := by omega
  have h64b : b.validators.val.size ≤ 2 ^ 64 := by omega
  unfold totBal
  show (match (do
      let active ← EthCLSpecs.Heze.getActiveValidatorIndices (pureState b)
        (currentEpochOf (pureState b))
      EthCLSpecs.Heze.getTotalBalance (pureState b) active) with
      | .ok g => g | .error _ => 0) =
    (match (do
      let active ← EthCLSpecs.Heze.getActiveValidatorIndices (pureState a)
        (currentEpochOf (pureState a))
      EthCLSpecs.Heze.getTotalBalance (pureState a) active) with
      | .ok g => g | .error _ => 0)
  rw [getActiveValidatorIndices_ok b _ h64b, getActiveValidatorIndices_ok a _ h64a]
  simp only [bind, Except.bind]
  rw [hidx]
  unfold EthCLSpecs.Heze.getTotalBalance
  dsimp only
  congr 2
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  congr 1
  refine list_mapM_congr _ fun x hx => ?_
  rw [activeValidatorIndicesOf_toList, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨hir, -⟩ := List.mem_filter.mp hi
  have hi' := List.mem_range.mp hir
  have hib : i < b.validators.val.size := by rw [hsz]; exact hi'
  rw [EthCLLib.Proofs.toNat_ofNat_lt64 (Nat.lt_trans hi' h64)]
  unfold sszGetIdx liftErr
  rw [show IdxRead.get? (pureState b).view.validators i = some b.validators.val[i] from
      getElem?_pos b.validators.val i hib,
    show IdxRead.get? (pureState a).view.validators i = some a.validators.val[i] from
      getElem?_pos a.validators.val i hi']
  show Except.ok b.validators.val[i].effectiveBalance = Except.ok a.validators.val[i].effectiveBalance
  rw [eb_of_ebView heb hib hi']

/-! ## The target test along a run -/

/-- **The target test of the previous epoch passes along a run inside one epoch.** At `s`, the
honest validators that the test of `e₀` can count have their target flags, and they hold two
thirds of the total active balance. The run from `s` to `z` stays in the epoch of `s`. No
honest validator is slashed at `s` or at `z`. Then at `z` the test of `e₀` passes. -/
theorem jp_along {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep} {s z : BeaconState}
    (h : ChainRun hi q s z) (hep : s.slot.toNat / slotsPerEpoch = z.slot.toNat / slotsPerEpoch)
    {honestOf : ValidatorIndex → Bool} {e₀ : Epoch} (he₀ : e₀ = previousEpochOf (pureState s))
    (hne : e₀ ≠ currentEpochOf (pureState s))
    (hw₀ : CommitteeWindow e₀ (pureState s))
    (hw₁ : CommitteeWindow (currentEpochOf (pureState s)) (pureState s))
    (hus : ∀ j < s.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (s.validators.val[j]!).slashed = false)
    (huz : ∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (z.validators.val[j]!).slashed = false)
    (hflags : ∀ x ∈ honestList s honestOf e₀, TargetFlagSet s x.toNat e₀)
    (hstake : 3 * honestStake s honestOf e₀ ≥ 2 * (totBal s).toNat)
    (htot : RunTotals z) {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState z)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e₀ = .ok idx) :
    (tgtBal z e₀).toNat * 3 ≥ (totBal z).toNat * 2 := by
  have h64 : s.validators.val.size < 2 ^ 64 := hw₁.2.2.2.2.2
  -- The two views at `s`, as values with a `true` window flag.
  have hc₀ : comView e₀ (pureState s) = (true, (comView e₀ (pureState s)).2) := by
    show ((comView e₀ (pureState s)).1, (comView e₀ (pureState s)).2) = _
    have : (comView e₀ (pureState s)).1 = true := by simpa [comView] using hw₀
    rw [this]
  have hc₁ : comView (currentEpochOf (pureState s)) (pureState s) =
      (true, (comView (currentEpochOf (pureState s)) (pureState s)).2) := by
    show ((comView _ (pureState s)).1, (comView _ (pureState s)).2) = _
    have : (comView (currentEpochOf (pureState s)) (pureState s)).1 = true := by
      simpa [comView] using hw₁
    rw [this]
  obtain ⟨heb, hz₀⟩ := h.views_of_epoch hhi hep hc₀
  obtain ⟨-, hz₁⟩ := h.views_of_epoch hhi hep hc₁
  have hcur : currentEpochOf (pureState z) = currentEpochOf (pureState s) :=
    (epochs_eq_of_toNat hep.symm).1
  -- The honest list, the honest stake, and the total stay.
  have hm₀ := act_of_comView hc₀ hz₀
  have hl := honestList_eq_of_views hm₀ hus huz
  have hsk := honestStake_eq_of_views hm₀ heb h64 hus huz
  have htb := totBal_eq_of_views hcur (act_of_comView hc₁ hz₁) heb h64
  -- Each honest validator of the test at `z` keeps its flag from `s`.
  have hflags' : ∀ x ∈ honestList z honestOf e₀, TargetFlagSet z x.toNat e₀ := by
    intro x hx
    rw [hl] at hx
    have hs₁ : epochOf s = e₀.toNat + 1 := by
      have := previousEpochOf_epochOf s
      have hc := currentEpochOf_epochOf s
      rw [← he₀] at this
      have hne' : e₀.toNat ≠ (currentEpochOf (pureState s)).toNat :=
        fun h' => hne (UInt64.toNat_inj.mp h')
      omega
    refine h.targetFlag_carry hhi (by omega) (by unfold epochOf at *; omega) (hflags x hx) ?_
    intro h'
    omega
  have hle := honestStake_le_tgtBal htot hidx hflags'
  rw [hsk] at hle
  rw [htb]
  omega

end

end EthCLSpecs.Proofs.Heze
