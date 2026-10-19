import EthCLSpecs.Proofs.Heze.DriftChurn

/-!
# `EthCLSpecs.Proofs.Heze.DriftTotal`: the total active balance within a step

The exit churn of one epoch is a function of the total active balance. The total active
balance reads the slot, and the effective balance of each validator active at the current
epoch (`totalActive_congr`). A block writes no effective balance and no slot, and an exit
sets an exit epoch after the current epoch. So every exit of a block meets the churn of the
start of the block, and the facts that an exit needs at the start of a block hold at each
exit inside it (`StepPre.keep`, `DriftSlash.lean`).

`AcKeep a b` names the reads that the total active balance needs: the slot, the size of the
registry, the active gate and the effective balance of each active validator.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei
  currentEpochOf isActiveValidator)

/-- A left fold reads the members of its list alone. -/
theorem foldl_mem_congr {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) →
      l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact foldl_mem_congr f g l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

section
variable [Preset] [HasherTag]

/-- The reads of the total active balance stay from `a` to `b`. -/
structure AcKeep (a b : BeaconState) : Prop where
  slot : b.slot = a.slot
  size : sizeOf b = sizeOf a
  gate : ∀ i, acB b i = acB a i
  eb : ∀ i, acB a i = true → ebN b i = ebN a i

theorem AcKeep.refl (a : BeaconState) : AcKeep a a :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem AcKeep.trans {a b c : BeaconState} (h1 : AcKeep a b) (h2 : AcKeep b c) : AcKeep a c :=
  ⟨h2.slot.trans h1.slot, h2.size.trans h1.size, fun i => (h2.gate i).trans (h1.gate i),
    fun i hi => (h2.eb i (by rw [h1.gate]; exact hi)).trans (h1.eb i hi)⟩

/-- A step that keeps the slot and the registry keeps the reads. -/
theorem AcKeep.of_validators {a b : BeaconState} (hs : b.slot = a.slot)
    (hv : b.validators = a.validators) : AcKeep a b := by
  have hc : EthCLSpecs.Heze.currentEpochOf (pureState b) =
      EthCLSpecs.Heze.currentEpochOf (pureState a) := by
    show EthCLSpecs.Heze.computeEpochAtSlot b.slot = EthCLSpecs.Heze.computeEpochAtSlot a.slot
    rw [hs]
  exact ⟨hs, by simp [sizeOf, hv], fun i => by unfold acB; rw [hc, hv],
    fun i _ => by unfold ebN; rw [hv]⟩

/-- **The total active balance reads `AcKeep` alone.** The two reads compare as `Except` values:
the active indices agree, and each balance read at an active index returns the same effective
balance. So a fault in one read is a fault in the other. -/
theorem totalActive_congr {a b : BeaconState} (h : AcKeep a b)
    (h64 : a.validators.val.size < 2 ^ 64) :
    EthCLSpecs.Heze.getTotalActiveBalance (pureState b) =
      EthCLSpecs.Heze.getTotalActiveBalance (pureState a) := by
  have hsz : b.validators.val.size = a.validators.val.size := h.size
  -- The gate of the active indices, at a registry index, is `acB`.
  have hq : ∀ (u : BeaconState) i, i < u.validators.val.size →
      isActiveValidator u.validators.val[i]! (currentEpochOf (pureState u)) = acB u i := by
    intro u i hi
    unfold acB
    rw [getElem?_pos u.validators.val i hi, getElem!_pos u.validators.val i hi]
  have hfil : ((List.range b.validators.val.size).filter fun i =>
        isActiveValidator b.validators.val[i]! (currentEpochOf (pureState b))) =
      (List.range a.validators.val.size).filter fun i =>
        isActiveValidator a.validators.val[i]! (currentEpochOf (pureState a)) := by
    rw [hsz]
    refine List.filter_congr fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [hq b i (by rw [hsz]; exact hi'), hq a i hi', h.gate]
  have hidx : EthCLSpecs.Heze.getActiveValidatorIndices (pureState b)
        (currentEpochOf (pureState b)) =
      EthCLSpecs.Heze.getActiveValidatorIndices (pureState a) (currentEpochOf (pureState a)) := by
    apply Array.toList_inj.mp
    rw [getActiveValidatorIndices_toList, getActiveValidatorIndices_toList, hfil]
  show EthCLSpecs.Heze.getTotalBalance (pureState b) (EthCLSpecs.Heze.getActiveValidatorIndices
      (pureState b) (currentEpochOf (pureState b))) =
    EthCLSpecs.Heze.getTotalBalance (pureState a) (EthCLSpecs.Heze.getActiveValidatorIndices
      (pureState a) (currentEpochOf (pureState a)))
  rw [hidx]
  unfold EthCLSpecs.Heze.getTotalBalance
  dsimp only
  -- Each read at an active index returns one effective balance in both states.
  congr 1
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  congr 1
  refine list_mapM_congr _ fun x hx => ?_
  rw [getActiveValidatorIndices_toList, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨hir, hia⟩ := List.mem_filter.mp hi
  have hi' := List.mem_range.mp hir
  have hib : i < b.validators.val.size := by rw [hsz]; exact hi'
  rw [EthCLLib.Proofs.toNat_ofNat_lt64 (Nat.lt_trans hi' h64)]
  have he := h.eb i (by rw [← hq a i hi']; exact hia)
  unfold ebN at he
  rw [getElem?_pos a.validators.val i hi', getElem?_pos b.validators.val i hib] at he
  unfold sszGetIdx liftErr
  rw [show (pureState b).view.validators.val[i]? = some b.validators.val[i] from
      getElem?_pos b.validators.val i hib,
    show (pureState a).view.validators.val[i]? = some a.validators.val[i] from
      getElem?_pos a.validators.val i hi']
  show Except.ok b.validators.val[i].effectiveBalance = Except.ok a.validators.val[i].effectiveBalance
  rw [UInt64.toNat_inj.mp he]

/-- The total active balance value reads `AcKeep` alone. -/
theorem totBal_congr {a b : BeaconState} (h : AcKeep a b)
    (h64 : a.validators.val.size < 2 ^ 64) : totBal b = totBal a := by
  unfold totBal
  rw [totalActive_congr h h64]

/-- The exit churn of one epoch reads `AcKeep` alone. -/
theorem exitChurn_congr [Config] {a b : BeaconState} (h : AcKeep a b)
    (h64 : a.validators.val.size < 2 ^ 64) : exitChurn b = exitChurn a := by
  unfold exitChurn EthCLSpecs.Heze.getExitChurnLimit
  rw [totalActive_congr h h64]

/-- The epoch reads the slot alone. -/
theorem AcKeep.epoch {a b : BeaconState} (h : AcKeep a b) : epochN b = epochN a := by
  show (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat =
    (EthCLSpecs.Heze.computeEpochAtSlot a.slot).toNat
  rw [h.slot]

omit [HasherTag] in
/-- At most every validator has an exit epoch. -/
theorem exitedCount_le (u : BeaconState) : exitedCount u ≤ sizeOf u := by
  unfold exitedCount
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq List.length_range)

end

end EthCLSpecs.Proofs.Heze
