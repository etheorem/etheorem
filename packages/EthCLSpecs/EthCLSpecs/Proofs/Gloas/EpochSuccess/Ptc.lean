import EthCLSpecs.Proofs.Gloas.EpochSuccess.Selection
import EthCLSpecs.Proofs.Gloas.ConfigValid

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Ptc`: every slot's payload-timeliness committee draws

`compute_ptc(state, slot)` concatenates the slot's beacon committees and takes a balance-weighted
selection from them, which asserts a nonempty candidate list. With `n` active validators and
`c` committees per slot, the slot's committee `k` is the slice `[n·k / (c·SPE), n·(k+1) / (c·SPE))`
of the shuffled active set. `get_committee_count_per_slot` keeps `c · SLOTS_PER_EPOCH ≤ n` once
`n ≥ SLOTS_PER_EPOCH` (it floors at one committee, and otherwise divides `n` by `SLOTS_PER_EPOCH`
and `TARGET_COMMITTEE_SIZE`), so every slice, the first one included, holds at least one
validator. `computePtc_ok` reads that off, and the selection then fills under the hash premise.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs (pureState ZeroChunksOften)
open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas

/-- `(x + y) / c` gains at least one over `x / c` when `y ≥ c > 0`. -/
theorem div_add_ge_succ {x y c : Nat} (hc : 0 < c) (hy : c ≤ y) : x / c + 1 ≤ (x + y) / c := by
  rw [Nat.le_div_iff_mul_le hc, Nat.succ_mul]
  have := Nat.div_mul_le_self x c
  omega

/-- Appending to an accumulator never shrinks it, and the first block appended is all there. -/
theorem foldl_append_size_ge {α : Type} (g : Nat → Array α) :
    ∀ (l : List Nat) (init : Array α), init.size ≤ (l.foldl (fun acc i => acc ++ g i) init).size
  | [], _ => Nat.le_refl _
  | i :: rest, init => by
    rw [List.foldl_cons]
    exact Nat.le_trans (by simp) (foldl_append_size_ge g rest (init ++ g i))

section

variable [Preset] [HasherTag]

/-- At least `SLOTS_PER_EPOCH` active validators leave room for one validator per committee:
`committees_per_slot · SLOTS_PER_EPOCH ≤ n`. -/
theorem committeeCount_mul_le [PresetValid] (st : BeaconState) (epoch : Epoch)
    (hcount : Const.slotsPerEpoch ≤ (getActiveValidatorIndices (pureState st) epoch).size) :
    1 ≤ getCommitteeCountPerSlot (pureState st) epoch ∧
      getCommitteeCountPerSlot (pureState st) epoch * Const.slotsPerEpoch ≤
        (getActiveValidatorIndices (pureState st) epoch).size := by
  unfold getCommitteeCountPerSlot
  generalize (getActiveValidatorIndices (pureState st) epoch).size = n at hcount ⊢
  have hq : n / Const.slotsPerEpoch / Const.targetCommitteeSize * Const.slotsPerEpoch ≤ n := by
    have h1 : n / Const.slotsPerEpoch / Const.targetCommitteeSize ≤ n / Const.slotsPerEpoch :=
      Nat.div_le_self _ _
    have h2 := Nat.div_mul_le_self n Const.slotsPerEpoch
    exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
  dsimp only
  unfold Nat.max
  refine ⟨Nat.le_max_left _ _, ?_⟩
  rcases Nat.le_total 1 (Nat.min Const.maxCommitteesPerSlot
      (n / Const.slotsPerEpoch / Const.targetCommitteeSize)) with h | h
  · rw [Nat.max_eq_right h]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_right _ _)) hq
  · rw [Nat.max_eq_left h, Nat.one_mul]
    exact hcount

/-- `compute_ptc` succeeds at a slot whose epoch has at least `SLOTS_PER_EPOCH` active validators. -/
theorem computePtc_ok [PresetValid] (st : BeaconState) (slot : Slot)
    (hz : ZeroChunksOften Const.ptcSize)
    (hcount : Const.slotsPerEpoch ≤
      (getActiveValidatorIndices (pureState st) (computeEpochAtSlot slot)).size) :
    ∃ r, computePtc (pureState st) slot = .ok r := by
  obtain ⟨hc1, hcn⟩ := committeeCount_mul_le st _ hcount
  have hspe : 2 ≤ Const.slotsPerEpoch := (PresetValid.toFulu (self := ‹_›)).twoLeSlotsPerEpoch
  unfold computePtc
  dsimp only
  -- The slot's first committee is a nonempty slice, so the concatenation is nonempty.
  have hne : 0 < ((Array.range (getCommitteeCountPerSlot (pureState st) (computeEpochAtSlot slot))).foldl
      (fun acc i => acc ++ getBeaconCommittee (pureState st) slot i) (#[] : Array ValidatorIndex)).size := by
    rw [← Array.foldl_toList, Array.toList_range]
    unfold getBeaconCommittee computeCommittee
    dsimp only
    generalize hgc : getCommitteeCountPerSlot (pureState st) (computeEpochAtSlot slot) = c at hc1 hcn ⊢
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    rw [List.range_succ_eq_map, List.foldl_cons]
    refine Nat.lt_of_lt_of_le ?_ (foldl_append_size_ge _ _ _)
    simp only [Array.size_append, Array.size_empty, Nat.zero_add, Array.size_map, Array.size_range]
    generalize (getActiveValidatorIndices (pureState st) (computeEpochAtSlot slot)).size = n at hcn ⊢
    generalize ((slot % UInt64.ofNat Const.slotsPerEpoch).toNat * (k + 1) + 0) = j
    have hcpos : 0 < (k + 1) * Const.slotsPerEpoch := Nat.mul_pos (by omega) (by omega)
    have := div_add_ge_succ (x := n * j) hcpos hcn
    rw [Nat.mul_add, Nat.mul_one]
    omega
  obtain ⟨s, hs⟩ := computeBalanceWeightedSelection_ok st _
    (EthCLLib.Spec.sha (getSeed (pureState st) (computeEpochAtSlot slot) Const.domainPtcAttester ++
      EthCLLib.Spec.uint64ToBytes slot)) Const.ptcSize false hz hne
  rw [hs]
  exact ⟨_, rfl⟩

end

end EthCLSpecs.Proofs.Gloas
