import EthCLSpecs.Proofs.Gloas.Shuffle
import EthCLLib.Proofs.CheckedOps
import EthCLLib.Proofs.CommitteePartition
import EthCLLib.Proofs.IndicesWhere

/-!
# `EthCLSpecs.Proofs.Gloas.Committees`: one epoch's committees partition the active set

Gloas inherits `computeCommittee` (`Gloas/EpochProcessing.lean:137`) and
`getBeaconCommittee` (`Gloas/EpochProcessing.lean:138`) from Fulu. Gloas
therefore elaborates its own constants from the Fulu bodies. These are the Fulu
bridges of `EthCLSpecs.Proofs.Fulu.Committees`, restated for the Gloas
constants. That module docstring gives the hypotheses and their reasons.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError checkedMul checkedAdd throwArithmetic
  liftErr)
open EthCLLib.Proofs
open EthCLSpecs.Gloas (Preset BeaconState ValidatorIndex Bytes32 Epoch Slot
  computeShuffledPermutation computeCommittee getBeaconCommittee
  getActiveValidatorIndices getCommitteeCountPerSlot getSeed
  computeStartSlotAtEpoch computeEpochAtSlot)
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  validatorRegistryLimit domainBeaconAttester shuffleRoundCount maxCommitteesPerSlot)

/-- `compute_committee`: on these bounds the run succeeds, and committee `index` of `count`
is the slice `[len * index / count, len * (index + 1) / count)` of `indices`, read through
this fork's shuffled permutation. -/
@[characterizes EthCLSpecs.Gloas.computeCommittee]
theorem computeCommittee_ok [Preset] [HasherTag] (indices : Array ValidatorIndex)
    (seed : Bytes32) (k c : Nat) (hk : k < c) (hc64 : c < 2 ^ 64)
    (hcap : indices.size * c < 2 ^ 64) (hdom : indices.size ≤ 2 ^ 40)
    (hR : shuffleRoundCount ≤ 256) :
    computeCommittee indices seed k c =
      .ok (committeeSlice indices (swapOrNotArray indices.size shuffleRoundCount seed) k c) := by
  have hk64 : k < 2 ^ 64 := by omega
  have hl64 : indices.size < 2 ^ 64 := by omega
  have hlk1 : indices.size * (k + 1) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hk) hcap
  have hlk : indices.size * k < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_succ k)) hlk1
  have h1 := checkedMul_ok (descr := "compute_committee: len(indices) * index") hl64 hk64 hlk
  have hone : (1 : UInt64) = UInt64.ofNat 1 := rfl
  have h2 := checkedAdd_ok (descr := "compute_committee: index + 1") hk64
    (b := 1) (by decide) (by omega)
  have h3 := checkedMul_ok (descr := "compute_committee: len(indices) * (index + 1)") hl64
    (b := k + 1) (by omega) hlk1
  have hdiv : ∀ x, x < 2 ^ 64 → (UInt64.ofNat x / UInt64.ofNat c).toNat = x / c := by
    intro x hx
    rw [UInt64.toNat_div, toNat_ofNat_lt64 hx, toNat_ofNat_lt64 hc64]
  have hc0 : (c == 0) = false := by simp; omega
  have hstop : indices.size * (k + 1) / c ≤ indices.size :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm c]; exact Nat.mul_le_mul_left _ hk)
  unfold computeCommittee committeeSlice
  simp only [show ¬ (2 ^ 64 ≤ k ∨ 2 ^ 64 ≤ c) by omega, ↓reduceIte, h1, hc0,
    Bool.false_eq_true, hone, h2, h3, bind, Except.bind, pure, Except.pure, hdiv _ hlk,
    hdiv _ hlk1]
  by_cases hst : indices.size * (k + 1) / c ≤ indices.size * k / c
  · simp [hst, Nat.sub_eq_zero_of_le hst]
  · have hstart : indices.size * k / c < indices.size :=
      Nat.lt_of_lt_of_le (Nat.lt_of_not_le hst) hstop
    have hpos : 0 < indices.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hstart
    simp only [hst, ↓reduceIte, hstart, hstop,
      computeShuffledPermutation_ok seed hpos hdom hR]

/-- On the bounds of `computeCommittee_ok`, committees `0 … count-1`, laid end to end, are a
permutation of `indices`. The committees are named through `cs`. -/
theorem computeCommittee_partition [Preset] [HasherTag] (indices : Array ValidatorIndex)
    (seed : Bytes32) (c : Nat) (hc : 0 < c) (hc64 : c < 2 ^ 64)
    (hcap : indices.size * c < 2 ^ 64) (hdom : indices.size ≤ 2 ^ 40)
    (hR : shuffleRoundCount ≤ 256) (cs : Nat → Array ValidatorIndex)
    (hcs : ∀ k, k < c → computeCommittee indices seed k c = .ok (cs k)) :
    ((List.range c).flatMap (fun k => (cs k).toList)).Perm indices.toList := by
  have heq : ∀ k ∈ List.range c, (cs k).toList =
      (committeeSlice indices (swapOrNotArray indices.size shuffleRoundCount seed) k c).toList :=
    fun k hk => by
      have h := (hcs k (List.mem_range.mp hk)).symm.trans
        (computeCommittee_ok indices seed k c (List.mem_range.mp hk) hc64 hcap hdom hR)
      rw [Except.ok.inj h]
  rw [flatMap_congr_mem heq]
  exact committeeSlice_partition indices _ c hc _ (shuffleNat_perm _ _)
    (fun p hp => (swapOrNotArray_spec seed (by omega) _).2 p hp)

/-- The active set fits the shuffle's bound. -/
theorem getActiveValidatorIndices_size_le [Preset] [HasherTag] (state : BeaconState)
    (e : Epoch) (hlim : validatorRegistryLimit ≤ 2 ^ 40) :
    (getActiveValidatorIndices (pureState state) e).size ≤ 2 ^ 40 := by
  unfold getActiveValidatorIndices
  exact Nat.le_trans (indicesWhere_size_le _ _)
    (Nat.le_trans state.validators.property hlim)

/-- The active set has no duplicate index. -/
theorem getActiveValidatorIndices_nodup [Preset] [HasherTag] (state : BeaconState)
    (e : Epoch) (hlim : validatorRegistryLimit ≤ 2 ^ 40) :
    (getActiveValidatorIndices (pureState state) e).toList.Nodup := by
  unfold getActiveValidatorIndices
  exact indicesWhere_nodup _ _ (Nat.le_trans
    (Nat.le_trans state.validators.property hlim) (by decide))

/-- At least one committee per slot. -/
theorem getCommitteeCountPerSlot_pos [Preset] [HasherTag] (state : BeaconState)
    (e : Epoch) : 0 < getCommitteeCountPerSlot (pureState state) e := by
  unfold getCommitteeCountPerSlot
  exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

/-- At most `MAX_COMMITTEES_PER_SLOT + 1` committees per slot. -/
theorem getCommitteeCountPerSlot_le [Preset] [HasherTag] (state : BeaconState)
    (e : Epoch) : getCommitteeCountPerSlot (pureState state) e ≤ maxCommitteesPerSlot + 1 := by
  unfold getCommitteeCountPerSlot
  exact Nat.max_le.mpr ⟨by omega, Nat.le_trans (Nat.min_le_left _ _) (by omega)⟩

/-- A start slot that `compute_start_slot_at_epoch` returns is the product
`e * SLOTS_PER_EPOCH`. -/
theorem computeStartSlotAtEpoch_ok_eq [Preset] {e start : Epoch}
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start) :
    start = e * UInt64.ofNat slotsPerEpoch := by
  simp only [computeStartSlotAtEpoch, checkedMul] at hstart
  split at hstart
  · simp [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept] at hstart
  · exact (Except.ok.inj hstart).symm

/-- The committee at slot `compute_start_slot_at_epoch(e) + j`, index `idx`, is committee
`j * cps + idx` of the epoch's `cps * SLOTS_PER_EPOCH`. -/
theorem getBeaconCommittee_epochSlot [Preset] [HasherTag] (state : BeaconState) (e : Epoch)
    (start : Slot)
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start)
    (hcap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23)
    (j idx : Nat) (hj : j < slotsPerEpoch)
    (hidx : idx < getCommitteeCountPerSlot (pureState state) e)
    (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64) :
    getBeaconCommittee (pureState state) (start + UInt64.ofNat j) idx =
      computeCommittee (getActiveValidatorIndices (pureState state) e)
        (getSeed (pureState state) e domainBeaconAttester)
        (j * getCommitteeCountPerSlot (pureState state) e + idx)
        (getCommitteeCountPerSlot (pureState state) e * slotsPerEpoch) := by
  rw [computeStartSlotAtEpoch_ok_eq hstart]
  generalize hcps : getCommitteeCountPerSlot (pureState state) e = cps at hidx ⊢
  have hcpsle : cps ≤ maxCommitteesPerSlot + 1 := hcps ▸ getCommitteeCountPerSlot_le state e
  have hcspe : cps * slotsPerEpoch ≤ 2 ^ 23 :=
    Nat.le_trans (Nat.mul_le_mul_right _ hcpsle) hcap
  have hnum : j * cps + idx < slotsPerEpoch * cps :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hidx _)
      (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj)
  have hnum' : j * cps + idx < 2 ^ 23 :=
    Nat.lt_of_lt_of_le hnum (by rw [Nat.mul_comm]; exact hcspe)
  have hnum64 : j * cps + idx < 2 ^ 64 := Nat.lt_trans hnum' (by decide)
  have hjc : j * cps < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hnum64
  have hj64 : j < 2 ^ 64 := Nat.lt_trans hj slotsPerEpochLt
  have hidx64 : idx < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hnum64
  have hcs64 : cps * slotsPerEpoch < 2 ^ 64 := Nat.lt_of_le_of_lt hcspe (by decide)
  have hcps64 : cps < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right cps slotsPerEpochPos) hcs64
  have hmod : (e * UInt64.ofNat slotsPerEpoch + UInt64.ofNat j) % UInt64.ofNat slotsPerEpoch
      = UInt64.ofNat j := by
    apply UInt64.toNat_inj.mp
    rw [epochSlot_mod hj slotsPerEpochLt hov, toNat_ofNat_lt64 hj64]
  unfold getBeaconCommittee
  simp only [computeEpochAtSlot, epochSlot_div hj slotsPerEpochLt hov, hcps, hmod,
    show ¬ 2 ^ 64 ≤ idx by omega, ↓reduceIte,
    checkedMul_ok (a := j) (b := cps) hj64 hcps64 hjc,
    checkedAdd_ok (a := j * cps) (b := idx) hjc hidx64 hnum64,
    checkedMul_ok (a := cps) (b := slotsPerEpoch) hcps64 slotsPerEpochLt hcs64,
    bind, Except.bind, pure, Except.pure, toNat_ofNat_lt64 hnum64, toNat_ofNat_lt64 hcs64]

/-- `get_beacon_committee`: every committee of the epoch succeeds, and it is slice
`j * cps + idx` of the shuffled active set. -/
@[characterizes EthCLSpecs.Gloas.getBeaconCommittee]
theorem getBeaconCommittee_ok [Preset] [HasherTag] (state : BeaconState) (e : Epoch)
    (start : Slot)
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start)
    (hlim : validatorRegistryLimit ≤ 2 ^ 40) (hR : shuffleRoundCount ≤ 256)
    (hcap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23)
    (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64)
    (j idx : Nat) (hj : j < slotsPerEpoch)
    (hidx : idx < getCommitteeCountPerSlot (pureState state) e) :
    getBeaconCommittee (pureState state) (start + UInt64.ofNat j) idx =
      .ok (committeeSlice (getActiveValidatorIndices (pureState state) e)
        (swapOrNotArray (getActiveValidatorIndices (pureState state) e).size shuffleRoundCount
          (getSeed (pureState state) e domainBeaconAttester))
        (j * getCommitteeCountPerSlot (pureState state) e + idx)
        (getCommitteeCountPerSlot (pureState state) e * slotsPerEpoch)) := by
  rw [getBeaconCommittee_epochSlot state e start hstart hcap j idx hj hidx hov]
  have hsize := getActiveValidatorIndices_size_le state e hlim
  have hcspe : getCommitteeCountPerSlot (pureState state) e * slotsPerEpoch ≤ 2 ^ 23 :=
    Nat.le_trans (Nat.mul_le_mul_right _ (getCommitteeCountPerSlot_le state e)) hcap
  have hnum : j * getCommitteeCountPerSlot (pureState state) e + idx <
      getCommitteeCountPerSlot (pureState state) e * slotsPerEpoch := by
    rw [Nat.mul_comm _ slotsPerEpoch]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hidx _)
      (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj)
  have hprod : (getActiveValidatorIndices (pureState state) e).size *
      (getCommitteeCountPerSlot (pureState state) e * slotsPerEpoch) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hsize hcspe) (by decide)
  exact computeCommittee_ok _ _ _ _ hnum (by omega) hprod hsize hR

/-- The committees `committees j idx` of the epoch are the `.ok` results of
`get_beacon_committee`. -/
abbrev EpochCommitteesOf [Preset] [HasherTag] (state : BeaconState) (start : Slot) (e : Epoch)
    (committees : Nat → Nat → Array ValidatorIndex) : Prop :=
  ∀ j, j < slotsPerEpoch → ∀ idx, idx < getCommitteeCountPerSlot (pureState state) e →
    getBeaconCommittee (pureState state) (start + UInt64.ofNat j) idx = .ok (committees j idx)

/-- Each committee of `EpochCommitteesOf` is its slice. -/
private theorem committees_eq_slice [Preset] [HasherTag] {state : BeaconState} {e : Epoch}
    {start : Slot}
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start)
    (hlim : validatorRegistryLimit ≤ 2 ^ 40) (hR : shuffleRoundCount ≤ 256)
    (hcap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23)
    (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64)
    {committees : Nat → Nat → Array ValidatorIndex}
    (hcomm : EpochCommitteesOf state start e committees) :
    ∀ j, j < slotsPerEpoch → ∀ idx, idx < getCommitteeCountPerSlot (pureState state) e →
      committees j idx = committeeSlice (getActiveValidatorIndices (pureState state) e)
        (swapOrNotArray (getActiveValidatorIndices (pureState state) e).size shuffleRoundCount
          (getSeed (pureState state) e domainBeaconAttester))
        (j * getCommitteeCountPerSlot (pureState state) e + idx)
        (getCommitteeCountPerSlot (pureState state) e * slotsPerEpoch) :=
  fun j hj idx hidx => Except.ok.inj ((hcomm j hj idx hidx).symm.trans
    (getBeaconCommittee_ok state e start hstart hlim hR hcap hov j idx hj hidx))

/-- `get_beacon_committee`: over one epoch, the committees for every slot and committee
index are a permutation of the active set. -/
theorem getBeaconCommittee_partition [Preset] [HasherTag] (state : BeaconState) (e : Epoch)
    (start : Slot)
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start)
    (hlim : validatorRegistryLimit ≤ 2 ^ 40) (hR : shuffleRoundCount ≤ 256)
    (hcap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23)
    (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64)
    (committees : Nat → Nat → Array ValidatorIndex)
    (hcomm : EpochCommitteesOf state start e committees) :
    ((List.range slotsPerEpoch).flatMap (fun j =>
        (List.range (getCommitteeCountPerSlot (pureState state) e)).flatMap (fun idx =>
          (committees j idx).toList))).Perm
      (getActiveValidatorIndices (pureState state) e).toList :=
  epoch_partition _ _ _ _ slotsPerEpochPos (getCommitteeCountPerSlot_pos state e) _
    (shuffleNat_perm _ _)
    (fun _ hp => (swapOrNotArray_spec _ (by
      have := getActiveValidatorIndices_size_le state e hlim; omega) _).2 _ hp)
    _ (committees_eq_slice hstart hlim hR hcap hov hcomm)

/-- No validator sits in two committees of the epoch, or twice in one. -/
theorem getBeaconCommittee_nodup [Preset] [HasherTag] (state : BeaconState) (e : Epoch)
    (start : Slot)
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start)
    (hlim : validatorRegistryLimit ≤ 2 ^ 40) (hR : shuffleRoundCount ≤ 256)
    (hcap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23)
    (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64)
    (committees : Nat → Nat → Array ValidatorIndex)
    (hcomm : EpochCommitteesOf state start e committees) :
    ((List.range slotsPerEpoch).flatMap (fun j =>
        (List.range (getCommitteeCountPerSlot (pureState state) e)).flatMap (fun idx =>
          (committees j idx).toList))).Nodup :=
  (getBeaconCommittee_partition state e start hstart hlim hR hcap hov committees
    hcomm).nodup_iff.mpr (getActiveValidatorIndices_nodup state e hlim)

/-- Every active validator sits in some committee of the epoch. -/
theorem getBeaconCommittee_covers [Preset] [HasherTag] (state : BeaconState) (e : Epoch)
    (start : Slot)
    (hstart : (computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok start)
    (hlim : validatorRegistryLimit ≤ 2 ^ 40) (hR : shuffleRoundCount ≤ 256)
    (hcap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23)
    (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64)
    (committees : Nat → Nat → Array ValidatorIndex)
    (hcomm : EpochCommitteesOf state start e committees)
    (v : ValidatorIndex) (hv : v ∈ (getActiveValidatorIndices (pureState state) e).toList) :
    ∃ j, j < slotsPerEpoch ∧ ∃ idx, idx < getCommitteeCountPerSlot (pureState state) e ∧
      v ∈ (committees j idx).toList := by
  simpa only [List.mem_flatMap, List.mem_range] using
    (getBeaconCommittee_partition state e start hstart hlim hR hcap hov committees
      hcomm).mem_iff.mpr hv

end EthCLSpecs.Proofs.Gloas
