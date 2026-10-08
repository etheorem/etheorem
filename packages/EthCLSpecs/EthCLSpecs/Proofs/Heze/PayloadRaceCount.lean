import EthCLSpecs.Proofs.Heze.PayloadRaceExec
import EthCLSpecs.Proofs.Heze.PayloadRaceBounds
import EthCLSpecs.Proofs.Heze.Committees

/-!
# `EthCLSpecs.Proofs.Heze.PayloadRaceCount`: the count of the race from the committees

`race_empty_persists_exec` takes a counting inequality over the validators of the justified
state `jst`. This module derives it from the committees of the window.

A validator votes in slot `t` when it is in a committee of slot `t` (`committeeVotes`).
`RaceCommittees` states three conditions:

- Each validator votes in at most one slot of the window (`OneVoteIn`). For a window inside
  one epoch, the committee partition of `getBeaconCommittee` gives this
  (`EpochCommittees.oneVoteIn`).
- In the committee of the first slot, the honest balance is more than the adversarial balance
  plus the proposer score `proposerScoreOf jst`.
- In each later committee, the honest balance is at least the adversarial balance.

`RaceCommittees.count` gives the inequality (`count_of_slots`).

`EpochCommittees` states that the window lies inside one epoch `e` and that its committees
are the `.ok` committees of a plain state `st` at `e`. A validator then sits in at most one
committee of the epoch (`getBeaconCommittee_nodup`, `Committees.lean`), so it votes in at
most one slot. The bounds of `getBeaconCommittee_ok` and `getBeaconCommittee_nodup` are
fields of `EpochCommittees`: three preset bounds, the size of the active set of `st` at `e`
below which the shuffle does not raise, the registry bound that keeps the indices distinct,
and the bound on `e` below which `get_seed` does not raise.
`RaceCommittees.of_epoch` builds `RaceCommittees` from `EpochCommittees` and the two
balance conditions.
`raceCommittees_first_of_fraction` gives the first-slot condition from more than 70 % honest
balance in that committee. It needs a committee balance of at least the committee weight of
`jst`. That is the uniform-committee premise of `PayloadRaceBounds.lean`, for the one slot
that needs it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (pureState epochSlot_toNat epochSlot_div toNat_ofNat_lt64
  flatMap_nodup_block_eq committeeSlice swapOrNotArray)
open EthCLSpecs.Heze (Preset Config State BeaconState Epoch Slot ValidatorIndex
  computeEpochAtSlot computeStartSlotAtEpoch getBeaconCommittee committeeCountOf
  activeValidatorIndicesOf seedOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt
  shuffleRoundCount maxCommitteesPerSlot domainBeaconAttester minSeedLookahead
  epochsPerHistoricalVector)
open EthCLSpecs.Proofs.Heze.PayloadRace (slotBalance OneVoteIn count_of_slots first_of_fraction
  advVoted honestVoted)

section Count
variable [Preset] [HasherTag] [Config]

/-- The validators of the race: the active unslashed validators of `jst`, each with its
honesty flag and the slots of its committees. The score reads the uncached box of `jst`. -/
noncomputable abbrev raceVs (jst : BeaconState) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) : List PayloadRace.Validator :=
  raceValidators (pureState jst) honestOf (committeeVotes committees)

/-- The committees of the vote slots `[lo, hi)`, against the validators of the justified
state `jst`. Each validator votes in at most one of these slots. The first committee beats
the proposer score. Each later committee has at least as much honest as adversarial
balance. -/
structure RaceCommittees (jst : BeaconState) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) (lo hi : Nat) : Prop where
  /-- Each validator votes in at most one slot of `[lo, hi)`. -/
  one : OneVoteIn (raceVs jst honestOf committees) lo hi
  /-- The first committee beats the proposer score. -/
  first : slotBalance (raceVs jst honestOf committees) false lo + proposerScoreOf (pureState jst)
    < slotBalance (raceVs jst honestOf committees) true lo
  /-- Each later committee has at least as much honest as adversarial balance. -/
  later : ∀ t, lo < t → t < hi →
    slotBalance (raceVs jst honestOf committees) false t
      ≤ slotBalance (raceVs jst honestOf committees) true t

/-- `RaceCommittees` gives the counting inequality of `race_empty_persists_exec`. -/
theorem RaceCommittees.count {jst : BeaconState} {honestOf : ValidatorIndex → Bool}
    {committees : Nat → Nat → Array ValidatorIndex} {lo hi : Nat}
    (h : RaceCommittees jst honestOf committees lo hi) :
    ∀ s, lo < s → s ≤ hi →
      advVoted (raceVs jst honestOf committees) lo s + proposerScoreOf (pureState jst)
        < honestVoted (raceVs jst honestOf committees) lo s :=
  count_of_slots _ lo hi _ h.one h.first h.later

/-- The first-slot condition of `RaceCommittees` from more than 70 % honest balance in the
committee of `lo`. The committee weight of `jst` reads as `w` (`committeeWeightOf`, the
unslashed active balance over `SLOTS_PER_EPOCH`), the committee balance is at least `w`, and
the boost cast is at most `40`. -/
theorem raceCommittees_first_of_fraction (jst : BeaconState) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) (lo : Nat)
    (hpsb : (UInt64.ofNat EthCLSpecs.Heze.Const.proposerScoreBoost).toNat ≤ 40)
    (w : EthCLSpecs.Heze.Gwei) (hw : committeeWeightOf (pureState jst) = .ok w)
    (hcw : w.toNat ≤
      slotBalance (raceVs jst honestOf committees) true lo +
        slotBalance (raceVs jst honestOf committees) false lo)
    (h70 : 70 * (slotBalance (raceVs jst honestOf committees) true lo +
        slotBalance (raceVs jst honestOf committees) false lo)
      < 100 * slotBalance (raceVs jst honestOf committees) true lo) :
    slotBalance (raceVs jst honestOf committees) false lo + proposerScoreOf (pureState jst)
      < slotBalance (raceVs jst honestOf committees) true lo := by
  have hle := proposerScoreOf_le jst w hw
  have := first_of_fraction _ _ _ _ hpsb hcw h70
  omega

/-! ## One vote per validator from one epoch's committees -/

/-- The committees of the vote slots `[lo, hi)` are those of the plain state `st`, and the
window lies inside the epoch `e`. Each slot has the first `get_committee_count_per_slot`
committees of `st`, and none above. The last slot of `e` fits in `uint64`. The active-set
bound, the registry bound, the three preset bounds and the seed bound are the premises of
`getBeaconCommittee_ok` and `getBeaconCommittee_nodup`. -/
structure EpochCommittees (committees : Nat → Nat → Array ValidatorIndex) (st : BeaconState)
    (e : Epoch) (lo hi : Nat) : Prop where
  /-- The window starts in `e`. -/
  start : e.toNat * slotsPerEpoch ≤ lo
  /-- The window ends in `e`. -/
  stop : hi ≤ (e.toNat + 1) * slotsPerEpoch
  /-- The last slot of `e` fits in `uint64`. -/
  fits : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64
  /-- The active set of `st` at `e` is inside the domain of the shuffle. Above `2 ^ 40`,
  `compute_shuffled_permutation` overflows `Uint32(position_bucket)` and raises. -/
  active : (activeValidatorIndicesOf (pureState st) e).size ≤ 2 ^ 40
  /-- The registry of `st` has at most `2 ^ 64` entries. Every index then fits the
  `ValidatorIndex(index)` cast, so the active-index walk and the committee count do not raise,
  and the indices are distinct `uint64` values. -/
  indices : st.validators.val.size ≤ 2 ^ 64
  /-- The shuffle round count is inside the domain of the shuffle. -/
  rounds : shuffleRoundCount ≤ 256
  /-- The committee count of the epoch fits the checked products of `compute_committee`. -/
  cap : (maxCommitteesPerSlot + 1) * slotsPerEpoch ≤ 2 ^ 23
  /-- The randao-mix vector is longer than `MIN_SEED_LOOKAHEAD`, so `get_seed`'s subtractions
  cannot underflow. -/
  lookahead : minSeedLookahead.toNat + 1 ≤ epochsPerHistoricalVector
  /-- `e + EPOCHS_PER_HISTORICAL_VECTOR` fits in `uint64`, so `get_seed` does not raise. -/
  seed : e.toNat + epochsPerHistoricalVector < 2 ^ 64
  /-- Below the count, each committee of a window slot is the `.ok` value of
  `getBeaconCommittee` on `st`. Above the count, the committee is empty. -/
  eq : ∀ t, lo ≤ t → t < hi → ∀ ci,
    if ci < committeeCountOf (pureState st) (computeEpochAtSlot (UInt64.ofNat t)) then
      getBeaconCommittee (pureState st) (UInt64.ofNat t) ci = .ok (committees t ci)
    else committees t ci = #[]

/-- The committees of the epoch `e` of `st`, as the slices of `getBeaconCommittee_ok`. Slot
`j` of the epoch, index `idx`, is slice `j * cps + idx` of the shuffled active set. -/
abbrev epochSlices (st : BeaconState) (e : Epoch) (j idx : Nat) :
    Array ValidatorIndex :=
  committeeSlice (activeValidatorIndicesOf (pureState st) e)
    (swapOrNotArray (activeValidatorIndicesOf (pureState st) e).size shuffleRoundCount
      (seedOf (pureState st) e domainBeaconAttester))
    (j * committeeCountOf (pureState st) e + idx)
    (committeeCountOf (pureState st) e * slotsPerEpoch)

omit [HasherTag] [Config] in
/-- When the last slot of `e` fits in `uint64`, so does its first slot, the bound of
`computeStartSlotAtEpoch_ok_of_lt`. -/
private theorem start_lt_of_fits {e : Epoch} (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64) :
    e.toNat * slotsPerEpoch < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (by rw [Nat.succ_mul]; exact Nat.lt_add_of_pos_right slotsPerEpochPos) hov

omit [HasherTag] [Config] in
/-- A slot `t` of the epoch `e` is slot `t - e * SLOTS_PER_EPOCH` of the epoch, in the form
`start + j` of `getBeaconCommittee_nodup`, with `start = e * SLOTS_PER_EPOCH`. -/
private theorem slot_eq_epochSlot {e : Epoch} {t : Nat} (h1 : e.toNat * slotsPerEpoch ≤ t)
    (h2 : t < (e.toNat + 1) * slotsPerEpoch) (hov : (e.toNat + 1) * slotsPerEpoch ≤ 2 ^ 64) :
    UInt64.ofNat t =
      e * UInt64.ofNat slotsPerEpoch + UInt64.ofNat (t - e.toNat * slotsPerEpoch) := by
  have hj : t - e.toNat * slotsPerEpoch < slotsPerEpoch := by rw [Nat.succ_mul] at h2; omega
  apply UInt64.toNat_inj.mp
  rw [toNat_ofNat_lt64 (by omega), epochSlot_toNat hj slotsPerEpochLt hov]
  omega

omit [Config] in
/-- The slices of `epochSlices` are the `.ok` committees of the epoch. -/
private theorem EpochCommittees.epochCommitteesOf {committees : Nat → Nat → Array ValidatorIndex}
    {st : BeaconState} {e : Epoch} {lo hi : Nat} (h : EpochCommittees committees st e lo hi) :
    EpochCommitteesOf st (e * UInt64.ofNat slotsPerEpoch) e (epochSlices st e) :=
  fun j hj idx hidx => getBeaconCommittee_ok st e _
    (computeStartSlotAtEpoch_ok_of_lt (start_lt_of_fits h.fits)) h.active h.indices h.rounds h.cap
    h.fits
    h.lookahead h.seed j idx hj hidx

omit [Config] in
/-- A vote of a window slot `s` puts the validator in a committee of slot
`s - e * SLOTS_PER_EPOCH` of the epoch `e`. -/
private theorem EpochCommittees.mem_epochSlot {committees : Nat → Nat → Array ValidatorIndex}
    {st : BeaconState} {e : Epoch} {lo hi : Nat} (h : EpochCommittees committees st e lo hi)
    (i : ValidatorIndex) (s : Nat) (hs1 : lo ≤ s) (hs2 : s < hi)
    (hvs : committeeVotes committees i s = true) :
    ∃ j, j < slotsPerEpoch ∧ s = e.toNat * slotsPerEpoch + j ∧
      i ∈ (List.range (committeeCountOf (pureState st) e)).flatMap fun idx =>
        (epochSlices st e j idx).toList := by
  have h1 : e.toNat * slotsPerEpoch ≤ s := Nat.le_trans h.start hs1
  have h2 : s < (e.toNat + 1) * slotsPerEpoch := Nat.lt_of_lt_of_le hs2 h.stop
  have hj : s - e.toNat * slotsPerEpoch < slotsPerEpoch := by rw [Nat.succ_mul] at h2; omega
  have hslot := slot_eq_epochSlot h1 h2 h.fits
  have hepoch : computeEpochAtSlot (UInt64.ofNat s) = e := by
    rw [hslot]
    simp only [computeEpochAtSlot]
    exact epochSlot_div hj slotsPerEpochLt h.fits
  simp only [committeeVotes, decide_eq_true_eq] at hvs
  obtain ⟨ci, hci⟩ := hvs
  have heq := h.eq s hs1 hs2 ci
  rw [hepoch] at heq
  split at heq
  · rename_i hlt
    -- The window committee and the epoch slice are the same `.ok` value.
    have hsl : committees s ci = epochSlices st e (s - e.toNat * slotsPerEpoch) ci := by
      rw [hslot] at heq
      exact Except.ok.inj (heq.symm.trans (h.epochCommitteesOf _ hj ci hlt))
    refine ⟨_, hj, by omega, List.mem_flatMap.mpr ⟨ci, List.mem_range.mpr hlt, ?_⟩⟩
    rw [← hsl]
    exact Array.mem_toList_iff.mpr hci
  · rw [heq] at hci
    simp at hci

omit [Config] in
/-- Each validator votes in at most one slot of a window inside one epoch. A vote of slot `t`
puts the validator in a committee of slot `t` (`committeeVotes`), and no validator sits in
committees of two slots of the epoch (`getBeaconCommittee_nodup`). -/
theorem EpochCommittees.oneVoteIn {committees : Nat → Nat → Array ValidatorIndex}
    {st : BeaconState} {e : Epoch} {lo hi : Nat} (h : EpochCommittees committees st e lo hi)
    (jst : BeaconState) (honestOf : ValidatorIndex → Bool) :
    OneVoteIn (raceVs jst honestOf committees) lo hi := by
  intro v hv t t' hlo hhi hlo' hhi' hvt hvt'
  obtain ⟨i, -, -, rfl⟩ := mem_raceValidators jst honestOf _ v hv
  obtain ⟨j, hj, rfl, hm⟩ := h.mem_epochSlot i t hlo hhi hvt
  obtain ⟨j', hj', rfl, hm'⟩ := h.mem_epochSlot i t' hlo' hhi' hvt'
  have := flatMap_nodup_block_eq (getBeaconCommittee_nodup st e _
      (computeStartSlotAtEpoch_ok_of_lt (start_lt_of_fits h.fits)) h.active h.indices h.rounds
      h.cap h.fits h.lookahead h.seed
      _ h.epochCommitteesOf)
    (List.mem_range.mpr hj) (List.mem_range.mpr hj') hm hm'
  omega

/-- `RaceCommittees` from the committees of one epoch and the two balance conditions. -/
theorem RaceCommittees.of_epoch {jst : BeaconState} {honestOf : ValidatorIndex → Bool}
    {committees : Nat → Nat → Array ValidatorIndex} {st : BeaconState} {e : Epoch} {lo hi : Nat}
    (hep : EpochCommittees committees st e lo hi)
    (first : slotBalance (raceVs jst honestOf committees) false lo + proposerScoreOf (pureState jst)
      < slotBalance (raceVs jst honestOf committees) true lo)
    (later : ∀ t, lo < t → t < hi →
      slotBalance (raceVs jst honestOf committees) false t
        ≤ slotBalance (raceVs jst honestOf committees) true t) :
    RaceCommittees jst honestOf committees lo hi :=
  ⟨hep.oneVoteIn jst honestOf, first, later⟩

end Count

end EthCLSpecs.Proofs.Heze
