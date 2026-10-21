import EthCLSpecs.Proofs.Heze.PayloadRaceCount

/-!
# `EthCLSpecs.Proofs.Heze.RaceLong`: the count of the race over several epochs

`race_empty_persists_long` (`PayloadRaceExec.lean`) takes a counting inequality at each slot
`s` of the window, over the validators of the justified state `jstOf s`. `RaceCount` names
that inequality. This module gives it in two ways.

- In the first epoch of the window, `RaceCommittees.count` (`PayloadRaceCount.lean`) gives
  it with one justified state. It needs at most one vote per validator (`OneVoteIn`), which holds
  inside one epoch only.
- After a full epoch of the window, every validator of the epoch's committees has voted
  (`EpochCommittees.votes_of_active`). Then the honest balance that has voted is the honest
  total. So the count follows from a margin of the totals (`count_of_epoch`). This needs no
  bound on the number of votes of a validator. `storeSide_empty` puts an honest validator on
  EMPTY whatever its other votes are.

`hcount_of_parts` joins the two forms at the end of the first part of the window.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (pureState)
open EthCLSpecs.Heze (Preset Config BeaconState Epoch ValidatorIndex getActiveValidatorIndices
  currentEpochOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

namespace PayloadRace

/-! ## The totals of the race -/

/-- The balance of the validators with the honesty flag `honest`, with or without a vote. -/
def sideTotal (vs : List Validator) (honest : Bool) : Nat :=
  balanceSum (vs.filter fun v => v.honest == honest)

/-- The honest balance. -/
abbrev honestTotal (vs : List Validator) : Nat := sideTotal vs true

/-- The adversarial balance. -/
abbrev advTotal (vs : List Validator) : Nat := sideTotal vs false

/-- When every validator has a vote in `[lo, s)`, a margin of the totals gives the counting
inequality. The adversarial balance that has voted is at most the adversarial total. The
honest balance that has voted is the honest total. -/
theorem count_of_all_voted (vs : List Validator) (lo s boost : Nat)
    (hall : ∀ v ∈ vs, votedIn v.votes lo s = true) (hm : advTotal vs + boost < honestTotal vs) :
    advVoted vs lo s + boost < honestVoted vs lo s := by
  unfold advVoted honestVoted votedBalance advTotal honestTotal sideTotal at *
  have h1 := balanceSum_filter_mono vs (fun v => v.honest == false && votedIn v.votes lo s)
    (fun v => v.honest == false) (by
      intro v _ hp
      simp only [Bool.and_eq_true] at hp
      exact hp.1)
  have h2 := balanceSum_filter_mono vs (fun v => v.honest == true)
    (fun v => v.honest == true && votedIn v.votes lo s) (by
      intro v hv hp
      simp [hp, hall v hv])
  omega

end PayloadRace

open EthCLSpecs.Proofs.Heze.PayloadRace (advVoted honestVoted advTotal honestTotal votedIn_iff
  count_of_all_voted)

section Count
variable [Preset] [HasherTag] [Config]

/-- The counting inequality of the race at the slot `s`, for the window from `lo`, over the
validators of the justified state `jst`. The honest balance that has voted in `[lo, s)` is
more than the adversarial balance that has voted there, plus the proposer score of `jst`. -/
noncomputable abbrev RaceCount (jst : BeaconState) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) (lo s : Nat) : Prop :=
  advVoted (raceVs jst honestOf committees) lo s + proposerScoreOf (pureState jst)
    < honestVoted (raceVs jst honestOf committees) lo s

/-- The count after a full epoch `e` of the window. The committees of `e` are those of a
plain state `st`. Every validator of `jst` is active in `st` at `e`. Then every validator of
`jst` has voted in `[lo, s)`, so a margin of the totals gives the count. -/
theorem count_of_epoch {committees : Nat → Nat → Array ValidatorIndex} {st jst : BeaconState}
    {e : Epoch} (honestOf : ValidatorIndex → Bool) {lo s : Nat}
    (hep : EpochCommittees committees st e (e.toNat * slotsPerEpoch)
      ((e.toNat + 1) * slotsPerEpoch))
    (hlo : lo ≤ e.toNat * slotsPerEpoch) (hs : (e.toNat + 1) * slotsPerEpoch ≤ s)
    (hcover : ∀ i ∈ (getActiveValidatorIndices (pureState jst)
        (currentEpochOf (pureState jst))).toList,
      i ∈ (getActiveValidatorIndices (pureState st) e).toList)
    (hmargin : advTotal (raceVs jst honestOf committees) + proposerScoreOf (pureState jst)
      < honestTotal (raceVs jst honestOf committees)) :
    RaceCount jst honestOf committees lo s := by
  refine count_of_all_voted _ lo s _ ?_ hmargin
  intro v hv
  obtain ⟨i, hi, -, rfl⟩ := mem_raceValidators jst honestOf _ v hv
  obtain ⟨t, ht1, ht2, hvote⟩ := hep.votes_of_active i (hcover i hi)
  exact (votedIn_iff _ _ _).mpr ⟨t, by omega, by omega, hvote⟩

/-- The count over the whole window from two parts. At each slot up to and including `b`, the
justified state is `jst` and `RaceCommittees` gives the count. After `b`, a premise gives the
count at each slot. -/
theorem hcount_of_parts {jstOf : Nat → BeaconState} {jst : BeaconState}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {lo b hi : Nat} (hjst : ∀ s, lo < s → s ≤ b → jstOf s = jst)
    (hfirst : RaceCommittees jst honestOf committees lo b)
    (hlater : ∀ s, b < s → s ≤ hi → RaceCount (jstOf s) honestOf committees lo s) :
    ∀ s, lo < s → s ≤ hi → RaceCount (jstOf s) honestOf committees lo s := by
  intro s h1 h2
  by_cases hs : s ≤ b
  · rw [hjst s h1 hs]
    exact hfirst.count s h1 hs
  · exact hlater s (by omega) h2

end Count

end EthCLSpecs.Proofs.Heze
