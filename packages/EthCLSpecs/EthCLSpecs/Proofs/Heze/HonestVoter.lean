import EthCLSpecs.Proofs.Heze.Accountable

/-!
# `EthCLSpecs.Proofs.Heze.HonestVoter`: a justified checkpoint has an honest voter

Take a run from the anchor state `A` and its abstract chain (`ffgChain`). A checkpoint that
the chain justifies after its base came from a link (`Justified.link_of_not_base`). The link
voters hold two thirds of the total of the state that weighs the link epoch (`ChainMatches`).
That state is on a prefix of the run. When the adversary holds less than two thirds there
(`advStake`), some link voter is honest. Its vote is a placed vote of the run with the
checkpoint as its target (`justified_honest_voter`).

## The state that weighs the link

The link epoch `e` is the epoch of the checkpoint or the next one. The run has a weigh state at
`e`, of epoch `e`, or it ends in epoch `e` or before (`ChainRun.weighAt_of_cross`). So the
epoch of that state is at most the epoch of the checkpoint plus one.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLLib.Proofs.FFG (stakeSum)
open EthCLSpecs.Heze (Preset Config BeaconState AttestationData ValidatorIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The adversarial stake of `u`: the link stake of the registry indices that are not
honest. -/
def advStake (u : BeaconState) (honestOf : ValidatorIndex → Bool) : Nat :=
  stakeSum (linkStake u) (regVals.filter fun i => !honestOf i)

omit [Config] [CryptoBackend] in
/-- **The adversary stays below two thirds within the drift.** At `A`, three times the
adversarial stake plus five times `D` is below twice the total active balance. A state `u`
within the drift `D` of `A` over `regVals` has an adversarial stake below two thirds of its
total. The adversarial stake grows by at most the drift of the link stakes
(`stakeSum_le_add_absDiffSum`). The total falls by at most the shortfall term of the drift. -/
theorem advStake_lt_of_drift (honestOf : ValidatorIndex → Bool) {A u : BeaconState} {D : Nat}
    (hmargin : 3 * advStake A honestOf + 5 * D <
      2 * (totBal A).toNat)
    (hdrift : drift regVals A u ≤ D) :
    3 * advStake u honestOf <
      2 * (totBal u).toNat := by
  have h := EthCLLib.Proofs.FFG.stakeSum_le_add_absDiffSum (linkStake u) (linkStake A)
    (fun i => !honestOf i) regVals
  unfold advStake at hmargin ⊢
  unfold drift at hdrift
  omega

/-- **`allChains` from the drift.** When every state of a run from `A` up to epoch `B` stays
within the drift `D` of `A`, the margin at `A` gives the stake premise of the finality
theorems on every such state. -/
theorem allChains_of_drift (honestOf : ValidatorIndex → Bool) {A : BeaconState} {B D : Nat}
    (hmargin : 3 * advStake A honestOf + 5 * D <
      2 * (totBal A).toNat)
    (hdrift : ∀ steps u, ChainRun (2 ^ 64 - 1) steps A u → epochOf u ≤ B →
      drift regVals A u ≤ D) :
    ∀ steps u, ChainRun (2 ^ 64 - 1) steps A u → epochOf u ≤ B →
      3 * advStake u honestOf <
        2 * (totBal u).toNat :=
  fun steps u hrun hB => advStake_lt_of_drift honestOf hmargin (hdrift steps u hrun hB)

/-- The state that weighs epoch `e` on a run from `A` is on a prefix of the run. Its epoch is at
most `e`, when the anchor epoch is below `e`. -/
theorem stakeState_prefix {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) {e : Nat} (hA : epochOf A < e) :
    ∃ (p q : List ChainStep) (u : BeaconState), steps = p ++ q ∧
      stakeState (2 ^ 64 - 1) steps A e = some u ∧ ChainRun (2 ^ 64 - 1) p A u ∧ epochOf u ≤ e := by
  have hhi : (2 ^ 64 - 1 : Nat) ≤ 2 ^ 64 - 1 := Nat.le_refl _
  by_cases hw : ∃ u, WeighAt (2 ^ 64 - 1) steps A e u
  · obtain ⟨u, hu⟩ := hw
    obtain ⟨s₁, s₂, hs, hr, -, he⟩ := id hu
    exact ⟨s₁, .slot :: s₂, u, hs, stakeState_of_weigh hhi hu, hr, Nat.le_of_eq he⟩
  · refine ⟨steps, [], v, (List.append_nil _).symm,
      stakeState_of_end hrun fun u hu => hw ⟨u, hu⟩, hrun, ?_⟩
    -- A run past the end of `e` has a weigh state at `e`.
    refine Nat.le_of_not_lt fun hlt => hw ?_
    have hp := slotsPerEpochPos
    refine hrun.weighAt_of_cross hhi e ?_ ?_
    · have h1 := Nat.lt_mul_div_succ A.slot.toNat hp
      have h2 : (A.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤ (e + 1) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by unfold epochOf at hA; omega)
      rw [Nat.mul_comm] at h1
      omega
    · have h1 := Nat.div_mul_le_self v.slot.toNat slotsPerEpoch
      have h2 : (e + 1) * slotsPerEpoch ≤ (v.slot.toNat / slotsPerEpoch) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by unfold epochOf at hlt; omega)
      omega

/-- **A justified checkpoint past the base has an honest voter.** Take a run from `A` and a
checkpoint `x` that its chain justifies, past `anchorK A`, with `x.epoch + 1 ≤ B`. On every
prefix of the run up to epoch `B`, the adversary holds less than two thirds of the total
active balance. Then an honest validator has a placed vote of the run with the target `x`. -/
theorem justified_honest_voter {steps : List ChainStep} {A v : BeaconState}
    (hrun : ChainRun (2 ^ 64 - 1) steps A v) (hcps : AnchorCps A) (hord : StateCkptOrd A)
    (honestOf : ValidatorIndex → Bool) {B : Nat}
    (hall : ∀ p q u, steps = p ++ q → ChainRun (2 ^ 64 - 1) p A u → epochOf u ≤ B →
      3 * advStake u honestOf < 2 * (totBal u).toNat)
    {x : Cp} (hj : EthCLLib.Proofs.FFG.Justified (ffgChain (2 ^ 64 - 1) steps A regVals) x)
    (hx : anchorK A < x.epoch) (hxB : x.epoch + 1 ≤ B) :
    ∃ (i : ValidatorIndex) (d : AttestationData), honestOf i = true ∧
      RunVote (2 ^ 64 - 1) A steps i d ∧ toCp d.target = x := by
  have hhi : (2 ^ 64 - 1 : Nat) ≤ 2 ^ 64 - 1 := Nat.le_refl _
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hcps hord
    (hrun.blocks_slot_ge hhi)
  -- `x` is past the base, so a link reaches it.
  have hnb : x ∉ (ffgChain (2 ^ 64 - 1) steps A regVals).base := fun h => by
    have := (hm.base x h).1
    omega
  obtain ⟨s, -, -, -, -, e, he1, he2, hstake⟩ := hj.link_of_not_base hnb
  have hK : epochOf A < anchorK A := by unfold anchorK; omega
  obtain ⟨p, q, u, hpq, hu, hpu, heu⟩ := stakeState_prefix hrun (e := e) (by omega)
  obtain ⟨htot, hst⟩ := hm.stake e u hu
  have hadv := hall p q u hpq hpu (by omega)
  rw [htot] at hstake
  -- Some link voter is honest: the voters outweigh the adversary.
  have hvoters : ∃ i ∈ EthCLLib.Proofs.FFG.linkVoters (ffgChain (2 ^ 64 - 1) steps A regVals) s x,
      honestOf i = true := by
    refine Classical.byContradiction fun hno => ?_
    have hsub : ∀ i ∈ EthCLLib.Proofs.FFG.linkVoters (ffgChain (2 ^ 64 - 1) steps A regVals) s x,
        i ∈ regVals.filter fun i => !honestOf i := by
      intro i hi
      have hreg : i ∈ regVals := (List.mem_filter.mp hi).1
      refine List.mem_filter.mpr ⟨hreg, ?_⟩
      cases hh : honestOf i
      · rfl
      · exact absurd ⟨i, hi, hh⟩ hno
    have hnd : (EthCLLib.Proofs.FFG.linkVoters (ffgChain (2 ^ 64 - 1) steps A regVals) s x).Nodup :=
      regVals_nodup.filter _
    have hle := sum_map_le_of_subset (linkStake u) _ _ hnd hsub
    have heq : stakeSum ((ffgChain (2 ^ 64 - 1) steps A regVals).stake e)
        (EthCLLib.Proofs.FFG.linkVoters (ffgChain (2 ^ 64 - 1) steps A regVals) s x) =
        stakeSum (linkStake u)
          (EthCLLib.Proofs.FFG.linkVoters (ffgChain (2 ^ 64 - 1) steps A regVals) s x) := by
      unfold stakeSum
      exact congrArg List.sum (List.map_congr_left fun i _ => hst i)
    unfold advStake stakeSum at hadv
    unfold stakeSum at heq hstake
    omega
  obtain ⟨i, hi, hhon⟩ := hvoters
  -- The honest voter has a vote of the chain from `s` to `x`.
  have hvoted := (List.mem_filter.mp hi).2
  unfold EthCLLib.Proofs.FFG.voted at hvoted
  obtain ⟨y, hy, hyd⟩ := List.any_eq_true.mp hvoted
  obtain ⟨hyi, -, hyx⟩ := of_decide_eq_true hyd
  obtain ⟨-, d, hd, -, hdt⟩ := (hm.votes y).mp hy
  rw [hyi] at hd
  exact ⟨i, d, hhon, hd, hdt.symm.trans hyx⟩

end

end EthCLSpecs.Proofs.Heze
