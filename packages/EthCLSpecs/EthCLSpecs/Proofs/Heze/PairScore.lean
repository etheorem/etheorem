import EthCLSpecs.Proofs.Heze.AncestorAny
import EthCLSpecs.Proofs.Heze.PayloadRaceExec

/-!
# `EthCLSpecs.Proofs.Heze.PairScore`: the score of two sibling nodes is a race weight

`PayloadRaceRefines.lean` ties the scores of EMPTY and FULL `r` to the abstract race weight of
`PayloadRace.lean`. The `getHead` walk compares every pair of viable children of a node. This
module ties the scores of any two distinct children `a` and `z` of one node to the same
abstract weight. `pairSide` puts an index on `full` when it supports `z` and on `empty` when it
supports `a`. No index supports both (`supportsVal_siblings_exclusive`), so each score is the
weight of one side (`score_left_refines`, `score_right_refines`).

`weightAhead_pair` puts `a` strictly ahead of `z` on weight off the decision slot, under three
conditions:

- Every honest validator that voted in the honest window supports `a`.
- Every index on `z` is adversarial, with a vote in the adversarial window.
- The counting inequality holds with the proposer score.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok pureState LawfulFcMap)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root ForkChoiceNode Gwei
  ValidatorIndex getAttestationScore getWeight getProposerScore isPreviousSlotPayloadDecision)
open EthCLSpecs.Proofs.Heze.PayloadRace (Side Validator sideWeight balanceSum votedIn
  honestVoted advVoted)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The side that the store gives index `n` between the two nodes `a` and `z`: `full` when it
supports `z`, `empty` when it supports `a`, `neither` otherwise. -/
def pairSide (store : Store map) (a z : ForkChoiceNode) (n : Nat) : Side :=
  if supportsVal store z (UInt64.ofNat n) then .full
  else if supportsVal store a (UInt64.ofNat n) then .empty
  else .neither

/-- The score of `z` is the weight on `full`. -/
theorem score_right_refines (store : Store map) (state : BeaconState) (a z : ForkChoiceNode)
    (honestOf : ValidatorIndex → Bool) (votesOf : ValidatorIndex → Nat → Bool)
    {t t' : Store map} {w : Gwei}
    (h : (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
      store z (pureState state)).run t = .ok (w, t')) :
    w.toNat = sideWeight (raceValidators (pureState state) honestOf votesOf)
      (fun v => pairSide store a z v.index) .full := by
  rw [(getAttestationScore_run_ok store _ state h).2]
  unfold sideWeight raceValidators
  rw [sideSum_eq state (pairSide store a z) .full (supportsVal store z)]
  · rfl
  · intro i
    simp only [pairSide, UInt64.ofNat_toNat]
    cases hz : supportsVal store z i <;> cases ha : supportsVal store a i <;> simp

/-- The score of `a` is the weight on `empty`, for two distinct children of one node. -/
theorem score_left_refines [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {x a z : ForkChoiceNode} (hxa : NodeEdge store x a)
    (hxz : NodeEdge store x z) (hne : a ≠ z) (hx : (FcMap.lookup store.blocks x.root).isSome)
    (state : BeaconState) (honestOf : ValidatorIndex → Bool)
    (votesOf : ValidatorIndex → Nat → Bool) {t t' : Store map} {w : Gwei}
    (h : (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
      store a (pureState state)).run t = .ok (w, t')) :
    w.toNat = sideWeight (raceValidators (pureState state) honestOf votesOf)
      (fun v => pairSide store a z v.index) .empty := by
  rw [(getAttestationScore_run_ok store _ state h).2]
  unfold sideWeight raceValidators
  rw [sideSum_eq state (pairSide store a z) .empty (supportsVal store a)]
  · rfl
  · intro i
    simp only [pairSide, UInt64.ofNat_toNat]
    by_cases hz : supportsVal store z i
    · have ha : supportsVal store a i = false := by
        cases ha : supportsVal store a i
        · rfl
        · exact (supportsVal_siblings_exclusive store hslots hxa hxz hne hx i ha hz).elim
      simp [hz, ha]
    · cases ha : supportsVal store a i <;> simp [hz]

variable [Config]

/-- **`a` is ahead of `z` on weight.** Off the decision slot, take two distinct children `a`
and `z` of one node. Every honest validator with a vote in `[lo, s)` supports `a`. Every index
that supports `z` is adversarial, with a vote in `[lo', s)`. The adversarial balance of that
window plus `boost` is below the honest balance of `[lo, s)`, and `boost` bounds every proposer
score. Then every pair of weight runs puts `a` strictly ahead. -/
theorem weightAhead_pair [LawfulFcMap map Root] (store : Store map)
    (hslots : SlotsIncrease store) {x a z : ForkChoiceNode} (hxa : NodeEdge store x a)
    (hxz : NodeEdge store x z) (hne : a ≠ z) (hx : (FcMap.lookup store.blocks x.root).isSome)
    (hp : StorePure store) (honestOf : ValidatorIndex → Bool)
    (votesOf : ValidatorIndex → Nat → Bool) (lo lo' s boost : Nat) (jst : BeaconState)
    (hjst : FcMap.lookup store.checkpointStates store.justifiedCheckpoint = some (pureState jst))
    (hnda : ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store a).run t = .ok (b, t') → b = false)
    (hndz : ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store z).run t = .ok (b, t') → b = false)
    (hboost : ∀ (t t' : Store map) (ps : Gwei),
      (getProposerScore (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t
        = .ok (ps, t') → ps.toNat ≤ boost)
    (hhon : ∀ i, i ∈ (EthCLSpecs.Heze.activeValidatorIndicesOf (pureState jst)
        (EthCLSpecs.Heze.currentEpochOf (pureState jst))).toList →
      slashedB (pureState jst) i = false → honestOf i = true →
      votedIn (votesOf i) lo s = true →
      (∃ (b : Bool) (u : Store map), (supports store a i).run store = .ok (b, u)) →
      supportsVal store a i = true)
    (hadv : ∀ i, supportsVal store z i = true →
      honestOf i = false ∧ votedIn (votesOf i) lo' s = true)
    (hcount : advVoted (raceValidators (pureState jst) honestOf votesOf) lo' s + boost
      < honestVoted (raceValidators (pureState jst) honestOf votesOf) lo s) :
    ∀ (s₁ s₁' s₂ s₂' : Store map) (wA wZ : Gwei),
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store a).run s₁
        = .ok (wA, s₁') →
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store z).run s₂
        = .ok (wZ, s₂') →
      wZ < wA := by
  intro s₁ s₁' s₂ s₂' wA wZ hA hZ
  obtain ⟨st, sA, t1, t1', hst, hsA, hwA⟩ := getWeight_run_bounds store _ hp hnda hA
  obtain ⟨st', sZ, t2, t2', hst', hsZ, hwZ⟩ := getWeight_run_bounds store _ hp hndz hZ
  rw [hjst] at hst hst'
  injection hst with hst
  injection hst' with hst'
  have e1 : jst = st := congrArg SizzLean.Cache.SSZ.Box.view hst
  have e2 : jst = st' := congrArg SizzLean.Cache.SSZ.Box.view hst'
  subst e1 e2
  rw [score_left_refines store hslots hxa hxz hne hx jst honestOf votesOf hsA] at hwA
  have hA' := score_left_refines store hslots hxa hxz hne hx jst honestOf votesOf hsA
  have hZ' := score_right_refines store jst a z honestOf votesOf hsZ
  have h1 := honestVoted_le_empty_of (raceValidators (pureState jst) honestOf votesOf)
    (fun w => pairSide store a z w.index) lo s (by
      intro w hw' hh hvoted
      obtain ⟨i, hi, hsl, rfl⟩ := mem_raceValidators jst honestOf _ w hw'
      have hsa := hhon i hi hsl hh hvoted (getAttestationScore_supports _ _ jst hsA i hi hsl)
      have hsz : supportsVal store z i = false := by
        cases hz : supportsVal store z i
        · rfl
        · exact (supportsVal_siblings_exclusive store hslots hxa hxz hne hx i hsa hz).elim
      simp [pairSide, hsa, hsz])
  have h2 := full_le_advVoted_of (raceValidators (pureState jst) honestOf votesOf)
    (fun w => pairSide store a z w.index) lo' s (by
      intro w hw' hfull
      obtain ⟨i, hi, hsl, rfl⟩ := mem_raceValidators jst honestOf _ w hw'
      have hz : supportsVal store z i = true := by
        simp only [pairSide, UInt64.ofNat_toNat] at hfull
        split at hfull
        · assumption
        · split at hfull <;> cases hfull
      exact hadv i hz)
  have hEa : sA.toNat ≤ wA.toNat := by
    rcases hwA with h | ⟨ps, _, _, _, h⟩
    · rw [h]; exact Nat.le_refl _
    · omega
  have hFz : wZ.toNat ≤ sZ.toNat + boost := by
    rcases hwZ with h | ⟨ps, _, _, hps, h⟩
    · rw [h]; omega
    · have := hboost _ _ _ hps; omega
  rw [UInt64.lt_iff_toNat_lt]
  omega

end

end EthCLSpecs.Proofs.Heze
