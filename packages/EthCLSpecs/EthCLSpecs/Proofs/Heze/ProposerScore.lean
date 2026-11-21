import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.Checked

/-!
# `EthCLSpecs.Proofs.Heze.ProposerScore`: the proposer score of a store

`get_proposer_score` (phase0 `fork-choice.md:369-371`) reads the justified checkpoint state.
It returns `compute_proposer_score` of that state (`:362-363`), the committee fraction at
`PROPOSER_SCORE_BOOST` (`calculate_committee_fraction`, `:300`). Heze inherits all three.
The model reads the state with `getOrThrowKey` and lifts `computeProposerScore`, a plain
`Except` function of the state.

So the proposer score is one value per justified state. `proposerScoreOf` is that value in
`Nat`, and a successful run returns it (`getProposerScore_run_eq`). `committeeWeightOf` is
the `committee_weight` of the fraction, over the unslashed active validators. The score is
at most that weight times the boost over `100` (`proposerScoreOf_le`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_liftErr_eq_ok pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState getProposerScore
  computeProposerScore Gwei)

section Score
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- `compute_proposer_score` (phase0 `fork-choice.md:362-363`) of `jst`, in `Nat`. When it
faults, the run of `getProposerScore` fails, so the value `0` there is never a result. -/
def proposerScoreOf (jst : State) : Nat :=
  match computeProposerScore jst with
  | .ok ps => ps.toNat
  | .error _ => 0

/-- A successful `getProposerScore` run returns `proposerScoreOf` of the justified state,
the uncached box of `jst`. -/
theorem getProposerScore_run_eq (store : Store map) (jst : BeaconState)
    (hjst : FcMap.lookup store.checkpointStates store.justifiedCheckpoint = some (pureState jst))
    {t t' : Store map} {ps : Gwei}
    (h : (getProposerScore (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t
      = .ok (ps, t')) :
    ps.toNat = proposerScoreOf (pureState jst) := by
  simp only [getProposerScore, FcMap.getOrThrowKey, hjst] at h
  obtain ⟨_, _, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  -- The read of the justified state returns its box.
  cases EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hread
  obtain ⟨hcps, -⟩ := run_liftErr_eq_ok _ _ _ _ h
  unfold proposerScoreOf
  rw [hcps]

/-- `committee_weight` of `calculate_committee_fraction` (phase0 `fork-choice.md:300-307`):
the total balance of the unslashed active validators, divided by `SLOTS_PER_EPOCH`. The text
is the first part of the model body, so `computeProposerScore_eq` holds by unfolding. -/
def committeeWeightOf (st : State) : Except StateTransitionError Gwei := do
  let validators := sszGet st validators
  let unslashedAndActive :=
    (← EthCLSpecs.Heze.getActiveValidatorIndices st (EthCLSpecs.Heze.currentEpochOf st)).filter
      fun i => !(validators[i.toNat]!).slashed
  pure ((← EthCLSpecs.Heze.getTotalBalance st unslashedAndActive) /
    UInt64.ofNat EthCLSpecs.Heze.Const.slotsPerEpoch)

/-- `compute_proposer_score` is the committee weight, then the checked product with the boost,
divided by `100`. -/
theorem computeProposerScore_eq (st : BeaconState) :
    computeProposerScore (pureState st) = (do
      let product ← checkedMul (← committeeWeightOf (pureState st))
        (UInt64.ofNat EthCLSpecs.Heze.Const.proposerScoreBoost)
        "calculate_committee_fraction: committee_weight * committee_percent"
      pure (product / 100)) := by
  simp only [computeProposerScore, EthCLSpecs.Heze.calculateCommitteeFraction, committeeWeightOf,
    bind_assoc, pure_bind]

/-- The proposer score is at most the committee weight times the boost, divided by `100`.
When the product overflows, `compute_proposer_score` raises, and `proposerScoreOf` is `0`. -/
theorem proposerScoreOf_le (st : BeaconState) (w : Gwei)
    (hw : committeeWeightOf (pureState st) = .ok w) :
    proposerScoreOf (pureState st)
      ≤ w.toNat * (UInt64.ofNat EthCLSpecs.Heze.Const.proposerScoreBoost).toNat / 100 := by
  unfold proposerScoreOf
  rw [computeProposerScore_eq, hw]
  cases hm : (checkedMul w (UInt64.ofNat EthCLSpecs.Heze.Const.proposerScoreBoost)
      "calculate_committee_fraction: committee_weight * committee_percent" :
      Except StateTransitionError Gwei) with
  | error e =>
    simp only [bind, Except.bind, hm]
    exact Nat.zero_le _
  | ok r =>
    simp only [bind, Except.bind, hm, pure, Except.pure]
    rw [UInt64.toNat_div, EthCLLib.Proofs.checkedMul_eq_ok _ _ _ _ hm]
    exact Nat.le_refl _

end Score

end EthCLSpecs.Proofs.Heze
