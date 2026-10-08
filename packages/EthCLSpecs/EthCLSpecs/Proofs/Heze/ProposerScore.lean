import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.ProposerScore`: the proposer score of a store

`get_proposer_score` (phase0 `fork-choice.md:350-352`) reads the justified checkpoint state.
It returns `compute_proposer_score` of that state (`:342-344`): the committee weight times
`PROPOSER_SCORE_BOOST`, divided by `100`. Heze inherits both. The model puts
`compute_proposer_score` inside `getProposerScore` (`Gloas/ForkChoice.lean:346`), and the
product goes through `checkedMul`.

So the proposer score is one value per justified state. `proposerScoreOf` is that value in
`Nat`, and a successful run returns it (`getProposerScore_run_eq`). A success of
`checkedMul` means that the `UInt64` product did not wrap (`toNat_mul_of_guard`,
`EthCLLib/Proofs/StoreRun.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun toNat_mul_of_guard pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState getProposerScore committeeWeight
  Gwei)

section Score
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- `compute_proposer_score` (phase0 `fork-choice.md:342-344`) in `Nat`: the committee weight
of `jst` times `PROPOSER_SCORE_BOOST`, divided by `100`. The boost is the `UInt64` cast that
`getProposerScore` multiplies by. The committee weight is an `Except` read. When it faults,
the run of `getProposerScore` fails, so the value `0` there is never a result. -/
def proposerScoreOf (jst : State) : Nat :=
  match committeeWeight jst with
  | .ok w => w.toNat * (UInt64.ofNat EthCLSpecs.Heze.Const.proposerScoreBoost).toNat / 100
  | .error _ => 0

/-- A successful `getProposerScore` run returns `proposerScoreOf` of the justified state,
the uncached box of `jst`. The committee weight read succeeds on such a run. The product goes
through `checkedMul`, so a successful run has no overflow. -/
theorem getProposerScore_run_eq (store : Store map) (jst : BeaconState)
    (hjst : FcMap.lookup store.checkpointStates store.justifiedCheckpoint = some (pureState jst))
    {t t' : Store map} {ps : Gwei}
    (h : (getProposerScore (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t
      = .ok (ps, t')) :
    ps.toNat = proposerScoreOf (pureState jst) := by
  simp only [getProposerScore, FcMap.getOrThrowKey, hjst, pure_bind] at h
  unfold proposerScoreOf
  cases hcw : committeeWeight (pureState jst) with
  | error e =>
    rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_error _ _ (by rw [hcw]; rfl),
      EthCLLib.Proofs.except_bind_error] at h
    cases h
  | ok w =>
    rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [hcw]; rfl),
      EthCLLib.Proofs.except_bind_ok] at h
    simp only [checkedMul] at h
    split at h
    · simp only [EthCLLib.Proofs.run_bind,
        EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run,
        EthCLLib.Proofs.except_bind_error] at h
      cases h
    · rename_i hno
      simp [StateT.run, pure] at h
      obtain ⟨rfl, -⟩ := h
      dsimp only
      rw [UInt64.toNat_div, toNat_mul_of_guard _ _ hno]
      rfl

end Score

end EthCLSpecs.Proofs.Heze
