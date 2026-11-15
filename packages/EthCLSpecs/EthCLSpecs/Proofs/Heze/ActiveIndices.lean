import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Proofs.Heze.ActiveIndices`: a successful active-index walk

`get_active_validator_indices` casts each kept position with `ValidatorIndex(i)`, and the cast
raises at `2 ^ 64`. So the model returns `Except`. A run that succeeded passed every cast, and
its result is the total walk `activeValidatorIndicesOf` (`getActiveValidatorIndices_eq_of_ok`).
The bound under which the run succeeds is `getActiveValidatorIndices_ok`
(`Proofs/Heze/Committees.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag throwArithmetic liftErr)
open EthCLLib.Proofs (pureState)
open EthCLSpecs.Heze (Preset BeaconState ValidatorIndex Epoch getActiveValidatorIndices
  activeValidatorIndicesOf)

/-- A successful `get_active_validator_indices` returns `activeValidatorIndicesOf`, with no
bound on the registry. -/
theorem getActiveValidatorIndices_eq_of_ok [Preset] [HasherTag] {s : BeaconState}
    {e : Epoch} {a : Array ValidatorIndex} (h : getActiveValidatorIndices (pureState s) e = .ok a) :
    a = activeValidatorIndicesOf (pureState s) e := by
  unfold getActiveValidatorIndices at h
  split at h
  · simp [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept, bind,
      Except.bind] at h
  · exact (Except.ok.inj h).symm

end EthCLSpecs.Proofs.Heze
