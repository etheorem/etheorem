import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Fulu.ConsolidationRequest`: `processConsolidationRequest`'s request gates

`process_consolidation_request` (EIP-7251) runs its request through a ladder of gates, and
this file gives each gate one theorem. A gate theorem's hypotheses carry the request past
every earlier gate and then fire the named gate, so the generator's `decide` on the witness
guarantees the vector reaches that gate. The theorems sit in the function's gate order.

Upstream tests live in `electra/block_processing/test_process_consolidation_request.py` at
pin `v1.7.0-alpha.11`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Fulu (Preset Config BeaconState ConsolidationRequest getConsolidationChurnLimit
  isValidSwitchToCompoundingRequest processConsolidationRequest)
open EthCLLib.Proofs (pureState run_bind run_get except_bind_ok)
open SizzLean.Proofs (view_uncachedBox)

/-- **Consolidation churn too low.** With distinct source and target pubkeys and room in the
pending-consolidations queue, a consolidation churn limit at or below `minActivationBalance`
fails the churn gate. The run stops there and returns with the state unchanged, because the
gate's arm is `pure ()`.

Upstream tests (`electra/block_processing/test_process_consolidation_request.py`,
`v1.7.0-alpha.11`): `test_incorrect_not_enough_consolidation_churn_available`. -/
theorem processConsolidationRequest_run_churn_too_low [Preset] [HasherTag] [Config] :
    ∀ (pre : BeaconState) (req : ConsolidationRequest),
      req.sourcePubkey ≠ req.targetPubkey →
      pre.pendingConsolidations.size < EthCLSpecs.Fulu.Const.pendingConsolidationsLimit →
      getConsolidationChurnLimit (pureState pre) ≤ EthCLSpecs.Fulu.Const.minActivationBalance →
      (processConsolidationRequest (StateTransition := FuluRun) req).run (pureState pre)
        = .ok ((), pureState pre) := by
  intro pre req hne hroom hchurn
  unfold processConsolidationRequest
  -- `run_bind` splits the do-block. `run_get` pairs the threaded box with itself, and beta
  -- plus `except_bind_ok` substitute `pureState pre` for the `state` binder.
  simp only [run_bind, run_get, except_bind_ok]
  -- The switch path. Its first check is the pubkey inequality, so `hne` makes the whole
  -- predicate answer `false`, and the run takes the else branch.
  have hswitch : ¬(isValidSwitchToCompoundingRequest (pureState pre) req = true) := by
    unfold isValidSwitchToCompoundingRequest
    simp [hne]
  rw [if_neg hswitch]
  -- G1: same pubkeys. `false` under `hne`.
  have hsame : ¬((req.sourcePubkey == req.targetPubkey) = true) := by
    simp [hne]
  rw [if_neg hsame]
  -- G2: queue at its cap. `false` under `hroom`.
  have hqueue : ¬((sszGet (pureState pre) pendingConsolidations).size
      == EthCLSpecs.Fulu.Const.pendingConsolidationsLimit) = true := by
    simp only [view_uncachedBox, beq_iff_eq]
    omega
  rw [if_neg hqueue]
  -- G3, the churn gate. The hypothesis fires it, and its body is `pure ()`: the run returns
  -- with the state unchanged.
  rw [if_pos hchurn]
  rfl

end EthCLSpecs.Proofs.Fulu
