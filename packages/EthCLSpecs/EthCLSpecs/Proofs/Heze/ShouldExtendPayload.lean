import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's FOCIL rejection gate

Heze's `shouldExtendPayload` follows the Gloas fork-choice decision flow but
inserts a FOCIL gate after payload verification and before the later timeliness,
data-availability, and proposer-boost logic.
This module proves that, once the common block/slot prefix succeeds, a verified
payload with a recorded `false` inclusion-list satisfaction verdict returns `false`
in the pure fork-choice runner `ForkChoiceStoreRun (Store map)`, leaving its
runner state unchanged.

The theorem assumes the successful block lookup, current-slot calculation,
non-overflowing slot increment, and recorded verdict. It needs no
`[ExecutionEngine]` binder: Heze records the inclusion-list satisfaction verdict
behind that seam in `recordPayloadInclusionListSatisfaction`, while
`shouldExtendPayload` only reads the stored result through
`isPayloadInclusionListSatisfied`. Verdict production and correctness, the
payload/verdict pairing invariant, missing-record behavior, inclusion-list
construction or validation, and end-to-end canonicality and liveness stay out of
scope.

The theorem lives in `EthCLSpecs.Proofs.Heze` because `shouldExtendPayload` exists
in both Gloas and Heze.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLSpecs.Proofs.Gloas (GloasRun)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd)
open EthCLSpecs.Fulu (Root)
-- `Preset` and `Config` come from Heze, not Fulu: `forkpreset` gives each fork its own
-- class, and `Heze.Store` is elaborated against Heze's. The downgrade instances run the
-- other way, so a Fulu binder would not synthesize here.
open EthCLSpecs.Heze (Preset Config Store shouldExtendPayload isPayloadInclusionListSatisfied
  isPayloadVerified getCurrentSlot BeaconBlock)

/-- A verified payload with a recorded `false` inclusion-list satisfaction verdict
is rejected by Heze's FOCIL gate once the preliminary block/slot checks succeed.
The result preserves the runner state and short-circuits later logic shared with Gloas.

`hverified` is logically unnecessary for the Boolean conclusion: an unverified
payload is rejected earlier. It is retained to establish that the FOCIL gate is
the rejecting branch. The converse is not claimed: `shouldExtendPayload` can also
return `false` for an unverified payload or because of later Gloas logic. -/
theorem shouldExtendPayload_run_eq_false_of_recorded_unsatisfied
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] :
    ∀ (store : Store map) (root : Root) (rootBlock : BeaconBlock),
      FcMap.lookup store.blocks root = some rootBlock →
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
        = .ok (rootBlock.slot + 1, store) →
      ¬ (rootBlock.slot + 1 < rootBlock.slot) →
      isPayloadVerified store root = true →
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (shouldExtendPayload (StoreTransition := ForkChoiceStoreRun (Store map)) store root).run
          store
        = .ok (false, store) := by
  intro store root rootBlock hblock hcurrentslot hnooverflow hverified hunsatisfied
  -- Targeted unfold of the FOCIL gate; residual goal is definitional.
  simp [shouldExtendPayload, isPayloadInclusionListSatisfied, FcMap.getOrThrow,
    FcMap.getOrThrowKey, FcMap.getOrAssert, hblock, checkedAdd, hnooverflow, hverified,
    hunsatisfied, hcurrentslot, Gloas.GloasRun.except_bind_ok]
  rfl

end EthCLSpecs.Proofs.Heze
