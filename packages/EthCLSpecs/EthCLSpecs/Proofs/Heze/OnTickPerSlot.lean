import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Run
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.OnTickPerSlot`: a per-slot tick keeps the block and answer maps

`onTickPerSlot` (inherited from Gloas) writes only `time`, `proposerBoostRoot`, and the
checkpoints. `onTickPerSlot_run_keeps` states that a successful run keeps the `blocks`
and `payloadInclusionListSatisfaction` maps, the two maps that `UnsatisfiedPayload`
(`CensorshipCost.lean`) reads. It does not cover the whole `onTick` loop.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun run_bind run_pure except_bind_ok)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Config Store getCurrentSlot onTickPerSlot)

/-- A successful `onTickPerSlot` keeps the `blocks` and `payloadInclusionListSatisfaction`
maps. -/
theorem onTickPerSlot_run_keeps {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
    (store post st st' : Store map) (time : UInt64)
    (h : (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store time).run st
      = .ok (post, st')) :
    post.blocks = store.blocks ∧
      post.payloadInclusionListSatisfaction = store.payloadInclusionListSatisfaction := by
  simp only [onTickPerSlot, run_bind] at h
  cases h1 : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run st
    with
  | error e => rw [h1] at h; exact nomatch h
  | ok p =>
    rw [h1, except_bind_ok] at h
    cases h2 : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
        { store with time := time }).run p.2 with
    | error e => rw [h2] at h; exact nomatch h
    | ok q =>
      rw [h2, except_bind_ok, run_pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      -- Each field read passes through the two `if`s of the body and the two of
      -- `updateCheckpoints`. None of them writes the two maps.
      refine ⟨?_, ?_⟩ <;> (repeat' split) <;>
        simp only [EthCLSpecs.Heze.updateCheckpoints] <;> (repeat' split) <;> rfl

end EthCLSpecs.Proofs.Heze
