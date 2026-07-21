import EthCLSpecs.Gloas.ForkChoice

/-!
# `EthCLSpecs.Proofs.UpdateCheckpoints`: checkpoint monotonicity

`EthCLSpecs.Gloas.updateCheckpoints` replaces the Store's justified and finalized
checkpoints only when the corresponding candidate has a strictly greater epoch.
This file characterizes both branches exactly and proves that each invocation
preserves or advances both recorded epochs.

All current updates to these fields use this function; `getForkchoiceStore` initializes
the fields directly and is outside this claim. The separate Fulu declaration is also
out of scope.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Monotonicity properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLSpecs.Gloas (Store updateCheckpoints Checkpoint)
open EthCLSpecs.Fulu (Preset)
open EthCLLib.Spec (MapKind HasherTag)

variable {map : MapKind} [Preset] [HasherTag]
  (store : Store map) (j f : Checkpoint)

/-- The resulting justified checkpoint is either unchanged because `j` is not newer,
or exactly `j` because its epoch is strictly greater. -/
theorem updateCheckpoints_justifiedCheckpoint_eq_or_advances :
    ((updateCheckpoints store j f).justifiedCheckpoint = store.justifiedCheckpoint ∧
        j.epoch ≤ store.justifiedCheckpoint.epoch) ∨
    ((updateCheckpoints store j f).justifiedCheckpoint = j ∧
        store.justifiedCheckpoint.epoch < j.epoch) := by
  -- Decide both guards so `simp` can reduce the nested record updates
  -- and project the checkpoint field unaffected by the other update.
  by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;>
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch
  · exact .inr ⟨by simp [updateCheckpoints, h1, h2], h1⟩
  · exact .inr ⟨by simp [updateCheckpoints, h1, h2], h1⟩
  · exact .inl ⟨by simp [updateCheckpoints, h1, h2], UInt64.not_lt.mp h1⟩
  · exact .inl ⟨by simp [updateCheckpoints, h1, h2], UInt64.not_lt.mp h1⟩

/-- The resulting finalized checkpoint is either unchanged because `f` is not newer,
or exactly `f` because its epoch is strictly greater. -/
theorem updateCheckpoints_finalizedCheckpoint_eq_or_advances :
    ((updateCheckpoints store j f).finalizedCheckpoint = store.finalizedCheckpoint ∧
        f.epoch ≤ store.finalizedCheckpoint.epoch) ∨
    ((updateCheckpoints store j f).finalizedCheckpoint = f ∧
        store.finalizedCheckpoint.epoch < f.epoch) := by
  -- Decide both guards so `simp` can reduce the nested record updates
  -- and project the checkpoint field unaffected by the other update.
  by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch <;>
    by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch
  · exact .inr ⟨by simp [updateCheckpoints, h1, h2], h2⟩
  · exact .inr ⟨by simp [updateCheckpoints, h1, h2], h2⟩
  · exact .inl ⟨by simp [updateCheckpoints, h1, h2], UInt64.not_lt.mp h2⟩
  · exact .inl ⟨by simp [updateCheckpoints, h1, h2], UInt64.not_lt.mp h2⟩

/-- `updateCheckpoints` never lowers the Store's justified epoch. -/
theorem updateCheckpoints_justifiedEpoch_le :
    store.justifiedCheckpoint.epoch ≤ (updateCheckpoints store j f).justifiedCheckpoint.epoch := by
  rcases updateCheckpoints_justifiedCheckpoint_eq_or_advances store j f with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]; exact UInt64.le_refl _
  · rw [h]; exact UInt64.le_of_lt hlt

/-- `updateCheckpoints` never lowers the Store's finalized epoch. -/
theorem updateCheckpoints_finalizedEpoch_le :
    store.finalizedCheckpoint.epoch ≤ (updateCheckpoints store j f).finalizedCheckpoint.epoch := by
  rcases updateCheckpoints_finalizedCheckpoint_eq_or_advances store j f with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]; exact UInt64.le_refl _
  · rw [h]; exact UInt64.le_of_lt hlt

end EthCLSpecs.Proofs
