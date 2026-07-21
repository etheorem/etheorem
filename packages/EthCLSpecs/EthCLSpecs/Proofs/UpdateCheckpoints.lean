import EthCLSpecs.Gloas.ForkChoice

/-!
# `EthCLSpecs.Proofs.UpdateCheckpoints`: `updateCheckpoints` checkpoint monotonicity

`EthCLSpecs.Gloas.updateCheckpoints` (`Gloas/ForkChoice.lean:470-472`) is the Store's
checkpoint-advancement primitive: given a justified candidate `j` and a finalized
candidate `f`, each of `store.justifiedCheckpoint` / `store.finalizedCheckpoint` is
overwritten with its candidate exactly when the candidate's epoch is strictly greater,
and left untouched otherwise. The current call sites, `on_block`'s post-state
checkpoints, `compute_pulled_up_tip`'s pulled-up-state checkpoints, and
`on_tick_per_slot`'s unrealized-checkpoint promotion, funnel through this one gate; the
genesis/anchor Store construction (`get_forkchoice_store`) writes both fields directly
instead, that's initialization, not an update, so it sits outside this claim, and
outside anything this file proves. Therefore, each invocation of `updateCheckpoints`
preserves or advances both recorded epochs.

The two guard conditions are read directly off the function body, so each result below
is a direct consequence of the `if`, not an inherited precondition: the "exact
characterization" theorems below (`_eq_or_advances`) restate the two-armed `if` as a
disjunction with *both* arms carrying the guard that produced them, `j.epoch ≤
store.justifiedCheckpoint.epoch` on the unchanged side, `store.justifiedCheckpoint.epoch
< j.epoch` on the advancing side, so the disjunction is the `if`'s condition and its
negation, not just its two possible outputs. The monotonicity theorems (`_epoch_le`) are
the corollary a reader actually wants, "epochs never go backwards." Scoped to
`EthCLSpecs.Gloas.updateCheckpoints` only. (The Fulu declaration of the same name is a
separate `forkdef` in a different namespace, not covered here.)

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Monotonicity properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLSpecs.Gloas (Store updateCheckpoints Checkpoint)
open EthCLSpecs.Fulu (Preset)
open EthCLLib.Spec (MapKind HasherTag)

variable {map : MapKind} [Preset] [HasherTag]
  (store : Store map) (j f : Checkpoint)

/-- The justified half of `updateCheckpoints`' two-armed `if`, restated as an exhaustive
disjunction over the guard `j.epoch > store.justifiedCheckpoint.epoch` and its negation,
not just over the two outputs: the unchanged arm additionally proves the guard *failed*
(`j.epoch ≤ store.justifiedCheckpoint.epoch`), the advancing arm additionally proves it
*fired* (`store.justifiedCheckpoint.epoch < j.epoch`). `UInt64.not_lt` turns the negated
guard into that `≤`. -/
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

/-- The finalized half of `updateCheckpoints`' two-armed `if`, restated as an exhaustive
disjunction over the guard `f.epoch > store.finalizedCheckpoint.epoch` and its negation,
the mirror of `updateCheckpoints_justifiedCheckpoint_eq_or_advances`. -/
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

/-- Monotonicity, the property the proof candidates doc names: `updateCheckpoints`
never lowers the Store's justified epoch. Either arm of
`updateCheckpoints_justifiedCheckpoint_eq_or_advances` gives it, the unchanged arm by
`UInt64.le_refl`, the advancing arm by `UInt64.le_of_lt` since its strict `<` is in
particular a `≤`. -/
theorem updateCheckpoints_justifiedEpoch_le :
    store.justifiedCheckpoint.epoch ≤ (updateCheckpoints store j f).justifiedCheckpoint.epoch := by
  rcases updateCheckpoints_justifiedCheckpoint_eq_or_advances store j f with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]; exact UInt64.le_refl _
  · rw [h]; exact UInt64.le_of_lt hlt

/-- Monotonicity for the finalized epoch, the mirror of
`updateCheckpoints_justifiedEpoch_le`. -/
theorem updateCheckpoints_finalizedEpoch_le :
    store.finalizedCheckpoint.epoch ≤ (updateCheckpoints store j f).finalizedCheckpoint.epoch := by
  rcases updateCheckpoints_finalizedCheckpoint_eq_or_advances store j f with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]; exact UInt64.le_refl _
  · rw [h]; exact UInt64.le_of_lt hlt

end EthCLSpecs.Proofs
