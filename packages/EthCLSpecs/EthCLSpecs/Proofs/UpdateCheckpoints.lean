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
`EthCLSpecs.Gloas.updateCheckpoints` only; the Fulu declaration of the same name has an
identical body but is a separate, unrelated `forkdef` in a different namespace, not
covered here.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Monotonicity properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLSpecs.Gloas (Store updateCheckpoints Checkpoint)
open EthCLSpecs.Fulu (Preset)
open EthCLLib.Spec (MapKind HasherTag)

variable {map : MapKind} [Preset] [HasherTag]
  (store : Store map) (j f : Checkpoint)

/-! ### Field independence

`updateCheckpoints`' two `if`s each write one field of the `Store`; the "each checkpoint
either remains unchanged or advances" reading of the function depends on those two
writes not interfering, on the finalized `if` never touching `justifiedCheckpoint` and
the justified `if` never touching `finalizedCheckpoint`. That's not an assumption about
`updateCheckpoints`, it's a property of the `{ s with field := v }` update notation both
`if`s use: the notation elaborates to a `Store.mk` application that substitutes the named
field and copies every other field straight from `s`, so for two distinct field names
the write and the read never alias. Recorded here as its own pair of `rfl` lemmas, true
by that elaboration alone, no unfolding of `updateCheckpoints` and no guard decision
needed, so the independence is confirmed as a standalone, citable fact rather than left
implicit in whatever `simp` happens to do inside the two theorems below. (`simp`'s own
default reduction of a record update performs the identical step when closing those
theorems' goals, which is *why* passing these lemmas to `simp` there is flagged
"unused": the fact is already load-bearing in the kernel check, just not under this
name.) -/

/-- Setting `justifiedCheckpoint` leaves `finalizedCheckpoint` untouched. Not consumed by
name anywhere (the two theorems below get the identical reduction for free from `simp`'s
own record-projection handling once both guards are decided), `private` because its role
is this file's own documentation, not public API. -/
private theorem finalizedCheckpoint_of_justifiedCheckpoint_update :
    ({ store with justifiedCheckpoint := j } : Store map).finalizedCheckpoint =
      store.finalizedCheckpoint := rfl

/-- The mirror: setting `finalizedCheckpoint` leaves `justifiedCheckpoint` untouched. -/
private theorem justifiedCheckpoint_of_finalizedCheckpoint_update :
    ({ store with finalizedCheckpoint := f } : Store map).justifiedCheckpoint =
      store.justifiedCheckpoint := rfl

/-- The justified half of `updateCheckpoints`' two-armed `if`, restated as an exhaustive
disjunction over the guard `j.epoch > store.justifiedCheckpoint.epoch` and its negation,
not just over the two outputs: the unchanged arm additionally proves the guard *failed*
(`j.epoch ≤ store.justifiedCheckpoint.epoch`), the advancing arm additionally proves it
*fired* (`store.justifiedCheckpoint.epoch < j.epoch`). `UInt64.not_lt` turns the negated
guard into that `≤`. The `by_cases` on `h2` is there only because `simp` can't push a
projection through an *undecided* `ite` (no generic `apply_ite`-style lemma is in scope
here), once `h2` pins down which of the `f`-arm's two branches fired, closing the
resulting concrete projection is exactly
`justifiedCheckpoint_of_finalizedCheckpoint_update`, `simp`'s own default reduction of a
record update already performs that same step, which is why the lemma is redundant to
name explicitly in the `simp` set below, its content, not its citation, is what the
`by_cases` is discharging. -/
theorem updateCheckpoints_justifiedCheckpoint_eq_or_advances :
    ((updateCheckpoints store j f).justifiedCheckpoint = store.justifiedCheckpoint ∧
        j.epoch ≤ store.justifiedCheckpoint.epoch) ∨
      ((updateCheckpoints store j f).justifiedCheckpoint = j ∧
        store.justifiedCheckpoint.epoch < j.epoch) := by
  by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;>
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch
  · exact .inr ⟨by simp [updateCheckpoints, h1, h2], h1⟩
  · exact .inr ⟨by simp [updateCheckpoints, h1, h2], h1⟩
  · exact .inl ⟨by simp [updateCheckpoints, h1, h2], UInt64.not_lt.mp h1⟩
  · exact .inl ⟨by simp [updateCheckpoints, h1, h2], UInt64.not_lt.mp h1⟩

/-- The finalized half of `updateCheckpoints`' two-armed `if`, restated as an exhaustive
disjunction over the guard `f.epoch > store.finalizedCheckpoint.epoch` and its negation,
the mirror of `updateCheckpoints_justifiedCheckpoint_eq_or_advances`. Symmetrically, the
`by_cases` on `h1` decides which of the `j`-arm's two branches fired before the
`finalizedCheckpoint` projection is taken; once decided, closing it is exactly
`finalizedCheckpoint_of_justifiedCheckpoint_update`, again already covered by `simp`'s
default record-projection reduction. -/
theorem updateCheckpoints_finalizedCheckpoint_eq_or_advances :
    ((updateCheckpoints store j f).finalizedCheckpoint = store.finalizedCheckpoint ∧
        f.epoch ≤ store.finalizedCheckpoint.epoch) ∨
      ((updateCheckpoints store j f).finalizedCheckpoint = f ∧
        store.finalizedCheckpoint.epoch < f.epoch) := by
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
