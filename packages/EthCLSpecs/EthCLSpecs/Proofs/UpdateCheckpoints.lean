import EthCLSpecs.Gloas.ForkChoice

/-!
# `EthCLSpecs.Proofs.UpdateCheckpoints`: checkpoint monotonicity

`EthCLSpecs.Gloas.updateCheckpoints` replaces the Store's justified and finalized
checkpoints only when the corresponding candidate has a strictly greater epoch.
This file pins the whole result down as one record update, characterizes each
checkpoint's two branches, and proves that every invocation preserves or advances
both recorded epochs.

All current updates to these fields use this function; `getForkchoiceStore` initializes
the fields directly and is outside this claim. The separate Fulu declaration is also
out of scope.

`updateCheckpoints` is declared identically in both forks, so unlike the Gloas-only
subjects of the sibling proof modules these theorem names would collide with a Fulu
companion. They live in `EthCLSpecs.Proofs.Gloas`, mirroring the `EthCLSpecs.Gloas`
namespace the subject itself sits in, leaving `EthCLSpecs.Proofs.Fulu` free.

## The shared proof shape

Every proof here decides both of the definition's guards with `by_cases`, then lets
`simp` reduce the resulting nested record updates. The second guard still matters
even where the statement never mentions it: the definition's outer `if` tests the
finalized epoch of the store the *inner* `if` already produced, so `simp` cannot
project either checkpoint field until both branches are settled. Dropping either
`by_cases` leaves unsolved goals.

`split` looks like the shorter route and is not available. `forkdef` elaborates
the definition's `let` into `have store := ...`, which `split` refuses to see
through ("Could not split an `if` or `match` expression in the goal").

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Monotonicity properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLSpecs.Gloas (Store updateCheckpoints Checkpoint)
open EthCLSpecs.Gloas (Preset)
open EthCLLib.Spec (MapKind HasherTag)

/-! Every theorem below is stated about one arbitrary Store and one arbitrary pair of
candidate checkpoints, under the `[Preset]` / `[HasherTag]` the `Store` forkstruct binds.
Lean includes each of these in a signature only when the statement mentions it, and all
five statements mention all five. -/
variable {map : MapKind} [Preset] [HasherTag] (store : Store map) (j f : Checkpoint)

/-- `updateCheckpoints` rewritten as a single record update: each checkpoint field
takes its candidate exactly when that candidate's epoch is strictly greater, and
every other field of the Store is carried through untouched.

This is the frame condition the two branch characterizations below do not carry.
They project one field each, so on their own they leave open whether the function
also disturbs `time`, `equivocatingIndices`, or any of the maps. A caller
threading a Store through a fork-choice transition needs to know it does not. -/
theorem updateCheckpoints_eq :
    updateCheckpoints store j f =
      { store with
        justifiedCheckpoint :=
          if j.epoch > store.justifiedCheckpoint.epoch then j else store.justifiedCheckpoint,
        finalizedCheckpoint :=
          if f.epoch > store.finalizedCheckpoint.epoch then f else store.finalizedCheckpoint } := by
  by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;>
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch <;>
      simp [updateCheckpoints, h1, h2]

/-- The resulting justified checkpoint is either unchanged because `j` is not newer,
or exactly `j` because its epoch is strictly greater. -/
theorem updateCheckpoints_justifiedCheckpoint_eq_or_advances :
    ((updateCheckpoints store j f).justifiedCheckpoint = store.justifiedCheckpoint ∧
        j.epoch ≤ store.justifiedCheckpoint.epoch) ∨
    ((updateCheckpoints store j f).justifiedCheckpoint = j ∧
        store.justifiedCheckpoint.epoch < j.epoch) := by
  by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch
  · refine .inr ⟨?_, h1⟩
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]
  · refine .inl ⟨?_, UInt64.not_lt.mp h1⟩
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]

/-- The resulting finalized checkpoint is either unchanged because `f` is not newer,
or exactly `f` because its epoch is strictly greater. -/
theorem updateCheckpoints_finalizedCheckpoint_eq_or_advances :
    ((updateCheckpoints store j f).finalizedCheckpoint = store.finalizedCheckpoint ∧
        f.epoch ≤ store.finalizedCheckpoint.epoch) ∨
    ((updateCheckpoints store j f).finalizedCheckpoint = f ∧
        store.finalizedCheckpoint.epoch < f.epoch) := by
  by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch
  · refine .inr ⟨?_, h2⟩
    by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]
  · refine .inl ⟨?_, UInt64.not_lt.mp h2⟩
    by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]

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

end EthCLSpecs.Proofs.Gloas
