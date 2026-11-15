import EthCLSpecs.Gloas.Operations
import EthCLLib.Spec.Errors
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded PTC window's two regions

`EthCLSpecs.Gloas.initializePtcWindow` (`Gloas/Operations.lean`) builds the cached
`ptcWindow` the Fulu → Gloas upgrade seeds, as one `Vector.ofFn` over
`Fin (3 * SLOTS_PER_EPOCH)`, branching on whether the index falls in the empty first epoch
or the remaining two `SLOTS_PER_EPOCH` regions. The function is pure and total: each entry
is an `Except` carrying that entry's own faults. The entry binds three checked steps, the
per-entry add `current_epoch + e`, `compute_start_slot_at_epoch`, and the slot's
intra-epoch offset add, and each raises `.arithmetic` with the repr of its exact
`ArithFault`. The entry then makes the `compute_ptc` read.
`completeUpgradeToGloas` maps the
entries in index order, so the first rejecting slot surfaces. The theorems here state the
function's entries, not a run: `initializePtcWindow_eq` is the whole contract, the vector
equation over the entry function; `initializePtcWindow_lt` / `initializePtcWindow_ge` read
the two regions; `initializePtcWindow_getElem` joins them at the element level; and
`initializePtcWindow_lt_default` restates the first region as the ambient `default`.
`initializePtcWindow_eq` carries the `@[characterizes]` tag. No induction, no
`native_decide`, no mathlib.

At v1.7.0-beta.4 `upgrade_to_gloas` computes the window over the Gloas post-state with
Gloas's own `compute_ptc` (`completeUpgradeToGloas` maps the entries), so the subject is an
ordinary Gloas `forkdef` over a Gloas state; alpha.12 computed it over the Fulu pre-state,
which made this file boundary code naming both forks. Statements bind plain
`Gloas.BeaconState` values, and the entry's `Except.bind` spelling is the `do`-block the
implementation writes, laid out so the statements carry no monad metavariable.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLLib.Proofs (pureState)
open EthCLSpecs.Gloas.Const (slotsPerEpochPos)
open EthCLSpecs.Gloas (Preset Config BeaconState ValidatorIndex initializePtcWindow computePtc
  computeStartSlotAtEpoch currentEpochOf)

/-- **The window contract.** The complete equation of `initializePtcWindow`: entry `i` is
the all-zero committee in the first `SLOTS_PER_EPOCH` positions, and in the remaining
`2 * SLOTS_PER_EPOCH` it binds the spec's three checked steps, the per-entry add
`current_epoch + e` (the epoch delta is the offset `i - SLOTS_PER_EPOCH` divided by
`SLOTS_PER_EPOCH`, `0` or `1`, a plain-`int` operand through the `natAdd` route),
`compute_start_slot_at_epoch`, and the slot's intra-epoch offset add, and then reads
`compute_ptc` at the bound slot. The `Except` in the entry's type carries every step's
fault: each checked step's `.arithmetic` carrying the repr of the exact `ArithFault`, and
`compute_ptc`'s empty-candidate reject. -/
@[characterizes EthCLSpecs.Gloas.initializePtcWindow]
theorem initializePtcWindow_eq [Preset] [Config] [HasherTag] (state : BeaconState) :
    initializePtcWindow (pureState state) =
      Vector.ofFn fun i : Fin (3 * Gloas.Const.slotsPerEpoch) =>
        if i.val < Gloas.Const.slotsPerEpoch then
          (Except.ok (Vector.replicate Gloas.Const.ptcSize 0) :
            Except StateTransitionError (Vector ValidatorIndex Gloas.Const.ptcSize))
        else
          Except.bind
            (liftM (currentEpochOf (pureState state)
                + ((i.val - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch)))
            fun epoch =>
          Except.bind (liftM (computeStartSlotAtEpoch epoch)) fun startSlot =>
          Except.bind
            (liftM (startSlot
                + ((i.val - Gloas.Const.slotsPerEpoch) % Gloas.Const.slotsPerEpoch)))
            fun slotJ =>
          computePtc (pureState state) slotJ := rfl

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous epoch", empty
because the pre-fork state carries no Gloas PTC) are the all-zero committee,
`initialize_ptc_window`'s `empty_previous_epoch`. The region involves no arithmetic, so the
entry is `Except.ok`. -/
theorem initializePtcWindow_lt [Preset] [Config] [HasherTag] (state : BeaconState)
    (i : Fin (3 * Gloas.Const.slotsPerEpoch)) (h : i.val < Gloas.Const.slotsPerEpoch) :
    (initializePtcWindow (pureState state))[i]
      = Except.ok (Vector.replicate Gloas.Const.ptcSize 0) := by
  rw [initializePtcWindow_eq state]
  simp [h]

/-- The window's remaining `2 * SLOTS_PER_EPOCH` entries bind the spec's three checked
steps, then read `compute_ptc` at the bound slot: split the offset
`k := i - SLOTS_PER_EPOCH` into an epoch delta (`k / SLOTS_PER_EPOCH`, the per-entry add's
plain-`int` operand) and an intra-epoch slot offset (`k % SLOTS_PER_EPOCH`), exactly as the
composed contract does. -/
theorem initializePtcWindow_ge [Preset] [Config] [HasherTag] (state : BeaconState)
    (i : Fin (3 * Gloas.Const.slotsPerEpoch)) (h : Gloas.Const.slotsPerEpoch ≤ i.val) :
    (initializePtcWindow (pureState state))[i] =
          Except.bind
            (liftM (currentEpochOf (pureState state)
                + ((i.val - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch)))
            fun epoch =>
          Except.bind (liftM (computeStartSlotAtEpoch epoch)) fun startSlot =>
          Except.bind
            (liftM (startSlot
                + ((i.val - Gloas.Const.slotsPerEpoch) % Gloas.Const.slotsPerEpoch)))
            fun slotJ =>
          computePtc (pureState state) slotJ := by
  rw [initializePtcWindow_eq state]
  simp [Nat.not_lt.mpr h]

/-- The element-level join of the two regions: every entry of the seeded window is the
all-zero committee in the first `SLOTS_PER_EPOCH` entries and, in the remaining
`2 * SLOTS_PER_EPOCH`, the bind of the three checked steps followed by `compute_ptc`. The
contract equation above is the whole behavior; this is its element reading. -/
theorem initializePtcWindow_getElem [Preset] [Config] [HasherTag] (state : BeaconState)
    (i : Fin (3 * Gloas.Const.slotsPerEpoch)) :
    (initializePtcWindow (pureState state))[i] =
      if i.val < Gloas.Const.slotsPerEpoch then
        (Except.ok (Vector.replicate Gloas.Const.ptcSize 0) :
          Except StateTransitionError (Vector ValidatorIndex Gloas.Const.ptcSize))
      else
        Except.bind
          (liftM (currentEpochOf (pureState state)
              + ((i.val - Gloas.Const.slotsPerEpoch) / Gloas.Const.slotsPerEpoch)))
          fun epoch =>
        Except.bind (liftM (computeStartSlotAtEpoch epoch)) fun startSlot =>
        Except.bind
          (liftM (startSlot
              + ((i.val - Gloas.Const.slotsPerEpoch) % Gloas.Const.slotsPerEpoch)))
          fun slotJ =>
        computePtc (pureState state) slotJ := by
  rw [initializePtcWindow_eq state]
  by_cases hlt : i.val < Gloas.Const.slotsPerEpoch
  · simp [hlt]
  · simp [hlt]

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Gloas.Const.ptcSize` (`ValidatorIndex := UInt64`'s `default` is `0`,
and `Vector`'s `Inhabited` instance is pointwise), so callers that already reason in terms of
`default` don't need to unfold the window a second time to get there. -/
theorem initializePtcWindow_lt_default [Preset] [Config] [HasherTag] (state : BeaconState)
    (i : Fin (3 * Gloas.Const.slotsPerEpoch)) (h : i.val < Gloas.Const.slotsPerEpoch) :
    (initializePtcWindow (pureState state))[i]
      = Except.ok default := by
  rw [initializePtcWindow_lt state i h]
  rfl

end EthCLSpecs.Proofs.Gloas
