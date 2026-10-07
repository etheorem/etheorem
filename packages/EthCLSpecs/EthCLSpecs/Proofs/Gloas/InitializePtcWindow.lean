import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded PTC window's two regions

`EthCLSpecs.Gloas.initializePtcWindow` (`Gloas/Upgrade.lean`) builds the
Fulu → Gloas fork transition's cached `ptcWindow` as one `Vector.ofFn` over
`Fin (3 * SLOTS_PER_EPOCH)`, branching on whether the index falls in the empty
first epoch or the remaining two SLOTS_PER_EPOCH regions. Both branches are proved by
unfolding the definition and letting `simp` reduce the `Vector.ofFn`
application and discharge the `if`, no induction, no `native_decide`,
no mathlib.

Statements bind plain `Fulu.BeaconState` values; the seeded window's builder
receives `pureState v`, and `view_uncachedBox` reduces the reads inside the
definition to plain fields.

This file names **both** forks, the sanctioned exception to the one-fork rule for
proofs: its subject is boundary code, which converts a Fulu pre-state into a Gloas
window, so the statements mention `Fulu.BeaconState` and Fulu's committee helpers
alongside Gloas's constants. `open scoped EthCLSpecs.Gloas.Downgrade` supplies the
`Gloas.Preset → Fulu.Preset` bridge that lets a single `[Preset]` binder carry
both sides, the same bridge `Gloas/Upgrade.lean` itself opens.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas (Preset initializePtcWindow computePtcFromFulu)
open EthCLSpecs.Fulu (computeStartSlotAtEpoch currentEpochOf)
open EthCLSpecs.Proofs (pureState)
open SizzLean.Proofs (view_uncachedBox)
open scoped EthCLSpecs.Gloas.Downgrade

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous
epoch", empty because the pre-fork Fulu state carries no PTC) are the all-zero
committee, `initialize_ptc_window`'s `emptyCommittee`. -/
theorem initializePtcWindow_lt [Preset] [HasherTag] :
    ∀ (v : Fulu.BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow (pureState v))[i] = Vector.replicate Gloas.Const.ptcSize 0 := by
  intro v i h
  simp [initializePtcWindow, h]

/-- The window's remaining `2 * SLOTS_PER_EPOCH` entries (the current epoch and
the one after it) are `computePtcFromFulu` evaluated at the slot
`initialize_ptc_window` computes for that offset: split the offset
`k := i - SLOTS_PER_EPOCH` into an epoch delta (`k / SLOTS_PER_EPOCH`) and an
intra-epoch slot offset (`k % SLOTS_PER_EPOCH`), exactly as the definition
does, rather than the collapsed `startSlot(currentEpoch) + k` form (which
would need a `UInt64` no-overflow side condition this statement doesn't
carry). -/
theorem initializePtcWindow_ge [Preset] [HasherTag] :
    ∀ (v : Fulu.BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      Gloas.Const.slotsPerEpoch ≤ i.val →
      (initializePtcWindow (pureState v))[i] =
        let k := i.val - Gloas.Const.slotsPerEpoch
        computePtcFromFulu (pureState v)
          (computeStartSlotAtEpoch (currentEpochOf (pureState v) +
              UInt64.ofNat (k / Gloas.Const.slotsPerEpoch)) +
            UInt64.ofNat (k % Gloas.Const.slotsPerEpoch)) := by
  intro v i h
  simp [initializePtcWindow, Nat.not_lt.mpr h]

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Gloas.Const.ptcSize` (`ValidatorIndex := UInt64`'s
`default` is `0`, and `Vector`'s `Inhabited` instance is pointwise), so callers
that already reason in terms of `default` don't need to unfold
`initializePtcWindow` a second time to get there. -/
theorem initializePtcWindow_lt_default [Preset] [HasherTag] :
    ∀ (v : Fulu.BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow (pureState v))[i] = default := by
  intro v i h
  exact initializePtcWindow_lt v i h

end EthCLSpecs.Proofs.Gloas
