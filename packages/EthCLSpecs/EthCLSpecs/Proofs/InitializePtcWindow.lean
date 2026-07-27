import EthCLSpecs.Gloas.Upgrade

/-!
# `EthCLSpecs.Proofs.InitializePtcWindow`: the seeded PTC window's two regions

`EthCLSpecs.Gloas.initializePtcWindow` (`Gloas/Upgrade.lean`) builds the
Fulu → Gloas fork transition's cached `ptcWindow` as one `Vector.ofFn` over
`Fin (3 * SLOTS_PER_EPOCH)`, branching on whether the index falls in the empty
first epoch or the remaining two SLOTS_PER_EPOCH regions. Both branches are proved by
unfolding the definition and letting `simp` reduce the `Vector.ofFn`
application and discharge the `if`, no induction, no `native_decide`,
no mathlib.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Fulu (Preset computeStartSlotAtEpoch currentEpochOf)
open EthCLSpecs.Gloas (initializePtcWindow computePtcFromFulu)

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous
epoch", empty because the pre-fork Fulu state carries no PTC) are the all-zero
committee, `initialize_ptc_window`'s `emptyCommittee`. -/
theorem initializePtcWindow_lt [Preset] [HasherTag] :
    ∀ (state : Fulu.State) (i : Fin (3 * Fulu.Const.slotsPerEpoch)),
      i.val < Fulu.Const.slotsPerEpoch →
      (initializePtcWindow state)[i] = Vector.replicate Fulu.Const.ptcSize 0 := by
  intro state i h
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
    ∀ (state : Fulu.State) (i : Fin (3 * Fulu.Const.slotsPerEpoch)),
      Fulu.Const.slotsPerEpoch ≤ i.val →
      (initializePtcWindow state)[i] =
        let k := i.val - Fulu.Const.slotsPerEpoch
        computePtcFromFulu state
          (computeStartSlotAtEpoch (currentEpochOf state + UInt64.ofNat (k / Fulu.Const.slotsPerEpoch)) +
            UInt64.ofNat (k % Fulu.Const.slotsPerEpoch)) := by
  intro state i h
  simp [initializePtcWindow, Nat.not_lt.mpr h]

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Fulu.Const.ptcSize` (`ValidatorIndex := UInt64`'s
`default` is `0`, and `Vector`'s `Inhabited` instance is pointwise), so callers
that already reason in terms of `default` don't need to unfold
`initializePtcWindow` a second time to get there. -/
theorem initializePtcWindow_lt_default [Preset] [HasherTag] :
    ∀ (state : Fulu.State) (i : Fin (3 * Fulu.Const.slotsPerEpoch)),
      i.val < Fulu.Const.slotsPerEpoch →
      (initializePtcWindow state)[i] = default := by
  intro state i h
  exact initializePtcWindow_lt state i h

end EthCLSpecs.Proofs
