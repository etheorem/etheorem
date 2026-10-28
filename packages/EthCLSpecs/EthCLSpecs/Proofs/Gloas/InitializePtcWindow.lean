import EthCLSpecs.Gloas.Operations
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.InitializePtcWindow`: the seeded PTC window's two regions

`EthCLSpecs.Gloas.initializePtcWindow` (`Gloas/Operations.lean`) builds the cached
`ptcWindow` the Fulu → Gloas upgrade seeds, as one `Vector.ofFn` over
`Fin (3 * SLOTS_PER_EPOCH)`, branching on whether the index falls in the empty first epoch
or the remaining two `SLOTS_PER_EPOCH` regions. Both branches are proved by unfolding the
definition and letting `simp` reduce the `Vector.ofFn` application and discharge the `if`,
no induction, no `native_decide`, no mathlib. `initializePtcWindow_getElem` joins the two into
the whole contract, the theorem that carries the `@[characterizes]` tag.

At v1.7.0-beta.4 `upgrade_to_gloas` computes the window over the Gloas post-state with
Gloas's own `compute_ptc` (`completeUpgradeToGloas` runs it), so the subject is an ordinary
Gloas `forkdef` over a Gloas state; alpha.12 computed it over the Fulu pre-state, which made
this file boundary code naming both forks. Statements bind plain `Gloas.BeaconState` values;
the window's builder receives `pureState state`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas (Preset Config BeaconState initializePtcWindow computePtc
  computeStartSlotAtEpoch currentEpochOf)
open EthCLLib.Proofs (pureState)

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous epoch", empty
because the pre-fork state carries no Gloas PTC) are the all-zero committee,
`initialize_ptc_window`'s `empty_previous_epoch`. -/
theorem initializePtcWindow_lt [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow (pureState state))[i] = Vector.replicate Gloas.Const.ptcSize 0 := by
  intro state i h
  simp [initializePtcWindow, h]

/-- The window's remaining `2 * SLOTS_PER_EPOCH` entries (the current epoch and the one
after it) are `compute_ptc` evaluated at the slot `initialize_ptc_window` computes for that
offset: split the offset `k := i - SLOTS_PER_EPOCH` into an epoch delta
(`k / SLOTS_PER_EPOCH`) and an intra-epoch slot offset (`k % SLOTS_PER_EPOCH`), exactly as
the definition does, rather than the collapsed `startSlot(currentEpoch) + k` form (which
would need a `UInt64` no-overflow side condition this statement doesn't carry). -/
theorem initializePtcWindow_ge [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      Gloas.Const.slotsPerEpoch ≤ i.val →
      (initializePtcWindow (pureState state))[i] =
        let k := i.val - Gloas.Const.slotsPerEpoch
        computePtc (pureState state)
          (computeStartSlotAtEpoch (currentEpochOf (pureState state) +
              UInt64.ofNat (k / Gloas.Const.slotsPerEpoch)) +
            UInt64.ofNat (k % Gloas.Const.slotsPerEpoch)) := by
  intro state i h
  simp [initializePtcWindow, Nat.not_lt.mpr h]

/-- **The window contract.** Every entry of `initialize_ptc_window(state)`: the all-zero
committee in the first `SLOTS_PER_EPOCH` entries, and `compute_ptc` at the offset's slot in the
remaining `2 * SLOTS_PER_EPOCH`. The two region lemmas above are its branches. -/
@[characterizes EthCLSpecs.Gloas.initializePtcWindow]
theorem initializePtcWindow_getElem [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      (initializePtcWindow (pureState state))[i] =
        if i.val < Gloas.Const.slotsPerEpoch then Vector.replicate Gloas.Const.ptcSize 0
        else
          let k := i.val - Gloas.Const.slotsPerEpoch
          computePtc (pureState state)
            (computeStartSlotAtEpoch (currentEpochOf (pureState state) +
                UInt64.ofNat (k / Gloas.Const.slotsPerEpoch)) +
              UInt64.ofNat (k % Gloas.Const.slotsPerEpoch)) := by
  intro state i
  split
  · exact initializePtcWindow_lt state i ‹_›
  · exact initializePtcWindow_ge state i (Nat.not_lt.mp ‹_›)

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Gloas.Const.ptcSize` (`ValidatorIndex := UInt64`'s `default` is `0`,
and `Vector`'s `Inhabited` instance is pointwise), so callers that already reason in terms of
`default` don't need to unfold `initializePtcWindow` a second time to get there. -/
theorem initializePtcWindow_lt_default [Preset] [Config] [HasherTag] :
    ∀ (state : BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow (pureState state))[i] = default := by
  intro state i h
  exact initializePtcWindow_lt state i h

end EthCLSpecs.Proofs.Gloas
