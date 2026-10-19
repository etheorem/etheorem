import EthCLSpecs.Gloas.Upgrade
import EthCLLib.Proofs.Run
import EthCLLib.Internal.ManualTerms
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
receives `pureState state`, and `view_uncachedBox` reduces the reads inside the
definition to plain fields.

This file names **both** forks, the sanctioned exception to the one-fork rule for
proofs: its subject is boundary code, which converts a Fulu pre-state into a Gloas
window, so the statements mention `Fulu.BeaconState` and Fulu's committee helpers
alongside Gloas's constants. `open scoped EthCLSpecs.Gloas.Downgrade` supplies the
`Gloas.Preset → Fulu.Preset` bridge that lets a single `[Preset]` binder carry
both sides, the same bridge `Gloas/Upgrade.lean` itself opens.

The three theorems carry the generator's witness terms as `theorem_vectors_manual`
registrations under them (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6). The search
never draws the terms they need. `default`'s empty validator set drives
`computePtcFromFulu`'s balance-weighted selection into its fuel bound, so
`activeState` supplies 64 active validators. The window offsets pin the smallest
index of the region each hypothesis names, and `default`'s `0` fails `_ge`'s
bound. `activeState` stays a named def because three registrations share it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas (Preset initializePtcWindow computePtcFromFulu)
open EthCLSpecs.Fulu (computeStartSlotAtEpoch currentEpochOf)
open EthCLLib.Proofs (pureState)
open SizzLean.Proofs (view_uncachedBox)
open scoped EthCLSpecs.Gloas.Downgrade

/-- The smallest offset of `initializePtcWindow`'s first region: the window
index whose value is `0`, which `initializePtcWindow_lt`'s hypothesis
accepts. -/
private def windowZero [Preset] : Fin (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  ⟨0, by
    have hp := EthCLSpecs.Gloas.Const.slotsPerEpochPos
    omega⟩

/-- The first offset of `initializePtcWindow`'s second region: the window
index whose value is `SLOTS_PER_EPOCH`, the smallest index the
`slotsPerEpoch ≤ i.val` hypothesis accepts. -/
private def windowEpoch [Preset] : Fin (3 * EthCLSpecs.Gloas.Const.slotsPerEpoch) :=
  ⟨EthCLSpecs.Gloas.Const.slotsPerEpoch,
    by
      have hp := EthCLSpecs.Gloas.Const.slotsPerEpochPos
      omega⟩

/-- One active validator at the maximum effective balance: every draw of
the balance-weighted selection accepts it, so a committee of these fills
its target size in `size` iterations. The pubkey and credential are the
zero vectors, which the verify-off backend accepts. -/
private def activeValidator [Preset] : EthCLSpecs.Fulu.Validator :=
  { pubkey := Vector.replicate 48 0
    withdrawalCredentials := Vector.replicate 32 0
    effectiveBalance := 32000000000
    slashed := false
    activationEligibilityEpoch := 0
    activationEpoch := 0
    exitEpoch := EthCLSpecs.Gloas.Const.farFutureEpoch
    withdrawableEpoch := EthCLSpecs.Gloas.Const.farFutureEpoch }

/-- The manual state for the window theorems: `default` with 64 active
validators and matching balances. A small active committee keeps the
spec's balance-weighted selection inside its fuel, which the default
state's empty validator set cannot. -/
private def activeState [Preset] : EthCLSpecs.Fulu.BeaconState :=
  let v := activeValidator
  let vs : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Validator EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
    (Array.range 64).foldl (fun xs _ => xs.push v) default
  let bs : SizzLean.Repr.SSZList EthCLSpecs.Gloas.Gwei EthCLSpecs.Gloas.Const.validatorRegistryLimit :=
    (Array.range 64).foldl (fun xs _ => xs.push 32000000000) default
  ({ (default : EthCLSpecs.Fulu.BeaconState) with validators := vs, balances := bs } :
    EthCLSpecs.Fulu.BeaconState)

/-- The window's first `SLOTS_PER_EPOCH` entries (the placeholder "previous
epoch", empty because the pre-fork Fulu state carries no PTC) are the all-zero
committee, `initialize_ptc_window`'s `emptyCommittee`. -/
theorem initializePtcWindow_lt [Preset] [HasherTag] :
    ∀ (state : Fulu.BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow (pureState state))[i] = Vector.replicate Gloas.Const.ptcSize 0 := by
  intro state i h
  simp [initializePtcWindow, h]

-- The generator's witnesses for the three theorems of this file
-- (`THEOREM_VECTORS_ARCHITECTURE.md` §14.6), written under them.
open EthCLLib.Internal in
theorem_vectors_manual initializePtcWindow_lt
  state := activeState
  i     := windowZero

/-- The window's remaining `2 * SLOTS_PER_EPOCH` entries (the current epoch and
the one after it) are `computePtcFromFulu` evaluated at the slot
`initialize_ptc_window` computes for that offset: split the offset
`k := i - SLOTS_PER_EPOCH` into an epoch delta (`k / SLOTS_PER_EPOCH`) and an
intra-epoch slot offset (`k % SLOTS_PER_EPOCH`), exactly as the definition
does, rather than the collapsed `startSlot(currentEpoch) + k` form (which
would need a `UInt64` no-overflow side condition this statement doesn't
carry). -/
theorem initializePtcWindow_ge [Preset] [HasherTag] :
    ∀ (state : Fulu.BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      Gloas.Const.slotsPerEpoch ≤ i.val →
      (initializePtcWindow (pureState state))[i] =
        let k := i.val - Gloas.Const.slotsPerEpoch
        computePtcFromFulu (pureState state)
          (computeStartSlotAtEpoch (currentEpochOf (pureState state) +
              UInt64.ofNat (k / Gloas.Const.slotsPerEpoch)) +
            UInt64.ofNat (k % Gloas.Const.slotsPerEpoch)) := by
  intro state i h
  simp [initializePtcWindow, Nat.not_lt.mpr h]

open EthCLLib.Internal in
theorem_vectors_manual initializePtcWindow_ge
  state := activeState
  i     := windowEpoch

/-- The first region's committee is also the ambient `default` for
`Vector ValidatorIndex Gloas.Const.ptcSize` (`ValidatorIndex := UInt64`'s
`default` is `0`, and `Vector`'s `Inhabited` instance is pointwise), so callers
that already reason in terms of `default` don't need to unfold
`initializePtcWindow` a second time to get there. -/
theorem initializePtcWindow_lt_default [Preset] [HasherTag] :
    ∀ (state : Fulu.BeaconState) (i : Fin (3 * Gloas.Const.slotsPerEpoch)),
      i.val < Gloas.Const.slotsPerEpoch →
      (initializePtcWindow (pureState state))[i] = default := by
  intro state i h
  exact initializePtcWindow_lt state i h

open EthCLLib.Internal in
theorem_vectors_manual initializePtcWindow_lt_default
  state := activeState
  i     := windowZero

end EthCLSpecs.Proofs.Gloas
