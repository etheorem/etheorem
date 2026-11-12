import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Proofs.Fulu.Reachable
import EthCLSpecs.Proofs.Gloas.ConfigValid

/-!
# `EthCLSpecs.Proofs.Gloas.Reachable`: the Gloas states the state transition reaches

The Gloas counterpart of `Proofs/Fulu/Reachable.lean`, which explains the anchor base case,
the split of `state_transition` into a `slots` step and a `block` step, the fork window, and
the `validated` flag. Gloas adds one constructor, `upgrade`, which enters Gloas from a
reachable Fulu state at the Gloas fork boundary.

## The upgrade step

Upstream `gloas/fork.md` makes the upgrade an irregular state change inside `process_slots`.
It fires when `state.slot % SLOTS_PER_EPOCH == 0` and
`compute_epoch_at_slot(state.slot) == GLOAS_FORK_EPOCH`, after the inner loop sets the slot.
The Lean `processSlots` has no fork check (`Gloas/Transition.lean:77-82`). The runner's
`runTransitionImpl` (`Gloas/Interface.lean:236-280`) applies the upgrade itself. So the
inductive states the trigger:

* the Fulu state is reachable inside the Fulu window that ends at `GLOAS_FORK_EPOCH`;
* its slot is exactly `forkSlot gloasForkEpoch`, the `Nat` form of the two `fork.md`
  conditions;
* `upgradeToGloas` builds the Gloas state, and `completeUpgradeToGloas` finishes it. The
  second part can reject (`Gloas/Operations.lean:217-220`), so its run must succeed.

The fork version and epoch are the config's `GLOAS_FORK_VERSION` and `GLOAS_FORK_EPOCH`, as
`upgrade_to_gloas` and `get_ptc` read them. The runner takes the epoch from the vector's
metadata and a fixed version per preset instead; the vectors set the config to agree.

The Fulu window ends at the Gloas boundary, so a Fulu block never lands on the boundary slot.
The first Gloas block at that slot is a `block` step straight after `upgrade`, with no
`processSlots`, as in the runner.

## The cross-fork bridge

The `upgrade` premise names `Fulu.ReachableState`, which needs a Fulu `Preset` and `Config`.
`open scoped EthCLSpecs.Gloas.Downgrade` supplies both from the Gloas ones, the bridge
`Gloas/Upgrade.lean` opens for the same reason (`SPECS_ARCHITECTURE.md` §6.2). It is open for
this module's declarations alone. Under the bridge, the Fulu `forkSlot` and the Gloas one
agree by `rfl`, which the second `example` below relies on.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag CryptoBackend htr)
open EthCLSpecs.Gloas (Preset Config BeaconState SignedBeaconBlock Slot Epoch
  processSlots processBlock verifyBlockSignature completeUpgradeToGloas upgradeToGloas)
open EthCLSpecs.Gloas.Const (slotsPerEpoch farFutureEpoch gloasForkEpoch gloasForkVersion)
open EthCLLib.Proofs (pureState runPure)
open scoped EthCLSpecs.Gloas.Downgrade

/-- The anchor states a Gloas chain may start from: a Fulu anchor, which reaches Gloas through
the upgrade, or a Gloas anchor, such as the pre-state of a vector run with
`GLOAS_FORK_EPOCH: 0`. -/
structure Anchors [Preset] extends toFulu : EthCLSpecs.Proofs.Fulu.Anchors where
  /-- The Gloas states a chain may start from. -/
  gloas : BeaconState → Prop

/-- The first slot of `epoch`, in `Nat`. The Gloas copy of `Fulu.forkSlot`, at the Gloas
preset. -/
def forkSlot [Preset] (epoch : Epoch) : Nat := epoch.toNat * slotsPerEpoch

/-- No slot reaches the `FAR_FUTURE_EPOCH` boundary at a valid preset, which has two or more
slots per epoch. -/
theorem slot_lt_forkSlot_farFutureEpoch [Preset] [PresetValid] (s : Slot) :
    s.toNat < forkSlot farFutureEpoch := by
  have hspe : 2 ≤ slotsPerEpoch := PresetValid.toFulu.twoLeSlotsPerEpoch
  have hs : s.toNat < 2 ^ 64 := s.toNat_lt
  have hfar : farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
  unfold forkSlot
  rw [hfar]
  omega

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The Gloas states reachable from `anchors` before the fork at `nextForkEpoch`.

* `anchor`: a Gloas anchor state inside the window.
* `upgrade`: the Gloas upgrade of a reachable Fulu state at the Gloas boundary, landing inside
  the window.
* `slots` and `block`: the two halves of `stateTransition`, as in the Fulu inductive. -/
inductive ReachableState (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch) :
    BeaconState → Prop where
  | anchor {v : BeaconState} :
      anchors.gloas v →
      v.slot.toNat ≤ forkSlot nextForkEpoch →
      ReachableState anchors validated nextForkEpoch v
  | upgrade {u : EthCLSpecs.Fulu.BeaconState} {w : BeaconState} :
      EthCLSpecs.Proofs.Fulu.ReachableState anchors.toFulu validated gloasForkEpoch u →
      u.slot.toNat = forkSlot gloasForkEpoch →
      u.slot.toNat ≤ forkSlot nextForkEpoch →
      runPure (completeUpgradeToGloas (StateTransition := GloasRun))
        (upgradeToGloas gloasForkVersion u) = .ok ((), w) →
      ReachableState anchors validated nextForkEpoch w
  | slots {v w : BeaconState} (target : Slot) :
      ReachableState anchors validated nextForkEpoch v →
      target.toNat ≤ forkSlot nextForkEpoch →
      runPure (processSlots (StateTransition := GloasRun) target) v = .ok ((), w) →
      ReachableState anchors validated nextForkEpoch w
  | block {v w : BeaconState} (signedBlock : SignedBeaconBlock) :
      ReachableState anchors validated nextForkEpoch v →
      v.slot.toNat < forkSlot nextForkEpoch →
      (validated = true → verifyBlockSignature (pureState v) signedBlock = true) →
      runPure (processBlock (StateTransition := GloasRun) signedBlock.message) v = .ok ((), w) →
      (validated = true → signedBlock.message.stateRoot = htr w) →
      ReachableState anchors validated nextForkEpoch w

namespace ReachableState

/-- More anchors, in either fork, reach more states. -/
theorem mono_anchors {anchors anchors' : Anchors} {validated : Bool} {nextForkEpoch : Epoch}
    (hFulu : ∀ u, anchors.fulu u → anchors'.fulu u)
    (hGloas : ∀ v, anchors.gloas v → anchors'.gloas v) {v : BeaconState}
    (hv : ReachableState anchors validated nextForkEpoch v) :
    ReachableState anchors' validated nextForkEpoch v := by
  induction hv with
  | anchor ha hw => exact .anchor (hGloas _ ha) hw
  | upgrade hu htrig hw hrun =>
    exact .upgrade (EthCLSpecs.Proofs.Fulu.ReachableState.mono_anchors hFulu hu) htrig hw hrun
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw hsig hrun hroot ih => exact .block sb ih hw hsig hrun hroot

/-- Skipping the signature and state-root checks loses no state, in Gloas or in the Fulu
history before the upgrade. -/
theorem unvalidated {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}
    {v : BeaconState} (hv : ReachableState anchors validated nextForkEpoch v) :
    ReachableState anchors false nextForkEpoch v := by
  induction hv with
  | anchor ha hw => exact .anchor ha hw
  | upgrade hu htrig hw hrun =>
    exact .upgrade (EthCLSpecs.Proofs.Fulu.ReachableState.unvalidated hu) htrig hw hrun
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw _ hrun _ ih =>
    exact .block sb ih hw (fun h => absurd h Bool.false_ne_true) hrun
      (fun h => absurd h Bool.false_ne_true)

end ReachableState

/-- A Gloas anchor inside the window is reachable at once. -/
example (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch) (v : BeaconState)
    (ha : anchors.gloas v) (hw : v.slot.toNat ≤ forkSlot nextForkEpoch) :
    ReachableState anchors validated nextForkEpoch v :=
  .anchor ha hw

/-- A Fulu anchor that sits on the Gloas boundary upgrades into Gloas. The Fulu window premise
is the trigger equation read at the Fulu `forkSlot`, which the bridge makes the same `Nat`. -/
example (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch)
    (u : EthCLSpecs.Fulu.BeaconState) (w : BeaconState) (ha : anchors.fulu u)
    (htrig : u.slot.toNat = forkSlot gloasForkEpoch)
    (hw : u.slot.toNat ≤ forkSlot nextForkEpoch)
    (hrun : runPure (completeUpgradeToGloas (StateTransition := GloasRun))
      (upgradeToGloas gloasForkVersion u) = .ok ((), w)) :
    ReachableState anchors validated nextForkEpoch w :=
  .upgrade (.anchor ha (Nat.le_of_eq htrig)) htrig hw hrun

end

end EthCLSpecs.Proofs.Gloas
