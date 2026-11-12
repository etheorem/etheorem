import EthCLSpecs.Heze.Transition
import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Proofs.Gloas.Reachable

/-!
# `EthCLSpecs.Proofs.Heze.Reachable`: the Heze states the state transition reaches

The Heze counterpart of `Proofs/Gloas/Reachable.lean`. The `upgrade` constructor enters Heze
from a reachable Gloas state at the Heze fork boundary, `forkSlot hezeForkEpoch`, under the
same `fork.md` trigger. The upgrade asserts that the eth1 deposit queue has drained, so
`upgradeToHeze` (`Heze/Upgrade.lean:88-138`) returns an `Except`, and the premise is that it
returns `.ok`. Heze needs no closing step: the PTC window and the builder registry already exist in
the Gloas pre-state.

Heze is the last modeled fork, but it still takes `nextForkEpoch`, so a later fork adds its
own inductive without editing this one. A chain that stays in Heze passes `farFutureEpoch`.

`open scoped EthCLSpecs.Heze.Downgrade` supplies the Gloas `Preset` and `Config` that
`Gloas.ReachableState` needs, the bridge `Heze/Upgrade.lean` opens. The Gloas inductive
carries its own bridge down to Fulu, but a statement here that names a Fulu anchor, such as
the `hFulu` premise of `mono_anchors`, binds a Fulu `BeaconState` and needs a Fulu `Preset`.
`open scoped EthCLSpecs.Gloas.Downgrade` adds the second link, so instance resolution goes
from Heze to Gloas to Fulu.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend htr)
open EthCLSpecs.Heze (Preset Config BeaconState SignedBeaconBlock Slot Epoch
  processSlots processBlock verifyBlockSignature upgradeToHeze)
open EthCLSpecs.Heze.Const (slotsPerEpoch farFutureEpoch hezeForkEpoch hezeForkVersion)
open EthCLLib.Proofs (pureState runPure)
open scoped EthCLSpecs.Heze.Downgrade EthCLSpecs.Gloas.Downgrade

/-- The anchor states a Heze chain may start from: a Fulu or Gloas anchor, which reaches Heze
through the upgrades, or a Heze anchor. -/
structure Anchors [Preset] extends toGloas : EthCLSpecs.Proofs.Gloas.Anchors where
  /-- The Heze states a chain may start from. -/
  heze : BeaconState → Prop

/-- The first slot of `epoch`, in `Nat`. The Heze copy of `Fulu.forkSlot`, at the Heze
preset. -/
def forkSlot [Preset] (epoch : Epoch) : Nat := epoch.toNat * slotsPerEpoch

/-- No slot reaches the `FAR_FUTURE_EPOCH` boundary at a preset with two or more slots per
epoch. -/
theorem slot_lt_forkSlot_farFutureEpoch [Preset] (hspe : 2 ≤ slotsPerEpoch) (s : Slot) :
    s.toNat < forkSlot farFutureEpoch := by
  have hs : s.toNat < 2 ^ 64 := s.toNat_lt
  have hfar : farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
  unfold forkSlot
  rw [hfar]
  omega

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The Heze states reachable from `anchors` before the fork at `nextForkEpoch`.

* `anchor`: a Heze anchor state inside the window.
* `upgrade`: the Heze upgrade of a reachable Gloas state at the Heze boundary, landing inside
  the window.
* `slots` and `block`: the two halves of `stateTransition`, as in the Fulu inductive. -/
inductive ReachableState (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch) :
    BeaconState → Prop where
  | anchor {v : BeaconState} :
      anchors.heze v →
      v.slot.toNat ≤ forkSlot nextForkEpoch →
      ReachableState anchors validated nextForkEpoch v
  | upgrade {u : EthCLSpecs.Gloas.BeaconState} {w : BeaconState} :
      EthCLSpecs.Proofs.Gloas.ReachableState anchors.toGloas validated hezeForkEpoch u →
      u.slot.toNat = forkSlot hezeForkEpoch →
      u.slot.toNat ≤ forkSlot nextForkEpoch →
      upgradeToHeze hezeForkVersion u = .ok w →
      ReachableState anchors validated nextForkEpoch w
  | slots {v w : BeaconState} (target : Slot) :
      ReachableState anchors validated nextForkEpoch v →
      target.toNat ≤ forkSlot nextForkEpoch →
      runPure (processSlots (StateTransition := HezeRun) target) v = .ok ((), w) →
      ReachableState anchors validated nextForkEpoch w
  | block {v w : BeaconState} (signedBlock : SignedBeaconBlock) :
      ReachableState anchors validated nextForkEpoch v →
      v.slot.toNat < forkSlot nextForkEpoch →
      (validated = true → verifyBlockSignature (pureState v) signedBlock = true) →
      runPure (processBlock (StateTransition := HezeRun) signedBlock.message) v = .ok ((), w) →
      (validated = true → signedBlock.message.stateRoot = htr w) →
      ReachableState anchors validated nextForkEpoch w

namespace ReachableState

/-- More anchors, in any fork of the lineage, reach more states. -/
theorem mono_anchors {anchors anchors' : Anchors} {validated : Bool} {nextForkEpoch : Epoch}
    (hFulu : ∀ u, anchors.fulu u → anchors'.fulu u)
    (hGloas : ∀ u, anchors.gloas u → anchors'.gloas u)
    (hHeze : ∀ v, anchors.heze v → anchors'.heze v) {v : BeaconState}
    (hv : ReachableState anchors validated nextForkEpoch v) :
    ReachableState anchors' validated nextForkEpoch v := by
  induction hv with
  | anchor ha hw => exact .anchor (hHeze _ ha) hw
  | upgrade hu htrig hw hup =>
    exact .upgrade (EthCLSpecs.Proofs.Gloas.ReachableState.mono_anchors hFulu hGloas hu)
      htrig hw hup
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw hsig hrun hroot ih => exact .block sb ih hw hsig hrun hroot

/-- Skipping the signature and state-root checks loses no state, in Heze or in the history
before either upgrade. -/
theorem unvalidated {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}
    {v : BeaconState} (hv : ReachableState anchors validated nextForkEpoch v) :
    ReachableState anchors false nextForkEpoch v := by
  induction hv with
  | anchor ha hw => exact .anchor ha hw
  | upgrade hu htrig hw hup =>
    exact .upgrade (EthCLSpecs.Proofs.Gloas.ReachableState.unvalidated hu) htrig hw hup
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw _ hrun _ ih =>
    exact .block sb ih hw (fun h => absurd h Bool.false_ne_true) hrun
      (fun h => absurd h Bool.false_ne_true)

end ReachableState

/-- A Heze anchor inside the window is reachable at once. -/
example (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch) (v : BeaconState)
    (ha : anchors.heze v) (hw : v.slot.toNat ≤ forkSlot nextForkEpoch) :
    ReachableState anchors validated nextForkEpoch v :=
  .anchor ha hw

/-- A Gloas anchor that sits on the Heze boundary upgrades into Heze. As in the Gloas module,
the Gloas window premise is the trigger equation read at the Gloas `forkSlot`. -/
example (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch)
    (u : EthCLSpecs.Gloas.BeaconState) (w : BeaconState) (ha : anchors.gloas u)
    (htrig : u.slot.toNat = forkSlot hezeForkEpoch)
    (hw : u.slot.toNat ≤ forkSlot nextForkEpoch)
    (hup : upgradeToHeze hezeForkVersion u = .ok w) :
    ReachableState anchors validated nextForkEpoch w :=
  .upgrade (.anchor ha (Nat.le_of_eq htrig)) htrig hw hup

end

end EthCLSpecs.Proofs.Heze
