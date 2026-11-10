import EthCLSpecs.Fulu.Transition
import EthCLSpecs.Proofs.Fulu.Run
import EthCLLib.Proofs.Run
import EthCLSpecs.Proofs.Fulu.ConfigValid

/-!
# `EthCLSpecs.Proofs.Fulu.Reachable`: the Fulu states the state transition reaches

`ReachableState anchors validated nextForkEpoch v` says the plain Fulu `BeaconState` `v` is
the end of a run of the state transition that starts at an anchor. A theorem that holds for
every reachable state, `SimpleStateInvariants` for one, then states a fact about the states a
chain can produce, and an arbitrary `BeaconState` no longer has to satisfy it.

## The base case is an anchor

The model has no genesis. Each fork's `Interface.lean` answers a genesis vector with
`.outOfScope`, and upstream defines a post-phase0 genesis only for testing. So the base case is a caller-supplied
predicate, `Anchors.fulu`. A theorem about reachable states then takes a hypothesis about the
anchors, for example that every anchor satisfies the invariant it proves. A modeled genesis, a
weak-subjectivity checkpoint state, or a test vector's pre-state can each instantiate the
anchor later, and the inductive does not change.

## The steps are the two halves of `state_transition`

`stateTransition` (`Fulu/Transition.lean:227-235`) is `processSlots block.slot` followed by
the block half: the signature check, `processBlock`, and the state-root check. The inductive
takes the two halves as separate steps, `slots` and `block`. Upstream `fork.md` runs the fork
upgrade inside `process_slots`, after the slot reaches the fork boundary, and before the
block at that slot. The Gloas inductive puts its `upgrade` step between the two halves, so a
block at exactly the boundary slot is reachable. `stateTransition` alone cannot apply that
block, because `processSlots` asserts `slot < target` (`Fulu/Transition.lean:72`).

The split admits no state an honest chain cannot produce. A `slots` step on its own is a
state advanced through empty slots, which fork choice computes for a checkpoint
(`storeTargetCheckpointState`). A `block` step needs the state at the block's slot with no
block there yet, because `processBlockHeader` asserts `block.slot == state.slot` and
`block.slot > latestBlockHeader.slot` (`Fulu/Transition.lean:82-96`).

## The window ends at the next fork

Fulu's `Config` has no field for the next fork's epoch, so `nextForkEpoch` is a parameter.
Every reachable state has `slot ≤ forkSlot nextForkEpoch`, and a block step needs the slot
strictly below it. At the boundary the next fork's upgrade runs before any block, so no Fulu
block lands there. A chain that stays in Fulu passes `farFutureEpoch`, and
`slot_lt_forkSlot_farFutureEpoch` shows that this window excludes no slot. The Fulu state at
the boundary, before the upgrade, counts as reachable. That is an over-approximation by one
transient state, which clients never expose.

`forkSlot` computes the boundary in `Nat`, because `FAR_FUTURE_EPOCH * SLOTS_PER_EPOCH` wraps
in `UInt64` and lands on a real slot.

## The `validated` flag

`validated` mirrors `stateTransition`'s `validateResult`. At `true` the block step needs the
proposer signature and the claimed post-state root, as an honest chain does. At `false` it
skips both. The checks only reject blocks and never change the post-state, so the `false`
set contains the `true` set (`ReachableState.unvalidated`). A theorem proved for every flag
value therefore holds for the larger set.

All statements bind plain `BeaconState` values. A step reads its run through `runPure`
(`SPECS_ARCHITECTURE.md` §11.1.1), at `FuluRun`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (HasherTag CryptoBackend htr)
open EthCLSpecs.Fulu (Preset Config BeaconState SignedBeaconBlock Slot Epoch
  processSlots processBlock verifyBlockSignature)
open EthCLSpecs.Fulu.Const (slotsPerEpoch farFutureEpoch)
open EthCLLib.Proofs (pureState runPure)

/-- The anchor states a chain may start from. A Fulu chain starts in Fulu, so there is one
field; the Gloas and Heze structures extend this one with a field per later fork, because a
later chain may start in any fork of its lineage. -/
structure Anchors [Preset] where
  /-- The Fulu states a chain may start from. -/
  fulu : BeaconState → Prop

/-- The first slot of `epoch`, `epoch * SLOTS_PER_EPOCH`, in `Nat`. The `UInt64` product
`computeStartSlotAtEpoch` wraps at `FAR_FUTURE_EPOCH`; this one does not, so a fork scheduled
at `FAR_FUTURE_EPOCH` has a boundary past every slot. -/
def forkSlot [Preset] (epoch : Epoch) : Nat := epoch.toNat * slotsPerEpoch

/-- No slot reaches the `FAR_FUTURE_EPOCH` boundary at a valid preset, which has two or more
slots per epoch (`PresetValid.twoLeSlotsPerEpoch`). So a chain that passes `farFutureEpoch` as
`nextForkEpoch` has a window that excludes no slot and no block. -/
theorem slot_lt_forkSlot_farFutureEpoch [Preset] [PresetValid] (s : Slot) :
    s.toNat < forkSlot farFutureEpoch := by
  have hspe : 2 ≤ slotsPerEpoch := PresetValid.twoLeSlotsPerEpoch
  have hs : s.toNat < 2 ^ 64 := s.toNat_lt
  have hfar : farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
  unfold forkSlot
  rw [hfar]
  omega

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The Fulu states reachable from `anchors` before the fork at `nextForkEpoch`.

* `anchor`: an anchor state inside the window.
* `slots`: a successful `processSlots target` from a reachable state, with `target` inside
  the window.
* `block`: the block half of `stateTransition` from a reachable state below the boundary. The
  signature and state-root premises apply only when `validated` is `true`. The state root is
  `htr w`, which is the root `stateTransition` reads through `getStateRoot` on `pureState w`.

The parameters stay fixed across the constructors, so each constructor's conclusion names the
same `anchors`, `validated` and `nextForkEpoch`. -/
inductive ReachableState (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch) :
    BeaconState → Prop where
  | anchor {v : BeaconState} :
      anchors.fulu v →
      v.slot.toNat ≤ forkSlot nextForkEpoch →
      ReachableState anchors validated nextForkEpoch v
  | slots {v w : BeaconState} (target : Slot) :
      ReachableState anchors validated nextForkEpoch v →
      target.toNat ≤ forkSlot nextForkEpoch →
      runPure (processSlots (StateTransition := FuluRun) target) v = .ok ((), w) →
      ReachableState anchors validated nextForkEpoch w
  | block {v w : BeaconState} (signedBlock : SignedBeaconBlock) :
      ReachableState anchors validated nextForkEpoch v →
      v.slot.toNat < forkSlot nextForkEpoch →
      (validated = true → verifyBlockSignature (pureState v) signedBlock = true) →
      runPure (processBlock (StateTransition := FuluRun) signedBlock.message) v = .ok ((), w) →
      (validated = true → signedBlock.message.stateRoot = htr w) →
      ReachableState anchors validated nextForkEpoch w

namespace ReachableState

/-- More anchors reach more states. -/
theorem mono_anchors {anchors anchors' : Anchors} {validated : Bool} {nextForkEpoch : Epoch}
    (h : ∀ v, anchors.fulu v → anchors'.fulu v) {v : BeaconState}
    (hv : ReachableState anchors validated nextForkEpoch v) :
    ReachableState anchors' validated nextForkEpoch v := by
  induction hv with
  | anchor ha hw => exact .anchor (h _ ha) hw
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw hsig hrun hroot ih => exact .block sb ih hw hsig hrun hroot

/-- Skipping the signature and state-root checks loses no state: every state reachable at
either flag value is reachable at `false`. A theorem about `ReachableState anchors false n`
therefore covers the honest set too. -/
theorem unvalidated {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}
    {v : BeaconState} (hv : ReachableState anchors validated nextForkEpoch v) :
    ReachableState anchors false nextForkEpoch v := by
  induction hv with
  | anchor ha hw => exact .anchor ha hw
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw _ hrun _ ih =>
    exact .block sb ih hw (fun h => absurd h Bool.false_ne_true) hrun
      (fun h => absurd h Bool.false_ne_true)

end ReachableState

/-- An anchor inside the window is reachable at once. The `example` pins the `anchor`
constructor's argument order. -/
example (anchors : Anchors) (validated : Bool) (nextForkEpoch : Epoch) (v : BeaconState)
    (ha : anchors.fulu v) (hw : v.slot.toNat ≤ forkSlot nextForkEpoch) :
    ReachableState anchors validated nextForkEpoch v :=
  .anchor ha hw

end

end EthCLSpecs.Proofs.Fulu
