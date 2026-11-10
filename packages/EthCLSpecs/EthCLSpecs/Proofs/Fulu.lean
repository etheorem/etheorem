import EthCLSpecs.Proofs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.Codec
import EthCLSpecs.Proofs.Fulu.ConfigValid
import EthCLSpecs.Proofs.Fulu.EpochSafe
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Balances
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Consolidations
import EthCLSpecs.Proofs.Fulu.EpochSuccess.FieldSteps
import EthCLSpecs.Proofs.Fulu.EpochSuccess.FrameSteps
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Rewards
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Selection
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Stage
import EthCLSpecs.Proofs.Fulu.Invariants.Block
import EthCLSpecs.Proofs.Fulu.Invariants.Epoch
import EthCLSpecs.Proofs.Fulu.Invariants.Helpers
import EthCLSpecs.Proofs.Fulu.Invariants.Justification
import EthCLSpecs.Proofs.Fulu.Invariants.Slots
import EthCLSpecs.Proofs.Fulu.Reachable
import EthCLSpecs.Proofs.Fulu.ReachableInvariants
import EthCLSpecs.Proofs.Fulu.StateInvariants
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Proofs.Fulu`: the Fulu fork's theorems (index)

Every theorem about an `EthCLSpecs.Fulu` declaration, one module per subject. The directory
mirrors `EthCLSpecs/Fulu/`. A fork elaborates its own constant for every declaration, inherited
ones included. A theorem here is about the Fulu constant. `increaseBalance` is the case that
shows it. Gloas and Heze inherit it, and each inheritance is a separate constant these theorems
leave untouched.

Every declaration here sits in the `EthCLSpecs.Proofs.Fulu` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Fulu.Run`: `FuluRun`, the state-transition monad every Fulu proof in this
  directory pins its theorems to.
* `EthCLSpecs.Proofs.Fulu.Balances`: `increaseBalance` and `decreaseBalance`, each with an exact
  run equation and an out-of-range reject, plus `increaseBalance`'s overflow reject and its
  exact stored sum, and `decreaseBalance`'s truncating difference.
* `EthCLSpecs.Proofs.Fulu.Codec`: the `BasicSupported` gate by kernel `decide`, roundtrip, and
  non-malleability (`serialize_injective`) for `BeaconState`, `BeaconBlockBody`, `BeaconBlock`,
  and `SignedBeaconBlock` at the two shipped presets.
* `EthCLSpecs.Proofs.Fulu.ConfigValid`: `PresetValid` and `ConfigValid`, the presets and configs
  the proofs accept: the upstream `test_config_invariants.py` rules plus the additions that rule
  out a spec failure, with `decide` instances at `minimal` and `mainnet`.
* `EthCLSpecs.Proofs.Fulu.EpochSafe`: `EpochSafe`, the states from which `processEpoch` cannot
  fail, with the per-call premise `RewardsWithin` and the budget `EpochBudget`.
* `EthCLSpecs.Proofs.Fulu.EpochSuccess.Stage`, `.Selection`, `.FrameSteps`: the stage invariant
  between substeps, the balance-weighted selection's success under `ZeroChunksOften`, and the
  success of the substeps that write none of the fields the stage reads.
* `EthCLSpecs.Proofs.Fulu.Reachable`: `ReachableState`, the Fulu states the state transition
  reaches from an anchor before the next fork, with its `Anchors`, the `Nat` fork boundary
  `forkSlot`, and the anchor-monotonicity and `unvalidated` lemmas.
* `EthCLSpecs.Proofs.Fulu.StateInvariants`: `SimpleStateInvariants`, four facts every
  reachable Fulu state satisfies; `coreFields` and `RegistrySizes`, the values they read; and
  `KeepsCore`, the step property nearly every substep has, with the frame tactics.
* `EthCLSpecs.Proofs.Fulu.Invariants.Helpers`, `.Epoch`, `.Justification`, `.Block`, `.Slots`:
  one fact per spec step. The shared mutators, fourteen epoch substeps and six block substeps
  are `KeepsCore`; justification moves the checkpoint bound from the previous to the current
  epoch; `processSlots_ensures` and the slot-increment lemmas join them over a run of slots.
* `EthCLSpecs.Proofs.Fulu.ReachableInvariants`: `ReachableState.simpleStateInvariants`, the
  induction; the window bound, slot monotonicity, closure under `stateTransition`, and
  `simpleStateInvariants_not_sufficient`.
-/
