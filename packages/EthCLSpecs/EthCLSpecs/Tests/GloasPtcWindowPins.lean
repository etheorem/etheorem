import EthCLSpecs.Gloas.EpochProcessing
import EthCLLib.Proofs.StoreRun

/-!
# `EthCLSpecs.Tests.GloasPtcWindowPins`: the PTC window range-end pins

`process_ptc_window` builds `range(start_slot, start_slot + SLOTS_PER_EPOCH)`. The range end is
a `Slot`, so a range end of `2^64` raises `ValueError` before the first `compute_ptc` call. The
pins state what the pinned pyspec (`v1.7.0-alpha.11`, minimal preset) raises on an empty
registry at the two slots on either side of that edge. The probe script that produced the
pyspec side is `.tmp/spike/ptc_window_probe.py` (local, not committed).

* At the edge the range end is `2^64`: pyspec raises `ValueError` (`.arithmetic`).
* One epoch below, the range end is `2^64 - SLOTS_PER_EPOCH`. The range forms, and the first
  `compute_ptc` raises `AssertionError` (`.assert`) on the empty registry.

Both pins close by `native_decide`. The second pin hashes through the FFI SHA-256.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasPtcWindowPins

open EthCLSpecs.Gloas
open EthCLLib.Proofs (pureState)

/-- The result raised the uncaught-fault kind (`.arithmetic`). -/
private def isArith {α : Type} : Except StateTransitionError α → Bool
  | .error (.arithmetic _) => true
  | _ => false

/-- The result raised the expected-rejection kind (`.assert`). -/
private def isAssert {α : Type} : Except StateTransitionError α → Bool
  | .error (.assert _) => true
  | _ => false

/-- `process_ptc_window` over an empty minimal Gloas state at `slot`, run in the proving
monad (`StateT` over `Except`). -/
private def runAt (slot : Nat) : Except StateTransitionError (Unit × @State minimal fastHasherTag) :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  (processPtcWindow (StateTransition := StateT State (Except StateTransitionError))).run
    (pureState { (default : BeaconState) with slot := UInt64.ofNat slot })

-- Edge: slot `2^64 - 24` puts `next_epoch` at `2^61 - 1`, so the range end is `2^64`.
example : isArith (runAt (2 ^ 64 - 24)) = true := by native_decide

-- One epoch below: the range end is `2^64 - 8`, and the empty-registry selection asserts.
example : isAssert (runAt (2 ^ 64 - 32)) = true := by native_decide

end EthCLSpecs.Tests.GloasPtcWindowPins
