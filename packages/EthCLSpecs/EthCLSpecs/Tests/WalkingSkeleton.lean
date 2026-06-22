import EthCLSpecs

/-!
# `EthCLSpecs.Tests.WalkingSkeleton`: the Phase 1 end-to-end self-test

Confirms the walking skeleton runs, not just typechecks (`PLAN.md` §1.1, §1.2
acceptance):

- a `forkdef` step (`processSlot`) **executes** at the fast config `EStateM
  StateTransitionError (Box Sha256 BeaconState)`, round-tripping `sszGet` /
  `sszUpdate` over the boxed state;
- the fork-interface `stateRoot` decodes a `BeaconState` and reproduces its root;
- the deferral safety net works: a `todo` stub a vector reaches fails loudly
  (the driver classifies it out-of-scope, never a silent pass);
- the generic driver dispatches a `CaseRequest` to the interface and classifies.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open EthCLSpecs.Fulu
open EthCLSpecs.Fulu.Interface
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.WalkingSkeleton

/-- Advance a default `BeaconState` to slot `n` through the real `processSlots`
(below the first epoch boundary, so no `processEpoch`) and read back the slot.
Exercises the generated header, `[HasherTag]`, the `EStateM`-over-a-box
composition, and `sszGet` / `sszUpdate`. -/
def slotAfter (n : Nat) : UInt64 :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let box0 : SSZ.Box Sha256 (@BeaconState minimal) := SSZ.FastBox default
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@BeaconState minimal)) Unit :=
    processSlots (UInt64.ofNat n)
  match action.run box0 with
  | .ok _ st   => sszGet st slot
  | .error _ _ => 0xdead

-- The spine runs: `processSlots` advances `slot` from 0 to the target.
#guard slotAfter 1 = 1
#guard slotAfter 5 = 5

/-- `stateRoot` decodes a serialized `BeaconState` and reproduces its root. The
FFI `Sha256` reduces only through the compiler, so `native_decide`. -/
example :
    (fuluInterface.stateRoot (SizzLean.SSZ.serialize (default : @BeaconState minimal))).toOption
      = some (stateRoot! (SSZ.FastBox (default : @BeaconState minimal))) := by
  native_decide

/-- `runSlots` through the interface advances the state and returns a root. -/
example :
    (fuluInterface.runSlots (SizzLean.SSZ.serialize (default : @BeaconState minimal)) 3).toOption.isSome := by
  native_decide

-- A still-deferred entry (`runGenesis`) returns a `todo` reject, the typed
-- deferral safety net: a vector that reaches it fails loudly, never silently.
#guard (match fuluInterface.runGenesis #[] {} with
  | .error (.spec (.todo _)) => true | _ => false)

/-- A `genesis` request. `runGenesis` is a `todo`; the driver classifies the
unimplemented path out-of-scope so the case fails rather than passing silently. -/
def sampleGenesisReq : CaseRequest :=
  { runner := "genesis", handler := "initialization",
    pre := ByteArray.empty, post := some ByteArray.empty, inputs := #[], caseMeta := {} }

-- The driver dispatches to the interface and classifies the unimplemented path.
#guard (@runCase fuluInterface sampleGenesisReq).passed = false
#guard (@runCase fuluInterface sampleGenesisReq).bucket = ClassifyBucket.outOfScope

end EthCLSpecs.Tests.WalkingSkeleton
