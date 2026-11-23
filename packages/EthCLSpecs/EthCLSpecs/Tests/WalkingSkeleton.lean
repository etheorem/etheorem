import EthCLSpecs

/-!
# `EthCLSpecs.Tests.WalkingSkeleton`: the Phase 1 end-to-end self-test

Confirms the walking skeleton runs, not just typechecks (`PLAN.md` §1.1, §1.2
acceptance):

- a `forkdef` step (`processSlot`) **executes** at the fast config `EStateM
  StateTransitionError BeaconState`, round-tripping `sszGet` / `sszUpdate` over
  the plain state;
- the fork-interface `stateRoot` decodes a `BeaconState` and reproduces its root;
- the deferral safety net works: a vector that reaches an `outOfScope` entry
  (`runGenesis`) does not pass, and the driver reports it in the `outOfScope` (`skip`) bucket;
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
Exercises the generated header, `[HasherTag]`, the `EStateM` composition over
the plain state, and `sszGet` / `sszUpdate`. -/
def slotAfter (n : Nat) : Nat :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st0 : @BeaconState minimal := default
  let action : EStateM StateTransitionError (@BeaconState minimal) Unit := do
    -- The target slot is the checked narrow of the plain count.
    let target ← CLUint64.ofNat? n
    processSlots target
  match action.run st0 with
  | .ok _ st   => (sszGet st slot).toPlainNat
  | .error _ _ => 0xdead

-- The spine runs: `processSlots` advances `slot` from 0 to the target.
#guard slotAfter 1 = 1
#guard slotAfter 5 = 5

/-- `stateRoot` decodes a serialized `BeaconState` and reproduces its root. The right
side roots the record with `Sha256`, the hasher of `fastHasherTag`, which the interface
roots with. The FFI `Sha256` reduces only through the compiler, so `native_decide`. -/
example :
    (fuluInterface.stateRoot (SizzLean.SSZ.serialize (default : @BeaconState minimal))).toOption
      = some (SizzLean.SSZ.hashTreeRoot Sha256 (default : @BeaconState minimal)) := by
  native_decide

/-- `runSlots` through the interface advances the state and returns a root. -/
example :
    (fuluInterface.runSlots (SizzLean.SSZ.serialize (default : @BeaconState minimal)) 3).toOption.isSome := by
  native_decide

-- An out-of-scope entry (`runGenesis`, a runner we deliberately do not model)
-- returns an `outOfScope` reject: a vector that reaches it is reported `skip`,
-- never silently passed and never counted in the `todo` work-queue.
#guard (match fuluInterface.runGenesis #[] {} with
  | .error (.spec (.outOfScope _)) => true | _ => false)

/-- A `genesis` request. `runGenesis` is `outOfScope`; the driver classifies the
unmodelled path `outOfScope` so the case is reported `skip` rather than passing
silently or inflating the `xfail` work-queue. -/
def sampleGenesisReq : CaseRequest :=
  { runner := "genesis", handler := "initialization",
    pre := ByteArray.empty, post := some ByteArray.empty, inputs := #[], caseMeta := {} }

-- The driver dispatches to the interface and classifies the unmodelled path.
#guard (@runCase fuluInterface sampleGenesisReq).passed = false
#guard (@runCase fuluInterface sampleGenesisReq).bucket = ClassifyBucket.outOfScope

end EthCLSpecs.Tests.WalkingSkeleton
