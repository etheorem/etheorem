import EthCLSpecs.Fulu
import EthCLSpecs.Gloas
import EthCLSpecs.Heze

/-!
# `EthCLSpecs.Tests.DepositOperationPins`: the `deposit` operation has no handler

No in-scope fork processes an in-block deposit. The pinned Fulu `process_operations`
(`fulu/minimal.py:1981-1998`) asserts `len(body.deposits) == 0` and drops
`process_deposit`, and Gloas and Heze carry no `process_deposit` either. The pin ships no
`operations/deposit` vector for any of the three forks.

So each fork interface rejects an `operations/deposit` request in the dispatch, before it
decodes the operation. The reject is a `todo` (`StateTransitionError.todo`), and the
driver reports it in the `todo` bucket (`xfail`). These pins hold that answer in all three
forks at both presets:

1. `runOperation .deposit` over a decodable pre-state rejects with `.spec (.todo _)`. The
   pre-state is the serialized default `BeaconState`, so a decode fault cannot stand in
   for the reject: a pre-state decode fault is `.decode`, which the pin does not accept.
2. The generic driver classifies an `operations/deposit` case in the `todo` bucket.

The operation bytes are empty. No fork decodes them, because the arm rejects first.
`decodeState` builds an FFI-backed box, so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests

namespace EthCLSpecs.Tests.DepositOperationPins

/-- `true` when interface `I` rejects `operations/deposit` over pre-state `pre` with a
`todo`. `ForkInterface` is a class, so `@` passes the instance `I` explicitly. -/
def rejectsDeposit (I : ForkInterface) (pre : ByteArray) : Bool :=
  match @ForkInterface.runOperation I .deposit pre ByteArray.empty {} with
  | .error (.spec (.todo _)) => true
  | _                        => false

/-- An `operations/deposit` case over pre-state `pre`, marked invalid (no post-state). -/
def depositReq (pre : ByteArray) : CaseRequest :=
  { runner := "operations", handler := "deposit", pre, post := none,
    inputs := #[ByteArray.empty], caseMeta := {} }

/-- `true` when the driver reports the `operations/deposit` case under `I` in the `todo`
bucket. -/
def depositBucketIsTodo (I : ForkInterface) (pre : ByteArray) : Bool :=
  (@runCase I (depositReq pre)).bucket == ClassifyBucket.todo

/-! ## Fulu -/

example : rejectsDeposit Fulu.Interface.fuluInterface
    (SizzLean.SSZ.serialize (default : @Fulu.BeaconState Fulu.minimal)) = true := by native_decide
example : rejectsDeposit Fulu.Interface.fuluInterfaceMainnet
    (SizzLean.SSZ.serialize (default : @Fulu.BeaconState Fulu.mainnet)) = true := by native_decide
example : depositBucketIsTodo Fulu.Interface.fuluInterface
    (SizzLean.SSZ.serialize (default : @Fulu.BeaconState Fulu.minimal)) = true := by native_decide

/-! ## Gloas -/

example : rejectsDeposit Gloas.Interface.gloasInterface
    (SizzLean.SSZ.serialize (default : @Gloas.BeaconState Gloas.minimal)) = true := by native_decide
example : rejectsDeposit Gloas.Interface.gloasInterfaceMainnet
    (SizzLean.SSZ.serialize (default : @Gloas.BeaconState Gloas.mainnet)) = true := by native_decide
example : depositBucketIsTodo Gloas.Interface.gloasInterface
    (SizzLean.SSZ.serialize (default : @Gloas.BeaconState Gloas.minimal)) = true := by native_decide

/-! ## Heze -/

example : rejectsDeposit Heze.Interface.hezeInterface
    (SizzLean.SSZ.serialize (default : @Heze.BeaconState Heze.minimal)) = true := by native_decide
example : rejectsDeposit Heze.Interface.hezeInterfaceMainnet
    (SizzLean.SSZ.serialize (default : @Heze.BeaconState Heze.mainnet)) = true := by native_decide
example : depositBucketIsTodo Heze.Interface.hezeInterface
    (SizzLean.SSZ.serialize (default : @Heze.BeaconState Heze.minimal)) = true := by native_decide

end EthCLSpecs.Tests.DepositOperationPins
