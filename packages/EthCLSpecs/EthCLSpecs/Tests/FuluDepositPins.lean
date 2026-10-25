import EthCLSpecs.Fulu.EpochProcessing
import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Tests.FuluDepositPins`: the removed eth1-bridge deposit mechanism

Fulu removes the Electra deposit mechanism (`fulu/beacon-chain.md`, modified
`process_operations`, `process_deposit_request` and `process_pending_deposits`). Each pin
states what the pinned pyspec (`v1.7.0-alpha.11`, minimal preset) does on the same input. The
probe script that produced the pyspec side is `.tmp/batchfaith/probe_b1.py` (local, not
committed). Every pin starts from the `default` state.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluDepositPins

open EthCLSpecs.Fulu
open EthCLLib.Proofs (runPure)
open EthCLSpecs.Proofs.Fulu (FuluRun)

section
-- The pins share one preset, config, hasher and crypto backend. The instances stay local to
-- this section.
local instance : Preset := minimal
local instance : Config := minimalConfig
local instance : HasherTag := fastHasherTag
local instance : CryptoBackend := CryptoBackend.realBackend

/-- The run succeeded. -/
private def isOk {α : Type} : Except StateTransitionError α → Bool
  | .ok _ => true
  | .error _ => false

/-- The run raised the expected-rejection kind (`.assert`). -/
private def isAssert {α : Type} : Except StateTransitionError α → Bool
  | .error (.assert _) => true
  | _ => false

/-- A state with `eth1_deposit_index = 0` below `eth1_data.deposit_count = 5`, and an unset
`deposit_requests_start_index`. At this state, the Electra gate requires five deposits in
the block. -/
private def gateState : BeaconState :=
  { (default : BeaconState) with
    eth1Data := { (default : Eth1Data) with depositCount := 5 }
    depositRequestsStartIndex := Const.unsetDepositRequestsStartIndex }

/-! ## `process_operations` -/

-- Q28: pyspec accepts a block with zero deposits.
example : isOk (runPure (processOperations (StateTransition := FuluRun) default) gateState)
    = true := by native_decide

-- Q28: pyspec rejects a block with one deposit (`AssertionError`).
example : isAssert (runPure (processOperations (StateTransition := FuluRun)
    { (default : BeaconBlockBody) with deposits := sszOfArray #[default] }) gateState)
    = true := by native_decide

/-! ## `process_deposit_request` -/

-- P2: pyspec appends one pending deposit and leaves the start index unset.
example : (match runPure (processDepositRequest (StateTransition := FuluRun)
      { (default : DepositRequest) with index := 7, amount := 10 ^ 9 }) gateState with
    | .ok (_, s) =>
      s.depositRequestsStartIndex == Const.unsetDepositRequestsStartIndex
        && s.pendingDeposits.toArray.size == 1
    | .error _ => false) = true := by native_decide

/-! ## `process_pending_deposits` -/

private def pk : BLSPubkey := Vector.replicate 48 0x11

/-- One validator with pubkey `pk` and a 32 ETH balance, a start index of 5 above
`eth1_deposit_index = 0`, finalized epoch 1, and one 1 ETH pending deposit at slot 1. -/
private def bridgeState : BeaconState :=
  { (default : BeaconState) with
    validators := sszOfArray #[{ (default : Validator) with pubkey := pk }]
    balances := sszOfArray #[32 * 10 ^ 9]
    previousEpochParticipation := sszOfArray #[0]
    currentEpochParticipation := sszOfArray #[0]
    inactivityScores := sszOfArray #[0]
    depositRequestsStartIndex := 5
    finalizedCheckpoint := { (default : Checkpoint) with epoch := 1 }
    pendingDeposits := sszOfArray #[{ (default : PendingDeposit) with
      pubkey := pk, amount := 10 ^ 9, slot := 1 }] }

-- P1: pyspec applies the deposit (pending left 0, balance 33 ETH). The Electra scan stopped
-- at it, since `eth1_deposit_index < deposit_requests_start_index`.
example : (match runPure (processPendingDeposits (StateTransition := FuluRun)) bridgeState with
    | .ok (_, s) =>
      s.pendingDeposits.toArray.size == 0 && s.balances.toArray[0]? == some 33000000000
    | .error _ => false) = true := by native_decide

end

end EthCLSpecs.Tests.FuluDepositPins
