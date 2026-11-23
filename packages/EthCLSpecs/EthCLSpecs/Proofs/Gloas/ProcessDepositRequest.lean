import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Proofs.Gloas.ProcessDepositRequest`: the whole-transition equation

`EthCLSpecs.Gloas.processDepositRequest` (inherited from Fulu) appends one
`PendingDeposit` to the queue, stamped with the current slot, and writes nothing else.
Fulu removed the Electra write of `deposit_requests_start_index`. The record update in
`processDepositRequest_run` leaves that field out, so the theorem states that the run
keeps it.

Statements bind plain `BeaconState` values, and the run reads `preState` itself: the Gloas
`State` is the plain `BeaconState`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLSpecs.Gloas (Slot Preset BeaconState DepositRequest PendingDeposit processDepositRequest)

/-- The pending deposit that `processDepositRequest` appends for `dr` at `slot`. -/
def depositRequestPending [Preset] (dr : DepositRequest) (slot : Slot) : PendingDeposit :=
  { pubkey := dr.pubkey, withdrawalCredentials := dr.withdrawalCredentials,
    amount := dr.amount, signature := dr.signature, slot }

/-- Exact whole-transition contract for `processDepositRequest`: the run on
`preState` appends `depositRequestPending dr preState.slot` to
`pendingDeposits`, and every other field, `depositRequestsStartIndex` included, keeps its
value. -/
@[characterizes EthCLSpecs.Gloas.processDepositRequest]
theorem processDepositRequest_run [Preset] (preState : BeaconState)
    (dr : DepositRequest) :
    (processDepositRequest (StateTransition := GloasRun) dr).run preState
      = .ok ((), { preState with
          pendingDeposits := preState.pendingDeposits.push
            (depositRequestPending dr preState.slot) }) := rfl

/-- The run keeps `deposit_requests_start_index`. -/
theorem processDepositRequest_keeps_startIndex [Preset] (preState : BeaconState)
    (dr : DepositRequest) :
    ((processDepositRequest (StateTransition := GloasRun) dr).run preState).map
        (fun r => r.2.depositRequestsStartIndex)
      = .ok preState.depositRequestsStartIndex := by
  rw [processDepositRequest_run preState dr]
  rfl

end EthCLSpecs.Proofs.Gloas
