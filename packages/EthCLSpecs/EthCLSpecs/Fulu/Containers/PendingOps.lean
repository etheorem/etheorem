import EthCLSpecs.Fulu.Containers.Deposit

/-!
# `EthCLSpecs.Fulu.Containers.PendingOps`: Electra pending-operation queues (load order row 15)

The three Electra pending-operation records the state queues: `PendingDeposit`,
`PendingPartialWithdrawal`, `PendingConsolidation` (`SPECS_ARCHITECTURE.md` §3.1).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- An Electra pending deposit. -/
forkcontainer PendingDeposit where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature
  slot                  : Slot

/-- An Electra pending partial withdrawal. -/
forkcontainer PendingPartialWithdrawal where
  validatorIndex    : ValidatorIndex
  amount            : Gwei
  withdrawableEpoch : Epoch

/-- An Electra pending consolidation. -/
forkcontainer PendingConsolidation where
  sourceIndex : ValidatorIndex
  targetIndex : ValidatorIndex

end EthCLSpecs.Fulu
