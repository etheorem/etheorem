import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Electra.PendingOperations`: Electra pending-ops containers

EIP-7251 introduces three pending-operations queues (deposits,
partial withdrawals, consolidations) that live on `BeaconState`. The
container definitions here are preset-invariant; their *list caps*
(consumed in `BeaconState`) are preset-sensitive.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Electra

open SizzLean

open LeanEthCS

/-- `PendingDeposit`: a deferred deposit waiting to be applied to
the validator registry. -/
structure PendingDeposit where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature
  slot                  : Slot
  deriving SSZRepr

/-- `PendingPartialWithdrawal`: a deferred partial withdrawal. -/
structure PendingPartialWithdrawal where
  validatorIndex   : ValidatorIndex
  amount           : Gwei
  withdrawableEpoch : Epoch
  deriving SSZRepr

/-- `PendingConsolidation`: a deferred merge of `source` into
`target`. -/
structure PendingConsolidation where
  sourceIndex : ValidatorIndex
  targetIndex : ValidatorIndex
  deriving SSZRepr

end LeanEthCS.Forks.Electra
