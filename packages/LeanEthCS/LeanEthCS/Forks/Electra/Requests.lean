import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Electra.Requests`: Electra execution-layer requests

EIPs 6110 (deposit requests), 7002 (withdrawal requests), and 7251
(consolidation requests) move three operation types from beacon-chain
processing into the execution layer. The EL emits them in
`ExecutionRequests`, which the beacon block embeds.

All four containers and their list caps are preset-invariant.

## Caps

* `MAX_DEPOSIT_REQUESTS_PER_PAYLOAD = 8192`
* `MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD = 16`
* `MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD = 2`
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Electra

open SizzLean

open SizzLean.Repr

open LeanEthCS

/-- `DepositRequest` (EIP-6110). -/
structure DepositRequest where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature
  index                 : UInt64
  deriving SSZRepr

/-- `WithdrawalRequest` (EIP-7002). -/
structure WithdrawalRequest where
  sourceAddress    : ExecutionAddress
  validatorPubkey  : BLSPubkey
  amount           : Gwei
  deriving SSZRepr

/-- `ConsolidationRequest` (EIP-7251). -/
structure ConsolidationRequest where
  sourceAddress : ExecutionAddress
  sourcePubkey  : BLSPubkey
  targetPubkey  : BLSPubkey
  deriving SSZRepr

/-- `ExecutionRequests`: the union of EL-emitted operation lists.
Preset-invariant: all three caps are the same on minimal and mainnet. -/
structure ExecutionRequests where
  deposits       : SSZList DepositRequest 8192
  withdrawals    : SSZList WithdrawalRequest 16
  consolidations : SSZList ConsolidationRequest 2
  deriving SSZRepr

end LeanEthCS.Forks.Electra
