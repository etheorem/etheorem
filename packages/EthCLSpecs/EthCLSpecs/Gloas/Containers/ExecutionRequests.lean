import EthCLSpecs.Gloas.Containers.BuilderPayment

/-!
# `EthCLSpecs.Gloas.Containers.ExecutionRequests`: EIP-8282 builder requests

EIP-8282 adds two execution-layer-triggered request types, `BuilderDepositRequest`
and `BuilderExitRequest`, and appends them as two lists to `ExecutionRequests`. Gloas
therefore overrides the inherited Fulu `ExecutionRequests` (3 lists) with this 5-list
version; the extra fields change its Merkle root, which cascades through `inherit` to
everything that embeds it (`BeaconBlockBody.parentExecutionRequests`,
`ExecutionPayloadEnvelope.executionRequests`). `DepositRequest` / `WithdrawalRequest`
/ `ConsolidationRequest` are the Fulu types inherited in `Gloas.Inherited`.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

/-- An execution-layer-triggered builder deposit (EIP-8282). -/
forkcontainer BuilderDepositRequest where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature

/-- An execution-layer-triggered builder exit (EIP-8282). -/
forkcontainer BuilderExitRequest where
  sourceAddress : ExecutionAddress
  pubkey        : BLSPubkey

/-- The execution requests bundled with a payload (Gloas / EIP-8282 / EIP-7688):
the Electra three plus the two builder-request lists, as a progressive
container of progressive lists. The per-payload caps are processing asserts,
not SSZ limits. -/
@[sizzlean_progressive]
forkcontainer ExecutionRequests where
  deposits        : ProgressiveList DepositRequest
  withdrawals     : ProgressiveList WithdrawalRequest
  consolidations  : ProgressiveList ConsolidationRequest
  builderDeposits : ProgressiveList BuilderDepositRequest
  builderExits    : ProgressiveList BuilderExitRequest

end EthCLSpecs.Gloas
