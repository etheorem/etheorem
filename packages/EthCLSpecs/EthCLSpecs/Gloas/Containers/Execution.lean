import EthCLSpecs.Gloas.Containers.PayloadAttestation

/-!
# `EthCLSpecs.Gloas.Containers.Execution`: the revealed payload + envelope (EIP-7732)

The execution payload is revealed separately from the block, wrapped in an
`ExecutionPayloadEnvelope` and verified by the fork-choice handler
`on_execution_payload_envelope`. The Gloas `ExecutionPayload` adds the EIP-7928
`block_access_list` (a byte list at this pin) and the EIP-7843 `slot_number`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- `ExecutionPayload` (Gloas): the Fulu payload plus `block_access_list` and
`slot_number`. -/
forkcontainer ExecutionPayload where
  parentHash      : Hash32
  feeRecipient    : ExecutionAddress
  stateRoot       : Bytes32
  receiptsRoot    : Bytes32
  logsBloom       : Vector UInt8 Const.bytesPerLogsBloom
  prevRandao      : Bytes32
  blockNumber     : UInt64
  gasLimit        : UInt64
  gasUsed         : UInt64
  timestamp       : UInt64
  extraData       : SSZList UInt8 Const.maxExtraDataBytes
  baseFeePerGas   : BitVec 256
  blockHash       : Hash32
  transactions    : SSZList Transaction Const.maxTransactionsPerPayload
  withdrawals     : SSZList Withdrawal Const.maxWithdrawalsPerPayload
  blobGasUsed     : UInt64
  excessBlobGas   : UInt64
  blockAccessList : SSZList UInt8 Const.maxBytesPerTransaction
  slotNumber      : UInt64

/-- `ExecutionPayloadEnvelope` (EIP-7732): the revealed payload plus its execution
requests and the bindings the envelope check verifies against the committed bid. -/
forkcontainer ExecutionPayloadEnvelope where
  payload                : ExecutionPayload
  executionRequests      : ExecutionRequests
  builderIndex           : BuilderIndex
  beaconBlockRoot        : Root
  parentBeaconBlockRoot  : Root

/-- A signed `ExecutionPayloadEnvelope`. -/
signedwrapper SignedExecutionPayloadEnvelope wraps ExecutionPayloadEnvelope

end EthCLSpecs.Gloas
