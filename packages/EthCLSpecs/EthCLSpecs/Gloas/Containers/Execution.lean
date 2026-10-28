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

namespace EthCLSpecs.Gloas

/-- `ExecutionPayload` (Gloas, EIP-7688): the Fulu payload plus
`block_access_list` and `slot_number`, as a progressive container.
`transactions` is a progressive list of `ProgressiveByteList`s;
`withdrawals` is a progressive list. `extraData` stays a capped byte list. -/
@[sizzlean_progressive]
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
  transactions    : ProgressiveList Transaction
  withdrawals     : ProgressiveList Withdrawal
  blobGasUsed     : UInt64
  excessBlobGas   : UInt64
  blockAccessList : ProgressiveList UInt8
  slotNumber      : UInt64

/-- `ExecutionPayloadEnvelope` (EIP-7732, EIP-7688): the revealed payload plus its
execution requests and the bindings the envelope check verifies against the
committed bid. A progressive container. -/
@[sizzlean_progressive]
forkcontainer ExecutionPayloadEnvelope where
  payload                : ExecutionPayload
  executionRequests      : ExecutionRequests
  builderIndex           : BuilderIndex
  beaconBlockRoot        : Root
  parentBeaconBlockRoot  : Root

/-- A signed `ExecutionPayloadEnvelope`. -/
signedwrapper SignedExecutionPayloadEnvelope wraps ExecutionPayloadEnvelope

/-- `NewPayloadRequest` (Gloas, EIP-7688, `gloas/beacon-chain.md:988-995`): the Electra
request as a progressive container of width 4, over the Gloas payload and execution
requests. `versioned_hashes` stays the capped `VersionedHashes` list, which Gloas does not
modify. No modeled path builds one: the engine answer reads the `[ExecutionEngine]` seam
(`verifyAndNotifyNewPayload`), which takes the request's fields directly. The `ssz_static`
vectors cover the container. -/
@[sizzlean_progressive]
forkcontainer NewPayloadRequest where
  executionPayload      : ExecutionPayload
  versionedHashes       : SSZList VersionedHash Const.maxBlobCommitmentsPerBlock
  parentBeaconBlockRoot : Root
  executionRequests     : ExecutionRequests

end EthCLSpecs.Gloas
