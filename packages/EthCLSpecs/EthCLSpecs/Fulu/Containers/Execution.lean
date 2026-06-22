import EthCLSpecs.Fulu.Containers.Sync

/-!
# `EthCLSpecs.Fulu.Containers.Execution`: the execution-payload header (load order row 14)

The Deneb/Electra `ExecutionPayloadHeader` the state keeps as
`latestExecutionPayloadHeader` (`SPECS_ARCHITECTURE.md` §3.1). The full
`ExecutionPayload` and `ExecutionRequests` a block carries live with the block
containers.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The Deneb execution-payload header (the state's `latestExecutionPayloadHeader`). -/
forkcontainer ExecutionPayloadHeader where
  parentHash       : Hash32
  feeRecipient     : ExecutionAddress
  stateRoot        : Bytes32
  receiptsRoot     : Bytes32
  logsBloom        : Vector UInt8 256
  prevRandao       : Bytes32
  blockNumber      : UInt64
  gasLimit         : UInt64
  gasUsed          : UInt64
  timestamp        : UInt64
  extraData        : SSZList UInt8 Const.maxExtraDataBytes
  baseFeePerGas    : BitVec 256
  blockHash        : Hash32
  transactionsRoot : Root
  withdrawalsRoot  : Root
  blobGasUsed      : UInt64
  excessBlobGas    : UInt64

end EthCLSpecs.Fulu
