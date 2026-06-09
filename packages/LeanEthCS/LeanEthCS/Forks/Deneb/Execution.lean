import LeanEthCS.Primitives
import LeanEthCS.Forks.Bellatrix.Execution
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Deneb.Execution`: Deneb execution-payload containers

Deneb extends Capella's payload with two new fields,
`blob_gas_used` and `excess_blob_gas`, both `uint64`. Otherwise the
shape carries over.

* `ExecutionPayload`: preset-variant (via the Capella-introduced
  `MAX_WITHDRAWALS_PER_PAYLOAD` cap; 4 minimal / 16 mainnet).
* `ExecutionPayloadHeader`: preset-invariant.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Deneb

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Bellatrix (Transaction)
open LeanEthCS.Forks.Capella (Withdrawal)
open LeanEthCS.Macros

ssz_struct_for_presets ExecutionPayload in LeanEthCS.Forks.Deneb
    for [minimal, mainnet] where
  parentHash    : Hash32,
  feeRecipient  : ExecutionAddress,
  stateRoot     : Bytes32,
  receiptsRoot  : Bytes32,
  logsBloom     : Vector UInt8 256,
  prevRandao    : Bytes32,
  blockNumber   : UInt64,
  gasLimit      : UInt64,
  gasUsed       : UInt64,
  timestamp     : UInt64,
  extraData     : SSZList UInt8 32,
  baseFeePerGas : BitVec 256,
  blockHash     : Hash32,
  transactions  : SSZList Transaction 1048576,
  withdrawals   : SSZList Withdrawal @@MAX_WITHDRAWALS_PER_PAYLOAD,
  blobGasUsed   : UInt64,
  excessBlobGas : UInt64

/-- `ExecutionPayloadHeader` (Deneb), Capella's header + two new
`uint64` blob-gas fields. Preset-invariant. -/
structure ExecutionPayloadHeader where
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
  extraData        : SSZList UInt8 32
  baseFeePerGas    : BitVec 256
  blockHash        : Hash32
  transactionsRoot : Root
  withdrawalsRoot  : Root
  blobGasUsed      : UInt64
  excessBlobGas    : UInt64
  deriving SSZRepr

end LeanEthCS.Forks.Deneb
