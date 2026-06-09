import LeanEthCS.Primitives
import LeanEthCS.Forks.Bellatrix.Execution
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Capella.Execution`: Capella execution-payload containers

Capella adds the `withdrawals` field to `ExecutionPayload` and the
matching `withdrawals_root` to `ExecutionPayloadHeader`. The rest of
the payload shape is unchanged from Bellatrix.

`ExecutionPayloadHeader` is preset-invariant (the new
`withdrawals_root` is a fixed-size `Root`); `ExecutionPayload` is
preset-variant via the `MAX_WITHDRAWALS_PER_PAYLOAD` cap (4 minimal /
16 mainnet).
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Capella

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Bellatrix (Transaction)
open LeanEthCS.Macros

ssz_struct_for_presets ExecutionPayload in LeanEthCS.Forks.Capella
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
  withdrawals   : SSZList Withdrawal @@MAX_WITHDRAWALS_PER_PAYLOAD

/-- `ExecutionPayloadHeader` (Capella), Bellatrix's header plus a
trailing `withdrawals_root`. Preset-invariant (no preset-sensitive
caps). -/
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
  deriving SSZRepr

end LeanEthCS.Forks.Capella
