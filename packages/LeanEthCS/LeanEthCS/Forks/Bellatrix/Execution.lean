import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Bellatrix.Execution`: execution-layer containers

Bellatrix is the merge fork that fuses the beacon chain with an
execution-layer block. This file declares the three execution-layer
containers:

* `ExecutionPayload`     : full payload with the transaction list.
* `ExecutionPayloadHeader`: same shape *minus* `transactions`,
  *plus* a `transactions_root : Root` field. Used in `BeaconState`
  so the state root stays bounded.
* `PowBlock`             : pre-merge anchor (only used during the
  transition handler; survives in the test vectors).

## Preset constants (mainnet *and* minimal agree on these)

* `BYTES_PER_LOGS_BLOOM = 256`
* `MAX_EXTRA_DATA_BYTES = 32`
* `MAX_BYTES_PER_TRANSACTION = 1_073_741_824` (= `2^30`)
* `MAX_TRANSACTIONS_PER_PAYLOAD = 1_048_576`  (= `2^20`)

`uint256` (used by `base_fee_per_gas` / `total_difficulty`) is
served by the `BitVec 256` `SSZRepr` instance in
`SizzLean/Repr/Instances.lean`.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Bellatrix

open SizzLean

open SizzLean.Repr

open LeanEthCS

/-- A single RLP-encoded EL transaction, viewed as an
`SSZ.List[byte, MAX_BYTES_PER_TRANSACTION]`. The cap is `2^30`
bytes, enough for any RLP-encoded transaction but small enough
that the Merkle tree depth stays bounded. -/
abbrev Transaction := SSZList UInt8 1073741824

/-- `ExecutionPayload` (Bellatrix): full EL block payload.
Variable-size (the trailing `extra_data` and `transactions` fields
are variable lists). -/
structure ExecutionPayload where
  parentHash    : Hash32
  feeRecipient  : ExecutionAddress
  stateRoot     : Bytes32
  receiptsRoot  : Bytes32
  logsBloom     : Vector UInt8 256
  prevRandao    : Bytes32
  blockNumber   : UInt64
  gasLimit      : UInt64
  gasUsed       : UInt64
  timestamp     : UInt64
  extraData     : SSZList UInt8 32
  baseFeePerGas : BitVec 256
  blockHash     : Hash32
  transactions  : SSZList Transaction 1048576
  deriving SSZRepr

/-- `ExecutionPayloadHeader` (Bellatrix): like `ExecutionPayload`
but with `transactions_root : Root` instead of the full list. Stored
in `BeaconState` so the state root size stays bounded. -/
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
  deriving SSZRepr

/-- `PowBlock`: pre-merge proof-of-work block anchor. Three
fields; only the merge-transition handler ever sees one. -/
structure PowBlock where
  blockHash       : Hash32
  parentHash      : Hash32
  totalDifficulty : BitVec 256
  deriving SSZRepr

end LeanEthCS.Forks.Bellatrix
