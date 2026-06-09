import LeanEthCS.Primitives
import LeanEthCS.Forks.Gloas.Primitives
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Electra.Requests
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.Execution`: ePBS execution-envelope containers

EIP-7732 splits the beacon block from its execution payload. The
proposer commits to a builder's *bid* (`ExecutionPayloadBid`) in the
beacon block; the builder later reveals the actual payload in a
signed *envelope* (`ExecutionPayloadEnvelope`).

## Note on `ExecutionPayload`

Gloas's `ExecutionPayload` is Deneb's payload plus two fields:
* `block_access_list : BlockAccessList` (EIP-7928), a variable-size
  byte list (`ByteList[MAX_BYTES_PER_TRANSACTION]`, `2^30` cap);
* `slot_number : uint64` (EIP-7843).

Both are defined below and the envelope's `payload` field points at
this Gloas `ExecutionPayload`.

## Containers

* `ExecutionPayloadBid`: what the proposer signs into the beacon
  block: the builder's commitment to a future payload (parent
  hashes, block hash, gas limit, value, etc.).
* `SignedExecutionPayloadBid`: bid + builder signature.
* `ExecutionPayloadEnvelope`: the post-attestation reveal: actual
  payload + execution requests + builder/block linkage.
* `SignedExecutionPayloadEnvelope`: envelope + builder signature.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Electra (ExecutionRequests)
open LeanEthCS.Forks.Bellatrix (Transaction)
open LeanEthCS.Forks.Capella (Withdrawal)
open LeanEthCS.Macros

ssz_struct_for_presets ExecutionPayloadBid in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  parentBlockHash       : Hash32,
  parentBlockRoot       : Root,
  blockHash             : Hash32,
  prevRandao            : Bytes32,
  feeRecipient          : ExecutionAddress,
  gasLimit              : UInt64,
  builderIndex          : BuilderIndex,
  slot                  : Slot,
  value                 : Gwei,
  executionPayment      : Gwei,
  blobKzgCommitments    : SSZList KZGCommitment @@MAX_BLOB_COMMITMENTS_PER_BLOCK,
  executionRequestsRoot : Root

ssz_struct_for_presets SignedExecutionPayloadBid in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  message   : @%ExecutionPayloadBid,
  signature : BLSSignature

/-- `BlockAccessList` (EIP-7928): `ByteList[MAX_BYTES_PER_TRANSACTION]` in this
spec revision (a variable-size byte list, `2^30` cap; empty in current vectors). -/
abbrev BlockAccessList := SSZList UInt8 1073741824

/-! Gloas `ExecutionPayload`: Deneb's payload plus the EIP-7928 `block_access_list`
and the EIP-7843 `slot_number`. -/
ssz_struct_for_presets ExecutionPayload in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  parentHash      : Hash32,
  feeRecipient    : ExecutionAddress,
  stateRoot       : Bytes32,
  receiptsRoot    : Bytes32,
  logsBloom       : Vector UInt8 256,
  prevRandao      : Bytes32,
  blockNumber     : UInt64,
  gasLimit        : UInt64,
  gasUsed         : UInt64,
  timestamp       : UInt64,
  extraData       : SSZList UInt8 32,
  baseFeePerGas   : BitVec 256,
  blockHash       : Hash32,
  transactions    : SSZList Transaction 1048576,
  withdrawals     : SSZList Withdrawal @@MAX_WITHDRAWALS_PER_PAYLOAD,
  blobGasUsed     : UInt64,
  excessBlobGas   : UInt64,
  blockAccessList : BlockAccessList,
  slotNumber      : UInt64

/-! The post-PTC-attestation envelope: the builder's actual payload plus
execution requests, linked back to the proposer's beacon block. -/
ssz_struct_for_presets ExecutionPayloadEnvelope in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  payload              : @%ExecutionPayload,
  executionRequests    : ExecutionRequests,
  builderIndex         : BuilderIndex,
  beaconBlockRoot      : Root,
  parentBeaconBlockRoot : Root

ssz_struct_for_presets SignedExecutionPayloadEnvelope in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  message   : @%ExecutionPayloadEnvelope,
  signature : BLSSignature

end LeanEthCS.Forks.Gloas
