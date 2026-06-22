import EthCLSpecs.Gloas.Containers.Builder

/-!
# `EthCLSpecs.Gloas.Containers.PayloadBid`: the execution-payload bid (EIP-7732)

The proposer's commitment to a builder's future execution payload
(`ExecutionPayloadBid`) and its signed wrapper (`SignedExecutionPayloadBid`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- The proposer's commitment to a builder's future execution payload. -/
forkcontainer ExecutionPayloadBid where
  parentBlockHash       : Hash32
  parentBlockRoot       : Root
  blockHash             : Hash32
  prevRandao            : Bytes32
  feeRecipient          : ExecutionAddress
  gasLimit              : UInt64
  builderIndex          : BuilderIndex
  slot                  : Slot
  value                 : Gwei
  executionPayment      : Gwei
  blobKzgCommitments    : SSZList KZGCommitment Const.maxBlobCommitmentsPerBlock
  executionRequestsRoot : Root

/-- A signed execution-payload bid. -/
signedwrapper SignedExecutionPayloadBid wraps ExecutionPayloadBid

end EthCLSpecs.Gloas
