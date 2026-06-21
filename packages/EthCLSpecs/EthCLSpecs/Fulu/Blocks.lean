import EthCLSpecs.Fulu.Containers
import EthCLSpecs.Forms

/-!
# `EthCLSpecs.Fulu.Blocks`: the block-body, operation, and execution containers

The containers a `BeaconBlock` carries: the attestation family
(`AttestationData` / `IndexedAttestation` / `Attestation`), the slashing /
exit / change operations, the deposit family, the Electra execution requests, the
Deneb/Electra `ExecutionPayload`, and the `BeaconBlockBody` / `BeaconBlock` /
`SignedBeaconBlock` that wrap them. Field types and caps are the per-fork
`Const.*` tier, so a child fork inherits or restates a field against its own
constants (`SPECS_ARCHITECTURE.md` §3.1, §4).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-! ## Attestations -/

/-- The attestation data: what slot / committee / chain the vote covers. -/
forkcontainer AttestationData where
  slot            : Slot
  index           : CommitteeIndex
  beaconBlockRoot : Root
  source          : Checkpoint
  target          : Checkpoint

/-- An indexed attestation: the resolved attesting-validator set plus the
aggregate signature (`is_valid_indexed_attestation`'s subject). The
`attesting_indices` cap is the Electra cross-committee bound. -/
forkcontainer IndexedAttestation where
  attestingIndices : SSZList ValidatorIndex (Const.maxValidatorsPerCommittee * Const.maxCommitteesPerSlot)
  data             : AttestationData
  signature        : BLSSignature

/-- A block attestation (Electra EIP-7549: per-committee aggregation bits plus a
`committee_bits` selector over the slot's committees). -/
forkcontainer Attestation where
  aggregationBits : Bitlist (Const.maxValidatorsPerCommittee * Const.maxCommitteesPerSlot)
  data            : AttestationData
  signature       : BLSSignature
  committeeBits    : Bitvector Const.maxCommitteesPerSlot

/-! ## Slashings, exits, changes -/

/-- A signed beacon block header (the slashing evidence unit). -/
signedwrapper SignedBeaconBlockHeader wraps BeaconBlockHeader

/-- A PeerDAS `DataColumnSidecar` (EIP-7594): one extended-blob column (`index`) of
cells, with the matching KZG commitments / proofs, the block header it belongs to,
and the commitments' Merkle inclusion proof. The fork-choice data-availability gate
verifies the cells against the commitments via the KZG cell-proof batch. -/
forkcontainer DataColumnSidecar where
  index                        : ColumnIndex
  column                       : SSZList Cell Const.maxBlobCommitmentsPerBlock
  kzgCommitments               : SSZList KZGCommitment Const.maxBlobCommitmentsPerBlock
  kzgProofs                    : SSZList KZGProof Const.maxBlobCommitmentsPerBlock
  signedBlockHeader            : SignedBeaconBlockHeader
  kzgCommitmentsInclusionProof : Vector Bytes32 Const.kzgCommitmentsInclusionProofDepth

/-- A proposer-slashing: two conflicting signed headers for one slot. -/
forkcontainer ProposerSlashing where
  signedHeader1 : SignedBeaconBlockHeader
  signedHeader2 : SignedBeaconBlockHeader

/-- An attester-slashing: two conflicting indexed attestations. -/
forkcontainer AttesterSlashing where
  attestation1 : IndexedAttestation
  attestation2 : IndexedAttestation

/-- A voluntary exit message. -/
forkcontainer VoluntaryExit where
  epoch          : Epoch
  validatorIndex : ValidatorIndex

/-- A signed voluntary exit. -/
signedwrapper SignedVoluntaryExit wraps VoluntaryExit

/-- A BLS-to-execution withdrawal-credential change message. -/
forkcontainer BLSToExecutionChange where
  validatorIndex     : ValidatorIndex
  fromBlsPubkey      : BLSPubkey
  toExecutionAddress : ExecutionAddress

/-- A signed BLS-to-execution change. -/
signedwrapper SignedBLSToExecutionChange wraps BLSToExecutionChange

/-! ## Deposits -/

/-- The deposit data committed to by the deposit contract Merkle tree. -/
forkcontainer DepositData where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature

/-- A deposit: its Merkle branch into the deposit-contract root plus the data. -/
forkcontainer Deposit where
  proof : Vector Bytes32 (Const.depositContractTreeDepth + 1)
  data  : DepositData

/-! ## Execution requests (Electra EIP-6110 / EIP-7002 / EIP-7251) -/

/-- An execution-layer-triggered deposit request. -/
forkcontainer DepositRequest where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature
  index                 : UInt64

/-- An execution-layer-triggered (partial) withdrawal request. -/
forkcontainer WithdrawalRequest where
  sourceAddress   : ExecutionAddress
  validatorPubkey : BLSPubkey
  amount          : Gwei

/-- An execution-layer-triggered consolidation request. -/
forkcontainer ConsolidationRequest where
  sourceAddress : ExecutionAddress
  sourcePubkey  : BLSPubkey
  targetPubkey  : BLSPubkey

/-- The execution requests bundled into a block (Electra). -/
forkcontainer ExecutionRequests where
  deposits       : SSZList DepositRequest Const.maxDepositRequestsPerPayload
  withdrawals    : SSZList WithdrawalRequest Const.maxWithdrawalRequestsPerPayload
  consolidations : SSZList ConsolidationRequest Const.maxConsolidationRequestsPerPayload

/-! ## Execution payload + sync aggregate -/

/-- The Deneb/Electra execution payload carried in the block body. -/
forkcontainer ExecutionPayload where
  parentHash    : Hash32
  feeRecipient  : ExecutionAddress
  stateRoot     : Bytes32
  receiptsRoot  : Bytes32
  logsBloom     : Vector UInt8 Const.bytesPerLogsBloom
  prevRandao    : Bytes32
  blockNumber   : UInt64
  gasLimit      : UInt64
  gasUsed       : UInt64
  timestamp     : UInt64
  extraData     : SSZList UInt8 Const.maxExtraDataBytes
  baseFeePerGas : BitVec 256
  blockHash     : Hash32
  transactions  : SSZList Transaction Const.maxTransactionsPerPayload
  withdrawals   : SSZList Withdrawal Const.maxWithdrawalsPerPayload
  blobGasUsed   : UInt64
  excessBlobGas : UInt64

/-- The sync-committee aggregate (Altair). -/
forkcontainer SyncAggregate where
  syncCommitteeBits      : Bitvector Const.syncCommitteeSize
  syncCommitteeSignature : BLSSignature

/-! ## Block body and block -/

/-- The full Fulu `BeaconBlockBody`. -/
forkcontainer BeaconBlockBody where
  randaoReveal          : BLSSignature
  eth1Data              : Eth1Data
  graffiti              : Bytes32
  proposerSlashings     : SSZList ProposerSlashing Const.maxProposerSlashings
  attesterSlashings     : SSZList AttesterSlashing Const.maxAttesterSlashingsElectra
  attestations          : SSZList Attestation Const.maxAttestationsElectra
  deposits              : SSZList Deposit Const.maxDeposits
  voluntaryExits        : SSZList SignedVoluntaryExit Const.maxVoluntaryExits
  syncAggregate         : SyncAggregate
  executionPayload      : ExecutionPayload
  blsToExecutionChanges : SSZList SignedBLSToExecutionChange Const.maxBlsToExecutionChanges
  blobKzgCommitments    : SSZList KZGCommitment Const.maxBlobCommitmentsPerBlock
  executionRequests     : ExecutionRequests

/-- A Fulu `BeaconBlock`. -/
forkcontainer BeaconBlock where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  body          : BeaconBlockBody

/-- A signed Fulu `BeaconBlock` (the `sanity/blocks` driver's unit). -/
signedwrapper SignedBeaconBlock wraps BeaconBlock

/-- Per-validator reward / penalty deltas, the `rewards/*` format's comparison
unit (`get_flag_index_deltas` / `get_inactivity_penalty_deltas` each produce one). -/
forkcontainer Deltas where
  rewards   : SSZList Gwei Const.validatorRegistryLimit
  penalties : SSZList Gwei Const.validatorRegistryLimit

end EthCLSpecs.Fulu
