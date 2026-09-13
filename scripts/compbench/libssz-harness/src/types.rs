//! The Fulu mainnet `BeaconState`, declared against libssz.
//!
//! This is the Rust copy of `SizzLeanBench.Fulu`'s container set. The two
//! must agree field for field, in order and in type, because the harness
//! decodes the wire bytes the Lean side emits. The benchmark driver checks
//! the agreement by comparing the roots the harnesses print.
//!
//! Preset constants are baked in at mainnet values, as they are on the Lean
//! side: 8192 block and state roots, 65536 randao mixes, 8192 slashings,
//! 512 sync-committee keys, 64 proposer-lookahead slots.

use ethereum_types::U256;
use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{SszBitvector, SszList, SszVector};

/// The SSZ list capacity the spec calls `VALIDATOR_REGISTRY_LIMIT`.
pub const VALIDATOR_REGISTRY_LIMIT: usize = 1_099_511_627_776;

/// The capacity of `historical_roots` and `historical_summaries`.
pub const HISTORICAL_ROOTS_LIMIT: usize = 16_777_216;

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Fork {
    pub previous_version: [u8; 4],
    pub current_version: [u8; 4],
    pub epoch: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Checkpoint {
    pub epoch: u64,
    pub root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Eth1Data {
    pub deposit_root: [u8; 32],
    pub deposit_count: u64,
    pub block_hash: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconBlockHeader {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Validator {
    pub pubkey: [u8; 48],
    pub withdrawal_credentials: [u8; 32],
    pub effective_balance: u64,
    pub slashed: bool,
    pub activation_eligibility_epoch: u64,
    pub activation_epoch: u64,
    pub exit_epoch: u64,
    pub withdrawable_epoch: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HistoricalSummary {
    pub block_summary_root: [u8; 32],
    pub state_summary_root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ExecutionPayloadHeader {
    pub parent_hash: [u8; 32],
    pub fee_recipient: [u8; 20],
    pub state_root: [u8; 32],
    pub receipts_root: [u8; 32],
    pub logs_bloom: [u8; 256],
    pub prev_randao: [u8; 32],
    pub block_number: u64,
    pub gas_limit: u64,
    pub gas_used: u64,
    pub timestamp: u64,
    pub extra_data: SszList<u8, 32>,
    pub base_fee_per_gas: U256,
    pub block_hash: [u8; 32],
    pub transactions_root: [u8; 32],
    pub withdrawals_root: [u8; 32],
    pub blob_gas_used: u64,
    pub excess_blob_gas: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SyncCommittee {
    pub pubkeys: SszVector<[u8; 48], 512>,
    pub aggregate_pubkey: [u8; 48],
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PendingDeposit {
    pub pubkey: [u8; 48],
    pub withdrawal_credentials: [u8; 32],
    pub amount: u64,
    pub signature: [u8; 96],
    pub slot: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PendingPartialWithdrawal {
    pub validator_index: u64,
    pub amount: u64,
    pub withdrawable_epoch: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PendingConsolidation {
    pub source_index: u64,
    pub target_index: u64,
}

/// The Fulu `BeaconState`, 37 fields at the mainnet preset.
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconState {
    pub genesis_time: u64,
    pub genesis_validators_root: [u8; 32],
    pub slot: u64,
    pub fork: Fork,
    pub latest_block_header: BeaconBlockHeader,
    pub block_roots: SszVector<[u8; 32], 8192>,
    pub state_roots: SszVector<[u8; 32], 8192>,
    pub historical_roots: SszList<[u8; 32], HISTORICAL_ROOTS_LIMIT>,
    pub eth1_data: Eth1Data,
    pub eth1_data_votes: SszList<Eth1Data, 2048>,
    pub eth1_deposit_index: u64,
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], 65536>,
    pub slashings: SszVector<u64, 8192>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<4>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_execution_payload_header: ExecutionPayloadHeader,
    pub next_withdrawal_index: u64,
    pub next_withdrawal_validator_index: u64,
    pub historical_summaries: SszList<HistoricalSummary, HISTORICAL_ROOTS_LIMIT>,
    pub deposit_requests_start_index: u64,
    pub deposit_balance_to_consume: u64,
    pub exit_balance_to_consume: u64,
    pub earliest_exit_epoch: u64,
    pub consolidation_balance_to_consume: u64,
    pub earliest_consolidation_epoch: u64,
    pub pending_deposits: SszList<PendingDeposit, 134_217_728>,
    pub pending_partial_withdrawals: SszList<PendingPartialWithdrawal, 134_217_728>,
    pub pending_consolidations: SszList<PendingConsolidation, 262_144>,
    pub proposer_lookahead: SszVector<u64, 64>,
}
