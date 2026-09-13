"""The ethereum/ssz-specs side of the SizzLean comparative benchmark.

    python ssz_specs_harness.py <state.ssz> <reps>

The harness decodes the ``BeaconState`` the Lean side emitted, roots it,
applies the scenario's writes, and roots it again, timing each of the five
phases. It reports a zero ``wrap_ns``: ssz-specs roots the decoded value
directly, with no wrapping step of its own. It prints one JSON object per line on stdout, with the same keys the
Lean and the Rust harnesses print, so the driver reads all three the same
way. Diagnostics go to stderr.

ssz-specs is the reference implementation the SSZ specification is written
as. It is Python, and it optimises for saying what the format is rather than
for throughput. Its numbers are two to three orders of magnitude off the two
compiled libraries, which is the expected result and not a defect. It does
carry a root memo, so a value whose parts did not change reuses their roots
on a second rooting, and the ``update1`` scenario shows that.

The container set below is the Python copy of ``SizzLeanBench.Fulu``. The
two must agree field for field, in order and in type. The benchmark driver
checks the agreement by comparing the roots the harnesses print.
"""

import io
import json
import sys
import time

from ssz.bitfields import BitVector
from ssz.byte_arrays import ByteList, ByteVector
from ssz.boolean import Boolean
from ssz.collections import List, Vector
from ssz.container import Container
from ssz.uint import Uint64, Uint256

# ── Preset constants, at mainnet values ──────────────────────────────────
#
# The Lean fixture bakes these in as literals too. Both sides read the same
# wire bytes, so a disagreement here shows up as a decode failure or as a
# root mismatch, never as a silent difference.

SLOTS_PER_HISTORICAL_ROOT = 8192
EPOCHS_PER_HISTORICAL_VECTOR = 65536
EPOCHS_PER_SLASHINGS_VECTOR = 8192
EPOCHS_PER_ETH1_VOTING_PERIOD_SLOTS = 2048
SYNC_COMMITTEE_SIZE = 512
PROPOSER_LOOKAHEAD_LENGTH = 64
VALIDATOR_REGISTRY_LIMIT = 1099511627776
HISTORICAL_ROOTS_LIMIT = 16777216
PENDING_DEPOSITS_LIMIT = 134217728
PENDING_PARTIAL_WITHDRAWALS_LIMIT = 134217728
PENDING_CONSOLIDATIONS_LIMIT = 262144
MAX_EXTRA_DATA_BYTES = 32
BYTES_PER_LOGS_BLOOM = 256

WRITES_PER_SHAPE = 250
"""Writes per shape in the ``update1000`` scenario. Four shapes, so the
scenario writes 1000 fields."""


# ── Byte-string aliases ──────────────────────────────────────────────────


class Bytes4(ByteVector):
    LENGTH = 4


class Bytes20(ByteVector):
    LENGTH = 20


class Bytes32(ByteVector):
    LENGTH = 32


class Bytes48(ByteVector):
    LENGTH = 48


class Bytes96(ByteVector):
    LENGTH = 96


class Bytes256(ByteVector):
    LENGTH = 256


class ExtraData(ByteList):
    LIMIT = MAX_EXTRA_DATA_BYTES


# ── Sub-containers ───────────────────────────────────────────────────────


class Fork(Container):
    previous_version: Bytes4
    current_version: Bytes4
    epoch: Uint64


class Checkpoint(Container):
    epoch: Uint64
    root: Bytes32


class Eth1Data(Container):
    deposit_root: Bytes32
    deposit_count: Uint64
    block_hash: Bytes32


class BeaconBlockHeader(Container):
    slot: Uint64
    proposer_index: Uint64
    parent_root: Bytes32
    state_root: Bytes32
    body_root: Bytes32


class Validator(Container):
    pubkey: Bytes48
    withdrawal_credentials: Bytes32
    effective_balance: Uint64
    slashed: Boolean
    activation_eligibility_epoch: Uint64
    activation_epoch: Uint64
    exit_epoch: Uint64
    withdrawable_epoch: Uint64


class HistoricalSummary(Container):
    block_summary_root: Bytes32
    state_summary_root: Bytes32


class ExecutionPayloadHeader(Container):
    parent_hash: Bytes32
    fee_recipient: Bytes20
    state_root: Bytes32
    receipts_root: Bytes32
    logs_bloom: Bytes256
    prev_randao: Bytes32
    block_number: Uint64
    gas_limit: Uint64
    gas_used: Uint64
    timestamp: Uint64
    extra_data: ExtraData
    base_fee_per_gas: Uint256
    block_hash: Bytes32
    transactions_root: Bytes32
    withdrawals_root: Bytes32
    blob_gas_used: Uint64
    excess_blob_gas: Uint64


class SyncCommitteePubkeys(Vector[Bytes48]):
    LENGTH = SYNC_COMMITTEE_SIZE


class SyncCommittee(Container):
    pubkeys: SyncCommitteePubkeys
    aggregate_pubkey: Bytes48


class PendingDeposit(Container):
    pubkey: Bytes48
    withdrawal_credentials: Bytes32
    amount: Uint64
    signature: Bytes96
    slot: Uint64


class PendingPartialWithdrawal(Container):
    validator_index: Uint64
    amount: Uint64
    withdrawable_epoch: Uint64


class PendingConsolidation(Container):
    source_index: Uint64
    target_index: Uint64


# ── The state's collection fields ────────────────────────────────────────


class BlockRoots(Vector[Bytes32]):
    LENGTH = SLOTS_PER_HISTORICAL_ROOT


class StateRoots(Vector[Bytes32]):
    LENGTH = SLOTS_PER_HISTORICAL_ROOT


class RandaoMixes(Vector[Bytes32]):
    LENGTH = EPOCHS_PER_HISTORICAL_VECTOR


class Slashings(Vector[Uint64]):
    LENGTH = EPOCHS_PER_SLASHINGS_VECTOR


class ProposerLookahead(Vector[Uint64]):
    LENGTH = PROPOSER_LOOKAHEAD_LENGTH


class HistoricalRoots(List[Bytes32]):
    LIMIT = HISTORICAL_ROOTS_LIMIT


class Eth1DataVotes(List[Eth1Data]):
    LIMIT = EPOCHS_PER_ETH1_VOTING_PERIOD_SLOTS


class Validators(List[Validator]):
    LIMIT = VALIDATOR_REGISTRY_LIMIT


class Balances(List[Uint64]):
    LIMIT = VALIDATOR_REGISTRY_LIMIT


class ParticipationFlags(ByteList):
    LIMIT = VALIDATOR_REGISTRY_LIMIT


class InactivityScores(List[Uint64]):
    LIMIT = VALIDATOR_REGISTRY_LIMIT


class HistoricalSummaries(List[HistoricalSummary]):
    LIMIT = HISTORICAL_ROOTS_LIMIT


class PendingDeposits(List[PendingDeposit]):
    LIMIT = PENDING_DEPOSITS_LIMIT


class PendingPartialWithdrawals(List[PendingPartialWithdrawal]):
    LIMIT = PENDING_PARTIAL_WITHDRAWALS_LIMIT


class PendingConsolidations(List[PendingConsolidation]):
    LIMIT = PENDING_CONSOLIDATIONS_LIMIT


class JustificationBits(BitVector):
    LENGTH = 4


class BeaconState(Container):
    """The Fulu ``BeaconState``, 37 fields at the mainnet preset."""

    genesis_time: Uint64
    genesis_validators_root: Bytes32
    slot: Uint64
    fork: Fork
    latest_block_header: BeaconBlockHeader
    block_roots: BlockRoots
    state_roots: StateRoots
    historical_roots: HistoricalRoots
    eth1_data: Eth1Data
    eth1_data_votes: Eth1DataVotes
    eth1_deposit_index: Uint64
    validators: Validators
    balances: Balances
    randao_mixes: RandaoMixes
    slashings: Slashings
    previous_epoch_participation: ParticipationFlags
    current_epoch_participation: ParticipationFlags
    justification_bits: JustificationBits
    previous_justified_checkpoint: Checkpoint
    current_justified_checkpoint: Checkpoint
    finalized_checkpoint: Checkpoint
    inactivity_scores: InactivityScores
    current_sync_committee: SyncCommittee
    next_sync_committee: SyncCommittee
    latest_execution_payload_header: ExecutionPayloadHeader
    next_withdrawal_index: Uint64
    next_withdrawal_validator_index: Uint64
    historical_summaries: HistoricalSummaries
    deposit_requests_start_index: Uint64
    deposit_balance_to_consume: Uint64
    exit_balance_to_consume: Uint64
    earliest_exit_epoch: Uint64
    consolidation_balance_to_consume: Uint64
    earliest_consolidation_epoch: Uint64
    pending_deposits: PendingDeposits
    pending_partial_withdrawals: PendingPartialWithdrawals
    pending_consolidations: PendingConsolidations
    proposer_lookahead: ProposerLookahead


# ── The scenarios ────────────────────────────────────────────────────────


def byte32(seed: int, pos: int) -> int:
    """One byte of a 32-byte root, from a seed.

    The Lean copy is ``SizzLeanBench.CompBench.Fixture.byte32``. The two must
    agree, because the roots the writes produce are compared across the
    harnesses.
    """
    return (seed * 31 + pos * 7 + 11) % 256


def mk_root(seed: int) -> Bytes32:
    """A 32-byte root from a seed."""
    return Bytes32(bytes(byte32(seed, pos) for pos in range(32)))


def write_one(state: BeaconState) -> None:
    """The single write: bump ``slot`` by one."""
    state.slot = Uint64(state.slot + 1)


def write_thousand(state: BeaconState) -> None:
    """The thousand writes, in the order the Lean harness applies them:
    validators, balances, ``block_roots``, ``randao_mixes``."""
    for i in range(WRITES_PER_SHAPE):
        validator = state.validators[i]
        validator.effective_balance = Uint64(validator.effective_balance + 1000000)
    for i in range(WRITES_PER_SHAPE):
        state.balances[i] = Uint64(state.balances[i] + 12345)
    for i in range(WRITES_PER_SHAPE):
        state.block_roots[i] = mk_root(i + 90000)
    for i in range(WRITES_PER_SHAPE):
        state.randao_mixes[i] = mk_root(i + 95000)


def run_once(data: bytes, scenario: str, rep: int, write) -> None:
    """Run one repetition of one scenario and print its line."""
    t0 = time.monotonic_ns()
    state = BeaconState.deserialize(io.BytesIO(data), len(data))
    t1 = time.monotonic_ns()

    root1 = state.hash_tree_root()
    t2 = time.monotonic_ns()

    write(state)
    t3 = time.monotonic_ns()

    root2 = state.hash_tree_root()
    t4 = time.monotonic_ns()

    print(
        json.dumps(
            {
                "impl": "ssz-specs",
                "scenario": scenario,
                "rep": rep,
                "deser_ns": t1 - t0,
                # ssz-specs has no wrapping step: it roots the decoded value
                # directly. The key is present so every harness emits the
                # same line shape.
                "wrap_ns": 0,
                "root1_ns": t2 - t1,
                "update_ns": t3 - t2,
                "root2_ns": t4 - t3,
                "root1": "0x" + root1.hex(),
                "root2": "0x" + root2.hex(),
            }
        ),
        flush=True,
    )


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: ssz_specs_harness.py <state.ssz> <reps>", file=sys.stderr)
        return 1
    with open(sys.argv[1], "rb") as handle:
        data = handle.read()
    reps = int(sys.argv[2])
    print(f"fixture bytes: {len(data)}", file=sys.stderr)

    for rep in range(reps):
        run_once(data, "update1", rep, write_one)
    for rep in range(reps):
        run_once(data, "update1000", rep, write_thousand)
    return 0


if __name__ == "__main__":
    sys.exit(main())
