import EthCLSpecs.Fulu.Containers

/-!
# `EthCLSpecs.Fulu.State`: the `BeaconState` definition and its boxed view (load order row 19)

The complete Fulu `BeaconState`, the accumulated Phase 0 → Fulu field list in SSZ
order, then the `State` abbrev that views it as an SSZ box. This module imports
all of the component containers (`Containers`) the state references
(`SPECS_ARCHITECTURE.md` §3.1 row 19).

**Naming note.** SSZ conformance is by field *order*, not field name, so the
consensus `fork` field is named `forkData` here to avoid the `fork` command
keyword; the wire format and root are unchanged.

`State` and the concrete-domain `modifyState` are declared once here by
`state_preamble BeaconState`; every operation file's `state_section` reuses them.
Field access is the framework's generic `sszGet` / `sszUpdate`, so there are no
per-field accessors to colocate.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The complete Fulu `BeaconState`: the accumulated Phase 0 → Fulu field list, in
SSZ order. The consensus `fork` field is `forkData` (keyword avoidance). -/
forkcontainer BeaconState where
  genesisTime                   : UInt64
  genesisValidatorsRoot         : Root
  slot                          : Slot
  forkData                      : Fork
  latestBlockHeader             : BeaconBlockHeader
  blockRoots                    : Vector Root Const.slotsPerHistoricalRoot
  stateRoots                    : Vector Root Const.slotsPerHistoricalRoot
  historicalRoots               : SSZList Root Const.historicalRootsLimit
  eth1Data                      : Eth1Data
  eth1DataVotes                 : SSZList Eth1Data (Const.epochsPerEth1VotingPeriod * Const.slotsPerEpoch)
  eth1DepositIndex              : UInt64
  validators                    : SSZList Validator Const.validatorRegistryLimit
  balances                      : SSZList Gwei Const.validatorRegistryLimit
  randaoMixes                   : Vector Bytes32 Const.epochsPerHistoricalVector
  slashings                     : Vector Gwei Const.epochsPerSlashingsVector
  previousEpochParticipation    : SSZList ParticipationFlags Const.validatorRegistryLimit
  currentEpochParticipation     : SSZList ParticipationFlags Const.validatorRegistryLimit
  justificationBits             : Bitvector Const.justificationBitsLength
  previousJustifiedCheckpoint   : Checkpoint
  currentJustifiedCheckpoint    : Checkpoint
  finalizedCheckpoint           : Checkpoint
  inactivityScores              : SSZList UInt64 Const.validatorRegistryLimit
  currentSyncCommittee          : SyncCommittee
  nextSyncCommittee             : SyncCommittee
  latestExecutionPayloadHeader  : ExecutionPayloadHeader
  nextWithdrawalIndex           : WithdrawalIndex
  nextWithdrawalValidatorIndex  : ValidatorIndex
  historicalSummaries           : SSZList HistoricalSummary Const.historicalRootsLimit
  depositRequestsStartIndex     : UInt64
  depositBalanceToConsume       : Gwei
  exitBalanceToConsume          : Gwei
  earliestExitEpoch             : Epoch
  consolidationBalanceToConsume : Gwei
  earliestConsolidationEpoch    : Epoch
  pendingDeposits               : SSZList PendingDeposit Const.pendingDepositsLimit
  pendingPartialWithdrawals     : SSZList PendingPartialWithdrawal Const.pendingPartialWithdrawalsLimit
  pendingConsolidations         : SSZList PendingConsolidation Const.pendingConsolidationsLimit
  proposerLookahead             : Vector ValidatorIndex (2 * Const.slotsPerEpoch)

-- The once-per-fork preamble: declares `State` (the boxed `BeaconState`) and the
-- concrete-domain `modifyState` (`SPEC_AUTHORING_MODEL.md` §6, `EthCLLib.Spec.Header`).
state_preamble BeaconState

end EthCLSpecs.Fulu
