import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving

/-!
# `SizzLeanBench.Fulu`: local copy of Fulu BeaconState types

The bench needs a realistic consensus-spec-shaped container to
measure cache vs pure behaviour against. LeanEthCS has the
spec-accurate definitions, but having SizzLeanBench depend on
LeanEthCS would create a cycle (`LeanEthCS` already depends on
`SizzLean`, and `SizzLeanBench` is a `lean_lib` inside the
`SizzLean` package). Instead, we hold a **copy** of the
container types here.

The copy is a reference fixture, *not* a spec replica. It tracks
the Fulu/main-branch `BeaconState` shape (37 fields, including
`proposer_lookahead`) at the moment of writing but is **not
expected to stay in sync** with LeanEthCS or the upstream spec.
If you need spec-accurate types use `LeanEthCS.Forks.Fulu.*`.

Differences vs the spec / LeanEthCS:

* Mainnet preset values are **baked in as literals** rather than
  parameterised by a `Preset` record. The bench only runs at
  mainnet scale; the minimal preset isn't built.
* `BeaconState` is one concrete `structure`, not a
  `ssz_struct_for_presets` pair. The `ssz_struct_for_presets`
  macro lives in LeanEthCS, keeping the bench types as plain
  `structure`s avoids the macro dependency.
* Sub-containers are byte-for-byte identical to the LeanEthCS
  versions where the LeanEthCS version is itself a plain
  `structure` (e.g. `Validator`, `Checkpoint`, `Eth1Data`); the
  preset-variant ones (`SyncCommittee`, `BeaconState`) are
  represented as the Mainnet variant only.

The `Inhabited` instance on `Validator` is provided here (the
spec definition only derives `SSZRepr`); the bench needs
`Inhabited` for `xs[i]!` semantics on the validators list.
-/

set_option autoImplicit false

namespace SizzLeanBench.Fulu

open SizzLean
open SizzLean.Repr

/-! ## Primitive type aliases (mainnet preset, baked-in) -/

abbrev Slot               : Type := UInt64
abbrev Epoch              : Type := UInt64
abbrev ValidatorIndex     : Type := UInt64
abbrev WithdrawalIndex    : Type := UInt64
abbrev Gwei               : Type := UInt64
abbrev ParticipationFlags : Type := UInt8
abbrev Bytes32            : Type := Vector UInt8 32
abbrev Root               : Type := Vector UInt8 32
abbrev Hash32             : Type := Vector UInt8 32
abbrev ExecutionAddress   : Type := Vector UInt8 20
abbrev BLSPubkey          : Type := Vector UInt8 48
abbrev BLSSignature       : Type := Vector UInt8 96
abbrev Version            : Type := Vector UInt8 4

/-! ## Sub-containers (Phase0, Altair, Capella, Deneb, Electra)

These are all preset-invariant in the spec and ported verbatim. -/

structure Fork where
  previousVersion : Version
  currentVersion  : Version
  epoch           : Epoch
  deriving SSZRepr

structure Checkpoint where
  epoch : Epoch
  root  : Root
  deriving SSZRepr

structure Eth1Data where
  depositRoot  : Root
  depositCount : UInt64
  blockHash    : Hash32
  deriving SSZRepr

structure BeaconBlockHeader where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  bodyRoot      : Root
  deriving SSZRepr

/-- `Validator`: eight fixed-size fields. Same layout as
`LeanEthCS.Forks.Phase0.Validator`, plus an `Inhabited`
instance so `xs[i]!` works on a list of validators. -/
structure Validator where
  pubkey                     : BLSPubkey
  withdrawalCredentials      : Bytes32
  effectiveBalance           : Gwei
  slashed                    : Bool
  activationEligibilityEpoch : Epoch
  activationEpoch            : Epoch
  exitEpoch                  : Epoch
  withdrawableEpoch          : Epoch
  deriving SSZRepr

instance : Inhabited Validator where
  default :=
    { pubkey                     := Vector.replicate 48 0
      withdrawalCredentials      := Vector.replicate 32 0
      effectiveBalance           := 0
      slashed                    := false
      activationEligibilityEpoch := 0
      activationEpoch            := 0
      exitEpoch                  := 0
      withdrawableEpoch          := 0 }

structure HistoricalSummary where
  blockSummaryRoot : Root
  stateSummaryRoot : Root
  deriving SSZRepr

/-- Deneb `ExecutionPayloadHeader`. Preset-invariant, `logsBloom`
is a fixed 256-byte vector, `extraData` is an `SSZList UInt8 32`
(SSZ wire cap), and the base-fee uses a `BitVec 256`. -/
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

/-- Altair `SyncCommittee`, mainnet preset. `pubkeys` is fixed at
`SYNC_COMMITTEE_SIZE = 512` for mainnet (32 for minimal, the bench
only builds the mainnet variant). -/
structure SyncCommittee where
  pubkeys         : Vector BLSPubkey 512
  aggregatePubkey : BLSPubkey
  deriving SSZRepr

/-! ### Electra pending-operation containers -/

structure PendingDeposit where
  pubkey                : BLSPubkey
  withdrawalCredentials : Bytes32
  amount                : Gwei
  signature             : BLSSignature
  slot                  : Slot
  deriving SSZRepr

structure PendingPartialWithdrawal where
  validatorIndex    : ValidatorIndex
  amount            : Gwei
  withdrawableEpoch : Epoch
  deriving SSZRepr

structure PendingConsolidation where
  sourceIndex : ValidatorIndex
  targetIndex : ValidatorIndex
  deriving SSZRepr

/-! ## `BeaconState` (Fulu, mainnet preset)

37 fields total. Preset literals baked in: `SLOTS_PER_HISTORICAL_ROOT
= 8192`, `EPOCHS_PER_HISTORICAL_VECTOR = 65536`,
`EPOCHS_PER_SLASHINGS_VECTOR = 8192`,
`EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH = 64 * 32 = 2048`,
`PENDING_PARTIAL_WITHDRAWALS_LIMIT = 134217728`,
`PENDING_CONSOLIDATIONS_LIMIT = 262144`,
`(MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH = 2 * 32 = 64`.

This shape follows consensus-specs main branch and includes
`proposer_lookahead` (EIP-7917, added post-v1.5.0). -/
structure BeaconState where
  genesisTime                   : UInt64
  genesisValidatorsRoot         : Root
  slot                          : Slot
  fork                          : Fork
  latestBlockHeader             : BeaconBlockHeader
  blockRoots                    : Vector Root 8192
  stateRoots                    : Vector Root 8192
  historicalRoots               : SSZList Root 16777216
  eth1Data                      : Eth1Data
  eth1DataVotes                 : SSZList Eth1Data 2048
  eth1DepositIndex              : UInt64
  validators                    : SSZList Validator 1099511627776
  balances                      : SSZList Gwei 1099511627776
  randaoMixes                   : Vector Bytes32 65536
  slashings                     : Vector Gwei 8192
  previousEpochParticipation    : SSZList ParticipationFlags 1099511627776
  currentEpochParticipation     : SSZList ParticipationFlags 1099511627776
  justificationBits             : Bitvector 4
  previousJustifiedCheckpoint   : Checkpoint
  currentJustifiedCheckpoint    : Checkpoint
  finalizedCheckpoint           : Checkpoint
  inactivityScores              : SSZList UInt64 1099511627776
  currentSyncCommittee          : SyncCommittee
  nextSyncCommittee             : SyncCommittee
  latestExecutionPayloadHeader  : ExecutionPayloadHeader
  nextWithdrawalIndex           : WithdrawalIndex
  nextWithdrawalValidatorIndex  : ValidatorIndex
  historicalSummaries           : SSZList HistoricalSummary 16777216
  depositRequestsStartIndex     : UInt64
  depositBalanceToConsume       : Gwei
  exitBalanceToConsume          : Gwei
  earliestExitEpoch             : Epoch
  consolidationBalanceToConsume : Gwei
  earliestConsolidationEpoch    : Epoch
  pendingDeposits               : SSZList PendingDeposit 134217728
  pendingPartialWithdrawals     : SSZList PendingPartialWithdrawal 134217728
  pendingConsolidations         : SSZList PendingConsolidation 262144
  proposerLookahead             : Vector ValidatorIndex 64
  deriving SSZRepr

end SizzLeanBench.Fulu
