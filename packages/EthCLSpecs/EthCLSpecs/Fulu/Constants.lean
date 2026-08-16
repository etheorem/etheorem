import EthCLLib
import EthCLSpecs.Fulu.Types

/-!
# `EthCLSpecs.Fulu.Constants`: the tier system (load order row 2)

The fork's constants in the three tiers (`SPECS_ARCHITECTURE.md` §9,
`FRAMEWORK_ARCHITECTURE.md` §4). The tier system is per fork, and every
declaration here is a capturing form, so a child fork replays what it keeps
instead of reaching into this namespace: `forkpreset` / `forkconfig` for the two
threaded classes, `forkpresetvalues` / `forkconfigvalues` for the injected value
sets, `forkabbrev` for each `Const` entry, `forkinstance` for the `ValidModulus`
registrations. The author writes `Const.x` everywhere; the tier is classified
once, here.

The `fork Fulu` lineage edge lives in `Fulu/Fork.lean` (row 0), which this module
reaches through `Types`. It has to elaborate before any capturing form runs.

Two numeric flavours, by design: `UInt64` / `Gwei` constants combine directly
with `uint64`-shaped state fields (slots, epochs, indices, balances); `Nat`
constants feed the reward / penalty arithmetic, evaluated in `Nat` (unbounded, no
wraparound) to match the pyspec's Python `int` exactly, narrowing back to `Gwei`
only at the application site. A `…G` suffix marks the `Gwei` form of a value that
also has a `Nat` form.

Values are Fulu/Electra, the conformance fork this body targets. Content a later
fork introduces lives in that fork: `Gloas/Constants.lean` owns the ePBS and
EIP-8282 entries, `Heze/Constants.lean` the FOCIL ones.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- The preset-varying constants. Threaded `[Preset]`; the runner injects
`minimal` or `mainnet`.

Membership is decided by the upstream file, not by whether the two presets
currently agree: everything under `presets/{minimal,mainnet}/*.yaml` sits here,
even where both files say the same number today. A preset value that shapes a
type would otherwise be baked in as a literal, and a future divergence would
silently produce a wrong cap and a wrong Merkle root rather than a build error.
Values the spec lists under its `## Constants` heading (weights, flag indices,
domain tags, sentinels, prefix bytes) stay flat in `Const`. -/
forkpreset where
  slotsPerEpoch : Nat
  slotsPerHistoricalRoot : Nat
  epochsPerHistoricalVector : Nat
  epochsPerSlashingsVector : Nat
  epochsPerEth1VotingPeriod : Nat
  epochsPerSyncCommitteePeriod : Nat
  syncCommitteeSize : Nat
  maxCommitteesPerSlot : Nat
  targetCommitteeSize : Nat
  shuffleRoundCount : Nat
  maxValidatorsPerWithdrawalsSweep : Nat
  maxPendingPartialsPerWithdrawalsSweep : Nat
  maxWithdrawalsPerPayload : Nat
  maxBlobCommitmentsPerBlock : Nat
  pendingPartialWithdrawalsLimit : Nat
  pendingConsolidationsLimit : Nat
  -- Registry and history caps.
  validatorRegistryLimit : Nat
  historicalRootsLimit : Nat
  pendingDepositsLimit : Nat
  -- Per-block operation caps.
  maxProposerSlashings : Nat
  maxAttesterSlashings : Nat
  maxAttestations : Nat
  maxAttesterSlashingsElectra : Nat
  maxAttestationsElectra : Nat
  maxDeposits : Nat
  maxVoluntaryExits : Nat
  maxBlsToExecutionChanges : Nat
  maxValidatorsPerCommittee : Nat
  maxDepositRequestsPerPayload : Nat
  maxWithdrawalRequestsPerPayload : Nat
  maxConsolidationRequestsPerPayload : Nat
  maxPendingDepositsPerEpoch : Nat
  -- Execution-payload shape.
  maxExtraDataBytes : Nat
  maxBytesPerTransaction : Nat
  maxTransactionsPerPayload : Nat
  bytesPerLogsBloom : Nat
  -- Timing and lifecycle.
  maxSeedLookahead : Epoch
  minSeedLookahead : Epoch
  minAttestationInclusionDelay : Slot
  minEpochsToInactivityPenalty : Epoch
  -- Balance thresholds. A `…G` field is the `Gwei` form of the value its
  -- suffix-free twin holds as a `Nat`; both flavours are preset entries because
  -- both read the same YAML key.
  effectiveBalanceIncrement : Nat
  effectiveBalanceIncrementG : Gwei
  minDepositAmountG : Gwei
  minActivationBalance : Gwei
  maxEffectiveBalanceG : Gwei
  maxEffectiveBalanceElectra : Nat
  maxEffectiveBalanceElectraG : Gwei
  hysteresisQuotient : Nat
  hysteresisDownwardMultiplier : Nat
  hysteresisUpwardMultiplier : Nat
  -- Reward / penalty quotients.
  baseRewardFactor : Nat
  minSlashingPenaltyQuotientElectra : Nat
  whistleblowerRewardQuotientElectra : Nat
  proportionalSlashingMultiplierBellatrix : Nat
  inactivityPenaltyQuotientBellatrix : Nat
  -- PeerDAS.
  numberOfColumns : Nat
  kzgCommitmentsInclusionProofDepth : Nat
  -- Well-formedness of the vector-length constants: each is a positive `uint64`-ranged
  -- value (positivity is what a modulo index into a length-`n` vector needs, `< 2 ^ 64`
  -- is the "it is a uint64" the value carries in pyspec). Carried on the preset so the
  -- `[Preset]` already threaded everywhere supplies the bound, with no extra seam.
  slotsPerEpochPos : 0 < slotsPerEpoch
  slotsPerEpochLt : slotsPerEpoch < 2 ^ 64
  slotsPerHistoricalRootPos : 0 < slotsPerHistoricalRoot
  slotsPerHistoricalRootLt : slotsPerHistoricalRoot < 2 ^ 64
  epochsPerHistoricalVectorPos : 0 < epochsPerHistoricalVector
  epochsPerHistoricalVectorLt : epochsPerHistoricalVector < 2 ^ 64

/-- The config-tier values (network parameters). Threaded `[Config]`; never
shapes a type. Membership follows `configs/{minimal,mainnet}.yaml` the same way
`Preset` follows the preset files. -/
forkconfig where
  churnLimitQuotient : UInt64
  minPerEpochChurnLimitElectra : Gwei
  maxPerEpochActivationExitChurnLimit : Gwei
  minValidatorWithdrawabilityDelay : UInt64
  shardCommitteePeriod : UInt64
  genesisForkVersion : Version
  capellaForkVersion : Version
  slotDurationMs : UInt64
  attestationDueBps : UInt64
  ejectionBalanceG : Gwei
  maxBlobsPerBlockElectra : Nat
  consolidationChurnLimitQuotient : UInt64

namespace Const
section
variable [Preset] [Config]

-- Preset tier (each carries `[Preset]`; `abbrev` is reducible so the width reduces
-- to a literal at a concrete preset, which the symbolic-cap derive needs).
forkabbrev slotsPerEpoch : Nat := Preset.slotsPerEpoch
forkabbrev slotsPerHistoricalRoot : Nat := Preset.slotsPerHistoricalRoot
forkabbrev epochsPerHistoricalVector : Nat := Preset.epochsPerHistoricalVector
forkabbrev epochsPerSlashingsVector : Nat := Preset.epochsPerSlashingsVector
forkabbrev epochsPerEth1VotingPeriod : Nat := Preset.epochsPerEth1VotingPeriod
forkabbrev epochsPerSyncCommitteePeriod : Nat := Preset.epochsPerSyncCommitteePeriod
forkabbrev syncCommitteeSize : Nat := Preset.syncCommitteeSize
forkabbrev maxCommitteesPerSlot : Nat := Preset.maxCommitteesPerSlot
forkabbrev targetCommitteeSize : Nat := Preset.targetCommitteeSize
forkabbrev shuffleRoundCount : Nat := Preset.shuffleRoundCount
forkabbrev maxValidatorsPerWithdrawalsSweep : Nat := Preset.maxValidatorsPerWithdrawalsSweep
forkabbrev maxPendingPartialsPerWithdrawalsSweep : Nat := Preset.maxPendingPartialsPerWithdrawalsSweep
forkabbrev maxWithdrawalsPerPayload : Nat := Preset.maxWithdrawalsPerPayload
forkabbrev maxBlobCommitmentsPerBlock : Nat := Preset.maxBlobCommitmentsPerBlock
forkabbrev pendingPartialWithdrawalsLimit : Nat := Preset.pendingPartialWithdrawalsLimit
forkabbrev pendingConsolidationsLimit : Nat := Preset.pendingConsolidationsLimit

-- Well-formedness of the vector-length constants (positive, `uint64`-ranged), surfaced
-- with the `Const.` prefix like the values. The proof-carrying premises of
-- `EthCLLib.Spec.uint64ModOfNatToNatLt` at a modulo index into the matching vector.
forkabbrev slotsPerEpochPos : 0 < slotsPerEpoch := Preset.slotsPerEpochPos
forkabbrev slotsPerEpochLt : slotsPerEpoch < 2 ^ 64 := Preset.slotsPerEpochLt
forkabbrev slotsPerHistoricalRootPos : 0 < slotsPerHistoricalRoot := Preset.slotsPerHistoricalRootPos
forkabbrev slotsPerHistoricalRootLt : slotsPerHistoricalRoot < 2 ^ 64 := Preset.slotsPerHistoricalRootLt
forkabbrev epochsPerHistoricalVectorPos : 0 < epochsPerHistoricalVector := Preset.epochsPerHistoricalVectorPos
forkabbrev epochsPerHistoricalVectorLt : epochsPerHistoricalVector < 2 ^ 64 := Preset.epochsPerHistoricalVectorLt

-- Universal tier (literal body, no binder, identical across presets).
forkabbrev farFutureEpoch : Epoch := 0xffffffffffffffff
forkabbrev genesisSlot : Slot := 0
forkabbrev genesisEpoch : Epoch := 0
forkabbrev validatorRegistryLimit : Nat := Preset.validatorRegistryLimit
forkabbrev historicalRootsLimit : Nat := Preset.historicalRootsLimit
forkabbrev pendingDepositsLimit : Nat := Preset.pendingDepositsLimit
forkabbrev justificationBitsLength : Nat := 4
forkabbrev maxExtraDataBytes : Nat := Preset.maxExtraDataBytes
forkabbrev depositContractTreeDepth : Nat := 32
-- per-block operation caps
forkabbrev maxProposerSlashings : Nat := Preset.maxProposerSlashings
forkabbrev maxAttesterSlashings : Nat := Preset.maxAttesterSlashings
forkabbrev maxAttestations : Nat := Preset.maxAttestations
forkabbrev maxDeposits : Nat := Preset.maxDeposits
forkabbrev maxVoluntaryExits : Nat := Preset.maxVoluntaryExits
forkabbrev maxBlsToExecutionChanges : Nat := Preset.maxBlsToExecutionChanges
forkabbrev maxValidatorsPerCommittee : Nat := Preset.maxValidatorsPerCommittee
forkabbrev maxDepositRequestsPerPayload : Nat := Preset.maxDepositRequestsPerPayload
forkabbrev maxWithdrawalRequestsPerPayload : Nat := Preset.maxWithdrawalRequestsPerPayload
forkabbrev maxConsolidationRequestsPerPayload : Nat := Preset.maxConsolidationRequestsPerPayload
forkabbrev maxAttestationsElectra : Nat := Preset.maxAttestationsElectra
forkabbrev maxAttesterSlashingsElectra : Nat := Preset.maxAttesterSlashingsElectra
forkabbrev maxPendingDepositsPerEpoch : Nat := Preset.maxPendingDepositsPerEpoch
forkabbrev maxBytesPerTransaction : Nat := Preset.maxBytesPerTransaction
forkabbrev maxTransactionsPerPayload : Nat := Preset.maxTransactionsPerPayload
forkabbrev bytesPerLogsBloom : Nat := Preset.bytesPerLogsBloom
-- Balance / effective-balance thresholds, in Gwei. The `G` suffix marks the
-- `Gwei` (`UInt64`) form; the letter abbreviates "Gwei". A threshold that
-- also feeds `Nat` ratio arithmetic carries a suffix-free `Nat` twin of the same
-- value, so `effectiveBalanceIncrement` and `maxEffectiveBalanceElectra` are the
-- `Nat` forms and their `…G` siblings are the `Gwei` forms.
forkabbrev effectiveBalanceIncrement : Nat := Preset.effectiveBalanceIncrement
forkabbrev effectiveBalanceIncrementG : Gwei := Preset.effectiveBalanceIncrementG
forkabbrev minDepositAmountG : Gwei := Preset.minDepositAmountG
forkabbrev minActivationBalance : Gwei := Preset.minActivationBalance
forkabbrev maxEffectiveBalanceG : Gwei := Preset.maxEffectiveBalanceG
forkabbrev maxEffectiveBalanceElectra : Nat := Preset.maxEffectiveBalanceElectra
forkabbrev maxEffectiveBalanceElectraG : Gwei := Preset.maxEffectiveBalanceElectraG
forkabbrev ejectionBalanceG : Gwei := Config.ejectionBalanceG
forkabbrev unsetDepositRequestsStartIndex : UInt64 := 0xffffffffffffffff
forkabbrev fullExitRequestAmount : Gwei := 0
/-- The BLS G2 point at infinity (`0xc0` then 95 zero bytes); the signature
placeholder a `queue_excess_active_balance` pending deposit carries. -/
forkabbrev g2PointAtInfinity : Vector UInt8 96 := Vector.ofFn (fun i : Fin 96 => if i.val == 0 then 0xc0 else 0)
-- timing / lifecycle
forkabbrev maxSeedLookahead : Epoch := Preset.maxSeedLookahead
forkabbrev minSeedLookahead : Epoch := Preset.minSeedLookahead
forkabbrev minAttestationInclusionDelay : Slot := Preset.minAttestationInclusionDelay
forkabbrev minEpochsToInactivityPenalty : Epoch := Preset.minEpochsToInactivityPenalty
-- reward / penalty weights + quotients (Nat)
forkabbrev baseRewardFactor : Nat := Preset.baseRewardFactor
forkabbrev weightDenominator : Nat := 64
forkabbrev proposerWeight : Nat := 8
forkabbrev syncRewardWeight : Nat := 2
forkabbrev timelySourceWeight : Nat := 14
forkabbrev timelyTargetWeight : Nat := 26
forkabbrev timelyHeadWeight : Nat := 14
forkabbrev timelySourceFlagIndex : Nat := 0
forkabbrev timelyTargetFlagIndex : Nat := 1
forkabbrev timelyHeadFlagIndex : Nat := 2
/-- `[TIMELY_SOURCE, TIMELY_TARGET, TIMELY_HEAD]` flag weights, in index order. -/
forkabbrev participationFlagWeights : List Nat := [timelySourceWeight, timelyTargetWeight, timelyHeadWeight]
forkabbrev minSlashingPenaltyQuotientElectra : Nat := Preset.minSlashingPenaltyQuotientElectra
forkabbrev whistleblowerRewardQuotientElectra : Nat := Preset.whistleblowerRewardQuotientElectra
forkabbrev proportionalSlashingMultiplierBellatrix : Nat := Preset.proportionalSlashingMultiplierBellatrix
forkabbrev inactivityPenaltyQuotientBellatrix : Nat := Preset.inactivityPenaltyQuotientBellatrix
forkabbrev inactivityScoreBias : UInt64 := 4
forkabbrev inactivityScoreRecoveryRate : UInt64 := 16
forkabbrev hysteresisQuotient : Nat := Preset.hysteresisQuotient
forkabbrev hysteresisDownwardMultiplier : Nat := Preset.hysteresisDownwardMultiplier
forkabbrev hysteresisUpwardMultiplier : Nat := Preset.hysteresisUpwardMultiplier
forkabbrev maxRandomValue : Nat := 65535
-- withdrawal-credential prefixes
forkabbrev blsWithdrawalPrefix : UInt8 := 0x00
forkabbrev eth1AddressWithdrawalPrefix : UInt8 := 0x01
forkabbrev compoundingWithdrawalPrefix : UInt8 := 0x02
-- BLS domain-type tags (4-byte prefixes, as ByteArrays for hashing)
forkabbrev domainBeaconProposer : ByteArray := ⟨#[0, 0, 0, 0]⟩
forkabbrev domainBeaconAttester : ByteArray := ⟨#[1, 0, 0, 0]⟩
forkabbrev domainRandao : ByteArray := ⟨#[2, 0, 0, 0]⟩
forkabbrev domainDeposit : ByteArray := ⟨#[3, 0, 0, 0]⟩
forkabbrev domainVoluntaryExit : ByteArray := ⟨#[4, 0, 0, 0]⟩
forkabbrev domainSyncCommittee : ByteArray := ⟨#[7, 0, 0, 0]⟩
forkabbrev domainBlsToExecutionChange : ByteArray := ⟨#[0x0A, 0, 0, 0]⟩

-- Config tier (carries `[Config]`).
forkabbrev churnLimitQuotient : UInt64 := Config.churnLimitQuotient
forkabbrev minPerEpochChurnLimitElectra : Gwei := Config.minPerEpochChurnLimitElectra
forkabbrev maxPerEpochActivationExitChurnLimit : Gwei := Config.maxPerEpochActivationExitChurnLimit
forkabbrev minValidatorWithdrawabilityDelay : UInt64 := Config.minValidatorWithdrawabilityDelay
forkabbrev shardCommitteePeriod : UInt64 := Config.shardCommitteePeriod
forkabbrev genesisForkVersion : Version := Config.genesisForkVersion
forkabbrev capellaForkVersion : Version := Config.capellaForkVersion
forkabbrev slotDurationMs : UInt64 := Config.slotDurationMs
forkabbrev attestationDueBps : UInt64 := Config.attestationDueBps
forkabbrev consolidationChurnLimitQuotient : UInt64 := Config.consolidationChurnLimitQuotient
/-- `MAX_BLOBS_PER_BLOCK_ELECTRA` (9 for both presets). With an empty `BLOB_SCHEDULE`
this is what `get_blob_parameters(epoch).max_blobs_per_block` returns. -/
forkabbrev maxBlobsPerBlockElectra : Nat := Config.maxBlobsPerBlockElectra
/-- Reorg weight thresholds (percent of the per-slot committee weight). -/
forkabbrev reorgHeadWeightThreshold : UInt64 := 20
forkabbrev reorgParentWeightThreshold : UInt64 := 160
/-- `REORG_MAX_EPOCHS_SINCE_FINALIZATION`: do not reorg if finality is older. -/
forkabbrev reorgMaxEpochsSinceFinalization : Epoch := 2
/-- `PROPOSER_REORG_CUTOFF_BPS`: the on-time deadline for a reorg proposal, in basis
points of the slot (~17%). -/
forkabbrev proposerReorgCutoffBps : UInt64 := 1667
/-- `NUMBER_OF_COLUMNS` (PeerDAS, `= CELLS_PER_EXT_BLOB`): the data-column count. -/
forkabbrev numberOfColumns : Nat := Preset.numberOfColumns
/-- Fulu `KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH` (4), the `DataColumnSidecar`'s proof
vector length. Distinct from the Deneb singular `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH`. -/
forkabbrev kzgCommitmentsInclusionProofDepth : Nat := Preset.kzgCommitmentsInclusionProofDepth
/-- `PROPOSER_SCORE_BOOST` (percent of the per-slot committee weight). -/
forkabbrev proposerScoreBoost : Nat := 40
/-- `BASIS_POINTS` denominator for the slot-component durations. -/
forkabbrev basisPoints : UInt64 := 10000

end
end Const

/-! ## `ValidModulus` instances for the ring-buffer divisors

Register the preset's well-formedness fields so a `vmodGet` read into a ring-buffer vector
(`blockRoots`, `randaoMixes`, `proposerLookahead`) names only the divisor. A child
fork replays these with `inherit`, so its copies bind to its own `Preset`. -/

forkinstance validModulusSlotsPerEpoch [Preset] : ValidModulus Const.slotsPerEpoch :=
  ⟨Const.slotsPerEpochPos, Const.slotsPerEpochLt⟩
forkinstance validModulusSlotsPerHistoricalRoot [Preset] : ValidModulus Const.slotsPerHistoricalRoot :=
  ⟨Const.slotsPerHistoricalRootPos, Const.slotsPerHistoricalRootLt⟩
forkinstance validModulusEpochsPerHistoricalVector [Preset] : ValidModulus Const.epochsPerHistoricalVector :=
  ⟨Const.epochsPerHistoricalVectorPos, Const.epochsPerHistoricalVectorLt⟩

/-- The `minimal` preset, an injected `@[reducible] def` (not a global instance,
so it coexists with `mainnet`). -/
forkpresetvalues minimal where
  slotsPerEpoch := 8
  slotsPerHistoricalRoot := 64
  epochsPerHistoricalVector := 64
  epochsPerSlashingsVector := 64
  epochsPerEth1VotingPeriod := 4
  epochsPerSyncCommitteePeriod := 8
  syncCommitteeSize := 32
  maxCommitteesPerSlot := 4
  targetCommitteeSize := 4
  shuffleRoundCount := 10
  maxValidatorsPerWithdrawalsSweep := 16
  maxPendingPartialsPerWithdrawalsSweep := 2
  maxWithdrawalsPerPayload := 4
  maxBlobCommitmentsPerBlock := 4096
  pendingPartialWithdrawalsLimit := 64
  pendingConsolidationsLimit := 64
  -- Registry and history caps.
  validatorRegistryLimit := 2 ^ 40
  historicalRootsLimit := 2 ^ 24
  pendingDepositsLimit := 2 ^ 27
  -- Per-block operation caps.
  maxProposerSlashings := 16
  maxAttesterSlashings := 1
  maxAttestations := 8
  maxAttesterSlashingsElectra := 1
  maxAttestationsElectra := 8
  maxDeposits := 16
  maxVoluntaryExits := 16
  maxBlsToExecutionChanges := 16
  maxValidatorsPerCommittee := 2048
  maxDepositRequestsPerPayload := 8192
  maxWithdrawalRequestsPerPayload := 16
  maxConsolidationRequestsPerPayload := 2
  maxPendingDepositsPerEpoch := 16
  -- Execution-payload shape.
  maxExtraDataBytes := 32
  maxBytesPerTransaction := 2 ^ 30
  maxTransactionsPerPayload := 2 ^ 20
  bytesPerLogsBloom := 256
  -- Timing and lifecycle.
  maxSeedLookahead := 4
  minSeedLookahead := 1
  minAttestationInclusionDelay := 1
  minEpochsToInactivityPenalty := 4
  -- Balance thresholds.
  effectiveBalanceIncrement := 1000000000
  effectiveBalanceIncrementG := 1000000000
  minDepositAmountG := 1000000000
  minActivationBalance := 32000000000
  maxEffectiveBalanceG := 32000000000
  maxEffectiveBalanceElectra := 2048000000000
  maxEffectiveBalanceElectraG := 2048000000000
  hysteresisQuotient := 4
  hysteresisDownwardMultiplier := 1
  hysteresisUpwardMultiplier := 5
  -- Reward / penalty quotients.
  baseRewardFactor := 64
  minSlashingPenaltyQuotientElectra := 4096
  whistleblowerRewardQuotientElectra := 4096
  proportionalSlashingMultiplierBellatrix := 3
  inactivityPenaltyQuotientBellatrix := 16777216
  -- PeerDAS.
  numberOfColumns := 128
  kzgCommitmentsInclusionProofDepth := 4
  slotsPerEpochPos := by decide
  slotsPerEpochLt := by decide
  slotsPerHistoricalRootPos := by decide
  slotsPerHistoricalRootLt := by decide
  epochsPerHistoricalVectorPos := by decide
  epochsPerHistoricalVectorLt := by decide

/-- The `mainnet` preset. -/
forkpresetvalues mainnet where
  slotsPerEpoch := 32
  slotsPerHistoricalRoot := 8192
  epochsPerHistoricalVector := 65536
  epochsPerSlashingsVector := 8192
  epochsPerEth1VotingPeriod := 64
  epochsPerSyncCommitteePeriod := 256
  syncCommitteeSize := 512
  maxCommitteesPerSlot := 64
  targetCommitteeSize := 128
  shuffleRoundCount := 90
  maxValidatorsPerWithdrawalsSweep := 16384
  maxPendingPartialsPerWithdrawalsSweep := 8
  maxWithdrawalsPerPayload := 16
  maxBlobCommitmentsPerBlock := 4096
  pendingPartialWithdrawalsLimit := 134217728
  pendingConsolidationsLimit := 262144
  -- Registry and history caps.
  validatorRegistryLimit := 2 ^ 40
  historicalRootsLimit := 2 ^ 24
  pendingDepositsLimit := 2 ^ 27
  -- Per-block operation caps.
  maxProposerSlashings := 16
  maxAttesterSlashings := 1
  maxAttestations := 8
  maxAttesterSlashingsElectra := 1
  maxAttestationsElectra := 8
  maxDeposits := 16
  maxVoluntaryExits := 16
  maxBlsToExecutionChanges := 16
  maxValidatorsPerCommittee := 2048
  maxDepositRequestsPerPayload := 8192
  maxWithdrawalRequestsPerPayload := 16
  maxConsolidationRequestsPerPayload := 2
  maxPendingDepositsPerEpoch := 16
  -- Execution-payload shape.
  maxExtraDataBytes := 32
  maxBytesPerTransaction := 2 ^ 30
  maxTransactionsPerPayload := 2 ^ 20
  bytesPerLogsBloom := 256
  -- Timing and lifecycle.
  maxSeedLookahead := 4
  minSeedLookahead := 1
  minAttestationInclusionDelay := 1
  minEpochsToInactivityPenalty := 4
  -- Balance thresholds.
  effectiveBalanceIncrement := 1000000000
  effectiveBalanceIncrementG := 1000000000
  minDepositAmountG := 1000000000
  minActivationBalance := 32000000000
  maxEffectiveBalanceG := 32000000000
  maxEffectiveBalanceElectra := 2048000000000
  maxEffectiveBalanceElectraG := 2048000000000
  hysteresisQuotient := 4
  hysteresisDownwardMultiplier := 1
  hysteresisUpwardMultiplier := 5
  -- Reward / penalty quotients.
  baseRewardFactor := 64
  minSlashingPenaltyQuotientElectra := 4096
  whistleblowerRewardQuotientElectra := 4096
  proportionalSlashingMultiplierBellatrix := 3
  inactivityPenaltyQuotientBellatrix := 16777216
  -- PeerDAS.
  numberOfColumns := 128
  kzgCommitmentsInclusionProofDepth := 4
  slotsPerEpochPos := by decide
  slotsPerEpochLt := by decide
  slotsPerHistoricalRootPos := by decide
  slotsPerHistoricalRootLt := by decide
  epochsPerHistoricalVectorPos := by decide
  epochsPerHistoricalVectorLt := by decide

/-- The `minimal` config. -/
forkconfigvalues minimalConfig where
  churnLimitQuotient := 32
  minPerEpochChurnLimitElectra := 64000000000
  maxPerEpochActivationExitChurnLimit := 128000000000
  minValidatorWithdrawabilityDelay := 256
  shardCommitteePeriod := 64
  genesisForkVersion := ⟨#[0, 0, 0, 1], by decide⟩
  capellaForkVersion := ⟨#[3, 0, 0, 1], by decide⟩
  slotDurationMs := 6000
  attestationDueBps := 3333
  ejectionBalanceG := 16000000000
  maxBlobsPerBlockElectra := 9
  consolidationChurnLimitQuotient := 32

/-- The `mainnet` config. -/
forkconfigvalues mainnetConfig where
  churnLimitQuotient := 65536
  minPerEpochChurnLimitElectra := 128000000000
  maxPerEpochActivationExitChurnLimit := 256000000000
  minValidatorWithdrawabilityDelay := 256
  shardCommitteePeriod := 256
  genesisForkVersion := ⟨#[0, 0, 0, 0], by decide⟩
  capellaForkVersion := ⟨#[3, 0, 0, 0], by decide⟩
  slotDurationMs := 12000
  attestationDueBps := 3333
  ejectionBalanceG := 16000000000
  maxBlobsPerBlockElectra := 9
  consolidationChurnLimitQuotient := 65536

end EthCLSpecs.Fulu
