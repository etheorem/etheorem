import EthCLLib
import EthCLSpecs.Fulu.Types

/-!
# `EthCLSpecs.Fulu.Constants`: the tier system and the fork declaration (row 2)

The fork's constants in the three tiers (`SPECS_ARCHITECTURE.md` §9,
`FRAMEWORK_ARCHITECTURE.md` §4), and the `fork Fulu` lineage declaration. The
tier system is per fork. The author writes `Const.x` everywhere; the tier is
classified once, here.

Two numeric flavours, by design: `UInt64` / `Gwei` constants combine directly
with `uint64`-shaped state fields (slots, epochs, indices, balances); `Nat`
constants feed the reward / penalty arithmetic, evaluated in `Nat` (unbounded, no
wraparound) to match the pyspec's Python `int` exactly, narrowing back to `Gwei`
only at the application site. A `…G` suffix marks the `Gwei` form of a value that
also has a `Nat` form.

Values are Fulu/Electra (the conformance fork), not the Gloas-tweaked ones in the
GloasSpec reference.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

fork Fulu

/-- The preset-varying constants (vector widths, list caps, committee / epoch
lengths). Threaded `[Preset]`; the runner injects `minimal` or `mainnet`. -/
class Preset where
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
  -- Gloas (EIP-7732) preset-varying constants.
  ptcSize : Nat
  maxBuildersPerWithdrawalsSweep : Nat
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
shapes a type. -/
class Config where
  secondsPerSlot : UInt64
  churnLimitQuotient : UInt64
  minPerEpochChurnLimitElectra : Gwei
  maxPerEpochActivationExitChurnLimit : Gwei
  minValidatorWithdrawabilityDelay : UInt64
  shardCommitteePeriod : UInt64
  genesisForkVersion : Version
  capellaForkVersion : Version
  slotDurationMs : UInt64
  attestationDueBps : UInt64
  -- Gloas (EIP-7732) config-tier constants.
  gloasForkVersion : Version
  churnLimitQuotientGloas : UInt64
  consolidationChurnLimitQuotient : UInt64
  maxPerEpochActivationChurnLimitGloas : Gwei
  minBuilderWithdrawabilityDelay : UInt64

namespace Const
section
variable [Preset] [Config]

-- Preset tier (each carries `[Preset]`; `abbrev` is reducible so the width reduces
-- to a literal at a concrete preset, which the symbolic-cap derive needs).
abbrev slotsPerEpoch : Nat := Preset.slotsPerEpoch
abbrev slotsPerHistoricalRoot : Nat := Preset.slotsPerHistoricalRoot
abbrev epochsPerHistoricalVector : Nat := Preset.epochsPerHistoricalVector
abbrev epochsPerSlashingsVector : Nat := Preset.epochsPerSlashingsVector
abbrev epochsPerEth1VotingPeriod : Nat := Preset.epochsPerEth1VotingPeriod
abbrev epochsPerSyncCommitteePeriod : Nat := Preset.epochsPerSyncCommitteePeriod
abbrev syncCommitteeSize : Nat := Preset.syncCommitteeSize
abbrev maxCommitteesPerSlot : Nat := Preset.maxCommitteesPerSlot
abbrev targetCommitteeSize : Nat := Preset.targetCommitteeSize
abbrev shuffleRoundCount : Nat := Preset.shuffleRoundCount
abbrev maxValidatorsPerWithdrawalsSweep : Nat := Preset.maxValidatorsPerWithdrawalsSweep
abbrev maxPendingPartialsPerWithdrawalsSweep : Nat := Preset.maxPendingPartialsPerWithdrawalsSweep
abbrev maxWithdrawalsPerPayload : Nat := Preset.maxWithdrawalsPerPayload
abbrev maxBlobCommitmentsPerBlock : Nat := Preset.maxBlobCommitmentsPerBlock
abbrev pendingPartialWithdrawalsLimit : Nat := Preset.pendingPartialWithdrawalsLimit
abbrev pendingConsolidationsLimit : Nat := Preset.pendingConsolidationsLimit
abbrev ptcSize : Nat := Preset.ptcSize
abbrev maxBuildersPerWithdrawalsSweep : Nat := Preset.maxBuildersPerWithdrawalsSweep

-- Well-formedness of the vector-length constants (positive, `uint64`-ranged), surfaced
-- with the `Const.` prefix like the values. The proof-carrying premises of
-- `EthCLLib.Spec.uint64ModOfNatToNatLt` at a modulo index into the matching vector.
abbrev slotsPerEpochPos : 0 < slotsPerEpoch := Preset.slotsPerEpochPos
abbrev slotsPerEpochLt : slotsPerEpoch < 2 ^ 64 := Preset.slotsPerEpochLt
abbrev slotsPerHistoricalRootPos : 0 < slotsPerHistoricalRoot := Preset.slotsPerHistoricalRootPos
abbrev slotsPerHistoricalRootLt : slotsPerHistoricalRoot < 2 ^ 64 := Preset.slotsPerHistoricalRootLt
abbrev epochsPerHistoricalVectorPos : 0 < epochsPerHistoricalVector := Preset.epochsPerHistoricalVectorPos
abbrev epochsPerHistoricalVectorLt : epochsPerHistoricalVector < 2 ^ 64 := Preset.epochsPerHistoricalVectorLt

-- Universal tier (literal body, no binder, identical across presets).
abbrev farFutureEpoch : Epoch := 0xffffffffffffffff
abbrev genesisSlot : Slot := 0
abbrev genesisEpoch : Epoch := 0
abbrev validatorRegistryLimit : Nat := 2 ^ 40
abbrev historicalRootsLimit : Nat := 2 ^ 24
abbrev pendingDepositsLimit : Nat := 2 ^ 27
abbrev justificationBitsLength : Nat := 4
abbrev maxExtraDataBytes : Nat := 32
abbrev depositContractTreeDepth : Nat := 32
-- per-block operation caps
abbrev maxProposerSlashings : Nat := 16
abbrev maxAttesterSlashings : Nat := 1
abbrev maxAttestations : Nat := 8
abbrev maxDeposits : Nat := 16
abbrev maxVoluntaryExits : Nat := 16
abbrev maxBlsToExecutionChanges : Nat := 16
abbrev maxValidatorsPerCommittee : Nat := 2048
abbrev maxDepositRequestsPerPayload : Nat := 8192
abbrev maxWithdrawalRequestsPerPayload : Nat := 16
abbrev maxConsolidationRequestsPerPayload : Nat := 2
-- EIP-8282 (Gloas builder deposits / exits): 2**8 and 2**4, identical across presets.
abbrev maxBuilderDepositRequestsPerPayload : Nat := 256
abbrev maxBuilderExitRequestsPerPayload : Nat := 16
-- EIP-7805 (Heze FOCIL): inclusion-list committee members per slot. A preset-file
-- value, identical across presets at v1.7.0-alpha.11 (both say 2**4); re-check at
-- every re-pin, and promote to a `Preset` field (like `ptcSize`) if they diverge.
abbrev inclusionListCommitteeSize : Nat := 16
abbrev maxAttestationsElectra : Nat := 8
abbrev maxAttesterSlashingsElectra : Nat := 1
abbrev maxPendingDepositsPerEpoch : Nat := 16
abbrev maxBytesPerTransaction : Nat := 2 ^ 30
abbrev maxTransactionsPerPayload : Nat := 2 ^ 20
abbrev bytesPerLogsBloom : Nat := 256
-- Balance / effective-balance thresholds, in Gwei. The `G` suffix marks the
-- `Gwei` (`UInt64`) form; it abbreviates "Gwei", not "Gloas". A threshold that
-- also feeds `Nat` ratio arithmetic carries a suffix-free `Nat` twin of the same
-- value, so `effectiveBalanceIncrement` and `maxEffectiveBalanceElectra` are the
-- `Nat` forms and their `…G` siblings are the `Gwei` forms.
abbrev effectiveBalanceIncrement : Nat := 1000000000
abbrev effectiveBalanceIncrementG : Gwei := 1000000000
abbrev minDepositAmountG : Gwei := 1000000000
abbrev minActivationBalance : Gwei := 32000000000
abbrev maxEffectiveBalanceG : Gwei := 32000000000
abbrev maxEffectiveBalanceElectra : Nat := 2048000000000
abbrev maxEffectiveBalanceElectraG : Gwei := 2048000000000
abbrev ejectionBalanceG : Gwei := 16000000000
abbrev unsetDepositRequestsStartIndex : UInt64 := 0xffffffffffffffff
abbrev fullExitRequestAmount : Gwei := 0
/-- The BLS G2 point at infinity (`0xc0` then 95 zero bytes); the signature
placeholder a `queue_excess_active_balance` pending deposit carries. -/
abbrev g2PointAtInfinity : Vector UInt8 96 := Vector.ofFn (fun i : Fin 96 => if i.val == 0 then 0xc0 else 0)
-- timing / lifecycle
abbrev maxSeedLookahead : Epoch := 4
abbrev minSeedLookahead : Epoch := 1
abbrev minAttestationInclusionDelay : Slot := 1
abbrev minEpochsToInactivityPenalty : Epoch := 4
-- reward / penalty weights + quotients (Nat)
abbrev baseRewardFactor : Nat := 64
abbrev weightDenominator : Nat := 64
abbrev proposerWeight : Nat := 8
abbrev syncRewardWeight : Nat := 2
abbrev timelySourceWeight : Nat := 14
abbrev timelyTargetWeight : Nat := 26
abbrev timelyHeadWeight : Nat := 14
abbrev timelySourceFlagIndex : Nat := 0
abbrev timelyTargetFlagIndex : Nat := 1
abbrev timelyHeadFlagIndex : Nat := 2
/-- `[TIMELY_SOURCE, TIMELY_TARGET, TIMELY_HEAD]` flag weights, in index order. -/
abbrev participationFlagWeights : List Nat := [timelySourceWeight, timelyTargetWeight, timelyHeadWeight]
abbrev minSlashingPenaltyQuotientElectra : Nat := 4096
abbrev whistleblowerRewardQuotientElectra : Nat := 4096
abbrev proportionalSlashingMultiplierBellatrix : Nat := 3
abbrev inactivityPenaltyQuotientBellatrix : Nat := 16777216
abbrev inactivityScoreBias : UInt64 := 4
abbrev inactivityScoreRecoveryRate : UInt64 := 16
abbrev hysteresisQuotient : Nat := 4
abbrev hysteresisDownwardMultiplier : Nat := 1
abbrev hysteresisUpwardMultiplier : Nat := 5
abbrev maxRandomValue : Nat := 65535
-- withdrawal-credential prefixes
abbrev blsWithdrawalPrefix : UInt8 := 0x00
abbrev eth1AddressWithdrawalPrefix : UInt8 := 0x01
abbrev compoundingWithdrawalPrefix : UInt8 := 0x02
-- BLS domain-type tags (4-byte prefixes, as ByteArrays for hashing)
abbrev domainBeaconProposer : ByteArray := ⟨#[0, 0, 0, 0]⟩
abbrev domainBeaconAttester : ByteArray := ⟨#[1, 0, 0, 0]⟩
abbrev domainRandao : ByteArray := ⟨#[2, 0, 0, 0]⟩
abbrev domainDeposit : ByteArray := ⟨#[3, 0, 0, 0]⟩
abbrev domainVoluntaryExit : ByteArray := ⟨#[4, 0, 0, 0]⟩
abbrev domainSyncCommittee : ByteArray := ⟨#[7, 0, 0, 0]⟩
abbrev domainBlsToExecutionChange : ByteArray := ⟨#[0x0A, 0, 0, 0]⟩

-- Config tier (carries `[Config]`).
abbrev secondsPerSlot : UInt64 := Config.secondsPerSlot
abbrev churnLimitQuotient : UInt64 := Config.churnLimitQuotient
abbrev minPerEpochChurnLimitElectra : Gwei := Config.minPerEpochChurnLimitElectra
abbrev maxPerEpochActivationExitChurnLimit : Gwei := Config.maxPerEpochActivationExitChurnLimit
abbrev minValidatorWithdrawabilityDelay : UInt64 := Config.minValidatorWithdrawabilityDelay
abbrev shardCommitteePeriod : UInt64 := Config.shardCommitteePeriod
abbrev genesisForkVersion : Version := Config.genesisForkVersion
abbrev capellaForkVersion : Version := Config.capellaForkVersion
abbrev slotDurationMs : UInt64 := Config.slotDurationMs
abbrev attestationDueBps : UInt64 := Config.attestationDueBps
abbrev gloasForkVersion : Version := Config.gloasForkVersion
abbrev churnLimitQuotientGloas : UInt64 := Config.churnLimitQuotientGloas
abbrev consolidationChurnLimitQuotient : UInt64 := Config.consolidationChurnLimitQuotient
abbrev maxPerEpochActivationChurnLimitGloas : Gwei := Config.maxPerEpochActivationChurnLimitGloas
abbrev minBuilderWithdrawabilityDelay : UInt64 := Config.minBuilderWithdrawabilityDelay
-- Gloas (EIP-7732) universal constants (identical across presets).
abbrev builderRegistryLimit : Nat := 2 ^ 40
abbrev builderPendingWithdrawalsLimit : Nat := 2 ^ 20
abbrev maxPayloadAttestations : Nat := 4
abbrev builderPaymentThresholdNumerator : UInt64 := 6
abbrev builderPaymentThresholdDenominator : UInt64 := 10
abbrev builderWithdrawalPrefix : UInt8 := 0x03
/-- `PAYLOAD_BUILDER_VERSION = uint8(0)` (EIP-8282): the version stamped on a
builder onboarded at the fork (`add_builder_to_registry`). -/
abbrev payloadBuilderVersion : UInt8 := 0
abbrev builderIndexFlag : UInt64 := 0x10000000000
/-- `BUILDER_INDEX_SELF_BUILD = BuilderIndex(UINT64_MAX)`: the bid's `builder_index`
sentinel marking a proposer self-build (no external builder). -/
abbrev builderIndexSelfBuild : UInt64 := 0xffffffffffffffff
/-- `MAX_BLOBS_PER_BLOCK_ELECTRA` (9 for both presets). With an empty `BLOB_SCHEDULE`
this is what `get_blob_parameters(epoch).max_blobs_per_block` returns. -/
abbrev maxBlobsPerBlockElectra : Nat := 9
abbrev domainBeaconBuilder : ByteArray := ⟨#[0x0B, 0, 0, 0]⟩
abbrev domainPtcAttester : ByteArray := ⟨#[0x0C, 0, 0, 0]⟩
-- EIP-8282 `DOMAIN_BUILDER_DEPOSIT` (`0x0E000000`). Consumed by the deferred
-- builder-deposit signature check; recorded now alongside the other domain tags.
abbrev domainBuilderDeposit : ByteArray := ⟨#[0x0E, 0, 0, 0]⟩
-- EIP-7805 `DOMAIN_INCLUSION_LIST_COMMITTEE` (`0x10000000`). The FOCIL inclusion-list
-- committee signature domain; consumed by `Heze.isValidInclusionListSignature`. Recorded
-- here with the other domain tags (where every fork's domains live, Heze's included).
abbrev domainInclusionListCommittee : ByteArray := ⟨#[0x10, 0, 0, 0]⟩
/-- ePBS fork-choice payload statuses for a `ForkChoiceNode`. -/
abbrev payloadStatusEmpty : UInt8 := 0
abbrev payloadStatusFull : UInt8 := 1
abbrev payloadStatusPending : UInt8 := 2
/-- `block_timeliness` deadline indices (attestation-due and PTC-due). -/
abbrev attestationTimelinessIndex : Nat := 0
abbrev ptcTimelinessIndex : Nat := 1
/-- PTC vote majority thresholds (`PTC_SIZE // 2`). -/
abbrev payloadTimelyThreshold : Nat := ptcSize / 2
abbrev dataAvailabilityTimelyThreshold : Nat := ptcSize / 2
/-- Reorg weight thresholds (percent of the per-slot committee weight). -/
abbrev reorgHeadWeightThreshold : UInt64 := 20
abbrev reorgParentWeightThreshold : UInt64 := 160
/-- `REORG_MAX_EPOCHS_SINCE_FINALIZATION`: do not reorg if finality is older. -/
abbrev reorgMaxEpochsSinceFinalization : Epoch := 2
/-- `PROPOSER_REORG_CUTOFF_BPS`: the on-time deadline for a reorg proposal, in basis
points of the slot (~17%). -/
abbrev proposerReorgCutoffBps : UInt64 := 1667
/-- `NUMBER_OF_COLUMNS` (PeerDAS, `= CELLS_PER_EXT_BLOB`): the data-column count. -/
abbrev numberOfColumns : Nat := 128
/-- Fulu `KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH` (4), the `DataColumnSidecar`'s proof
vector length. Distinct from the Deneb singular `KZG_COMMITMENT_INCLUSION_PROOF_DEPTH`. -/
abbrev kzgCommitmentsInclusionProofDepth : Nat := 4
/-- Gloas slot-component deadlines in basis points of the slot
(`ATTESTATION_DUE_BPS_GLOAS`, `PAYLOAD_ATTESTATION_DUE_BPS`). -/
abbrev attestationDueBpsGloas : UInt64 := 2500
abbrev payloadAttestationDueBps : UInt64 := 7500
/-- `PROPOSER_SCORE_BOOST` (percent of the per-slot committee weight). -/
abbrev proposerScoreBoost : Nat := 40
/-- `BASIS_POINTS` denominator for the slot-component durations. -/
abbrev basisPoints : UInt64 := 10000

end
end Const

/-! ## `ValidModulus` instances for the ring-buffer divisors

Register the preset's well-formedness fields so a `vmodGet` read into a ring-buffer vector
(`blockRoots`, `randaoMixes`, `proposerLookahead`, `ptcWindow`) names only the divisor. -/

instance [Preset] : ValidModulus Const.slotsPerEpoch :=
  ⟨Const.slotsPerEpochPos, Const.slotsPerEpochLt⟩
instance [Preset] : ValidModulus Const.slotsPerHistoricalRoot :=
  ⟨Const.slotsPerHistoricalRootPos, Const.slotsPerHistoricalRootLt⟩
instance [Preset] : ValidModulus Const.epochsPerHistoricalVector :=
  ⟨Const.epochsPerHistoricalVectorPos, Const.epochsPerHistoricalVectorLt⟩

/-- The `minimal` preset, an injected `@[reducible] def` (not a global instance,
so it coexists with `mainnet`). -/
@[reducible] def minimal : Preset where
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
  ptcSize := 16
  maxBuildersPerWithdrawalsSweep := 16
  slotsPerEpochPos := by decide
  slotsPerEpochLt := by decide
  slotsPerHistoricalRootPos := by decide
  slotsPerHistoricalRootLt := by decide
  epochsPerHistoricalVectorPos := by decide
  epochsPerHistoricalVectorLt := by decide

/-- The `mainnet` preset. -/
@[reducible] def mainnet : Preset where
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
  ptcSize := 512
  maxBuildersPerWithdrawalsSweep := 16384
  slotsPerEpochPos := by decide
  slotsPerEpochLt := by decide
  slotsPerHistoricalRootPos := by decide
  slotsPerHistoricalRootLt := by decide
  epochsPerHistoricalVectorPos := by decide
  epochsPerHistoricalVectorLt := by decide

/-- The `minimal` config. -/
@[reducible] def minimalConfig : Config where
  secondsPerSlot := 6
  churnLimitQuotient := 32
  minPerEpochChurnLimitElectra := 64000000000
  maxPerEpochActivationExitChurnLimit := 128000000000
  minValidatorWithdrawabilityDelay := 256
  shardCommitteePeriod := 64
  genesisForkVersion := ⟨#[0, 0, 0, 1], by decide⟩
  capellaForkVersion := ⟨#[3, 0, 0, 1], by decide⟩
  slotDurationMs := 6000
  attestationDueBps := 3333
  gloasForkVersion := ⟨#[0x07, 0, 0, 1], by decide⟩
  churnLimitQuotientGloas := 16
  consolidationChurnLimitQuotient := 32
  maxPerEpochActivationChurnLimitGloas := 128000000000
  minBuilderWithdrawabilityDelay := 2

/-- The `mainnet` config. -/
@[reducible] def mainnetConfig : Config where
  secondsPerSlot := 12
  churnLimitQuotient := 65536
  minPerEpochChurnLimitElectra := 128000000000
  maxPerEpochActivationExitChurnLimit := 256000000000
  minValidatorWithdrawabilityDelay := 256
  shardCommitteePeriod := 256
  genesisForkVersion := ⟨#[0, 0, 0, 0], by decide⟩
  capellaForkVersion := ⟨#[3, 0, 0, 0], by decide⟩
  slotDurationMs := 12000
  attestationDueBps := 3333
  gloasForkVersion := ⟨#[0x07, 0, 0, 0], by decide⟩
  churnLimitQuotientGloas := 32768
  consolidationChurnLimitQuotient := 65536
  maxPerEpochActivationChurnLimitGloas := 256000000000
  minBuilderWithdrawabilityDelay := 8192

end EthCLSpecs.Fulu
