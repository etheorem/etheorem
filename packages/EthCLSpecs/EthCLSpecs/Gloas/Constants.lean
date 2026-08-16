import EthCLSpecs.Gloas.Types

/-!
# `EthCLSpecs.Gloas.Constants`: the tier system (load order row 2)

Gloas's three constant tiers. The fork is a diff over Fulu
(`SPECS_ARCHITECTURE.md` §2, §4.1), so this module is written as a diff too:
`forkpreset` / `forkconfig` name only the fields EIP-7732 and EIP-8282 add, and
the framework merges them with Fulu's along the lineage into one flat
`Gloas.Preset` and `Gloas.Config`. The value sets work the same way, each naming
only its own assignments.

Everything Gloas keeps from Fulu arrives through `inherit`, one explicit line per
name, replayed into this namespace. That is what lets Gloas body code write
`Const.slotsPerEpoch` with the parent's namespace nowhere in sight. A replay is
no copy: the body's unqualified sibling calls late-bind here, so
`Const.payloadTimelyThreshold` divides *Gloas's* `ptcSize`.

`forkpreset` also emits the scoped downgrade instance to `Fulu.Preset`, the
bridge `Upgrade.lean` and `Interface.lean` open at the fork boundary
(`FRAMEWORK_ARCHITECTURE.md` §4).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

/-- The preset fields EIP-7732 and EIP-8282 add. Fulu's fields merge in through
the lineage, so the emitted `Gloas.Preset` is one flat class carrying both. -/
forkpreset where
  /-- `PTC_SIZE`: the payload-timeliness committee's member count. -/
  ptcSize : Nat
  /-- `MAX_BUILDERS_PER_WITHDRAWALS_SWEEP`: builders visited per sweep. -/
  maxBuildersPerWithdrawalsSweep : Nat
  /-- `BUILDER_REGISTRY_LIMIT`, the builder registry's SSZ list cap. -/
  builderRegistryLimit : Nat
  /-- `BUILDER_PENDING_WITHDRAWALS_LIMIT`. -/
  builderPendingWithdrawalsLimit : Nat
  /-- `MAX_PAYLOAD_ATTESTATIONS` per block. -/
  maxPayloadAttestations : Nat
  /-- EIP-8282 per-payload builder-deposit cap. -/
  maxBuilderDepositRequestsPerPayload : Nat
  /-- EIP-8282 per-payload builder-exit cap. -/
  maxBuilderExitRequestsPerPayload : Nat

/-- The config values EIP-7732 adds, merged with Fulu's the same way. -/
forkconfig where
  /-- `GLOAS_FORK_VERSION`. -/
  gloasForkVersion : Version
  /-- `CHURN_LIMIT_QUOTIENT_GLOAS`. -/
  churnLimitQuotientGloas : UInt64
  /-- `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`. -/
  maxPerEpochActivationChurnLimitGloas : Gwei
  /-- `MIN_BUILDER_WITHDRAWABILITY_DELAY`. -/
  minBuilderWithdrawabilityDelay : UInt64

namespace Const
section
variable [Preset] [Config]

-- Gloas's own entries, declared before the inherited block: a replayed Fulu body
-- that names one of these binds to the copy here, and `payloadTimelyThreshold`
-- below divides this fork's `ptcSize`.
forkabbrev ptcSize : Nat := Preset.ptcSize
forkabbrev maxBuildersPerWithdrawalsSweep : Nat := Preset.maxBuildersPerWithdrawalsSweep
forkabbrev builderRegistryLimit : Nat := Preset.builderRegistryLimit
forkabbrev builderPendingWithdrawalsLimit : Nat := Preset.builderPendingWithdrawalsLimit
forkabbrev maxPayloadAttestations : Nat := Preset.maxPayloadAttestations
forkabbrev maxBuilderDepositRequestsPerPayload : Nat := Preset.maxBuilderDepositRequestsPerPayload
forkabbrev maxBuilderExitRequestsPerPayload : Nat := Preset.maxBuilderExitRequestsPerPayload
forkabbrev gloasForkVersion : Version := Config.gloasForkVersion
forkabbrev churnLimitQuotientGloas : UInt64 := Config.churnLimitQuotientGloas
forkabbrev maxPerEpochActivationChurnLimitGloas : Gwei := Config.maxPerEpochActivationChurnLimitGloas
forkabbrev minBuilderWithdrawabilityDelay : UInt64 := Config.minBuilderWithdrawabilityDelay

/-- The builder-payment threshold, as a fraction of the bid
(`BUILDER_PAYMENT_THRESHOLD_NUMERATOR / …_DENOMINATOR`). -/
forkabbrev builderPaymentThresholdNumerator : UInt64 := 6
forkabbrev builderPaymentThresholdDenominator : UInt64 := 10
/-- `BUILDER_WITHDRAWAL_PREFIX` (`0x03`), the fourth withdrawal-credential prefix. -/
forkabbrev builderWithdrawalPrefix : UInt8 := 0x03
/-- `PAYLOAD_BUILDER_VERSION = uint8(0)` (EIP-8282): the version stamped on a
builder onboarded at the fork (`add_builder_to_registry`). -/
forkabbrev payloadBuilderVersion : UInt8 := 0
forkabbrev builderIndexFlag : UInt64 := 0x10000000000
/-- `BUILDER_INDEX_SELF_BUILD = BuilderIndex(UINT64_MAX)`: the bid's `builder_index`
sentinel marking a proposer self-build (no external builder). -/
forkabbrev builderIndexSelfBuild : UInt64 := 0xffffffffffffffff
-- EIP-7732 / EIP-8282 BLS domain-type tags, beside the ones inherited below.
forkabbrev domainBeaconBuilder : ByteArray := ⟨#[0x0B, 0, 0, 0]⟩
forkabbrev domainPtcAttester : ByteArray := ⟨#[0x0C, 0, 0, 0]⟩
-- EIP-8282 `DOMAIN_BUILDER_DEPOSIT` (`0x0E000000`). Consumed by the deferred
-- builder-deposit signature check; recorded now alongside the other domain tags.
forkabbrev domainBuilderDeposit : ByteArray := ⟨#[0x0E, 0, 0, 0]⟩
/-- ePBS fork-choice payload statuses for a `ForkChoiceNode`. -/
forkabbrev payloadStatusEmpty : UInt8 := 0
forkabbrev payloadStatusFull : UInt8 := 1
forkabbrev payloadStatusPending : UInt8 := 2
/-- `block_timeliness` deadline indices (attestation-due and PTC-due). -/
forkabbrev attestationTimelinessIndex : Nat := 0
forkabbrev ptcTimelinessIndex : Nat := 1
/-- PTC vote majority thresholds (`PTC_SIZE // 2`). -/
forkabbrev payloadTimelyThreshold : Nat := ptcSize / 2
forkabbrev dataAvailabilityTimelyThreshold : Nat := ptcSize / 2
/-- Gloas slot-component deadlines in basis points of the slot
(`ATTESTATION_DUE_BPS_GLOAS`, `PAYLOAD_ATTESTATION_DUE_BPS`). -/
forkabbrev attestationDueBpsGloas : UInt64 := 2500
forkabbrev payloadAttestationDueBps : UInt64 := 7500

-- Fulu's entries, replayed here in Fulu's own order so each body reaches its
-- dependencies. The list is the whole surface, not the subset Gloas happens to
-- call today: the fork owns its vocabulary, and a new call site should not have
-- to come back and edit this block.
inherit slotsPerEpoch slotsPerHistoricalRoot epochsPerHistoricalVector
inherit epochsPerSlashingsVector epochsPerEth1VotingPeriod epochsPerSyncCommitteePeriod
inherit syncCommitteeSize maxCommitteesPerSlot targetCommitteeSize shuffleRoundCount
inherit maxValidatorsPerWithdrawalsSweep maxPendingPartialsPerWithdrawalsSweep
inherit maxWithdrawalsPerPayload maxBlobCommitmentsPerBlock
inherit pendingPartialWithdrawalsLimit pendingConsolidationsLimit slotsPerEpochPos
inherit slotsPerEpochLt slotsPerHistoricalRootPos slotsPerHistoricalRootLt
inherit epochsPerHistoricalVectorPos epochsPerHistoricalVectorLt farFutureEpoch
inherit genesisSlot genesisEpoch validatorRegistryLimit historicalRootsLimit
inherit pendingDepositsLimit justificationBitsLength maxExtraDataBytes
inherit depositContractTreeDepth maxProposerSlashings maxAttesterSlashings
inherit maxAttestations maxDeposits maxVoluntaryExits maxBlsToExecutionChanges
inherit maxValidatorsPerCommittee maxDepositRequestsPerPayload
inherit maxWithdrawalRequestsPerPayload maxConsolidationRequestsPerPayload
inherit maxAttestationsElectra maxAttesterSlashingsElectra maxPendingDepositsPerEpoch
inherit maxBytesPerTransaction maxTransactionsPerPayload bytesPerLogsBloom
inherit effectiveBalanceIncrement effectiveBalanceIncrementG minDepositAmountG
inherit minActivationBalance maxEffectiveBalanceG maxEffectiveBalanceElectra
inherit maxEffectiveBalanceElectraG ejectionBalanceG unsetDepositRequestsStartIndex
inherit fullExitRequestAmount g2PointAtInfinity maxSeedLookahead minSeedLookahead
inherit minAttestationInclusionDelay minEpochsToInactivityPenalty baseRewardFactor
inherit weightDenominator proposerWeight syncRewardWeight timelySourceWeight
inherit timelyTargetWeight timelyHeadWeight timelySourceFlagIndex timelyTargetFlagIndex
inherit timelyHeadFlagIndex participationFlagWeights minSlashingPenaltyQuotientElectra
inherit whistleblowerRewardQuotientElectra proportionalSlashingMultiplierBellatrix
inherit inactivityPenaltyQuotientBellatrix inactivityScoreBias
inherit inactivityScoreRecoveryRate hysteresisQuotient hysteresisDownwardMultiplier
inherit hysteresisUpwardMultiplier maxRandomValue blsWithdrawalPrefix
inherit eth1AddressWithdrawalPrefix compoundingWithdrawalPrefix domainBeaconProposer
inherit domainBeaconAttester domainRandao domainDeposit domainVoluntaryExit
inherit domainSyncCommittee domainBlsToExecutionChange churnLimitQuotient
inherit minPerEpochChurnLimitElectra maxPerEpochActivationExitChurnLimit
inherit minValidatorWithdrawabilityDelay shardCommitteePeriod genesisForkVersion
inherit capellaForkVersion slotDurationMs attestationDueBps
inherit consolidationChurnLimitQuotient maxBlobsPerBlockElectra reorgHeadWeightThreshold
inherit reorgParentWeightThreshold reorgMaxEpochsSinceFinalization
inherit proposerReorgCutoffBps numberOfColumns kzgCommitmentsInclusionProofDepth
inherit proposerScoreBoost basisPoints
end
end Const

-- Gloas's own `ValidModulus` registrations, bound to this fork's `Preset`.
inherit validModulusSlotsPerEpoch validModulusSlotsPerHistoricalRoot
inherit validModulusEpochsPerHistoricalVector

/-- The `minimal` preset's Gloas entries; Fulu's merge in through the lineage. -/
forkpresetvalues minimal where
  ptcSize := 16
  maxBuildersPerWithdrawalsSweep := 16
  builderRegistryLimit := 2 ^ 40
  builderPendingWithdrawalsLimit := 2 ^ 20
  maxPayloadAttestations := 4
  maxBuilderDepositRequestsPerPayload := 256
  maxBuilderExitRequestsPerPayload := 16

/-- The `mainnet` preset's Gloas entries. -/
forkpresetvalues mainnet where
  ptcSize := 512
  maxBuildersPerWithdrawalsSweep := 16384
  builderRegistryLimit := 2 ^ 40
  builderPendingWithdrawalsLimit := 2 ^ 20
  maxPayloadAttestations := 4
  maxBuilderDepositRequestsPerPayload := 256
  maxBuilderExitRequestsPerPayload := 16

/-- The `minimal` config's Gloas entries. -/
forkconfigvalues minimalConfig where
  gloasForkVersion := ⟨#[0x07, 0, 0, 1], by decide⟩
  churnLimitQuotientGloas := 16
  maxPerEpochActivationChurnLimitGloas := 128000000000
  minBuilderWithdrawabilityDelay := 2

/-- The `mainnet` config's Gloas entries. -/
forkconfigvalues mainnetConfig where
  gloasForkVersion := ⟨#[0x07, 0, 0, 0], by decide⟩
  churnLimitQuotientGloas := 32768
  maxPerEpochActivationChurnLimitGloas := 256000000000
  minBuilderWithdrawabilityDelay := 8192

/-- `GLOAS_FORK_VERSION` at the `minimal` config (`0x07000001`). -/
def gloasForkVersionMinimal : Version := ⟨#[0x07, 0x00, 0x00, 0x01], by decide⟩
/-- `GLOAS_FORK_VERSION` at the `mainnet` config (`0x07000000`). -/
def gloasForkVersionMainnet : Version := ⟨#[0x07, 0x00, 0x00, 0x00], by decide⟩

end EthCLSpecs.Gloas
