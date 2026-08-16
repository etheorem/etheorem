import EthCLSpecs.Heze.Types

/-!
# `EthCLSpecs.Heze.Constants`: the tier system (load order row 2)

Heze's three constant tiers, written as a diff over Gloas exactly as
`Gloas/Constants.lean` is a diff over Fulu. EIP-7805 (FOCIL) adds one preset
field and two flat constants, and leaves the config tier alone; everything else
arrives by lineage merge (the tier classes and their value sets) or by `inherit`
(the `Const` entries), replayed into this namespace so Heze body code writes
`Const.slotsPerEpoch` with no ancestor namespace in sight. A tier form with no
diff to declare is still written, since the class or value set it emits has to be
this fork's own.

The replayed surface is nearly the whole of Gloas's, since EIP-7805 leaves the
ePBS containers and constants alone. The compiler enumerates it: a name Heze
calls but never inherits fails with an unknown identifier.

`forkpreset` also emits the scoped downgrade instance to `Gloas.Preset`, which
chains onward to `Fulu.Preset` through Gloas's own bridge. `Upgrade.lean` and
`Interface.lean` open it (`FRAMEWORK_ARCHITECTURE.md` §4).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

/-- The one preset field EIP-7805 adds. Gloas's and Fulu's merge in through the
lineage. -/
forkpreset where
  /-- `INCLUSION_LIST_COMMITTEE_SIZE`: FOCIL inclusion-list committee members per
  slot. -/
  inclusionListCommitteeSize : Nat

-- EIP-7805 adds no config value, and the fork still declares its own class: Heze
-- body code constrains `[Heze.Config]`, so the class has to exist here, carrying
-- the lineage's merged fields.
forkconfig

namespace Const
section
variable [Preset] [Config]

-- Heze's own entries, ahead of the inherited block so a replayed body that names
-- one binds to the copy here.
forkabbrev inclusionListCommitteeSize : Nat := Preset.inclusionListCommitteeSize
-- EIP-7805 `DOMAIN_INCLUSION_LIST_COMMITTEE` (`0x10000000`), the FOCIL
-- inclusion-list committee signature domain; `Heze.isValidInclusionListSignature`
-- (`Heze/Signing.lean`) verifies signatures under it.
forkabbrev domainInclusionListCommittee : ByteArray := ⟨#[0x10, 0, 0, 0]⟩
/-- `INCLUSION_LIST_DUE_BPS` (EIP-7805, ~67% of the slot): the timeliness deadline
for an inclusion list, in basis points of the slot
(`consensus-specs/specs/heze/fork-choice.md:38`). -/
forkabbrev inclusionListDueBps : UInt64 := 6667

-- Gloas's entries, replayed here in Gloas's own order (its additions, then the
-- Fulu surface it replays) so each body reaches its dependencies. The list is the
-- whole surface, not the subset Heze happens to call today: the fork owns its
-- vocabulary, and a new call site should not have to come back and edit this block.

-- Gloas's own ePBS and EIP-8282 entries.
inherit ptcSize maxBuildersPerWithdrawalsSweep builderRegistryLimit
inherit builderPendingWithdrawalsLimit maxPayloadAttestations
inherit maxBuilderDepositRequestsPerPayload maxBuilderExitRequestsPerPayload
inherit gloasForkVersion churnLimitQuotientGloas maxPerEpochActivationChurnLimitGloas
inherit minBuilderWithdrawabilityDelay builderPaymentThresholdNumerator
inherit builderPaymentThresholdDenominator builderWithdrawalPrefix payloadBuilderVersion
inherit builderIndexFlag builderIndexSelfBuild domainBeaconBuilder domainPtcAttester
inherit domainBuilderDeposit payloadStatusEmpty payloadStatusFull payloadStatusPending
inherit attestationTimelinessIndex ptcTimelinessIndex payloadTimelyThreshold
inherit dataAvailabilityTimelyThreshold attestationDueBpsGloas payloadAttestationDueBps

-- Preset-tier entries.
inherit slotsPerEpoch slotsPerHistoricalRoot epochsPerHistoricalVector
inherit epochsPerSlashingsVector epochsPerEth1VotingPeriod epochsPerSyncCommitteePeriod
inherit syncCommitteeSize maxCommitteesPerSlot targetCommitteeSize shuffleRoundCount
inherit maxValidatorsPerWithdrawalsSweep maxPendingPartialsPerWithdrawalsSweep
inherit maxWithdrawalsPerPayload maxBlobCommitmentsPerBlock
inherit pendingPartialWithdrawalsLimit pendingConsolidationsLimit

-- The preset's well-formedness premises.
inherit slotsPerEpochPos slotsPerEpochLt slotsPerHistoricalRootPos
inherit slotsPerHistoricalRootLt epochsPerHistoricalVectorPos
inherit epochsPerHistoricalVectorLt

-- Universal-tier entries: literal bodies, no binder.
inherit farFutureEpoch genesisSlot genesisEpoch validatorRegistryLimit
inherit historicalRootsLimit pendingDepositsLimit justificationBitsLength
inherit maxExtraDataBytes depositContractTreeDepth

-- Per-block operation caps.
inherit maxProposerSlashings maxAttesterSlashings maxAttestations maxDeposits
inherit maxVoluntaryExits maxBlsToExecutionChanges maxValidatorsPerCommittee
inherit maxDepositRequestsPerPayload maxWithdrawalRequestsPerPayload
inherit maxConsolidationRequestsPerPayload maxAttestationsElectra
inherit maxAttesterSlashingsElectra maxPendingDepositsPerEpoch maxBytesPerTransaction
inherit maxTransactionsPerPayload bytesPerLogsBloom

-- Balance and effective-balance thresholds.
inherit effectiveBalanceIncrement effectiveBalanceIncrementG minDepositAmountG
inherit minActivationBalance maxEffectiveBalanceG maxEffectiveBalanceElectra
inherit maxEffectiveBalanceElectraG ejectionBalanceG unsetDepositRequestsStartIndex
inherit fullExitRequestAmount g2PointAtInfinity

-- Timing and lifecycle.
inherit maxSeedLookahead minSeedLookahead minAttestationInclusionDelay
inherit minEpochsToInactivityPenalty

-- Reward / penalty weights and quotients.
inherit baseRewardFactor weightDenominator proposerWeight syncRewardWeight
inherit timelySourceWeight timelyTargetWeight timelyHeadWeight timelySourceFlagIndex
inherit timelyTargetFlagIndex timelyHeadFlagIndex participationFlagWeights
inherit minSlashingPenaltyQuotientElectra whistleblowerRewardQuotientElectra
inherit proportionalSlashingMultiplierBellatrix inactivityPenaltyQuotientBellatrix
inherit inactivityScoreBias inactivityScoreRecoveryRate hysteresisQuotient
inherit hysteresisDownwardMultiplier hysteresisUpwardMultiplier maxRandomValue

-- Withdrawal-credential prefixes.
inherit blsWithdrawalPrefix eth1AddressWithdrawalPrefix compoundingWithdrawalPrefix

-- BLS domain-type tags.
inherit domainBeaconProposer domainBeaconAttester domainRandao domainDeposit
inherit domainVoluntaryExit domainSyncCommittee domainBlsToExecutionChange

-- Config-tier entries, and the fork-choice tuning beside them.
inherit churnLimitQuotient minPerEpochChurnLimitElectra
inherit maxPerEpochActivationExitChurnLimit minValidatorWithdrawabilityDelay
inherit shardCommitteePeriod genesisForkVersion capellaForkVersion slotDurationMs
inherit attestationDueBps consolidationChurnLimitQuotient maxBlobsPerBlockElectra
inherit reorgHeadWeightThreshold reorgParentWeightThreshold
inherit reorgMaxEpochsSinceFinalization proposerReorgCutoffBps numberOfColumns
inherit kzgCommitmentsInclusionProofDepth proposerScoreBoost basisPoints
end
end Const

-- Heze's own `ValidModulus` registrations, bound to this fork's `Preset`.
inherit validModulusSlotsPerEpoch validModulusSlotsPerHistoricalRoot
inherit validModulusEpochsPerHistoricalVector

-- Each value set is declared here too, so `Heze.minimal` and friends are this
-- fork's own, typed at this fork's classes, and the runner injects them without
-- naming an ancestor. Only the FOCIL field needs a value; the rest merge in.
-- `INCLUSION_LIST_COMMITTEE_SIZE` is `2**4` in both preset files at the pin.
forkpresetvalues minimal where
  inclusionListCommitteeSize := 16
forkpresetvalues mainnet where
  inclusionListCommitteeSize := 16
forkconfigvalues minimalConfig
forkconfigvalues mainnetConfig

/-- `HEZE_FORK_VERSION` at the `minimal` config (`0x08000001`). -/
def hezeForkVersionMinimal : Version := ⟨#[0x08, 0x00, 0x00, 0x01], by decide⟩
/-- `HEZE_FORK_VERSION` at the `mainnet` config (`0x08000000`). -/
def hezeForkVersionMainnet : Version := ⟨#[0x08, 0x00, 0x00, 0x00], by decide⟩

end EthCLSpecs.Heze
