import EthCLSpecs.Heze.Types

/-!
# `EthCLSpecs.Heze.Constants`: the tier system (load order row 2)

Heze's three constant tiers, written as a diff over Gloas exactly as
`Gloas/Constants.lean` is a diff over Fulu. EIP-7805 (FOCIL) adds one preset
field, two flat constants, and three config values, and the fork adds its own fork
version and epoch to the config tier; everything else
arrives by lineage merge (the tier classes and their value sets) or by `inherit`
(the `Const` entries), replayed into this namespace so Heze body code writes
`Const.slotsPerEpoch` with no ancestor namespace in sight. A tier form with no
diff to declare is still written, since the class or value set it emits has to be
this fork's own.

`forkpreset` also emits the downgrade instance to `Gloas.Preset`, which chains
onward to `Fulu.Preset` through Gloas's own bridge, so injecting `Heze.minimal`
reaches either ancestor spine. `Upgrade.lean` and `Interface.lean` open it
(`FRAMEWORK_ARCHITECTURE.md` §4.2).
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

/-- The config values Heze adds. The lineage's fields merge in. -/
forkconfig where
  /-- `HEZE_FORK_VERSION`. -/
  hezeForkVersion : Version
  /-- `HEZE_FORK_EPOCH`. `FAR_FUTURE_EPOCH` in both config files; a vector that activates
  Heze at genesis overrides it to `0`. `compute_fork_version` reads it. -/
  hezeForkEpoch : Epoch
  /-- `INCLUSION_LIST_DUE_BPS` (~67% of the slot): the timeliness deadline for an
  inclusion list, in basis points of the slot. -/
  inclusionListDueBps : UInt64
  /-- `MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST` (8192): the cap on an inclusion list's
  summed transaction bytes, which `on_inclusion_list` asserts. v1.7.0-beta.4 renames
  alpha.12's `MAX_BYTES_PER_INCLUSION_LIST` to this. -/
  maxTransactionsBytesPerInclusionList : UInt64
  /-- `MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS` (1): how many slots past its own an
  inclusion list stays in the retention window `on_inclusion_list` asserts. -/
  minSlotsForInclusionListsRequests : UInt64

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
-- `consensus-specs/specs/heze/fork-choice.md:38`.
forkabbrev inclusionListDueBps : UInt64 := Config.inclusionListDueBps
forkabbrev hezeForkVersion : Version := Config.hezeForkVersion
forkabbrev hezeForkEpoch : Epoch := Config.hezeForkEpoch
forkabbrev maxTransactionsBytesPerInclusionList : UInt64 :=
  Config.maxTransactionsBytesPerInclusionList
forkabbrev minSlotsForInclusionListsRequests : UInt64 := Config.minSlotsForInclusionListsRequests

-- Gloas's entries, replayed here in Gloas's own order (its additions, then the
-- Fulu surface it replays) so each body reaches its dependencies. The list is the
-- whole surface, not the subset Heze happens to call today: the fork owns its
-- vocabulary, and a new call site should not have to come back and edit this block.

-- Gloas's own ePBS and EIP-8282 entries.
inherit ptcSize maxBuildersPerWithdrawalsSweep maxPayloadAttestations
inherit maxBuilderDepositRequestsPerPayload maxBuilderExitRequestsPerPayload
inherit gloasForkVersion gloasForkEpoch churnLimitQuotientGloas
inherit maxPerEpochActivationChurnLimitGloas
inherit minBuilderWithdrawabilityDelay builderPaymentThresholdNumerator
inherit builderPaymentThresholdDenominator builderWithdrawalPrefix payloadBuilderVersion
inherit builderIndexFlag builderIndexSelfBuild domainBeaconBuilder domainPtcAttester
inherit domainBuilderDeposit payloadStatusEmpty payloadStatusFull payloadStatusPending
inherit attestationTimelinessIndex ptcTimelinessIndex payloadTimelyThreshold
inherit dataAvailabilityTimelyThreshold attestationDueBpsGloas payloadAttestationDueBps
inherit gasLimitSchedule
inherit consolidationChurnLimitQuotient

-- Vector widths and committee / epoch lengths.
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

-- Sentinels, registry and history caps.
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

-- Network parameters, and the fork-choice tuning beside them.
inherit churnLimitQuotient minPerEpochChurnLimitElectra
inherit maxPerEpochActivationExitChurnLimit minValidatorWithdrawabilityDelay
inherit shardCommitteePeriod genesisForkVersion slotDurationMs
inherit altairForkVersion altairForkEpoch bellatrixForkVersion bellatrixForkEpoch
inherit capellaForkVersion capellaForkEpoch denebForkVersion denebForkEpoch
inherit electraForkVersion electraForkEpoch fuluForkVersion fuluForkEpoch
inherit attestationDueBps maxBlobsPerBlockElectra blobSchedule
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
forkconfigvalues minimalConfig where
  hezeForkVersion := ⟨#[0x08, 0, 0, 1], by decide⟩
  hezeForkEpoch := 0xffffffffffffffff
  inclusionListDueBps := 6667
  maxTransactionsBytesPerInclusionList := 8192
  minSlotsForInclusionListsRequests := 1
forkconfigvalues mainnetConfig where
  hezeForkVersion := ⟨#[0x08, 0, 0, 0], by decide⟩
  hezeForkEpoch := 0xffffffffffffffff
  inclusionListDueBps := 6667
  maxTransactionsBytesPerInclusionList := 8192
  minSlotsForInclusionListsRequests := 1

/-- `HEZE_FORK_VERSION` at the `minimal` config (`0x08000001`). -/
def hezeForkVersionMinimal : Version := ⟨#[0x08, 0x00, 0x00, 0x01], by decide⟩
/-- `HEZE_FORK_VERSION` at the `mainnet` config (`0x08000000`). -/
def hezeForkVersionMainnet : Version := ⟨#[0x08, 0x00, 0x00, 0x00], by decide⟩

end EthCLSpecs.Heze
