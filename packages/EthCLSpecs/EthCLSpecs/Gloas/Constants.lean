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

`forkpreset` also emits the downgrade instance to `Fulu.Preset`, the bridge
`Upgrade.lean` and `Interface.lean` open at the fork boundary
(`FRAMEWORK_ARCHITECTURE.md` §4.2).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

/-! ## The preset fields EIP-7732 and EIP-8282 add

Fulu's fields merge in through the lineage, so the emitted `Gloas.Preset` is one
flat class carrying both.

Stage 7.3b audit: the pinned module types every one of these `Uint64` (`PTC_SIZE`,
`MAX_BUILDERS_PER_WITHDRAWALS_SWEEP`, `MAX_PAYLOAD_ATTESTATIONS`,
`MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD`, `MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD`),
but each stays a structural `Nat`, with no checked view of its own. Each shapes a
type-level cap or sizes a plain iteration, and every executable read is
kind-blind: the `len(body.…) <= MAX_…` asserts and the `Nat.min` sweep limit
compare or choose a plain size, which orders the values exactly as Python's plain
`int` against a `Uint64` does, and `Array.range`/`Array.replicate` take a plain
count. `PTC_SIZE` alone also feeds an arithmetic formula, the majority threshold
`PTC_SIZE // 2`, so it is the one that carries a checked view (`ptcSizeC` below);
its `< 2 ^ 64` premise rides the preset, Fulu's own pattern. -/
forkpreset where
  /-- `PTC_SIZE`: the payload-timeliness committee's member count. -/
  ptcSize : Nat
  /-- `MAX_BUILDERS_PER_WITHDRAWALS_SWEEP`: builders visited per sweep. -/
  maxBuildersPerWithdrawalsSweep : Nat
  /-- `MAX_PAYLOAD_ATTESTATIONS` per block. -/
  maxPayloadAttestations : Nat
  /-- EIP-8282 per-payload builder-deposit cap. -/
  maxBuilderDepositRequestsPerPayload : Nat
  /-- EIP-8282 per-payload builder-exit cap. -/
  maxBuilderExitRequestsPerPayload : Nat
  /-- Well-formedness of `ptcSize`: a `uint64`-ranged value, the "it is a uint64"
  the value carries in the pyspec. Carried on the preset (Fulu's own pattern) so the
  `[Preset]` already threaded everywhere supplies the bound for the checked view. -/
  ptcSizeLt : ptcSize < 2 ^ 64

/-- The config values EIP-7732 adds, merged with Fulu's the same way. -/
forkconfig where
  /-- `GLOAS_FORK_VERSION`. -/
  gloasForkVersion : Version
  /-- `GLOAS_FORK_EPOCH`. `FAR_FUTURE_EPOCH` in both config files; a vector that activates
  Gloas at genesis overrides it to `0`, and a transition vector to its `fork_epoch`.
  `get_ptc` asserts the attested epoch is not before it. -/
  gloasForkEpoch : Epoch
  /-- `CHURN_LIMIT_QUOTIENT_GLOAS`: a `Uint64` in the pinned module, so the checked
  kind. `get_exit_churn_limit` / `get_activation_churn_limit` divide by it on the
  checked route. -/
  churnLimitQuotientGloas : CLUint64
  /-- `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`. -/
  maxPerEpochActivationChurnLimitGloas : Gwei
  /-- `MIN_BUILDER_WITHDRAWABILITY_DELAY`. -/
  minBuilderWithdrawabilityDelay : Epoch
  /-- `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`: a `Uint64` in the pinned module, so the
  checked kind. Electra's `get_consolidation_churn_limit` was a difference of two churn
  limits; EIP-7732 gives it its own quotient, so the value arrives with this fork rather
  than with Electra, and Gloas's `get_consolidation_churn_limit` divides by it on the
  checked route. -/
  consolidationChurnLimitQuotient : CLUint64
  /-- Slot-component deadlines in basis points of the slot. Both are `Uint64` in the pinned
  module, so the checked kind. -/
  attestationDueBpsGloas : CLUint64
  payloadAttestationDueBps : CLUint64
  /-- `GAS_LIMIT_SCHEDULE` (EIP-8261, new at v1.7.0-beta.4): the default and recommended maximum
  gas limit by epoch, one `(EPOCH, GAS_LIMIT)` record per entry. Empty in both config files.
  `get_scheduled_gas_limit` reads it; it adds no validity rule. -/
  gasLimitSchedule : List (Epoch × UInt64)

namespace Const
section
variable [Preset] [Config]

-- Gloas's own entries, declared before the inherited block: a replayed Fulu body
-- that names one of these binds to the copy here, and `payloadTimelyThreshold`
-- below divides this fork's `ptcSize`.
forkabbrev ptcSize : Nat := Preset.ptcSize
/-- The preset's `ptcSize < 2 ^ 64` premise, replayed as a `Const` entry the way
Fulu replays its own (`slotsPerEpochLt`), so the derived checked view below and a
child fork's inherits reach it without naming the tier. -/
forkabbrev ptcSizeLt : ptcSize < 2 ^ 64 := Preset.ptcSizeLt
/-- The checked view of `PTC_SIZE` (`SPEC_ARITHMETIC.md` §4.2): the pinned module
types it `Uint64`, and its one arithmetic projection, the majority threshold
`PTC_SIZE // 2`, divides the checked value. The range premise is the preset's own
`ptcSizeLt` field, so the view adds no `decide` and a child override re-proves
through the tier. -/
forkabbrev ptcSizeC : CLUint64 := CLUint64.ofNatLT Preset.ptcSize Preset.ptcSizeLt
forkabbrev maxBuildersPerWithdrawalsSweep : Nat := Preset.maxBuildersPerWithdrawalsSweep
forkabbrev maxPayloadAttestations : Nat := Preset.maxPayloadAttestations
forkabbrev maxBuilderDepositRequestsPerPayload : Nat := Preset.maxBuilderDepositRequestsPerPayload
forkabbrev maxBuilderExitRequestsPerPayload : Nat := Preset.maxBuilderExitRequestsPerPayload
forkabbrev gloasForkVersion : Version := Config.gloasForkVersion
forkabbrev gloasForkEpoch : Epoch := Config.gloasForkEpoch
/-- `CHURN_LIMIT_QUOTIENT_GLOAS`, the checked kind: the divisor of
`get_exit_churn_limit` and `get_activation_churn_limit`. A configuration value
keeps checked division: no `PositiveDivisor` view exists over a generic
configuration, whose accepted domain alone can supply positivity
(`SPEC_ARITHMETIC.md` §4.2). -/
forkabbrev churnLimitQuotientGloas : CLUint64 := Config.churnLimitQuotientGloas
forkabbrev maxPerEpochActivationChurnLimitGloas : Gwei := Config.maxPerEpochActivationChurnLimitGloas
forkabbrev minBuilderWithdrawabilityDelay : Epoch := Config.minBuilderWithdrawabilityDelay
/-- `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`, the checked kind: the divisor of Gloas's
`get_consolidation_churn_limit`. A configuration value keeps checked division: no
`PositiveDivisor` view exists over a generic configuration (`SPEC_ARITHMETIC.md`
§4.2). -/
forkabbrev consolidationChurnLimitQuotient : CLUint64 := Config.consolidationChurnLimitQuotient

/-- The builder-payment threshold, as a fraction of the bid
(`BUILDER_PAYMENT_THRESHOLD_NUMERATOR / …_DENOMINATOR`). Adjudication F2 closed by
the Stage 7.3b oracle run: the pinned module types both `Uint64(6)` / `Uint64(10)`
at every preset, so they store as `Gwei`, the checked kind the quorum product and
fraction in `get_builder_payment_quorum_threshold` use. -/
forkabbrev builderPaymentThresholdNumerator : Gwei := 6
forkabbrev builderPaymentThresholdDenominator : Gwei := 10
/-- `BUILDER_WITHDRAWAL_PREFIX` (`0xB0`), the credential prefix that marks a builder deposit.
A `Bytes1` at the pin, byte data: its one consumer compares it with the credentials' first
byte. -/
forkabbrev builderWithdrawalPrefix : UInt8 := 0xB0
/-- `PAYLOAD_BUILDER_VERSION = uint8(0)` (EIP-8282): the version stamped on a
builder onboarded at the fork (`add_builder_to_registry`). A version tag, not a number:
the pinned body stores it in `Builder.version` and compares it for equality, and no
operator touches it, so the raw `UInt8` carries it unchanged. -/
forkabbrev payloadBuilderVersion : UInt8 := 0
/-- `BUILDER_INDEX_FLAG = Uint64(2**40)`: the bit that marks a builder index carried in a
`ValidatorIndex`. A checked `Uint64`, so `&` and `|` with an index are the same-width
bitwise operators (`SPEC_ARITHMETIC.md` §5.1). -/
forkabbrev builderIndexFlag : CLUint64 := 0x10000000000
/-- `BUILDER_INDEX_SELF_BUILD = BuilderIndex(UINT64_MAX)`: the bid's `builder_index`
sentinel marking a proposer self-build (no external builder). -/
forkabbrev builderIndexSelfBuild : BuilderIndex := 0xffffffffffffffff
-- EIP-7732 / EIP-8282 BLS domain-type tags, beside the ones inherited below.
forkabbrev domainBeaconBuilder : ByteArray := ⟨#[0x0B, 0, 0, 0]⟩
forkabbrev domainPtcAttester : ByteArray := ⟨#[0x0C, 0, 0, 0]⟩
-- EIP-8282 `DOMAIN_BUILDER_DEPOSIT` (`0x0E000000`). Consumed by the deferred
-- builder-deposit signature check; recorded now alongside the other domain tags.
forkabbrev domainBuilderDeposit : ByteArray := ⟨#[0x0E, 0, 0, 0]⟩
/-- ePBS fork-choice payload statuses for a `ForkChoiceNode`: `PayloadStatus(Uint8)` sentinels
at the pin. The fork-choice bodies compare them for equality, and
`get_payload_status_tiebreaker` returns one of them or the literals `0`, `1`, `2` for the
`max` ordering. No operator touches them, so the raw `UInt8` carries the sentinels. -/
forkabbrev payloadStatusEmpty : UInt8 := 0
forkabbrev payloadStatusFull : UInt8 := 1
forkabbrev payloadStatusPending : UInt8 := 2
/-- `block_timeliness` deadline indices (attestation-due and PTC-due). The pinned
module types both `Uint64` (`Uint64(0)` / `Uint64(1)`), but each stays a structural
`Nat`: the only executable reads are the `arrGetIdx` indexes into the fixed
two-element `block_timeliness` arrays, in range on every input, and the index kind
cannot change a list read (`SPEC_ARITHMETIC.md` §3.7), so the `Nat` index gives the
same element (or the same `IndexError` on a short array). -/
forkabbrev attestationTimelinessIndex : Nat := 0
forkabbrev ptcTimelinessIndex : Nat := 1
/-- PTC vote majority thresholds, the checked kind: the pinned module derives each
as `PTC_SIZE // 2` over the checked `PTC_SIZE`, and the quotient of a checked value
by a literal stays checked (`SPEC_ARITHMETIC.md` §3.1); being in range proves
success, not a kind change. The division takes the proved-total `PositiveDivisor`
route, which cannot raise (the quotient is at most the dividend), so the view stays
pure. The one consumer compares a plain vote count against the threshold; Python's
mixed `int > Uint64` never raises and orders the values, which the comparison site
reads through `toPlainNat` (`SPEC_ARITHMETIC.md` §4.5). -/
forkabbrev payloadTimelyThreshold : CLUint64 := ptcSizeC / (⟨2, by decide⟩ : PositiveDivisor)
forkabbrev dataAvailabilityTimelyThreshold : CLUint64 :=
  ptcSizeC / (⟨2, by decide⟩ : PositiveDivisor)
forkabbrev attestationDueBpsGloas : CLUint64 := Config.attestationDueBpsGloas
forkabbrev payloadAttestationDueBps : CLUint64 := Config.payloadAttestationDueBps
forkabbrev gasLimitSchedule : List (Epoch × UInt64) := Config.gasLimitSchedule

-- Fulu's entries, replayed here in Fulu's own order so each body reaches its
-- dependencies. The list is the whole surface, not the subset Gloas happens to
-- call today: the fork owns its vocabulary, and a new call site should not have
-- to come back and edit this block.

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
inherit epochsPerHistoricalVectorLt shuffleRoundCountLe

-- The derived checked and proved-total views of the entries above
-- (`SPEC_ARITHMETIC.md` §4.2, §4.5). The replay binds each view to this fork's
-- own `Preset`, so Gloas's values use the same proof fields.
inherit slotsPerEpochC slotsPerEpochDiv slotsPerHistoricalRootC slotsPerHistoricalRootDiv
inherit epochsPerHistoricalVectorC epochsPerSlashingsVectorC
inherit epochsPerEth1VotingPeriodC epochsPerSyncCommitteePeriodC
inherit maxCommitteesPerSlotC targetCommitteeSizeC maxWithdrawalsPerPayloadC
inherit maxPendingPartialsPerWithdrawalsSweepC

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
inherit minActivationBalance maxEffectiveBalanceG
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

-- Gloas's own `ValidModulus` registrations, bound to this fork's `Preset`.
inherit validModulusSlotsPerEpoch validModulusSlotsPerHistoricalRoot
inherit validModulusEpochsPerHistoricalVector

/-- The `minimal` preset's Gloas entries; Fulu's merge in through the lineage. -/
forkpresetvalues minimal where
  ptcSize := 16
  maxBuildersPerWithdrawalsSweep := 16
  maxPayloadAttestations := 4
  maxBuilderDepositRequestsPerPayload := 64
  maxBuilderExitRequestsPerPayload := 16
  ptcSizeLt := by decide

/-- The `mainnet` preset's Gloas entries. -/
forkpresetvalues mainnet where
  ptcSize := 512
  maxBuildersPerWithdrawalsSweep := 16384
  maxPayloadAttestations := 4
  maxBuilderDepositRequestsPerPayload := 64
  maxBuilderExitRequestsPerPayload := 16
  ptcSizeLt := by decide

/-- The `minimal` config's Gloas entries. -/
forkconfigvalues minimalConfig where
  gasLimitSchedule := []
  consolidationChurnLimitQuotient := 32
  attestationDueBpsGloas := 2500
  payloadAttestationDueBps := 7500
  gloasForkVersion := ⟨#[0x07, 0, 0, 1], by decide⟩
  gloasForkEpoch := 0xffffffffffffffff
  churnLimitQuotientGloas := 16
  maxPerEpochActivationChurnLimitGloas := 128000000000
  minBuilderWithdrawabilityDelay := 2

/-- The `mainnet` config's Gloas entries. -/
forkconfigvalues mainnetConfig where
  gasLimitSchedule := []
  consolidationChurnLimitQuotient := 65536
  attestationDueBpsGloas := 2500
  payloadAttestationDueBps := 7500
  gloasForkVersion := ⟨#[0x07, 0, 0, 0], by decide⟩
  gloasForkEpoch := 0xffffffffffffffff
  churnLimitQuotientGloas := 32768
  maxPerEpochActivationChurnLimitGloas := 256000000000
  minBuilderWithdrawabilityDelay := 64

/-- `GLOAS_FORK_VERSION` at the `minimal` config (`0x07000001`). -/
def gloasForkVersionMinimal : Version := ⟨#[0x07, 0x00, 0x00, 0x01], by decide⟩
/-- `GLOAS_FORK_VERSION` at the `mainnet` config (`0x07000000`). -/
def gloasForkVersionMainnet : Version := ⟨#[0x07, 0x00, 0x00, 0x00], by decide⟩

end EthCLSpecs.Gloas
