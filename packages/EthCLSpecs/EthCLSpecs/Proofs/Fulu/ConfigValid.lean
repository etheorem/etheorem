import EthCLSpecs.Fulu.Constants

/-!
# `EthCLSpecs.Proofs.Fulu.ConfigValid`: the presets and configs the proofs accept

Some spec failures depend only on the constants. A preset with one slot per epoch makes the
justification step assert at the last slot of every epoch, whatever the state. `PresetValid`
and `ConfigValid` name the constants a theorem may assume, so the state invariants never
mention them.

## The source

Upstream states its config rules as tests, one `test_config_invariants.py` per fork under
`tests/core/pyspec/eth_consensus_specs/test/<fork>/unittests/` at the pinned tag
`v1.7.0-beta.4`. Each field below that mirrors one names the test. The tests that read a
constant this model does not carry (`MIN_PER_EPOCH_CHURN_LIMIT`, the networking and PeerDAS
blob-cell sizes) have no field.

## The additions

The upstream rules accept configs on which the spec itself fails. Each addition names the
failure it rules out, and each is a candidate upstream rule:

* `twoSlotsPerEpochLeSlotsPerHistoricalRoot`: `2·SPE ≤ SPHR`. At the last slot of epoch `E`,
  `get_block_root(previous_epoch)` asserts `state.slot ≤ start(E−1) + SPHR`, and the gap is
  `2·SPE − 1`. Upstream allows `SPHR = SPE`, which fails this assert whenever the
  previous-epoch target justifies.
* `twoLeSlotsPerEpoch`: `2 ≤ SPE`. With one slot per epoch the last slot is also the first,
  and `get_block_root(current_epoch)` asserts `start(E) < state.slot`.
* `epochsPerSyncCommitteePeriodPos`, `epochsPerEth1VotingPeriodPos`, and the churn floor in
  `ConfigValid`: the epoch reads each as a divisor. Python raises `ZeroDivisionError` on a zero
  divisor. The model returns `x % 0 = x` and `x / 0 = 0`, which silently turns off the sync
  committee rotation, the eth1 reset or the churn arithmetic.
* `effectiveBalanceIncrementPos`: Python's `%` in `test_balances` raises on a zero increment,
  so upstream requires it implicitly. Lean's `%` does not raise, so the rule is explicit.
* `minActivationBalanceLe`: `get_max_effective_balance` returns `MIN_ACTIVATION_BALANCE` or
  `MAX_EFFECTIVE_BALANCE_ELECTRA`, and the rule orders them, so every effective balance is at
  most the second.
* The two twin equations: the model carries `EFFECTIVE_BALANCE_INCREMENT` and
  `MAX_EFFECTIVE_BALANCE_ELECTRA` twice, as a `Nat` and as `Gwei`, because the reward arithmetic
  runs in `Nat` and the balance writes in `Gwei` (`Fulu/Constants.lean`). Both forms read the
  same YAML key, and the rule states that they agree.

## The shape

Both classes are `Prop`-valued and live on the proof side. A theorem takes them as instance
arguments, and at `minimal` and `mainnet` the instances below fill them by `decide`. They are
not fields of `Preset` or `Config`: the fork body needs none of these facts to typecheck, and
the runner builds `Config` at run time from a vector's `config.yaml`, where a field would force
a load-time check that pyspec does not make.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLSpecs.Fulu (Preset Config minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Fulu.Const

/-- The presets the proofs accept. -/
class PresetValid [Preset] : Prop where
  /-- `test_time`: `SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT`. -/
  slotsPerEpochLeSlotsPerHistoricalRoot : slotsPerEpoch ≤ slotsPerHistoricalRoot
  /-- `test_time`: `MIN_SEED_LOOKAHEAD < MAX_SEED_LOOKAHEAD`. -/
  minSeedLookaheadLtMaxSeedLookahead : minSeedLookahead < maxSeedLookahead
  /-- `test_time`: `SLOTS_PER_HISTORICAL_ROOT % SLOTS_PER_EPOCH == 0`. -/
  slotsPerHistoricalRootModSlotsPerEpoch : slotsPerHistoricalRoot % slotsPerEpoch = 0
  /-- `test_time`: `1 <= MIN_ATTESTATION_INCLUSION_DELAY <= SLOTS_PER_EPOCH`. -/
  minAttestationInclusionDelayBound :
    1 ≤ minAttestationInclusionDelay.toNat ∧ minAttestationInclusionDelay.toNat ≤ slotsPerEpoch
  /-- `test_balances`: `MAX_EFFECTIVE_BALANCE % EFFECTIVE_BALANCE_INCREMENT == 0`. -/
  maxEffectiveBalanceModIncrement : maxEffectiveBalanceG.toNat % effectiveBalanceIncrement = 0
  /-- `test_balances`: `MIN_DEPOSIT_AMOUNT >= 1`, and `MAX_EFFECTIVE_BALANCE` is at least
  `MIN_DEPOSIT_AMOUNT` and `EFFECTIVE_BALANCE_INCREMENT`. -/
  balanceBounds : 1 ≤ minDepositAmountG.toNat ∧ minDepositAmountG.toNat ≤ maxEffectiveBalanceG.toNat ∧
    effectiveBalanceIncrement ≤ maxEffectiveBalanceG.toNat
  /-- `test_hysteresis_quotient`: `1 <= DOWNWARD <= QUOTIENT <= UPWARD`. -/
  hysteresisOrder : 1 ≤ hysteresisDownwardMultiplier ∧
    hysteresisDownwardMultiplier ≤ hysteresisQuotient ∧ hysteresisQuotient ≤ hysteresisUpwardMultiplier
  /-- `test_incentives`: no ETH is minted in `slash_validator`. -/
  slashingPenaltyLeWhistleblowerReward :
    minSlashingPenaltyQuotientElectra ≤ whistleblowerRewardQuotientElectra
  /-- `test_validators`: the registry and committee caps are positive, and a committee fits
  the registry. -/
  committeeBounds : 1 ≤ validatorRegistryLimit ∧ 1 ≤ maxCommitteesPerSlot ∧
    1 ≤ targetCommitteeSize ∧ 1 ≤ maxValidatorsPerCommittee ∧
    maxValidatorsPerCommittee ≤ validatorRegistryLimit / slotsPerEpoch / maxCommitteesPerSlot
  /-- Electra `test_processing_pending_partial_withdrawals`. -/
  partialsLtWithdrawals : maxPendingPartialsPerWithdrawalsSweep < maxWithdrawalsPerPayload
  /-- Addition: `get_block_root(previous_epoch)` at the last slot of an epoch. -/
  twoSlotsPerEpochLeSlotsPerHistoricalRoot : 2 * slotsPerEpoch ≤ slotsPerHistoricalRoot
  /-- Addition: `get_block_root(current_epoch)` at the last slot of an epoch. -/
  twoLeSlotsPerEpoch : 2 ≤ slotsPerEpoch
  /-- Addition: the sync-committee period is a divisor. -/
  epochsPerSyncCommitteePeriodPos : 1 ≤ epochsPerSyncCommitteePeriod
  /-- Addition: the eth1 voting period is a divisor. -/
  epochsPerEth1VotingPeriodPos : 1 ≤ epochsPerEth1VotingPeriod
  /-- Addition: the increment is a divisor; upstream's `%` requires it implicitly. -/
  effectiveBalanceIncrementPos : 1 ≤ effectiveBalanceIncrement
  /-- Addition: the `Nat` and `Gwei` forms of `EFFECTIVE_BALANCE_INCREMENT` agree. -/
  effectiveBalanceIncrementTwin : effectiveBalanceIncrementG.toNat = effectiveBalanceIncrement
  /-- Addition: the `Nat` and `Gwei` forms of `MAX_EFFECTIVE_BALANCE_ELECTRA` agree. -/
  maxEffectiveBalanceElectraTwin : maxEffectiveBalanceElectraG.toNat = maxEffectiveBalanceElectra
  /-- Addition: `get_max_effective_balance` returns `MIN_ACTIVATION_BALANCE` or
  `MAX_EFFECTIVE_BALANCE_ELECTRA`, and the first is the smaller. Every effective balance is then at
  most `MAX_EFFECTIVE_BALANCE_ELECTRA`, which bounds the balance a consolidation moves. -/
  minActivationBalanceLe : minActivationBalance.toNat ≤ maxEffectiveBalanceElectra

/-- The configs the proofs accept, at a preset. -/
class ConfigValid [Preset] [Config] : Prop where
  /-- `test_validators`: `1 <= CHURN_LIMIT_QUOTIENT <= VALIDATOR_REGISTRY_LIMIT`. -/
  churnLimitQuotientBound :
    1 ≤ churnLimitQuotient.toNat ∧ churnLimitQuotient.toNat ≤ validatorRegistryLimit
  /-- `test_time`: `ATTESTATION_DUE_BPS <= BASIS_POINTS`. -/
  attestationDueBpsLe : attestationDueBps ≤ basisPoints
  /-- `test_fork_choice`: `PROPOSER_SCORE_BOOST <= 100`. -/
  proposerScoreBoostLe : proposerScoreBoost ≤ 100
  /-- `test_fork_choice`: `PROPOSER_REORG_CUTOFF_BPS <= BASIS_POINTS`. -/
  proposerReorgCutoffBpsLe : proposerReorgCutoffBps ≤ basisPoints
  /-- Altair `test_inactivity_score`: `INACTIVITY_SCORE_BIAS <= INACTIVITY_SCORE_RECOVERY_RATE`. -/
  inactivityScoreBiasLe : inactivityScoreBias ≤ inactivityScoreRecoveryRate
  /-- Electra `test_networking`: `MAX_BLOBS_PER_BLOCK_ELECTRA <= MAX_BLOB_COMMITMENTS_PER_BLOCK`. -/
  maxBlobsPerBlockElectraLe : maxBlobsPerBlockElectra ≤ maxBlobCommitmentsPerBlock
  /-- Fulu `test_blob_schedule`: each entry's blob count is under the commitment cap. Upstream
  runs this test at mainnet only, because its other half reads the fork epoch. -/
  blobScheduleLe : ∀ entry ∈ blobSchedule, entry.2 ≤ maxBlobCommitmentsPerBlock
  /-- Addition: the exit-churn floor is positive. The per-epoch exit churn is
  `min(MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT, max(MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA, …))`
  rounded down to an increment, and `compute_exit_epoch_and_update_churn` divides by it. -/
  exitChurnFloorPos : effectiveBalanceIncrementG ≤ minPerEpochChurnLimitElectra ∧
    effectiveBalanceIncrementG ≤ maxPerEpochActivationExitChurnLimit

/-- The weights add up to the denominator: altair `test_weight_denominator`. The weights are
spec constants, the same at every preset, so this is a theorem and no field. -/
theorem weights_sum [Preset] :
    timelyHeadWeight + timelySourceWeight + timelyTargetWeight + syncRewardWeight +
      proposerWeight = weightDenominator := rfl

-- `apply` names the preset in the constructor: the presets are reducible definitions, not
-- instances, so neither `constructor` nor an anonymous constructor finds one by synthesis.
instance presetValidMinimal : @PresetValid minimal := by
  apply @PresetValid.mk minimal <;> decide

instance presetValidMainnet : @PresetValid mainnet := by
  apply @PresetValid.mk mainnet <;> decide

instance configValidMinimal : @ConfigValid minimal minimalConfig := by
  apply @ConfigValid.mk minimal minimalConfig <;> decide

instance configValidMainnet : @ConfigValid mainnet mainnetConfig := by
  apply @ConfigValid.mk mainnet mainnetConfig <;> decide

end EthCLSpecs.Proofs.Fulu
