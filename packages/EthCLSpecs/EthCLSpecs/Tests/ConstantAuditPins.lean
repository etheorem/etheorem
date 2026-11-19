import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Tests.ConstantAuditPins`: the Fulu configuration constants at arbitrary values

Behavior pins for Stage 7.3a of the arithmetic transition, the Fulu rows of the constant
audit. The pinned module (`eth-consensus-specs` 1.7.0b4) types each of these configuration
values `Uint64`, or `Epoch` for `REORG_MAX_EPOCHS_SINCE_FINALIZATION`, so each `Config`
field and `Const` mirror is `CLUint64`:

| Constant | Consumer | Checked operation |
|---|---|---|
| `INACTIVITY_SCORE_BIAS` | `process_inactivity_updates` | `score += bias` |
| `INACTIVITY_SCORE_RECOVERY_RATE` | `process_inactivity_updates` | `saturating_sub` |
| `INACTIVITY_SCORE_BIAS` | `get_inactivity_penalty_deltas` | `bias * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX`, then `//` |
| `CHURN_LIMIT_QUOTIENT` | `get_balance_churn_limit` | `//` |
| `PROPOSER_SCORE_BOOST`, `REORG_HEAD_WEIGHT_THRESHOLD`, `REORG_PARENT_WEIGHT_THRESHOLD` | `calculate_committee_fraction` | `committee_weight * committee_percent` |

The checked kind decides the answer once a configuration leaves the shipped values. Each
pin below sets one value, and each failure pin has a nearby success that reaches the same
operation. A configuration value carries no positivity proof, so a zero divisor raises
Python's `ZeroDivisionError` (`SPEC_ARITHMETIC.md` §4.2).

Every expected value is the answer of the pinned pyspec (the `minimal` module with the one
`config` field replaced), read by running the probes on the state these pins build. Fulu,
Gloas, and Heze gave the same answers. The Gloas and Heze pins run the inherited
`calculate_committee_fraction` and `get_inactivity_penalty_deltas`. Gloas and Heze have no
`get_balance_churn_limit`, so the churn pins run in Fulu alone.

The pins close by `native_decide`, as the other migration pins do: the minimal
configuration is a large record.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.ConstantAuditPins

/-- What a call produced: the answer as a plain `Nat`, a range fault (Python's
`SSZValueError`), the zero divisor (Python's `ZeroDivisionError`), or another error. -/
private inductive Outcome where
  | answer (n : Nat)
  | rangeFault
  | zeroDivision
  | otherFault
  deriving DecidableEq

/-- Classify a state-transition error. -/
private def errorOutcome : StateTransitionError → Outcome
  | .arithmetic _ => .rangeFault
  | .zeroDivision _ => .zeroDivision
  | _ => .otherFault

/-- Classify a helper that returns one `Gwei`. -/
private def gweiOutcome : Except StateTransitionError CLUint64 → Outcome
  | .ok v => .answer v.toPlainNat
  | .error e => errorOutcome e

/-- Classify a delta helper over the one-validator registry: the single delta. -/
private def deltaOutcome : Except StateTransitionError (Array CLUint64) → Outcome
  | .ok ds => if h : 0 < ds.size then .answer ds[0].toPlainNat else .otherFault
  | .error e => errorOutcome e

/-- `2^40`, the least `INACTIVITY_SCORE_BIAS` whose product with
`INACTIVITY_PENALTY_QUOTIENT_BELLATRIX = 2^24` passes `2^64 - 1`. -/
private abbrev biasProductEdge : CLUint64 := 1099511627776

/-- `2^40 - 1`, the greatest bias whose product with `2^24` fits. -/
private abbrev biasBelowEdge : CLUint64 := 1099511627775

/-- `UINT64_MAX`. -/
private abbrev u64Max : CLUint64 := 18446744073709551615

/-- `UINT64_MAX - 100`: added to the score `100`, the sum is `UINT64_MAX` exactly. -/
private abbrev biasToMax : CLUint64 := 18446744073709551515

/-- `UINT64_MAX - 99`: added to the score `100`, the sum is `2^64`. -/
private abbrev biasPastMax : CLUint64 := 18446744073709551516

/-- `(2^64 - 1) // 4_000_000_000`, the greatest committee percent whose product with the
per-slot weight `4_000_000_000` (one `32 ETH` validator over eight slots) fits. -/
private abbrev percentEdge : CLUint64 := 4611686018

/-- `percentEdge + 1`, the least committee percent whose product passes `2^64 - 1`. -/
private abbrev percentPastEdge : CLUint64 := 4611686019

/-! ### Fulu -/

section Fulu
open EthCLSpecs.Fulu

/-- A validator active from epoch `0`, never exiting, with `32 ETH` effective balance. -/
private def activeValidator : @Validator minimal :=
  letI : Preset := minimal
  { (default : Validator) with
    activationEpoch := 0
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- A state at epoch `2` (slot `16`) with the one active validator, zero participation
flags, and an inactivity score of `100`. The validator is eligible and not a timely-target
voter. The finality delay is `1`, so the chain is not in an inactivity leak. -/
private def auditState : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  SSZ.FastBox
    { (default : @BeaconState minimal) with
      slot := 16
      validators := ⟨#[activeValidator], by decide⟩
      balances := ⟨#[32000000000], by decide⟩
      previousEpochParticipation := ⟨#[0], by decide⟩
      currentEpochParticipation := ⟨#[0], by decide⟩
      inactivityScores := ⟨#[100], by decide⟩ }

/-- The score `process_inactivity_updates` leaves under configuration `c`. -/
private def inactivityScoreAfter (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processInactivityUpdates : EStateM StateTransitionError State Unit).run auditState with
  | .ok _ post => .answer (sszGet post inactivityScores)[0]!.toPlainNat
  | .error e _ => errorOutcome e

/-- The one penalty `get_inactivity_penalty_deltas` returns under configuration `c`. -/
private def inactivityPenalty (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  deltaOutcome (getInactivityPenaltyDeltas auditState)

/-- `get_balance_churn_limit` under configuration `c`. -/
private def balanceChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getBalanceChurnLimit auditState)

/-- `compute_proposer_score` under configuration `c`. -/
private def proposerScore (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (computeProposerScore auditState)

/-- `calculate_committee_fraction` at the shipped configuration, for the percent `p`. -/
private def committeeFraction (p : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (calculateCommitteeFraction auditState p)

-- `process_inactivity_updates`: the bias add raises past `2^64 - 1`. The shipped run adds
-- `4` and subtracts `16`; at bias `UINT64_MAX - 100` the add reaches `UINT64_MAX` exactly.
example : inactivityScoreAfter minimalConfig = .answer 88 := by native_decide
example : inactivityScoreAfter { minimalConfig with inactivityScoreBias := biasToMax }
    = .answer 18446744073709551599 := by native_decide
example : inactivityScoreAfter { minimalConfig with inactivityScoreBias := biasPastMax }
    = .rangeFault := by native_decide
-- The recovery rate is a `saturating_sub` operand, so `UINT64_MAX` floors the score at zero.
example : inactivityScoreAfter { minimalConfig with inactivityScoreRecoveryRate := u64Max }
    = .answer 0 := by native_decide

-- `get_inactivity_penalty_deltas`: the divisor `INACTIVITY_SCORE_BIAS * 2^24` raises at bias
-- `2^40`, and a zero bias makes a zero divisor. The shipped penalty is
-- `32_000_000_000 * 100 // (4 * 2^24) = 47683`.
example : inactivityPenalty minimalConfig = .answer 47683 := by native_decide
example : inactivityPenalty { minimalConfig with inactivityScoreBias := 0 }
    = .zeroDivision := by native_decide
example : inactivityPenalty { minimalConfig with inactivityScoreBias := biasBelowEdge }
    = .answer 0 := by native_decide
example : inactivityPenalty { minimalConfig with inactivityScoreBias := biasProductEdge }
    = .rangeFault := by native_decide

-- `get_balance_churn_limit`: a zero quotient raises the zero divisor. Quotient `1` succeeds,
-- and `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA` still wins the `max`.
example : balanceChurnLimit minimalConfig = .answer 64000000000 := by native_decide
example : balanceChurnLimit { minimalConfig with churnLimitQuotient := 0 }
    = .zeroDivision := by native_decide
example : balanceChurnLimit { minimalConfig with churnLimitQuotient := 1 }
    = .answer 64000000000 := by native_decide

-- `compute_proposer_score`: `committee_weight * PROPOSER_SCORE_BOOST` raises past
-- `2^64 - 1`. The per-slot weight is `32_000_000_000 // 8 = 4_000_000_000`.
example : proposerScore minimalConfig = .answer 1600000000 := by native_decide
example : proposerScore { minimalConfig with proposerScoreBoost := 0 } = .answer 0 := by
  native_decide
example : proposerScore { minimalConfig with proposerScoreBoost := percentEdge }
    = .answer 184467440720000000 := by native_decide
example : proposerScore { minimalConfig with proposerScoreBoost := percentPastEdge }
    = .rangeFault := by native_decide
example : proposerScore { minimalConfig with proposerScoreBoost := u64Max }
    = .rangeFault := by native_decide

-- `calculate_committee_fraction` at the two reorg thresholds, the values `is_head_weak` and
-- `is_parent_strong` pass, and past the product edge.
example : committeeFraction (@Const.reorgHeadWeightThreshold minimalConfig)
    = .answer 800000000 := by native_decide
example : committeeFraction (@Const.reorgParentWeightThreshold minimalConfig)
    = .answer 6400000000 := by native_decide
example : committeeFraction percentPastEdge = .rangeFault := by native_decide

end Fulu

/-! ### Gloas: the inherited helpers -/

section Gloas
open EthCLSpecs.Gloas

/-- The Fulu audit state, over Gloas's own `BeaconState`. -/
private def gloasAuditState : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      activationEpoch := 0
      effectiveBalance := 32000000000
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch }
  SSZ.FastBox
    { (default : @BeaconState minimal) with
      slot := 16
      validators := ⟨#[v]⟩
      balances := ⟨#[32000000000]⟩
      previousEpochParticipation := ⟨#[0]⟩
      currentEpochParticipation := ⟨#[0]⟩
      inactivityScores := ⟨#[100]⟩ }

/-- Gloas `compute_proposer_score` under configuration `c`. -/
private def gloasProposerScore (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (computeProposerScore gloasAuditState)

/-- Gloas `get_inactivity_penalty_deltas` under configuration `c`. -/
private def gloasInactivityPenalty (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  deltaOutcome (getInactivityPenaltyDeltas gloasAuditState)

example : gloasProposerScore minimalConfig = .answer 1600000000 := by native_decide
example : gloasProposerScore { minimalConfig with proposerScoreBoost := percentEdge }
    = .answer 184467440720000000 := by native_decide
example : gloasProposerScore { minimalConfig with proposerScoreBoost := percentPastEdge }
    = .rangeFault := by native_decide
example : gloasInactivityPenalty minimalConfig = .answer 47683 := by native_decide
example : gloasInactivityPenalty { minimalConfig with inactivityScoreBias := biasProductEdge }
    = .rangeFault := by native_decide

end Gloas

/-! ### Heze: the inherited helpers -/

section Heze
open EthCLSpecs.Heze

/-- The Fulu audit state, over Heze's own `BeaconState`. -/
private def hezeAuditState : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      activationEpoch := 0
      effectiveBalance := 32000000000
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch }
  SSZ.FastBox
    { (default : @BeaconState minimal) with
      slot := 16
      validators := ⟨#[v]⟩
      balances := ⟨#[32000000000]⟩
      previousEpochParticipation := ⟨#[0]⟩
      currentEpochParticipation := ⟨#[0]⟩
      inactivityScores := ⟨#[100]⟩ }

/-- Heze `compute_proposer_score` under configuration `c`. -/
private def hezeProposerScore (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (computeProposerScore hezeAuditState)

/-- Heze `get_inactivity_penalty_deltas` under configuration `c`. -/
private def hezeInactivityPenalty (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  deltaOutcome (getInactivityPenaltyDeltas hezeAuditState)

example : hezeProposerScore minimalConfig = .answer 1600000000 := by native_decide
example : hezeProposerScore { minimalConfig with proposerScoreBoost := percentEdge }
    = .answer 184467440720000000 := by native_decide
example : hezeProposerScore { minimalConfig with proposerScoreBoost := percentPastEdge }
    = .rangeFault := by native_decide
example : hezeInactivityPenalty minimalConfig = .answer 47683 := by native_decide
example : hezeInactivityPenalty { minimalConfig with inactivityScoreBias := biasProductEdge }
    = .rangeFault := by native_decide

end Heze

end EthCLSpecs.Tests.ConstantAuditPins
