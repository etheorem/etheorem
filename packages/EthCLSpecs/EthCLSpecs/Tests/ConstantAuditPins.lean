import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Tests.ConstantAuditPins`: the configuration constants at arbitrary values

Behavior pins for the configuration constants that feed checked arithmetic: the Fulu rows,
then the Gloas rows, then the Heze rows. The pinned module (`eth-consensus-specs` 1.7.0b4)
types each of these configuration values `Uint64`, or `Epoch` for
`REORG_MAX_EPOCHS_SINCE_FINALIZATION`, so each `Config` field and `Const` mirror is
`CLUint64`:

| Constant | Consumer | Checked operation |
|---|---|---|
| `INACTIVITY_SCORE_BIAS` | `process_inactivity_updates` | `score += bias` |
| `INACTIVITY_SCORE_RECOVERY_RATE` | `process_inactivity_updates` | `saturating_sub` |
| `INACTIVITY_SCORE_BIAS` | `get_inactivity_penalty_deltas` | `bias * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX`, then `//` |
| `CHURN_LIMIT_QUOTIENT` | `get_balance_churn_limit` | `//` |
| `PROPOSER_SCORE_BOOST`, `REORG_HEAD_WEIGHT_THRESHOLD`, `REORG_PARENT_WEIGHT_THRESHOLD` | `calculate_committee_fraction` | `committee_weight * committee_percent` |
| `CHURN_LIMIT_QUOTIENT_GLOAS` | `get_exit_churn_limit`, `get_activation_churn_limit` | `//` |
| `CONSOLIDATION_CHURN_LIMIT_QUOTIENT` | `get_consolidation_churn_limit` | `//` |
| `BUILDER_PAYMENT_THRESHOLD_NUMERATOR` / `…_DENOMINATOR` | `get_builder_payment_quorum_threshold` | `*`, then `//` |
| `PAYLOAD_TIMELY_THRESHOLD`, `DATA_AVAILABILITY_TIMELY_THRESHOLD` | `payload_timeliness`, `payload_data_availability` | `PTC_SIZE // 2` at import, then `vote_count > threshold` |
| `MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST` | `on_inclusion_list` | mixed `int <= Uint64` against the plain byte sum (never raises) |
| `MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS` (`Slot`) | `on_inclusion_list` | the checked `Slot` add of the retention window |
| `INCLUSION_LIST_DUE_BPS` | `get_inclusion_list_due_ms` | `bps * SLOT_DURATION_MS // BASIS_POINTS` |

The checked kind decides the answer once a configuration leaves the shipped values. Each
pin below sets one value, and each failure pin has a nearby success that reaches the same
operation. A configuration value carries no positivity proof, so a zero divisor raises
Python's `ZeroDivisionError` (`SPEC_ARITHMETIC.md` §4.2).

Every expected value is the answer of the pinned pyspec (the `minimal` module with the one
`config` field replaced), read by running the probes on the state these pins build. Fulu,
Gloas, and Heze gave the same answers. The Gloas and Heze pins run the inherited
`calculate_committee_fraction` and `get_inactivity_penalty_deltas`. Fulu and Heze have no
`get_exit_churn_limit` of their own (it is Gloas's EIP-8061 override, inherited by Heze),
so those pins run in Gloas, and Heze re-runs the inherited churn helpers.

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
private def auditState : @State minimal :=
  letI : Preset := minimal
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
  letI : CryptoBackend := CryptoBackend.ffi
  match (processInactivityUpdates : EStateM StateTransitionError State Unit).run auditState with
  | .ok _ post => .answer post.inactivityScores[0]!.toPlainNat
  | .error e _ => errorOutcome e

/-- The one penalty `get_inactivity_penalty_deltas` returns under configuration `c`. -/
private def inactivityPenalty (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  deltaOutcome (getInactivityPenaltyDeltas auditState)

/-- `get_balance_churn_limit` under configuration `c`. -/
private def balanceChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getBalanceChurnLimit auditState)

/-- `compute_proposer_score` under configuration `c`. -/
private def proposerScore (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (computeProposerScore auditState)

/-- `calculate_committee_fraction` at the shipped configuration, for the percent `p`. -/
private def committeeFraction (p : CLUint64) : Outcome :=
  letI : Preset := minimal
  letI : Config := minimalConfig
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
private def gloasAuditState : @State minimal :=
  letI : Preset := minimal
  let v : Validator :=
    { (default : Validator) with
      activationEpoch := 0
      effectiveBalance := 32000000000
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch }
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
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (computeProposerScore gloasAuditState)

/-- Gloas `get_inactivity_penalty_deltas` under configuration `c`. -/
private def gloasInactivityPenalty (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
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

/-! ### Gloas: the churn and builder-payment rows

The Gloas churn quotients and the builder-payment threshold pair. Each pin's expected
value is the pinned module's answer for the same one-validator state (`gloasAuditState`
above), read with the one `config` field replaced. `get_exit_churn_limit`'s `max` keeps
`MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA` winning at both the shipped quotient `16` and `1`,
so the pair pins that the division ran without pinning its quotient alone;
`get_consolidation_churn_limit` has no floor, so its quotient `1` shows through. -/

/-- Gloas `get_exit_churn_limit` under configuration `c`. -/
private def gloasExitChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getExitChurnLimit gloasAuditState)

/-- Gloas `get_activation_churn_limit` under configuration `c`. -/
private def gloasActivationChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getActivationChurnLimit gloasAuditState)

/-- Gloas `get_consolidation_churn_limit` under configuration `c`. -/
private def gloasConsolidationChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getConsolidationChurnLimit gloasAuditState)

/-- Gloas `get_builder_payment_quorum_threshold` under configuration `c`. -/
private def gloasPaymentQuorum (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getBuilderPaymentQuorumThreshold gloasAuditState)

-- `get_exit_churn_limit`: the shipped quotient `16` and `1` both leave the min-churn
-- floor winning the `max`; a zero quotient raises the zero divisor.
example : gloasExitChurnLimit minimalConfig = .answer 64000000000 := by native_decide
example : gloasExitChurnLimit { minimalConfig with churnLimitQuotientGloas := 1 }
    = .answer 64000000000 := by native_decide
example : gloasExitChurnLimit { minimalConfig with churnLimitQuotientGloas := 0 }
    = .zeroDivision := by native_decide

-- `get_activation_churn_limit`: the `min` with `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`
-- (`128_000_000_000` at minimal) caps the exit churn's `64_000_000_000`.
example : gloasActivationChurnLimit minimalConfig = .answer 64000000000 := by native_decide

-- `get_consolidation_churn_limit`: no floor, so the quotient shows through: shipped `32`
-- gives `1_000_000_000`, quotient `1` gives the whole rounded balance, and zero divides by
-- zero.
example : gloasConsolidationChurnLimit minimalConfig = .answer 1000000000 := by native_decide
example : gloasConsolidationChurnLimit
    { minimalConfig with consolidationChurnLimitQuotient := 1 }
    = .answer 32000000000 := by native_decide
example : gloasConsolidationChurnLimit
    { minimalConfig with consolidationChurnLimitQuotient := 0 }
    = .zeroDivision := by native_decide

-- `get_builder_payment_quorum_threshold`: the checked `Uint64(6)` /
-- `Uint64(10)` pair over `32_000_000_000 / 8` per slot gives `2_400_000_000`.
example : gloasPaymentQuorum minimalConfig = .answer 2400000000 := by native_decide

/-- A two-validator edge state, both active at `2 ^ 63 - 1` each: the total active
balance `2 ^ 64 - 2` is the greatest that fits, and the quorum product
`(2 ^ 64 - 2) / 8 * 6` is the nearest in-range product the fixture can reach. -/
private def gloasEdgeState : @State minimal :=
  letI : Preset := minimal
  let v : Validator :=
    { (default : Validator) with
      activationEpoch := 0
      effectiveBalance := 9223372036854775807
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch }
  { (default : @BeaconState minimal) with
    slot := 16
    validators := ⟨#[v, v]⟩
    balances := ⟨#[9223372036854775807, 9223372036854775807]⟩
    previousEpochParticipation := ⟨#[0, 0]⟩
    currentEpochParticipation := ⟨#[0, 0]⟩
    inactivityScores := ⟨#[100, 100]⟩ }

/-- The quorum at the total-active-balance edge: the product stays in range, so the
threshold answers rather than raising. -/
private def gloasEdgePaymentQuorum : Outcome :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getBuilderPaymentQuorumThreshold gloasEdgeState)

example : gloasEdgePaymentQuorum = .answer 1383505805528216370 := by native_decide

/-! ### Gloas: the majority thresholds

`PAYLOAD_TIMELY_THRESHOLD` / `DATA_AVAILABILITY_TIMELY_THRESHOLD` are `PTC_SIZE // 2`
over the checked `PTC_SIZE` (`Uint64` at the pin), so each is `CLUint64`, derived at
import. The pins read the derived value at both presets, then run the comparison
end-to-end: `payload_timeliness` counts `some true` votes and compares the
plain count against the threshold's plain projection, exactly Python's mixed
`int > Uint64` (never raising, ordering the values). At `PTC_SIZE = 16` the threshold is
`8`, so `8` timely votes are not a majority and `9` are. -/

/-- The payload-timeliness threshold, `PTC_SIZE // 2`, at the `minimal` preset. -/
private def thresholdMinimal : Nat × Nat :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  (Const.payloadTimelyThreshold.toPlainNat, Const.dataAvailabilityTimelyThreshold.toPlainNat)

/-- The same at the `mainnet` preset. -/
private def thresholdMainnet : Nat × Nat :=
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  (Const.payloadTimelyThreshold.toPlainNat, Const.dataAvailabilityTimelyThreshold.toPlainNat)

example : thresholdMinimal = (8, 8) := by native_decide
example : thresholdMainnet = (256, 256) := by native_decide

/-- The pins' concrete fork-choice monad: the minimal preset over the deterministic
`treeMap`. -/
private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap)

/-- A store whose root has a revealed payload (so `is_payload_verified` holds) and a
16-vote timeliness array: `trues` entries `some true`, the rest `some false`. The empty
fields mirror `GloasForkChoicePins.pinStore`. -/
private def timelinessStore (trues : Nat) : @Store minimal treeMap :=
  letI : Preset := minimal
  let root : Root := Vector.replicate 32 9
  let votes : Array (Option Bool) :=
    (Array.range 16).map fun i => if i < trues then some true else some false
  { timeMs := 0, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.insert FcMap.empty root default
    payloadTimelinessVote := FcMap.insert FcMap.empty root votes
    payloadDataAvailabilityVote := FcMap.empty }

/-- `payload_timeliness(store, root, true)` for `trues` timely votes: the strict `>`
against the threshold `8`. -/
private def payloadTimelinessAt (trues : Nat) : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let store := timelinessStore trues
  match (payloadTimeliness (map := treeMap) store (Vector.replicate 32 9) true :
    PinM Bool).run store with
  | .ok b _ => some b
  | .error _ _ => none

example : payloadTimelinessAt 7 = some false := by native_decide
example : payloadTimelinessAt 8 = some false := by native_decide
example : payloadTimelinessAt 9 = some true := by native_decide

end Gloas

/-! ### Heze: the inherited helpers -/

section Heze
open EthCLSpecs.Heze

/-- The Fulu audit state, over Heze's own `BeaconState`. -/
private def hezeAuditState : @State minimal :=
  letI : Preset := minimal
  let v : Validator :=
    { (default : Validator) with
      activationEpoch := 0
      effectiveBalance := 32000000000
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch }
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
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (computeProposerScore hezeAuditState)

/-- Heze `get_inactivity_penalty_deltas` under configuration `c`. -/
private def hezeInactivityPenalty (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
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

/-- Heze re-runs Gloas's churn helpers through the inherit: `get_exit_churn_limit` and
`get_consolidation_churn_limit` over Heze's own state and configuration give the same
answers as the Gloas pins. -/
private def hezeExitChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getExitChurnLimit hezeAuditState)

/-- Heze `get_consolidation_churn_limit` under configuration `c`. -/
private def hezeConsolidationChurnLimit (c : Config) : Outcome :=
  letI : Preset := minimal
  letI : Config := c
  letI : CryptoBackend := CryptoBackend.ffi
  gweiOutcome (getConsolidationChurnLimit hezeAuditState)

example : hezeExitChurnLimit minimalConfig = .answer 64000000000 := by native_decide
example : hezeExitChurnLimit { minimalConfig with churnLimitQuotientGloas := 0 }
    = .zeroDivision := by native_decide
example : hezeConsolidationChurnLimit minimalConfig = .answer 1000000000 := by native_decide
example : hezeConsolidationChurnLimit
    { minimalConfig with consolidationChurnLimitQuotient := 0 }
    = .zeroDivision := by native_decide

/-! ### Heze: the inclusion-list rows

The table's last three rows. `MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST` is
`Uint64(8192)` in the pinned module at both presets, so its `Config` field and mirror are
`CLUint64`; `on_inclusion_list` compares the plain byte sum against it as Python's mixed
`int <= Uint64`, which never raises and orders the values, so the consumer reads the plain
projection. `MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS` is `Slot(1)` (the checked kind), and
`on_inclusion_list`'s retention window is the checked `Slot` add. `INCLUSION_LIST_DUE_BPS`
feeds the checked `bpsDeadlineMs` route, pinned in `Tests/HezeForkChoicePins.lean`. The value
pins read all three at both presets; the handler pins below set one configuration value
each and run `on_inclusion_list` end-to-end, expected values from the pinned module (a
one-byte list filed at the shipped cap, rejected at cap `0`, the window edge at current
slot 2). Each pin module keeps its harness private, so the
`on_inclusion_list` fixture repeats `Tests/HezeForkChoicePins`'s shape at the arbitrary
configurations this file exists to drive. -/

/-- The three Heze config rows at the `minimal` preset: the byte cap, the retention-window
width, and the inclusion-list due bps, all plain. -/
private def hezeRowsMinimal : Nat × Nat × Nat :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  (Const.maxTransactionsBytesPerInclusionList.toPlainNat,
    Const.minSlotsForInclusionListsRequests.toPlainNat, Const.inclusionListDueBps.toPlainNat)

/-- The same at the `mainnet` preset. -/
private def hezeRowsMainnet : Nat × Nat × Nat :=
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  (Const.maxTransactionsBytesPerInclusionList.toPlainNat,
    Const.minSlotsForInclusionListsRequests.toPlainNat, Const.inclusionListDueBps.toPlainNat)

example : hezeRowsMinimal = (8192, 1, 6667) := by native_decide
example : hezeRowsMainnet = (8192, 1, 6667) := by native_decide

/-- What the pin's `on_inclusion_list` run did: filed the list with its timeliness, one of
the handler's own asserts fired, or another reject. -/
private inductive HezeIlOutcome where
  /-- The list filed under `(slot, dependent_root)` with this timeliness bit. -/
  | filed (timely : Bool)
  /-- The handler's assert fired (the window or the byte cap). -/
  | assertReject
  /-- Any other reject. Never expected. -/
  | otherReject
  deriving DecidableEq

/-- `on_inclusion_list` over a one-byte list from the committee's first member for slot `0`,
its dependent root the anchor's, under configuration `c`, the store clock `intoSlotMs` ms into
slot 0 (genesis time `0`). `SLOTS_PER_EPOCH` active validators make slot 0's committee
non-empty; the anchor block's `stateRoot` fixes `get_forkchoice_store`'s opening assert; the
verify-off backend accepts the empty signature. `getForkchoiceStore` hashes (FFI `Sha256`),
so the pins are `native_decide` `example`s. -/
private def hezeOnIl (c : Config) (intoSlotMs : CLUint64) : HezeIlOutcome :=
  open EthCLLib.PySpecTests in
  letI : Preset := minimal
  letI : Config := c
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  let base := (default : @EthCLSpecs.Heze.BeaconState minimal)
  let activeValidator : Validator := { (default : Validator) with exitEpoch := Const.farFutureEpoch }
  let vals := (Array.replicate Const.slotsPerEpoch activeValidator).foldl (·.push ·) base.validators
  let populated := { base with validators := vals }
  let state : State := populated
  let anchorBlock : @EthCLSpecs.Heze.BeaconBlock minimal :=
    { (default : @EthCLSpecs.Heze.BeaconBlock minimal) with stateRoot := htr populated }
  let anchorRoot := htr anchorBlock
  match (getForkchoiceStore (map := treeMap) state anchorBlock,
      getInclusionListCommittee (StoreTransition := Except StoreTransitionError) state 0) with
  | (.ok store0, .ok committee) =>
    let validatorIndex := vget committee 0
    let signed : SignedInclusionList :=
      { message :=
          { slot := 0, validatorIndex := validatorIndex, dependentRoot := anchorRoot,
            transactions := ⟨#[⟨#[0xAB]⟩]⟩ }
        signature := default }
    match (store0.genesisTimeMs + intoSlotMs : Checked CLUint64) with
    | .error _ => .otherReject
    | .ok timeMs =>
      let store := { store0 with timeMs := timeMs }
      match runOn store
          (onInclusionList (map := treeMap) signed : EStateM StoreTransitionError (Store treeMap) Unit) with
      | .ok after =>
        let entries := (FcMap.lookup after.inclusionListStore.inclusionLists (0, anchorRoot)).getD
          FcMap.empty
        match (FcMap.lookup entries validatorIndex).map (·.timely) with
        | some b => .filed b
        | none   => .otherReject
      -- `runOn` returns `Except (ε × σ) σ`: the reject and the error-time store.
      | .error (.assert _, _) => .assertReject
      | .error _              => .otherReject
  | _ => .otherReject

-- The byte cap at arbitrary configurations: cap `0` rejects the one-byte list (the mixed
-- comparison `1 <= 0` fails at the cap assert), cap `1` admits it, filed timely (0 ms into
-- its own slot is before the 4000 ms deadline). The checked field drives the assert.
example : hezeOnIl { minimalConfig with maxTransactionsBytesPerInclusionList := 0 } 0
    = .assertReject := by native_decide
example : hezeOnIl { minimalConfig with maxTransactionsBytesPerInclusionList := 1 } 0
    = .filed true := by native_decide

-- The retention window at arbitrary configurations: at current slot 2 (12000 ms) the shipped
-- width `1` no longer admits the slot-0 list (`0 + 1 < 2`, the window assert), while width `2`
-- admits it at the inclusive edge (`0 + 2 >= 2`), filed untimely (not its own slot).
example : hezeOnIl minimalConfig 12000 = .assertReject := by native_decide
example : hezeOnIl { minimalConfig with minSlotsForInclusionListsRequests := 2 } 12000
    = .filed false := by native_decide

end Heze

end EthCLSpecs.Tests.ConstantAuditPins
