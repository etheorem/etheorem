import EthCLSpecs.Fulu.EpochProcessing
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Tests.FuluEpochPins`: where the epoch helpers and substeps raise

Each pin states what the pinned pyspec (`v1.7.0-alpha.11`, minimal preset) does on the same
input. The probe script that produced the pyspec side is `.tmp/batchfaith/probe_b3.py` (local,
not committed). The pyspec kinds map as the runner maps them: `IndexError` is `.outOfBounds`,
`ValueError` is `.arithmetic`, and `AssertionError` is `.assert`.

Every fixture starts from the `default` state. `fixture` adds active validators with the
given effective balances, and the participation, score and balance lists the pin names.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluEpochPins

open EthCLSpecs.Fulu
open EthCLLib.Proofs (runPure pureState)
open EthCLSpecs.Proofs.Fulu (FuluRun)

section
-- The pins share one preset, config, hasher and crypto backend. The instances stay local to
-- this section.
local instance : Preset := minimal
local instance : Config := minimalConfig
local instance : HasherTag := fastHasherTag
local instance : CryptoBackend := CryptoBackend.realBackend

/-- The result raised the uncaught-fault kind (`.arithmetic`). -/
private def isArith {α : Type} : Except StateTransitionError α → Bool
  | .error (.arithmetic _) => true
  | _ => false

/-- The result raised the index-read kind (`.outOfBounds`). -/
private def isOob {α : Type} : Except StateTransitionError α → Bool
  | .error (.outOfBounds _ _) => true
  | _ => false

/-- The result raised the expected-rejection kind (`.assert`). -/
private def isAssert {α : Type} : Except StateTransitionError α → Bool
  | .error (.assert _) => true
  | _ => false

private def u64Max : UInt64 := 18446744073709551615
private def eth32 : Gwei := 32000000000

/-- An active validator (activation epoch 0, exit and withdrawable epochs far in the future)
with effective balance `eff` and pubkey byte `k`. -/
private def activeValidator (eff : Gwei) (k : UInt8) : Validator :=
  { (default : Validator) with
    pubkey := Vector.replicate 48 k, effectiveBalance := eff
    exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }

/-- The SSZ list of `a`. Every fixture array is far below the list limit, so the empty-list
branch never runs. The branch exists because `fixture` takes its arrays as variables. -/
private def listOf {α : Type} {cap : Nat} (a : Array α) : SSZList α cap :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], Nat.zero_le _⟩

/-- A state at `slot` with one active validator per entry of `effs`, and the given
participation flags (both epochs), inactivity scores and balances. -/
private def fixture (effs : Array Gwei) (slot : Slot := 0) (part : Array UInt8)
    (scores : Array UInt64) (balances : Array Gwei) : BeaconState :=
  { (default : BeaconState) with
    slot
    validators := listOf (effs.mapIdx fun i e => activeValidator e (UInt8.ofNat (0x11 + i)))
    balances := listOf balances
    previousEpochParticipation := listOf part
    currentEpochParticipation := listOf part
    inactivityScores := listOf scores }

/-- The result succeeded with exactly `v`. -/
private def okIs {α : Type} [BEq α] (r : Except StateTransitionError α) (v : α) : Bool :=
  match r with
  | .ok a => a == v
  | .error _ => false

/-- One validator of 32 ETH at `slot`, no participation, score 0, balance 32 ETH. -/
private def plain (slot : Slot := 0) : BeaconState :=
  fixture #[eth32] slot #[0] #[0] #[eth32]

/-! ## P7: `get_total_balance` -/

-- Two effective balances of `2 ^ 63`: the sum raises `ValueError`.
example : isArith (getTotalBalance (pureState (fixture #[9223372036854775808, 9223372036854775808]
    0 #[0, 0] #[0, 0] #[eth32, eth32])) #[0, 1]) = true := by native_decide

-- An index past the registry raises `IndexError`.
example : isOob (getTotalBalance (pureState (plain)) #[5]) = true := by native_decide

-- Two 32 ETH validators total 64 ETH.
example : okIs (getTotalBalance (pureState (fixture #[eth32, eth32] 0 #[0, 0] #[0, 0]
    #[eth32, eth32])) #[0, 1]) 64000000000 = true := by native_decide

/-! ## P8: `get_unslashed_participating_indices`

At slot 16 the previous epoch is 1 and the current epoch is 2. -/

private def p8State : BeaconState := fixture #[eth32] 16 #[7] #[0] #[eth32]

-- Epochs outside `(previous, current)` raise `AssertionError`.
example : isAssert (getUnslashedParticipatingIndices (pureState p8State) 0 3) = true := by
  native_decide
example : isAssert (getUnslashedParticipatingIndices (pureState p8State) 0 0) = true := by
  native_decide

-- The participating validator, at the previous epoch.
example : okIs (getUnslashedParticipatingIndices (pureState p8State) 0 1) #[0] = true := by
  native_decide

-- An empty participation list raises `IndexError`.
example : isOob (getUnslashedParticipatingIndices
    (pureState (fixture #[eth32] 16 #[] #[0] #[eth32])) 0 1) = true := by native_decide

/-! ## P9: `weigh_justification_and_finalization` -/

-- `previous_epoch_target_balance * 3` raises `ValueError`.
example : isArith (runPure (weighJustificationAndFinalization (StateTransition := FuluRun)
    1000000000 9223372036854775808 0) plain) = true := by native_decide

-- `total_active_balance * 2` raises `ValueError`.
example : isArith (runPure (weighJustificationAndFinalization (StateTransition := FuluRun)
    9223372036854775808 0 0) plain) = true := by native_decide

-- Bits 1 to 3 hold after the shift, so the first rule forms
-- `old_previous_justified_checkpoint.epoch + 3`, which raises `ValueError`.
private def p9Bits : Bitvector Const.justificationBitsLength :=
  bitSet (bitSet (bitSet default 0 true) 1 true) 2 true
example : isArith (runPure (weighJustificationAndFinalization (StateTransition := FuluRun)
    1000000000 0 0)
    { plain with justificationBits := p9Bits
                 previousJustifiedCheckpoint := { epoch := u64Max - 1, root := default } })
    = true := by native_decide

/-! ## P4: `process_registry_updates` -/

-- A validator eligible for both the queue and activation (finalized epoch far in the future)
-- takes only the first branch: eligibility set to `current + 1`, activation unchanged.
private def p4State : BeaconState :=
  let st := plain
  { st with
    validators := sszOfArray #[{ activeValidator eth32 0x11 with
      activationEligibilityEpoch := Const.farFutureEpoch, activationEpoch := Const.farFutureEpoch }]
    finalizedCheckpoint := { epoch := Const.farFutureEpoch, root := default } }
example : (match runPure (processRegistryUpdates (StateTransition := FuluRun)) p4State with
    | .ok (_, s) => s.validators.toArray.map (fun v => (v.activationEligibilityEpoch, v.activationEpoch))
        == #[(1, Const.farFutureEpoch)]
    | .error _ => false) = true := by native_decide

/-! ## P10: `process_effective_balance_updates` -/

-- An empty balance list raises `IndexError`.
example : isOob (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
    (fixture #[eth32] 0 #[0] #[0] #[])) = true := by native_decide

-- `balance + DOWNWARD_THRESHOLD` raises `ValueError`.
example : isArith (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
    (fixture #[eth32] 0 #[0] #[0] #[u64Max])) = true := by native_decide

-- The first test fails exactly, so the pyspec forms `effective_balance + UPWARD_THRESHOLD`,
-- which raises `ValueError`.
example : isArith (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
    (fixture #[u64Max] 0 #[0] #[0] #[u64Max - 250000000])) = true := by native_decide

/-! ## Q1: `get_finality_delay` -/

-- A finalized epoch past the previous epoch raises `ValueError`.
example : isArith (getFinalityDelay (pureState
    { plain with finalizedCheckpoint := { epoch := 1, root := default } })) = true := by
  native_decide

/-! ## Q2: `process_inactivity_updates` (slot 8, so the previous epoch is 0) -/

-- An empty score list raises `IndexError`.
example : isOob (runPure (processInactivityUpdates (StateTransition := FuluRun))
    (fixture #[eth32] 8 #[0] #[] #[eth32])) = true := by native_decide

-- `score + INACTIVITY_SCORE_BIAS` raises `ValueError`.
example : isArith (runPure (processInactivityUpdates (StateTransition := FuluRun))
    (fixture #[eth32] 8 #[0] #[u64Max] #[eth32])) = true := by native_decide

/-! ## Q3: `get_flag_index_deltas` -/

-- One participating validator of effective balance `2 ^ 63`: the reward numerator raises
-- `ValueError`.
example : isArith (getFlagIndexDeltas (pureState
    (fixture #[9223372036854775808] 8 #[7] #[0] #[eth32])) 0) = true := by native_decide

/-! ## Q4: `get_inactivity_penalty_deltas` -/

-- An empty score list raises `IndexError`.
example : isOob (getInactivityPenaltyDeltas (pureState
    (fixture #[eth32] 8 #[0] #[] #[eth32]))) = true := by native_decide

-- `effective_balance * inactivity_score` raises `ValueError`.
example : isArith (getInactivityPenaltyDeltas (pureState
    (fixture #[9223372036854775808] 8 #[0] #[4] #[eth32]))) = true := by native_decide

/-! ## Q5: `process_slashings` -/

private def twoPow63 : Gwei := 9223372036854775808
private def oneSlashing : BeaconState :=
  { plain with slashings := plain.slashings.set! 0 twoPow63 }
private def twoSlashings : BeaconState :=
  { plain with slashings := oneSlashing.slashings.set! 1 twoPow63 }

-- Two slashings of `2 ^ 63`: the sum raises `ValueError`.
example : isArith (runPure (processSlashings (StateTransition := FuluRun)) twoSlashings)
    = true := by native_decide

-- One slashing of `2 ^ 63`: the multiplier product raises `ValueError`.
example : isArith (runPure (processSlashings (StateTransition := FuluRun)) oneSlashing)
    = true := by native_decide

/-! ## Q6: `process_pending_deposits` -/

-- `deposit_balance_to_consume + churn` raises `ValueError`.
example : isArith (runPure (processPendingDeposits (StateTransition := FuluRun))
    { plain with depositBalanceToConsume := u64Max }) = true := by native_decide

-- The churn limit of this state is 64 ETH (the pyspec probe prints it), so
-- `available_for_processing` is `2 ^ 64 - 1`. Two deposits of `2 ^ 63` for the known
-- validator: the first fits, and `processed_amount + deposit.amount` for the second raises
-- `ValueError`.
private def q6Deposit : PendingDeposit :=
  { (default : PendingDeposit) with
    pubkey := Vector.replicate 48 0x11
    amount := 9223372036854775808 }
example : isArith (runPure (processPendingDeposits (StateTransition := FuluRun))
    { plain with depositBalanceToConsume := u64Max - 64000000000
                 pendingDeposits := sszOfArray #[q6Deposit, q6Deposit] }) = true := by
  native_decide

end

/-! ## Item 5: the `uint64` products under patched constants

The rows of `specs/2026-10-24-batchfaith-probes.md` (local, not committed). Each probe sets a
module constant of the pinned pyspec so that one product overflows, and the pin sets the same
`Preset` or `Config` field. The `Preset` holds `EFFECTIVE_BALANCE_INCREMENT` twice, so a patch
of it sets both fields. This section binds the preset in each pin, so the fixture below takes
it as an argument. -/

section
local instance : Config := minimalConfig
local instance : HasherTag := fastHasherTag
local instance : CryptoBackend := CryptoBackend.realBackend

/-- The result raised `.arithmetic` with the description `d`, which names the product. -/
private def arithAt {α : Type} (d : String) : Except StateTransitionError α → Bool
  | .error (.arithmetic e) => e == d
  | _ => false

/-- `fixture` of the section above, under the preset `P`. `Validator` depends on the preset,
so the validators are built here rather than through `activeValidator`. -/
private def fixtureAt (P : Preset) (effs : Array Gwei) (slot : Slot) (part : Array UInt8)
    (scores : Array UInt64) (balances : Array Gwei) : @BeaconState P :=
  letI : Preset := P
  let validator (e : Gwei) (k : UInt8) : Validator :=
    { (default : Validator) with
      pubkey := Vector.replicate 48 k, effectiveBalance := e
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : BeaconState) with
    slot
    validators := listOf (effs.mapIdx fun i e => validator e (UInt8.ofNat (0x11 + i)))
    balances := listOf balances
    previousEpochParticipation := listOf part
    currentEpochParticipation := listOf part
    inactivityScores := listOf scores }

/-- `EFFECTIVE_BALANCE_INCREMENT = 1`. -/
@[reducible] private def ebi1 : Preset :=
  { minimal with effectiveBalanceIncrement := 1, effectiveBalanceIncrementG := 1 }
/-- `EFFECTIVE_BALANCE_INCREMENT = 1`, `BASE_REWARD_FACTOR = 2 ^ 40`. -/
@[reducible] private def ebi1Brf40 : Preset := { ebi1 with baseRewardFactor := 2 ^ 40 }
/-- `BASE_REWARD_FACTOR = 2 ^ 40`. -/
@[reducible] private def brf40 : Preset := { minimal with baseRewardFactor := 2 ^ 40 }
/-- `HYSTERESIS_DOWNWARD_MULTIPLIER = 2 ^ 40`. -/
@[reducible] private def down40 : Preset := { minimal with hysteresisDownwardMultiplier := 2 ^ 40 }
/-- `HYSTERESIS_UPWARD_MULTIPLIER = 2 ^ 40`. -/
@[reducible] private def up40 : Preset := { minimal with hysteresisUpwardMultiplier := 2 ^ 40 }
/-- Both hysteresis multipliers at `2 ^ 40`. -/
@[reducible] private def both40 : Preset := { down40 with hysteresisUpwardMultiplier := 2 ^ 40 }

private def pow58 : Gwei := 288230376151711744
private def pow50 : Gwei := 1125899906842624
private def pow63 : Gwei := 9223372036854775808

/-! ### a. `get_flag_index_deltas`: `active_increments * WEIGHT_DENOMINATOR` -/

-- Overflow: one participant of `2 ^ 58` at slot 8. The base reward is 0, so the numerator
-- cannot fault first, and the divisor `2 ^ 58 * 64` raises.
example : (letI : Preset := ebi1
    arithAt "get_flag_index_deltas: active_increments * WEIGHT_DENOMINATOR"
      (getFlagIndexDeltas (pureState (fixtureAt ebi1 #[pow58] 8 #[7] #[0] #[eth32])) 0))
    = true := by native_decide

-- Never reached: the validator does not participate.
example : (letI : Preset := ebi1
    okIs (getFlagIndexDeltas (pureState (fixtureAt ebi1 #[pow58] 8 #[0] #[0] #[eth32])) 0)
      (#[0], #[0])) = true := by native_decide

-- Never reached: at slot 80 the chain is in the leak, so the participant gets no reward.
example : (letI : Preset := ebi1
    okIs (getFlagIndexDeltas (pureState (fixtureAt ebi1 #[pow58] 80 #[7] #[0] #[eth32])) 0)
      (#[0], #[0])) = true := by native_decide

-- Order: with `BASE_REWARD_FACTOR = 2 ^ 40`, `get_base_reward` raises first.
example : (letI : Preset := ebi1Brf40
    arithAt "get_base_reward: increments * get_base_reward_per_increment"
      (getFlagIndexDeltas (pureState (fixtureAt ebi1Brf40 #[pow58] 8 #[7] #[0] #[eth32])) 0))
    = true := by native_decide

/-! ### b. `get_base_reward`: `increments * get_base_reward_per_increment` -/

-- Overflow: `2 ^ 50` increments times `2 ^ 15` per increment.
example : (letI : Preset := ebi1Brf40
    arithAt "get_base_reward: increments * get_base_reward_per_increment"
      (getBaseReward (pureState (fixtureAt ebi1Brf40 #[pow50] 0 #[0] #[0] #[eth32])) 0))
    = true := by native_decide

-- Order: index 5 is past the registry, so `state.validators[index]` raises first.
example : (letI : Preset := ebi1Brf40
    isOob (getBaseReward (pureState (fixtureAt ebi1Brf40 #[pow50] 0 #[0] #[0] #[eth32])) 5))
    = true := by native_decide

-- The minimal preset: pyspec returns 11448672.
example : (letI : Preset := minimal
    okIs (getBaseReward (pureState (fixtureAt minimal #[eth32] 0 #[0] #[0] #[eth32])) 0)
      11448672) = true := by native_decide

/-! ### c. `get_base_reward_per_increment`: the product before the total -/

private def perIncrementDescr : String :=
  "get_base_reward_per_increment: EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR"

-- Overflow: `10 ^ 9 * 2 ^ 40`.
example : (letI : Preset := brf40
    arithAt perIncrementDescr
      (getBaseRewardPerIncrement (pureState (fixtureAt brf40 #[eth32] 0 #[0] #[0] #[eth32]))))
    = true := by native_decide

-- Order: the total of two `2 ^ 63` balances also overflows, and the product raises first.
example : (letI : Preset := brf40
    arithAt perIncrementDescr
      (getBaseRewardPerIncrement (pureState
        (fixtureAt brf40 #[pow63, pow63] 0 #[0, 0] #[0, 0] #[eth32, eth32]))))
    = true := by native_decide

-- The total fault alone, at the minimal preset: the `get_total_balance` sum raises.
example : (letI : Preset := minimal
    arithAt "get_total_balance: sum of effective balances"
      (getBaseRewardPerIncrement (pureState
        (fixtureAt minimal #[pow63, pow63] 0 #[0, 0] #[0, 0] #[eth32, eth32]))))
    = true := by native_decide

/-! ### d. `get_inactivity_penalty_deltas`: the denominator, inside the loop -/

private def denominatorDescr : String :=
  "get_inactivity_penalty_deltas: INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX"

/-- `INACTIVITY_SCORE_BIAS = 2 ^ 40`. -/
@[reducible] private def bias40 : Config := { minimalConfig with inactivityScoreBias := 2 ^ 40 }

-- Overflow: one non-participant at slot 8, score 1. `2 ^ 40 * 2 ^ 24` raises.
example : (letI : Preset := minimal; letI : Config := bias40
    arithAt denominatorDescr
      (getInactivityPenaltyDeltas (pureState (fixtureAt minimal #[eth32] 8 #[0] #[1] #[eth32]))))
    = true := by native_decide

-- Never reached: the validator participates.
example : (letI : Preset := minimal; letI : Config := bias40
    okIs (getInactivityPenaltyDeltas (pureState (fixtureAt minimal #[eth32] 8 #[7] #[1] #[eth32])))
      #[0]) = true := by native_decide

-- Never reached: the registry is empty.
example : (letI : Preset := minimal; letI : Config := bias40
    okIs (getInactivityPenaltyDeltas (pureState (fixtureAt minimal #[] 8 #[] #[] #[]))) #[])
    = true := by native_decide

-- Order: `effective_balance * inactivity_score` (`2 ^ 63 * 4`) raises first.
example : (letI : Preset := minimal; letI : Config := bias40
    arithAt "get_inactivity_penalty_deltas: effective_balance * inactivity_scores[index]"
      (getInactivityPenaltyDeltas (pureState (fixtureAt minimal #[pow63] 8 #[0] #[4] #[eth32]))))
    = true := by native_decide

/-! ### e. `process_effective_balance_updates`: the hysteresis thresholds -/

private def downDescr : String :=
  "process_effective_balance_updates: HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER"

-- Overflow, downward: `2.5 * 10 ^ 8 * 2 ^ 40`.
example : (letI : Preset := down40
    arithAt downDescr (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
      (fixtureAt down40 #[eth32] 0 #[0] #[0] #[eth32]))) = true := by native_decide

-- Overflow, upward.
example : (letI : Preset := up40
    arithAt "process_effective_balance_updates: HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER"
      (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
        (fixtureAt up40 #[eth32] 0 #[0] #[0] #[eth32]))) = true := by native_decide

-- Order: an empty balance list raises `IndexError` first.
example : (letI : Preset := down40
    isOob (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
      (fixtureAt down40 #[eth32] 0 #[0] #[0] #[]))) = true := by native_decide

-- Order: with both multipliers patched, the downward product raises first.
example : (letI : Preset := both40
    arithAt downDescr (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
      (fixtureAt both40 #[eth32] 0 #[0] #[0] #[eth32]))) = true := by native_decide

-- Never reached: the registry is empty.
example : (letI : Preset := down40
    (runPure (processEffectiveBalanceUpdates (StateTransition := FuluRun))
      (fixtureAt down40 #[] 0 #[] #[] #[])).isOk) = true := by native_decide

end

end EthCLSpecs.Tests.FuluEpochPins
