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

end EthCLSpecs.Tests.FuluEpochPins
