import EthCLSpecs.Fulu
import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Tests.ValidatorIndexMigrationPins`: the `ValidatorIndex` behavior pins

Behavior pins for the checked `ValidatorIndex` kind. Each pin pairs
a targeted failure case with a nearby success that reaches the same operation, and the
successes read back exact values. Every failure pin fails under the pre-migration body, which
the pin's own comment names.

1. `update_next_withdrawal_validator_index` (Fulu and Gloas): the cursor advance
   `(next_withdrawal_validator_index + MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP) % len(validators)`
   raises `ZeroDivisionError` on an empty registry, and the checked add raises first at
   a cursor of `UINT64_MAX`. The old body wrapped through a zero-default modulo helper and
   stored `0`. The
   success advances a cursor of `1` over three validators to `(1 + 16) % 3 = 2`.
2. `get_total_balance`: `state.validators[index]` raises `IndexError` past the registry's
   end. The old body read the `[i]!` default and returned the one-increment floor.
3. `process_effective_balance_updates`: `state.balances[index]` raises `IndexError` when
   `balances` is shorter than the registry. The old body read the `[i]!` default `0`.
4. `process_inactivity_updates`: `state.inactivity_scores[index]` raises `IndexError` when
   the scores list is shorter than the registry. The old body read the default `0`.
5. `process_voluntary_exit` and `process_proposer_slashing`: the registry read raises
   `IndexError`, so the reject is `outOfBounds`. The old body guarded the read with an
   `assert` and rejected with the `assert` class. The nearby success passes the read and
   rejects at the next assert, which the pin names.

The pins hash through the FFI `Sha256` (`fastHasherTag`), so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.ValidatorIndexMigrationPins

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

/-- A Fulu state over the given registry, balances, and withdrawal cursor. -/
private def fuluState (vs : Array (@Validator minimal)) (bals : Array Gwei)
    (cursor : ValidatorIndex) (hv : vs.size ≤ 4 := by decide) (hb : bals.size ≤ 4 := by decide) :
    @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { (default : @BeaconState minimal) with
    validators := ⟨vs, Nat.le_trans hv (by decide)⟩
    balances := ⟨bals, Nat.le_trans hb (by decide)⟩
    nextWithdrawalValidatorIndex := cursor }

/-! ### 1. The withdrawal validator cursor (Fulu) -/

/-- An empty registry: the cursor modulo raises `ZeroDivisionError`. The old zero-default
modulo helper stored `0` and the run succeeded. -/
private def pinFuluCursorEmptyRegistryRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processWithdrawals (default : ExecutionPayload) :
      EStateM StateTransitionError State Unit).run (fuluState #[] #[] 0) with
  | .error (.zeroDivision _) _ => true
  | _ => false
example : pinFuluCursorEmptyRegistryRaises = true := by native_decide

/-- A cursor at `UINT64_MAX` over an empty registry: the checked add raises before the
modulo. The old `Nat` add never raised, and the old zero-default modulo helper stored `0`. -/
private def pinFuluCursorMaxAddRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processWithdrawals (default : ExecutionPayload) :
      EStateM StateTransitionError State Unit).run
      (fuluState #[] #[] 18446744073709551615) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinFuluCursorMaxAddRaises = true := by native_decide

/-- Three validators without execution credentials, cursor `1`: the sweep reads all three
and withdraws nothing, and the short payload advances the cursor to `(1 + 16) % 3 = 2`. -/
private def pinFuluCursorAdvanceReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processWithdrawals (default : ExecutionPayload) :
      EStateM StateTransitionError State Unit).run
      (fuluState #[default, default, default] #[0, 0, 0] 1) with
  | .ok _ post => (sszGet post nextWithdrawalValidatorIndex).toPlainNat = 2
  | _ => false
example : pinFuluCursorAdvanceReads = true := by native_decide

/-! ### 2. `get_total_balance` -/

/-- Index `5` on a one-validator registry: the read raises `IndexError`. The old `[i]!`
read returned the default validator, and the total floored at one increment. -/
private def pinTotalBalanceOutOfRangeRaises : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match getTotalBalance (fuluState #[activeValidator] #[32000000000] 0) #[5] with
  | .error (.outOfBounds 5 1) => true
  | _ => false
example : pinTotalBalanceOutOfRangeRaises = true := by native_decide

private def pinTotalBalanceInRangeReads : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match getTotalBalance (fuluState #[activeValidator] #[32000000000] 0) #[0] with
  | .ok total => total.toPlainNat = 32000000000
  | _ => false
example : pinTotalBalanceInRangeReads = true := by native_decide

/-! ### 3. `process_effective_balance_updates` -/

/-- A one-validator registry with an empty `balances` list: the balance read raises
`IndexError`. The old `[i]!` read the default `0` and lowered the effective balance. -/
private def pinEffectiveBalanceShortBalancesRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processEffectiveBalanceUpdates : EStateM StateTransitionError State Unit).run
      (fuluState #[activeValidator] #[] 0) with
  | .error (.outOfBounds 0 0) _ => true
  | _ => false
example : pinEffectiveBalanceShortBalancesRaises = true := by native_decide

/-- A balance of `31 ETH` against a `32 ETH` effective balance: past the downward
hysteresis threshold, so the effective balance drops to `31 ETH`. -/
private def pinEffectiveBalanceInRangeReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processEffectiveBalanceUpdates : EStateM StateTransitionError State Unit).run
      (fuluState #[activeValidator] #[31000000000] 0) with
  | .ok _ post => (sszGet post validators)[0]!.effectiveBalance.toPlainNat = 31000000000
  | _ => false
example : pinEffectiveBalanceInRangeReads = true := by native_decide

/-! ### 4. `process_inactivity_updates` -/

/-- A state at epoch `2` (slot `16`) with one active validator and zero participation flags,
so the validator is eligible and not a timely-target voter. `withScore` picks an inactivity
scores list of `[100]` or an empty one. -/
private def inactivityState (withScore : Bool) : @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let base : @BeaconState minimal :=
    { (default : @BeaconState minimal) with
      slot := 16
      validators := ⟨#[activeValidator], by decide⟩
      balances := ⟨#[32000000000], by decide⟩
      previousEpochParticipation := ⟨#[0], by decide⟩
      currentEpochParticipation := ⟨#[0], by decide⟩ }
  (if withScore then { base with inactivityScores := ⟨#[100], by decide⟩ } else base)

/-- An empty scores list: the score read raises `IndexError`. The old `[i]!` read the
default `0` and the write past the end was a no-op, so the run succeeded. -/
private def pinInactivityShortScoresRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processInactivityUpdates : EStateM StateTransitionError State Unit).run
      (inactivityState false) with
  | .error (.outOfBounds 0 0) _ => true
  | _ => false
example : pinInactivityShortScoresRaises = true := by native_decide

/-- A score of `100`: the non-voter gains `INACTIVITY_SCORE_BIAS = 4`, and outside a leak
(finality delay `1`) it loses `INACTIVITY_SCORE_RECOVERY_RATE = 16`, so it reads `88`. -/
private def pinInactivityInRangeReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processInactivityUpdates : EStateM StateTransitionError State Unit).run
      (inactivityState true) with
  | .ok _ post => (sszGet post inactivityScores)[0]!.toPlainNat = 88
  | _ => false
example : pinInactivityInRangeReads = true := by native_decide

/-! ### 5. The registry reads of `process_voluntary_exit` and `process_proposer_slashing` -/

/-- A voluntary exit for validator `index` at epoch `0`. -/
private def exitFor (index : ValidatorIndex) : @SignedVoluntaryExit minimal :=
  letI : Preset := minimal
  { message := { epoch := 0, validatorIndex := index }, signature := default }

/-- Index `5` on a one-validator registry: the read raises `IndexError` (`outOfBounds`).
The old body rejected at its `assertH` range guard with the `assert` class. -/
private def pinVoluntaryExitOutOfRangeRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processVoluntaryExit (exitFor 5) : EStateM StateTransitionError State Unit).run
      (fuluState #[default] #[0] 0) with
  | .error (.outOfBounds 5 1) _ => true
  | _ => false
example : pinVoluntaryExitOutOfRangeRaises = true := by native_decide

/-- Index `0`: the read succeeds, and the default validator (exit epoch `0`) fails the next
check, `is_active_validator`, with the `assert` class. -/
private def pinVoluntaryExitInRangeReachesActiveCheck : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processVoluntaryExit (exitFor 0) : EStateM StateTransitionError State Unit).run
      (fuluState #[default] #[0] 0) with
  | .error (.assert _) _ => true
  | _ => false
example : pinVoluntaryExitInRangeReachesActiveCheck = true := by native_decide

/-- Two headers for proposer `index` at slot `0` that differ in their parent root. -/
private def slashingFor (index : ValidatorIndex) : @ProposerSlashing minimal :=
  letI : Preset := minimal
  let h1 : BeaconBlockHeader := { (default : BeaconBlockHeader) with proposerIndex := index }
  let h2 : BeaconBlockHeader :=
    { h1 with parentRoot := Vector.replicate 32 (1 : UInt8) }
  { signedHeader1 := { message := h1, signature := default },
    signedHeader2 := { message := h2, signature := default } }

/-- Proposer `5` on a one-validator registry: the read raises `IndexError`
(`outOfBounds`). The old body rejected at its `assertH` range guard with `assert`. -/
private def pinProposerSlashingOutOfRangeRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processProposerSlashing (slashingFor 5) : EStateM StateTransitionError State Unit).run
      (fuluState #[default] #[0] 0) with
  | .error (.outOfBounds 5 1) _ => true
  | _ => false
example : pinProposerSlashingOutOfRangeRaises = true := by native_decide

/-- Proposer `0`: the read succeeds, and the default validator fails the next check,
`is_slashable_validator`, with the `assert` class. -/
private def pinProposerSlashingInRangeReachesSlashableCheck : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processProposerSlashing (slashingFor 0) : EStateM StateTransitionError State Unit).run
      (fuluState #[default] #[0] 0) with
  | .error (.assert _) _ => true
  | _ => false
example : pinProposerSlashingInRangeReachesSlashableCheck = true := by native_decide

end Fulu

section Gloas
open EthCLSpecs.Gloas

/-- A Gloas state over `n` default validators (zero balances) and the given cursor. The
default bid and the default latest block hash agree, so `process_withdrawals` runs. -/
private def gloasState (n : Nat) (cursor : ValidatorIndex) : @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { (default : @BeaconState minimal) with
    validators := ⟨Array.replicate n default⟩
    balances := ⟨Array.replicate n 0⟩
    nextWithdrawalValidatorIndex := cursor }

/-! ### 1. The withdrawal validator cursor (Gloas) -/

/-- An empty registry: the cursor modulo raises `ZeroDivisionError`. The old zero-default
modulo helper stored `0` and the run succeeded. -/
private def pinGloasCursorEmptyRegistryRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processWithdrawals : EStateM StateTransitionError State Unit).run (gloasState 0 0) with
  | .error (.zeroDivision _) _ => true
  | _ => false
example : pinGloasCursorEmptyRegistryRaises = true := by native_decide

/-- Three validators without execution credentials, cursor `1`: the short payload advances
the cursor to `(1 + 16) % 3 = 2`. -/
private def pinGloasCursorAdvanceReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processWithdrawals : EStateM StateTransitionError State Unit).run (gloasState 3 1) with
  | .ok _ post => (sszGet post nextWithdrawalValidatorIndex).toPlainNat = 2
  | _ => false
example : pinGloasCursorAdvanceReads = true := by native_decide

end Gloas

end EthCLSpecs.Tests.ValidatorIndexMigrationPins
