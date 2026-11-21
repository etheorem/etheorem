import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Tests.EpochMigrationPins`: the `Epoch` wrap-site pins

Four behavior pins, one per migration site where the pre-migration body wrapped
a raw `UInt64` and the migrated body raises (the `Epoch` migration's
discriminating tests). Each pin pairs a targeted failure case with a nearby
success that reaches the same operation. The failure case is the input that
used to wrap and now raises the checked range fault. The pin
fails under the old wrapping form (`SPEC_ARITHMETIC.md` §3.1: the checked kind
raises where the raw kind wrapped).

1. `compute_start_slot_at_epoch`: `epoch * SLOTS_PER_EPOCH` past `2^64 - 1`
   (epoch `2^61` overflows at the minimal preset's `SLOTS_PER_EPOCH = 8`),
   beside epoch `1000`;
2. `compute_activation_exit_epoch`: `epoch + 1 + MAX_SEED_LOOKAHEAD` at
   `epoch = UINT64_MAX`, beside epoch `0`;
3. `initiate_validator_exit`: the withdrawability sum
   `exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` with the delay config set
   to `UINT64_MAX` (a config is free to pick any delay, and no run-time guard
   caps it), beside the default delay, whose success reads back the exact
   Python epochs (`exit_epoch = 105`, `withdrawable_epoch = 361`: the state's
   slot `800` is epoch `100` at the minimal preset, the exit epoch is
   `100 + 1 + MAX_SEED_LOOKAHEAD = 105`, and the churn limit covers the one
   `32 Gwei` exit);
4. `process_withdrawal_request` (full exit): the same validator exit reached
   through the request path with the huge delay config, beside the default
   delay with the same exact epochs.

Pins 1 and 2 run the `Checked` helper alone, so the raise surfaces as the
`ArithFault` range cause, `.error (.range _ 64 _ _)`. Pins 3 and 4 run the
transition, where the lift turns that fault into `.error (.arithmetic _)`. The
old wrapping form returned a wrapped `.ok`, so each failure pin discriminates.
`State` is FFI-backed, so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLSpecs.Gloas

namespace EthCLSpecs.Tests.EpochMigrationPins

/-! ### 1. `compute_start_slot_at_epoch` -/

/-- Epoch `2^61`: `2^61 * SLOTS_PER_EPOCH = 2^64` overflows the checked
product at the minimal preset (`SLOTS_PER_EPOCH = 8`). -/
private def startSlotOverflowEpoch : Gloas.Epoch :=
  CLUint64.ofNatLT 2305843009213693952 (by decide)

private def pinStartSlotOverflowRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match (computeStartSlotAtEpoch startSlotOverflowEpoch : Checked Gloas.Slot) with
  | .error (.range _ 64 _ _) => true
  | _ => false
example : pinStartSlotOverflowRaises = true := by native_decide

private def pinStartSlotInRangeReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match (computeStartSlotAtEpoch (1000 : Gloas.Epoch) : Checked Gloas.Slot) with
  | .ok s => s.toPlainNat = 8000
  | _ => false
example : pinStartSlotInRangeReads = true := by native_decide

/-! ### 2. `compute_activation_exit_epoch` -/

private def pinActivationExitMaxEpochRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match (computeActivationExitEpoch (18446744073709551615 : Gloas.Epoch) :
      Checked Gloas.Epoch) with
  | .error (.range _ 64 _ _) => true
  | _ => false
example : pinActivationExitMaxEpochRaises = true := by native_decide

private def pinActivationExitGenesisReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  match (computeActivationExitEpoch (0 : Gloas.Epoch) : Checked Gloas.Epoch) with
  | .ok e => e.toPlainNat = 5
  | _ => false
example : pinActivationExitGenesisReads = true := by native_decide

/-! ### 3. `initiate_validator_exit` -/

/-- The overflow-delay config: `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` is a
`[Config]` field with no run-time cap, so a config may pin it at `UINT64_MAX`,
where the checked `exit_epoch + delay` raises for every epoch. The
`@[instance_reducible]` mark answers the class-definition warning: the pins
elaborate instances through this config. -/
@[instance_reducible]
private def hugeDelayConfig : Gloas.Config :=
  { minimalConfig with minValidatorWithdrawabilityDelay := 18446744073709551615 }

/-- A one-validator state whose validator is active at `slot = 800`
(current epoch `100`), so `initiate_validator_exit`'s gates pass and the
withdrawability sum is reached. The config argument is the run's, so the two
pins below can run the same state under the two configs. -/
private def exitState (_cfg : Gloas.Config) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      activationEligibilityEpoch := 0
      activationEpoch := 36
      effectiveBalance := 32000000000
      pubkey := (Vector.replicate 48 (1 : UInt8))
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch
      withdrawalCredentials := (Vector.replicate 32 (1 : UInt8)) }
  SSZ.FastBox
    { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
      slot := 800
      validators := ⟨#[v]⟩, balances := ⟨#[32000000000]⟩ }

private def pinValidatorExitOverflowRaises : Bool :=
  letI : Preset := minimal
  letI : Config := hugeDelayConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (initiateValidatorExit 0 : EStateM StateTransitionError State Unit).run
      (exitState hugeDelayConfig) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinValidatorExitOverflowRaises = true := by native_decide

private def pinValidatorExitDefaultReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (initiateValidatorExit 0 : EStateM StateTransitionError State Unit).run
      (exitState minimalConfig) with
  | .ok _ post =>
    -- The exact Python epochs: slot `800` is epoch `100` at the minimal
    -- preset, the exit epoch is `100 + 1 + MAX_SEED_LOOKAHEAD = 105` (the
    -- churn limit covers the one `32 Gwei` exit), and the withdrawability
    -- epoch is `105 + 256`.
    let v := (SSZ.Box.view post).validators[0]!
    v.exitEpoch.toPlainNat = 105 && v.withdrawableEpoch.toPlainNat = 361
  | _ => false
example : pinValidatorExitDefaultReads = true := by native_decide

/-! ### 4. `process_withdrawal_request` (full exit) -/

/-- A full-exit request for the active validator: execution-credential prefix,
matching (all-ones) source address, and `amount = FULL_EXIT_REQUEST_AMOUNT` (= 0
in this fork body), so the request passes the gates and reaches
`initiate_validator_exit`. -/
private def pinWithdrawalRequestOverflowRaises : Bool :=
  letI : Preset := minimal
  letI : Config := hugeDelayConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let wr : WithdrawalRequest :=
    { sourceAddress := (Vector.replicate 20 (1 : UInt8))
      validatorPubkey := (Vector.replicate 48 (1 : UInt8))
      amount := 0 }
  match (processWithdrawalRequest wr :
      EStateM StateTransitionError State Unit).run (exitState hugeDelayConfig) with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinWithdrawalRequestOverflowRaises = true := by native_decide

private def pinWithdrawalRequestDefaultReads : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let wr : WithdrawalRequest :=
    { sourceAddress := (Vector.replicate 20 (1 : UInt8))
      validatorPubkey := (Vector.replicate 48 (1 : UInt8))
      amount := 0 }
  match (processWithdrawalRequest wr :
      EStateM StateTransitionError State Unit).run (exitState minimalConfig) with
  | .ok _ post =>
    -- The same exact epochs the direct validator-exit pin asserts: the request
    -- path reaches `initiate_validator_exit` and writes `105` and `361`.
    let v := (SSZ.Box.view post).validators[0]!
    v.exitEpoch.toPlainNat = 105 && v.withdrawableEpoch.toPlainNat = 361
  | _ => false
example : pinWithdrawalRequestDefaultReads = true := by native_decide

end EthCLSpecs.Tests.EpochMigrationPins
