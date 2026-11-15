import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Fulu.RegistryUpdates
import EthCLSpecs.Fulu.Time
import EthCLSpecs.Fulu.WeakSubjectivity

/-!
# `EthCLSpecs.Tests.FuluArithPins`: the Fulu checked-arithmetic pins

Four sites used to wrap and return a wrong value; with `Epoch` and `Slot` on `CLUint64`
they raise where the pyspec raises. Each raise pin locks one raise at a value near `2^64`,
so a regression back to wrapping fails `lake build EthCLSpecsTests` instead of passing
silently. The weak-subjectivity section at the end pins the values of the validator guide's
`compute_weak_subjectivity_period`, the helper the model did not have; its oracle numbers
come from the built pyspec at the pin (see the spike stage report).

They live in `EthCLSpecsTests` rather than beside the declarations they pin, the same
pattern as the fork-choice pins: a pin compiled into `EthCLSpecs` is shipped weight,
since `native_decide` bakes its evaluation into the shipped module. The pinned
declarations are all public, so nothing is lost by the move except adjacency.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluArithPins

open EthCLSpecs.Fulu

/-! ### The `Checked` helpers: the raise leaves in the `Except` value -/

/-- `compute_start_slot_at_epoch` rejects at the multiply's first out-of-range product:
an epoch at or past `2^64 // SLOTS_PER_EPOCH`. The pin sits on the exact boundary,
`epoch = 2^64 / 8 = 2^61` at minimal, where `epoch * 8` hits `2^64` and the plain-`int`
narrowing `Uint64()` rejects it. A wrapped result (`slot = 0`) instead would corrupt
every downstream `get_block_root` read. -/
private def pinStartSlotFault : Checked Slot :=
  letI : Preset := minimal
  computeStartSlotAtEpoch 2305843009213693952

-- The fault equality is definitional, so kernel `rfl` closes it: the `Checked` value is
-- hash-free, and `decide` is unavailable because Lean core carries no `DecidableEq
-- (Except …)` instance.
example : pinStartSlotFault = .error (.range "Uint64()" 18446744073709551616 0) := by
  rfl

/-- `compute_activation_exit_epoch` rejects at the top of the chain: at
`epoch = 2^64 - 1` the first checked add (`epoch + 1`) leaves the range. Every caller
binds the result, so a wrapped sum (`(2^64 - 1) + 1 + 4 ≡ 4`) would hand the registry an
activation / exit epoch of 4. -/
private def pinActivationExitFault : Checked Epoch :=
  letI : Preset := minimal
  computeActivationExitEpoch 18446744073709551615

example : pinActivationExitFault = .error (.range "Uint64()" 18446744073709551616 0) := by
  rfl

/-! ### The state-machine sites: the raise surfaces as `.error (.arithmetic …)` -/

/-- The shared fixture for the two `exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY`
sites. One active compounding validator at epoch 64 (past `SHARD_COMMITTEE_PERIOD`),
`earliest_exit_epoch` set to `2^64 - 256`, and `exit_balance_to_consume` covering the
validator's effective balance. The coverage makes `reserve_churn` take its no-rollover
branch, so `compute_exit_epoch_and_update_churn` returns the pinned epoch untouched and
the withdrawable-epoch sum is the first arithmetic step to leave the range:
`2^64 - 256 + 256 = 2^64`. -/
private def pinArithState : @EthCLSpecs.Fulu.BeaconState minimal :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let cred : Bytes32 :=
    Vector.ofFn (fun i : Fin 32 => if i.val == 0 then Const.compoundingWithdrawalPrefix else 0)
  let v : Validator :=
    { pubkey := default, withdrawalCredentials := cred
      effectiveBalance := 32000000000, slashed := false
      activationEligibilityEpoch := 0, activationEpoch := 0
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
    slot := 512
    validators := sszOfArray #[v] (by decide)
    balances := sszOfArray #[32000000010] (by decide)
    exitBalanceToConsume := 32000000000
    earliestExitEpoch := 18446744073709551360 }

/-- `initiate_validator_exit` rejects (`uncaught arithmetic fault`) the
`withdrawable_epoch = exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` sum when the
assigned exit epoch is `2^64 - 256`: the reserved epoch fits, its own bookkeeping stays
in range, and the delay sum is the step that hits `2^64`. -/
private def pinInitiateValidatorExitRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let state : State := SSZ.FastBox pinArithState
  match (initiateValidatorExit 0 : EStateM StateTransitionError State Unit).run state with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinInitiateValidatorExitRaises = true := by native_decide

/-- `process_withdrawal_request` rejects (`uncaught arithmetic fault`) at the partial
withdrawal's `we` bind, the same sum one rung down the validity ladder: the request
clears every gate (execution credential, active, past the shard-committee period, not a
full exit, balance in excess), reserves the exit epoch `2^64 - 256`, and the
`withdrawable_epoch` sum overflows. A wrapped `we` would queue a partial withdrawal
withdrawable before its own exit. -/
private def pinWithdrawalRequestRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let wr : WithdrawalRequest := { sourceAddress := default, validatorPubkey := default, amount := 1 }
  let state : State := SSZ.FastBox pinArithState
  match (processWithdrawalRequest wr : EStateM StateTransitionError State Unit).run state with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinWithdrawalRequestRaises = true := by native_decide

/-! ### `compute_weak_subjectivity_period` (validator guide)

The helper the model did not have (Stage 6.2 of the plan). Each pin's oracle value comes
from the built pyspec at `v1.7.0-beta.4` over a state with the same shape: active
compounding validators, activation epoch 0, exit at `FAR_FUTURE_EPOCH`, slot 512
(epoch 64 at minimal).
-/

/-- The weak-subjectivity fixture: `n` active compounding validators of `eff` Gwei
effective balance each, at slot 512. The Fulu `get_total_balance` sums
`effective_balance`, so the `balances` list rides along only for state shape. The
registry cap is literal because the fixture is a minimal-preset state and the
signature carries no `[Preset]`. -/
private def pinWSState (n : Nat) (eff : Gwei)
    (hv : n ≤ 2 ^ 40) (hb : n ≤ 2 ^ 40) :
    @EthCLSpecs.Fulu.BeaconState minimal :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let cred : Bytes32 :=
    Vector.ofFn (fun i : Fin 32 => if i.val == 0 then Const.compoundingWithdrawalPrefix else 0)
  let v : Validator :=
    { pubkey := default, withdrawalCredentials := cred
      effectiveBalance := eff, slashed := false
      activationEligibilityEpoch := 0, activationEpoch := 0
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
    slot := 512
    validators := sszOfArray (Array.replicate n v)
      (by rw [Array.size_replicate]; exact hv)
    balances := sszOfArray (Array.replicate n eff)
      (by rw [Array.size_replicate]; exact hb) }

/-- One active validator at 32 ETH: `t = 32 ETH`, below the 64 ETH churn floor, so
`delta = 64 ETH` and the churn term is `10 * t // (2 * delta * 100) = 0`; the period is
the withdrawability delay alone. Oracle: 256. -/
private def pinWeakSubjectivitySingle : Nat :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match computeWeakSubjectivityPeriod (SSZ.FastBox (pinWSState 1 32000000000 (by decide) (by decide))) with
  | .ok v => v.toPlainInt
  | .error _ => 0
example : pinWeakSubjectivitySingle = 256 := by native_decide

/-- 128 active validators at 32 ETH: `t = 4096 ETH`, so `delta = max(64 ETH, t // 32)
= 128 ETH` and the churn term is `10 * t // (2 * delta * 100) = 1`. Oracle: 257. -/
private def pinWeakSubjectivityChurn : Nat :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match computeWeakSubjectivityPeriod (SSZ.FastBox (pinWSState 128 32000000000 (by decide) (by decide))) with
  | .ok v => v.toPlainInt
  | .error _ => 0
example : pinWeakSubjectivityChurn = 257 := by native_decide

/-- The raise: one validator at `2^63` Gwei, so `t = 2^63` and the checked product
`SAFETY_DECAY * t = 10 * 2^63` is the first step past `2^64` — the same first-faulting
step the pyspec raises at (`SSZValueError: … is out of range for Gwei`). -/
private def pinWeakSubjectivityOverflowRaises : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match computeWeakSubjectivityPeriod (SSZ.FastBox (pinWSState 1 9223372036854775808 (by decide) (by decide))) with
  | .error _ => true
  | _ => false
example : pinWeakSubjectivityOverflowRaises = true := by native_decide

end EthCLSpecs.Tests.FuluArithPins
