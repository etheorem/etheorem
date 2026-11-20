import EthCLSpecs.Fulu
import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Tests.PendingDepositsScanPins`: the deposit-scan decision points

Behavior pins for `process_pending_deposits` (`fulu/mainnet.py:6098-6152`,
`gloas/mainnet.py:6796-6850`). Each decision point of the scan has a pin pair: two
nearby inputs that land on the two sides of the decision. Every pin reads back the
exact values the pinned Python writes.

1. Churn reached: the second deposit's `processed_amount + deposit.amount` exceeds
   `available_for_processing`. The scan stops there, the deposit stays queued, and
   `deposit_balance_to_consume` carries `available_for_processing - processed_amount`
   forward. The paired success sums to exactly the budget, which still fits (`>` is
   strict), so both apply and the balance to consume resets to zero.
2. Finalized-slot stop: a deposit one slot past the finalized checkpoint's start
   slot stops the scan and stays queued. The paired deposit at the start slot
   applies. A stop that is not the churn stop resets a nonzero
   `deposit_balance_to_consume` to zero.
3. Withdrawable boundary: the exiting validator's `withdrawable_epoch` sits one
   below `next_epoch` (withdrawn: the deposit applies without churn) or at
   `next_epoch` (not withdrawn: the deposit is postponed). The postponed deposit
   lands after the unprocessed queue tail, the pinned
   `pending_deposits[next_deposit_index:] + deposits_to_postpone` order.
4. Gloas churn budget: Gloas reads `get_activation_churn_limit`, Fulu
   `get_activation_exit_churn_limit`. With sixty-four active validators at the
   minimal config the two budgets differ (Gloas `128 ETH`, Fulu `64 ETH`), so a
   `100 ETH` deposit fits the Gloas body and a further `30 ETH` deposit hits the
   Gloas churn stop.

The fixture states sit at slot `800` (epoch `100`, so `next_epoch = 101`) with the
finalized checkpoint at epoch `10` (start slot `80`). Each deposit's pubkey is a
known validator's, so `apply_pending_deposit` takes the top-up branch and no
signature check runs. With one active `32 ETH` validator the Fulu budget is the
minimal config's `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA = 64 ETH`. `State` is
FFI-backed, so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.PendingDepositsScanPins

/-- `n` ETH in Gwei. -/
private def eth (n : Nat) : Nat := n * 1000000000

/-- A fixture `Nat` as a checked word. Every fixture value is far below `2^64`, so the
`0` fallback never fires. -/
private def u64 (n : Nat) : CLUint64 :=
  match CLUint64.ofNat? n with
  | .ok v => v
  | .error _ => 0

/-! ## Fulu -/

section FuluPins

open EthCLSpecs.Fulu

/-- A capped array built from `a` when `a` fits the cap, and the empty one otherwise. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- Validator `0`: active, `32 ETH`, pubkey `0x01…`. -/
private def activeValidator : @Validator minimal :=
  letI : Preset := minimal
  { (default : @Validator minimal) with
    pubkey := Vector.replicate 48 (1 : UInt8)
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- Validator `1`: exited at epoch `50`, withdrawable at `w`, pubkey `0x02…`. -/
private def exitingValidator (w : Nat) : @Validator minimal :=
  letI : Preset := minimal
  { (default : @Validator minimal) with
    pubkey := Vector.replicate 48 (2 : UInt8)
    effectiveBalance := 32000000000
    exitEpoch := 50
    withdrawableEpoch := u64 w }

/-- A deposit of `amount` Gwei to the validator with pubkey byte `pk`, queued at `slot`. -/
private def deposit (pk : UInt8) (amount slot : Nat) : @PendingDeposit minimal :=
  letI : Preset := minimal
  { (default : @PendingDeposit minimal) with
    pubkey := Vector.replicate 48 pk
    amount := u64 amount
    slot := u64 slot }

/-- The fixture state: `validators` with `32 ETH` balances, the pending queue `queue`,
and `deposit_balance_to_consume = carry`. -/
private def scanState (validators : Array (@Validator minimal))
    (queue : Array (@PendingDeposit minimal)) (carry : Nat) :
    SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState minimal) :=
  letI : Preset := minimal
  SSZ.FastBox
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
      slot := 800
      finalizedCheckpoint := { (default : @Checkpoint minimal) with epoch := 10 }
      validators := capped validators
      balances := capped (Array.replicate validators.size 32000000000)
      depositBalanceToConsume := u64 carry
      pendingDeposits := capped queue }

/-- Runs Fulu `process_pending_deposits` and reads back the queue's amounts, the
balances, and `deposit_balance_to_consume`, all as plain `Nat`s. -/
private def scanRun (st : SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState minimal)) :
    Option (List Nat × List Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processPendingDeposits : EStateM StateTransitionError
      (SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState minimal)) Unit).run st with
  | .ok _ post =>
    let v := SSZ.Box.view post
    some (v.pendingDeposits.val.toList.map (·.amount.toPlainNat),
      v.balances.val.toList.map (·.toPlainNat), v.depositBalanceToConsume.toPlainNat)
  | .error _ _ => none

/-! ### 1. Churn reached -/

/-- `40 + 40 > 64`: the second deposit hits the churn stop. It stays queued, and the
budget left after the first, `64 - 40 = 24 ETH`, carries forward. -/
example : scanRun (scanState #[activeValidator]
    #[deposit 1 (eth 40) 80, deposit 1 (eth 40) 80] 0) =
    some ([eth 40], [eth 72], eth 24) := by native_decide

/-- `40 + 24 = 64`, not above the budget: both apply, and the balance to consume
resets to zero. -/
example : scanRun (scanState #[activeValidator]
    #[deposit 1 (eth 40) 80, deposit 1 (eth 24) 80] 0) =
    some ([], [eth 96], 0) := by native_decide

/-! ### 2. Finalized-slot stop -/

/-- Slot `81` is past the finalized start slot `80`: the scan stops at once, the deposit
stays queued, and the carried `5 ETH` resets to zero. -/
example : scanRun (scanState #[activeValidator] #[deposit 1 (eth 1) 81] (eth 5)) =
    some ([eth 1], [eth 32], 0) := by native_decide

/-- Slot `80` is the finalized start slot: the deposit applies. -/
example : scanRun (scanState #[activeValidator] #[deposit 1 (eth 1) 80] (eth 5)) =
    some ([], [eth 33], 0) := by native_decide

/-! ### 3. Withdrawable boundary -/

/-- `withdrawable_epoch = 100 < next_epoch = 101`: validator `1` is withdrawn, so its
`1 ETH` deposit applies without churn. The `2 ETH` deposit at slot `81` then stops the
scan and stays queued. -/
example : scanRun (scanState #[activeValidator, exitingValidator 100]
    #[deposit 2 (eth 1) 80, deposit 1 (eth 2) 81] 0) =
    some ([eth 2], [eth 32, eth 33], 0) := by native_decide

/-- `withdrawable_epoch = 101 = next_epoch`: validator `1` is exiting and not withdrawn,
so its deposit is postponed. It lands after the unprocessed `2 ETH` tail. -/
example : scanRun (scanState #[activeValidator, exitingValidator 101]
    #[deposit 2 (eth 1) 80, deposit 1 (eth 2) 81] 0) =
    some ([eth 2, eth 1], [eth 32, eth 32], 0) := by native_decide

end FuluPins

/-! ## Gloas -/

section GloasPins

open EthCLSpecs.Gloas

/-- An active `32 ETH` validator whose pubkey bytes are all `pk`. -/
private def gloasValidator (pk : UInt8) : @Validator minimal :=
  letI : Preset := minimal
  { (default : @Validator minimal) with
    pubkey := Vector.replicate 48 pk
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- A deposit of `amount` Gwei to validator `0` (pubkey byte `0`), queued at slot `80`. -/
private def gloasDeposit (amount : Nat) : @PendingDeposit minimal :=
  letI : Preset := minimal
  { (default : @PendingDeposit minimal) with
    pubkey := Vector.replicate 48 0
    amount := u64 amount
    slot := 80 }

/-- Sixty-four active validators (`2048 ETH` total) and the pending queue `queue`. The
Gloas budget is `min(128, max(64, 2048 / 16)) = 128 ETH`; Fulu's would be
`min(128, max(64, 2048 / 32)) = 64 ETH`. -/
private def gloasScanState (queue : Array (@PendingDeposit minimal)) :
    SSZ.Box Sha256 (@EthCLSpecs.Gloas.BeaconState minimal) :=
  letI : Preset := minimal
  let validators := (Array.range 64).map fun i => gloasValidator (UInt8.ofNat i)
  SSZ.FastBox
    { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
      slot := 800
      finalizedCheckpoint := { (default : @Checkpoint minimal) with epoch := 10 }
      validators := ⟨validators⟩
      balances := ⟨Array.replicate 64 32000000000⟩
      pendingDeposits := ⟨queue⟩ }

/-- Runs Gloas `process_pending_deposits` and reads back the queue's amounts,
validator `0`'s balance, and `deposit_balance_to_consume`. -/
private def gloasScanRun (st : SSZ.Box Sha256 (@EthCLSpecs.Gloas.BeaconState minimal)) :
    Option (List Nat × Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processPendingDeposits : EStateM StateTransitionError
      (SSZ.Box Sha256 (@EthCLSpecs.Gloas.BeaconState minimal)) Unit).run st with
  | .ok _ post =>
    let v := SSZ.Box.view post
    some (v.pendingDeposits.toArray.toList.map (·.amount.toPlainNat),
      v.balances.toArray[0]!.toPlainNat, v.depositBalanceToConsume.toPlainNat)
  | .error _ _ => none

/-! ### 4. Gloas churn budget -/

/-- `100 ETH` fits the Gloas `128 ETH` budget, where Fulu's `64 ETH` would stop. -/
example : gloasScanRun (gloasScanState #[gloasDeposit (eth 100)]) =
    some ([], eth 132, 0) := by native_decide

/-- `100 + 30 > 128`: the Gloas churn stop. `128 - 100 = 28 ETH` carries forward. -/
example : gloasScanRun (gloasScanState #[gloasDeposit (eth 100), gloasDeposit (eth 30)]) =
    some ([eth 30], eth 132, eth 28) := by native_decide

end GloasPins

end EthCLSpecs.Tests.PendingDepositsScanPins
