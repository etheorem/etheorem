import EthCLSpecs.Fulu
import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Tests.TransitionFamilyAuditPins`: the Fulu state-transition family pins

Behavior pins for two decisions in the Fulu state-transition family. Each decision has a
pin pair: two nearby inputs that land on its two sides.

1. `process_registry_updates` (`fulu/mainnet.py:1852-1868`) is one `if` / `elif` /
   `elif` chain, so a validator takes at most one of its three updates. The old body ran
   three independent `if`s. A queue-eligible validator also took the activation update
   when the finalized epoch is `FAR_FUTURE_EPOCH`, and the ejection exit when
   `EJECTION_BALANCE` is at least `MIN_ACTIVATION_BALANCE`. The pins read back
   `(activation_eligibility_epoch, activation_epoch, exit_epoch)` of validator `0`.
2. `process_slashings` (`fulu/mainnet.py:1871-1891`) forms
   `epoch + EPOCHS_PER_SLASHINGS_VECTOR // 2` only after `validator.slashed` passes,
   because Python's `and` short-circuits. The old body bound the sum before the loop, so
   a registry with no slashed validator raised the sum's range fault where Python
   succeeds. The shipped presets cannot reach that sum's range limit: the current epoch
   is at most `(2^64 - 1) // SLOTS_PER_EPOCH`. The pins use the `minimal` preset with
   `SLOTS_PER_EPOCH = 1`, an accepted configuration, so the epoch reaches the limit.

Gloas and Heze inherit both bodies. The Gloas pin shows that the inherited body
carries the fix. The fixture states sit at slot `800` (epoch `100`). At the minimal
preset `compute_activation_exit_epoch(100) = 100 + 1 + MAX_SEED_LOOKAHEAD = 105`.
The pins hash through the FFI `Sha256` (`fastHasherTag`). The Fulu state is an FFI-backed
box, and the Gloas state is the plain record. So `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.TransitionFamilyAuditPins

/-- `FAR_FUTURE_EPOCH`, `2^64 - 1`, as a plain `Nat`. -/
private def farFuture : Nat := 18446744073709551615

/-- A fixture `Nat` as a checked word. Every fixture value is at most `2^64 - 1`, so the
`0` fallback never fires. -/
private def u64 (n : Nat) : CLUint64 :=
  match CLUint64.ofNat? n with
  | .ok v => v
  | .error _ => 0

/-- A capped array built from `a` when `a` fits the cap, and the empty one otherwise. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-! ## Fulu -/

section FuluPins

open EthCLSpecs.Fulu

/-- A `32 ETH` validator with the given lifecycle epochs, `exit_epoch = FAR_FUTURE_EPOCH`.
At `32 ETH` it passes the queue's `effective_balance >= MIN_ACTIVATION_BALANCE` test. -/
private def validator (eligibility activation : Nat) (slashed : Bool := false) :
    @Validator minimal :=
  letI : Preset := minimal
  { (default : @Validator minimal) with
    pubkey := Vector.replicate 48 (1 : UInt8)
    effectiveBalance := 32000000000
    slashed := slashed
    activationEligibilityEpoch := u64 eligibility
    activationEpoch := u64 activation
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- The registry-update fixture: validator `v` with a `32 ETH` balance, at slot `800`,
with the finalized checkpoint at `finalized`. -/
private def registryState (v : @Validator minimal) (finalized : Nat) :
    SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState minimal) :=
  letI : Preset := minimal
  SSZ.FastBox
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
      slot := 800
      finalizedCheckpoint := { (default : @Checkpoint minimal) with epoch := u64 finalized }
      validators := capped #[v]
      balances := capped #[32000000000] }

/-- The minimal config with `EJECTION_BALANCE = 32 ETH`, equal to
`MIN_ACTIVATION_BALANCE`. -/
@[reducible] private def ejectAtActivation : Config :=
  { minimalConfig with ejectionBalanceG := 32000000000 }

/-- Runs Fulu `process_registry_updates` under `cfg` and reads back validator `0`'s
`(activation_eligibility_epoch, activation_epoch, exit_epoch)`. -/
private def registryRun (st : SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState minimal))
    (cfg : Config := minimalConfig) : Option (Nat × Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := cfg
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processRegistryUpdates : EStateM StateTransitionError
      (SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState minimal)) Unit).run st with
  | .ok _ post =>
    let v := (SSZ.Box.view post).validators.val[0]!
    some (v.activationEligibilityEpoch.toPlainNat, v.activationEpoch.toPlainNat,
      v.exitEpoch.toPlainNat)
  | .error _ _ => none

/-! ### 1. Registry updates: one branch per validator -/

/-- A queue-eligible validator under a finalized epoch of `FAR_FUTURE_EPOCH`: the first
branch sets `activation_eligibility_epoch = 101`, and the `elif` skips the activation
branch, so `activation_epoch` stays `FAR_FUTURE_EPOCH`. The old body also wrote
`activation_epoch = 105`. -/
example : registryRun (registryState (validator farFuture farFuture) farFuture) =
    some (101, farFuture, farFuture) := by native_decide

/-- A validator past the queue (`activation_eligibility_epoch = 50`, finalized `60`)
takes the activation branch: `activation_epoch = 105`. -/
example : registryRun (registryState (validator 50 farFuture) 60) =
    some (50, 105, farFuture) := by native_decide

/-- A queue-eligible validator that is also active at `EJECTION_BALANCE = 32 ETH`: the
first branch sets `activation_eligibility_epoch = 101`, and the `elif` skips the
ejection, so `exit_epoch` stays `FAR_FUTURE_EPOCH`. The old body also initiated the
exit. -/
example : registryRun (registryState (validator farFuture 0) 10) ejectAtActivation =
    some (101, 0, farFuture) := by native_decide

/-- The same active validator past the queue (`activation_eligibility_epoch = 0`) takes
the ejection branch: `initiate_validator_exit` sets `exit_epoch = 105`. -/
example : registryRun (registryState (validator 0 0) 10) ejectAtActivation =
    some (0, 0, 105) := by native_decide

/-! ### 2. Slashings: the half-ring sum forms only for a slashed validator -/

/-- The minimal preset with `SLOTS_PER_EPOCH = 1`, so the current epoch equals the slot
and can reach the `Epoch` range limit. `EPOCHS_PER_SLASHINGS_VECTOR // 2 = 32`. -/
@[reducible] private def oneSlotEpochs : Preset :=
  { minimal with slotsPerEpoch := 1, slotsPerEpochPos := by decide,
                 slotsPerEpochLt := by decide }

/-- The slashings fixture at `oneSlotEpochs`: one validator (`slashed` as given, active,
withdrawable at `FAR_FUTURE_EPOCH`) at slot `slot`. -/
private def slashingsState (slot : Nat) (slashed : Bool) :
    SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState oneSlotEpochs) :=
  letI : Preset := oneSlotEpochs
  let v : @Validator oneSlotEpochs :=
    { (default : @Validator oneSlotEpochs) with
      pubkey := Vector.replicate 48 (1 : UInt8)
      effectiveBalance := 32000000000
      slashed := slashed
      exitEpoch := Const.farFutureEpoch
      withdrawableEpoch := Const.farFutureEpoch }
  SSZ.FastBox
    { (default : @EthCLSpecs.Fulu.BeaconState oneSlotEpochs) with
      slot := u64 slot
      validators := capped #[v]
      balances := capped #[32000000000] }

/-- Runs Fulu `process_slashings` at `oneSlotEpochs` and reads back validator `0`'s
balance (`.inr`), or whether the error is the `.arithmetic` range fault (`.inl`). -/
private def slashingsRun (st : SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState oneSlotEpochs)) :
    Bool ⊕ Nat :=
  letI : Preset := oneSlotEpochs
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processSlashings : EStateM StateTransitionError
      (SSZ.Box Sha256 (@EthCLSpecs.Fulu.BeaconState oneSlotEpochs)) Unit).run st with
  | .ok _ post => .inr (SSZ.Box.view post).balances.val[0]!.toPlainNat
  | .error (.arithmetic _) _ => .inl true
  | .error _ _ => .inl false

/-- Epoch `2^64 - 32` and no slashed validator: Python never forms
`epoch + 32 = 2^64`, so the step succeeds with the balance unchanged. The old body
raised the sum's range fault before the loop. -/
example : slashingsRun (slashingsState (farFuture - 31) false) = .inr 32000000000 := by
  native_decide

/-- The same epoch with a slashed validator: `epoch + 32` passes `2^64 - 1` and raises the
range fault. -/
example : slashingsRun (slashingsState (farFuture - 31) true) = .inl true := by
  native_decide

/-- One epoch earlier, `epoch + 32 = 2^64 - 1` fits, so a slashed validator runs the
comparison (`FAR_FUTURE_EPOCH == FAR_FUTURE_EPOCH`) and takes the zero penalty. -/
example : slashingsRun (slashingsState (farFuture - 32) true) = .inr 32000000000 := by
  native_decide

end FuluPins

/-! ## Gloas -/

section GloasPins

open EthCLSpecs.Gloas

/-- The Gloas registry-update fixture: validator `v` with a `32 ETH` balance, at slot
`800`, with the finalized checkpoint at `finalized`. -/
private def gloasRegistryState (v : @Validator minimal) (finalized : Nat) :
    @EthCLSpecs.Gloas.BeaconState minimal :=
  letI : Preset := minimal
  { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
    slot := 800
    finalizedCheckpoint := { (default : @Checkpoint minimal) with epoch := u64 finalized }
    validators := ⟨#[v]⟩
    balances := ⟨#[32000000000]⟩ }

/-- A Gloas queue-eligible `32 ETH` validator, `activation_epoch = FAR_FUTURE_EPOCH`. -/
private def gloasQueueEligible : @Validator minimal :=
  letI : Preset := minimal
  { (default : @Validator minimal) with
    pubkey := Vector.replicate 48 (1 : UInt8)
    effectiveBalance := 32000000000
    activationEligibilityEpoch := Const.farFutureEpoch
    activationEpoch := Const.farFutureEpoch
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- Runs Gloas `process_registry_updates` and reads back validator `0`'s
`(activation_eligibility_epoch, activation_epoch)`. -/
private def gloasRegistryRun (st : @EthCLSpecs.Gloas.BeaconState minimal) :
    Option (Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processRegistryUpdates : EStateM StateTransitionError
      (@EthCLSpecs.Gloas.BeaconState minimal) Unit).run st with
  | .ok _ post =>
    let v := post.validators.toArray[0]!
    some (v.activationEligibilityEpoch.toPlainNat, v.activationEpoch.toPlainNat)
  | .error _ _ => none

/-- The inherited Gloas body takes one branch: the queue-eligible validator gets only
`activation_eligibility_epoch = 101`. -/
example : gloasRegistryRun (gloasRegistryState gloasQueueEligible farFuture) =
    some (101, farFuture) := by native_decide

end GloasPins

end EthCLSpecs.Tests.TransitionFamilyAuditPins
