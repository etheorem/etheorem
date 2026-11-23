import EthCLSpecs.Fulu
import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Tests.IndexMigrationPins`: the other index behavior pins

Behavior pins for `BuilderIndex`, `WithdrawalIndex`, `CommitteeIndex`, `ColumnIndex`, and
`CellIndex` as the checked `CLUint64` kind. Each pin pairs a targeted failure case with a
nearby success that reaches the same operation, and the successes read back exact values. The
pinned pyspec gives the same class or value at every pin. Every failure pin fails under the
pre-migration body, which the pin's own comment names.

1. `withdrawal_index += 1` (Fulu `get_expected_withdrawals`, Gloas `get_builder_withdrawals`):
   the checked `WithdrawalIndex` add raises at `UINT64_MAX`. The old body wrapped to `0`.
2. `compute_committee`: `(len(indices) * index) // count` and
   `(len(indices) * Uint64(index + 1)) // count` are checked chains. The product raises
   past `2^64 - 1` and `// count` raises `ZeroDivisionError` on a zero count. The old body
   computed in `Nat`, so the product never raised and `/ 0` returned `0`.
3. `get_beacon_committee`: `Uint64(slot % SLOTS_PER_EPOCH) * committees_per_slot + index`
   raises at the checked add. The old `Nat` sum never raised.
4. `process_attestation` (Fulu and Gloas): `attestation.aggregation_bits[committee_offset +
   index]` raises `IndexError` past the bit list's end. The old body read the `[i]!` default
   `false`, so the attestation rejected with the `assert` class.
5. `process_execution_payload_bid` (Gloas): `is_active_builder` reads
   `state.builders[builder_index]`, which raises `IndexError` out of range. The old body read
   the `[i]!` default builder, which is not active, so the bid rejected with the `assert`
   class.
6. The builder flag conversions (Gloas) keep their values: `convert_validator_index_to_builder_index`
   is the mixed `&` with the plain `~BUILDER_INDEX_FLAG` and cannot raise, so these are value
   pins with no failure case.

The pins hash through the FFI `Sha256` (`fastHasherTag`), so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.IndexMigrationPins

/-- `2^64 - 1`, the largest checked value. -/
private def maxU64 : Nat := 18446744073709551615

section Fulu
open EthCLSpecs.Fulu

/-! ### 1. `withdrawal_index += 1` (Fulu) -/

/-- A Fulu state at slot `8` with one fully withdrawable validator (an `0x01` credential,
withdrawable at epoch `0`, balance `32 ETH`) and the given `next_withdrawal_index`. -/
private def withdrawableState (nextIndex : WithdrawalIndex) : @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      withdrawalCredentials := Vector.ofFn (fun i => if i.val = 0 then 1 else 0)
      effectiveBalance := 32000000000, exitEpoch := 0, withdrawableEpoch := 0 }
  { (default : @BeaconState minimal) with
    slot := 8
    validators := ⟨#[v], by decide⟩
    balances := ⟨#[32000000000], by decide⟩
    nextWithdrawalIndex := nextIndex }

/-- Runs Fulu `get_expected_withdrawals` and reads back each withdrawal's index, validator
index, and amount. -/
private def fuluExpected (nextIndex : WithdrawalIndex) :
    Except StateTransitionError (List (Nat × Nat × Nat)) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st := withdrawableState nextIndex
  match (getExpectedWithdrawals st : EStateM StateTransitionError State _).run st with
  | .ok (ws, _) _ =>
    .ok (ws.toList.map fun w => (w.index.toPlainNat, w.validatorIndex.toPlainNat, w.amount.toPlainNat))
  | .error e _ => .error e

/-- `next_withdrawal_index = UINT64_MAX`: the sweep queues one withdrawal, and the
`withdrawal_index += 1` after it raises (`SSZValueError` at the pin). The old `UInt64` add
wrapped to `0` and the call succeeded. -/
private def pinFuluWithdrawalIndexMaxRaises : Bool :=
  match fuluExpected 18446744073709551615 with
  | .error (.arithmetic _) => true
  | _ => false
example : pinFuluWithdrawalIndexMaxRaises = true := by native_decide

/-- `next_withdrawal_index = UINT64_MAX - 1`: the same add reaches `UINT64_MAX`, and the
sweep queues the one withdrawal at the starting index. -/
private def pinFuluWithdrawalIndexBelowMaxReads : Bool :=
  match fuluExpected 18446744073709551614 with
  | .ok ws => ws == [(18446744073709551614, 0, 32000000000)]
  | .error _ => false
example : pinFuluWithdrawalIndexBelowMaxReads = true := by native_decide

/-! ### 2. `compute_committee` -/

/-- Runs `compute_committee` over the indices `0 … 7` and a zero seed, reading back the
committee's indices. -/
private def committeeOf (index count : CLUint64) : Except StateTransitionError (List Nat) :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  (computeCommittee ((Array.range 8).map fun i => ((CLUint64.ofNat? i).toOption.getD 0))
      (Vector.replicate 32 0) index count).map fun c => c.toList.map (·.toPlainNat)

/-- `index = 2^61 - 1`, `count = UINT64_MAX`: `len(indices) * Uint64(index + 1)` is
`8 * 2^61 = 2^64`, so the checked product raises. The old `Nat` product never raised and the
call returned an empty committee. -/
private def pinComputeCommitteeProductRaises : Bool :=
  match committeeOf 2305843009213693951 18446744073709551615 with
  | .error (.arithmetic op) => op == "*"
  | _ => false
example : pinComputeCommitteeProductRaises = true := by native_decide

/-- `index = 2^61 - 2`: both products fit, and both bounds divide to `0`. -/
private def pinComputeCommitteeProductFits : Bool :=
  (committeeOf 2305843009213693950 18446744073709551615).toOption == some []
example : pinComputeCommitteeProductFits = true := by native_decide

/-- `count = 0`: `// count` raises `ZeroDivisionError`. The old `Nat` division returned `0`
and the call returned an empty committee. -/
private def pinComputeCommitteeZeroCountRaises : Bool :=
  match committeeOf 0 0 with
  | .error (.zeroDivision _) => true
  | _ => false
example : pinComputeCommitteeZeroCountRaises = true := by native_decide

/-- `count = 1`: the whole shuffled registry, in the pinned shuffle order. -/
private def pinComputeCommitteeOneCountReads : Bool :=
  (committeeOf 0 1).toOption == some [4, 1, 0, 2, 6, 5, 3, 7]
example : pinComputeCommitteeOneCountReads = true := by native_decide

/-- `index = 1`, `count = 4`: the slice `[2, 4)` of the shuffled registry. -/
private def pinComputeCommitteeSliceReads : Bool :=
  (committeeOf 1 4).toOption == some [0, 2]
example : pinComputeCommitteeSliceReads = true := by native_decide

/-! ### 3. `get_beacon_committee` -/

/-- A Fulu state at slot `s` with eight active validators. At the minimal preset each slot
has one committee of one member. -/
private def activeState (s : Slot) : @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @BeaconState minimal) with
    slot := s
    validators := ⟨Array.replicate 8 v, by decide⟩
    balances := ⟨Array.replicate 8 32000000000, by decide⟩ }

/-- Slot `1`, committee index `UINT64_MAX`: `Uint64(1 % 8) * 1 + index` raises at the
checked add. The old `Nat` sum never raised. -/
private def pinBeaconCommitteeIndexAddRaises : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match (getBeaconCommittee (activeState 1) 1 18446744073709551615 :
      Except StateTransitionError (Array ValidatorIndex)) with
  | .error (.arithmetic op) => op == "+"
  | _ => false
example : pinBeaconCommitteeIndexAddRaises = true := by native_decide

/-- Slot `1`, committee index `0`: the add fits, and the committee is validator `7`. -/
private def pinBeaconCommitteeIndexAddReads : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match (getBeaconCommittee (activeState 1) 1 0 :
      Except StateTransitionError (Array ValidatorIndex)) with
  | .ok c => c.toList.map (·.toPlainNat) == [7]
  | .error _ => false
example : pinBeaconCommitteeIndexAddReads = true := by native_decide

/-! ### 4. The aggregation-bit reads (Fulu) -/

/-- An attestation at slot `8` for target epoch `1`, committee `0`, with the given
aggregation bits. -/
private def fuluAtt (bits : Array Bool) (h : bits.size ≤ 4 := by decide) : @Attestation minimal :=
  letI : Preset := minimal
  { (default : Attestation) with
    aggregationBits := ⟨bits, Nat.le_trans h (by decide)⟩
    data := { (default : AttestationData) with
      slot := 8, target := { (default : Checkpoint) with epoch := 1 } }
    committeeBits := bitSet default 0 true }

/-- Runs Fulu `process_attestation` at state slot `9`. -/
private def fuluRun (att : @Attestation minimal) :
    EStateM.Result StateTransitionError (@State minimal) Unit :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  (processAttestation att : EStateM StateTransitionError State Unit).run (activeState 9)

/-- No aggregation bits: the committee's one member reads `aggregation_bits[0]`, which
raises `IndexError`. The old `[i]!` read `false`, and the attestation rejected with the
`assert` class. -/
private def pinFuluEmptyBitsRaises : Bool :=
  match fuluRun (fuluAtt #[]) with
  | .error (.outOfBounds 0 0) _ => true
  | _ => false
example : pinFuluEmptyBitsRaises = true := by native_decide

/-- One `false` bit: the read succeeds, the committee has no attester, and the attestation
rejects with the caught assert. -/
private def pinFuluFalseBitRejectsAssert : Bool :=
  match fuluRun (fuluAtt #[false]) with
  | .error (.assert _) _ => true
  | _ => false
example : pinFuluFalseBitRejectsAssert = true := by native_decide

end Fulu

section Gloas
open EthCLSpecs.Gloas

/-! ### 1. `withdrawal_index += 1` (Gloas) -/

/-- A Gloas state with one pending builder withdrawal of `7` Gwei for builder `3`. -/
private def builderPendingState : @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { (default : @BeaconState minimal) with
    builderPendingWithdrawals := ⟨#[{ (default : BuilderPendingWithdrawal) with
      amount := 7, builderIndex := 3 }]⟩ }

/-- Runs Gloas `get_builder_withdrawals` from `withdrawalIndex` with no prior withdrawals,
reading back the withdrawals, the next index, and the processed count. -/
private def gloasBuilderWs (withdrawalIndex : WithdrawalIndex) :
    Except StateTransitionError (List (Nat × Nat × Nat) × Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (getBuilderWithdrawals withdrawalIndex #[] : EStateM StateTransitionError State _).run
      builderPendingState with
  | .ok (ws, wi, n) _ =>
    .ok (ws.toList.map (fun w => (w.index.toPlainNat, w.validatorIndex.toPlainNat, w.amount.toPlainNat)),
      wi.toPlainNat, n)
  | .error e _ => .error e

/-- `withdrawal_index = UINT64_MAX`: the builder withdrawal queues, and the
`withdrawal_index += 1` after it raises. The old `UInt64` add wrapped to `0`. -/
private def pinGloasBuilderWithdrawalIndexMaxRaises : Bool :=
  match gloasBuilderWs 18446744073709551615 with
  | .error (.arithmetic _) => true
  | _ => false
example : pinGloasBuilderWithdrawalIndexMaxRaises = true := by native_decide

/-- `withdrawal_index = UINT64_MAX - 1`: the add reaches `UINT64_MAX`. The withdrawal carries
the builder's flagged index `2^40 + 3`. -/
private def pinGloasBuilderWithdrawalIndexBelowMaxReads : Bool :=
  match gloasBuilderWs 18446744073709551614 with
  | .ok r => r == ([(18446744073709551614, 1099511627779, 7)], maxU64, 1)
  | .error _ => false
example : pinGloasBuilderWithdrawalIndexBelowMaxReads = true := by native_decide

/-! ### 4. The aggregation-bit reads (Gloas) -/

/-- A Gloas state at slot `s` with eight active validators. -/
private def gloasActiveState (s : Slot) : @State minimal :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @BeaconState minimal) with
    slot := s
    validators := ⟨Array.replicate 8 v⟩
    balances := ⟨Array.replicate 8 32000000000⟩ }

/-- Runs Gloas `process_attestation` at state slot `9` with `parent_slot = 0`, for an
attestation at slot `8`, target epoch `1`, committee `0`, with the given aggregation bits. -/
private def gloasAttRun (bits : Array Bool) :
    EStateM.Result StateTransitionError (@State minimal) Unit :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let att : Attestation :=
    { (default : Attestation) with
      aggregationBits := ⟨bits⟩
      data := { (default : AttestationData) with
        slot := 8, target := { (default : Checkpoint) with epoch := 1 } }
      committeeBits := bitSet default 0 true }
  (processAttestation att 0 : EStateM StateTransitionError State Unit).run (gloasActiveState 9)

/-- Gloas twin of `pinFuluEmptyBitsRaises`. -/
private def pinGloasEmptyBitsRaises : Bool :=
  match gloasAttRun #[] with
  | .error (.outOfBounds 0 0) _ => true
  | _ => false
example : pinGloasEmptyBitsRaises = true := by native_decide

/-- Gloas twin of `pinFuluFalseBitRejectsAssert`. -/
private def pinGloasFalseBitRejectsAssert : Bool :=
  match gloasAttRun #[false] with
  | .error (.assert _) _ => true
  | _ => false
example : pinGloasFalseBitRejectsAssert = true := by native_decide

/-! ### 5. The builder read in `process_execution_payload_bid` -/

/-- Runs Gloas `process_execution_payload_bid` at state slot `1` over `n` default builders,
for a bid at slot `1` naming `builderIndex`. -/
private def bidRun (n : Nat) (builderIndex : BuilderIndex) :
    EStateM.Result StateTransitionError (@State minimal) Unit :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st : State :=
    { (default : @BeaconState minimal) with
      slot := 1
      builders := ⟨Array.replicate n default⟩ }
  let bid : SignedExecutionPayloadBid :=
    { (default : SignedExecutionPayloadBid) with
      message := { (default : ExecutionPayloadBid) with builderIndex, slot := 1 } }
  (processExecutionPayloadBid bid : EStateM StateTransitionError State Unit).run st

/-- Builder `5` over an empty builder list: `is_active_builder` reads
`state.builders[5]`, which raises `IndexError`. The old `[i]!` read the default builder,
which is not active, and the bid rejected with the `assert` class. -/
private def pinBidBuilderOutOfRangeRaises : Bool :=
  match bidRun 0 5 with
  | .error (.outOfBounds 5 0) _ => true
  | _ => false
example : pinBidBuilderOutOfRangeRaises = true := by native_decide

/-- Builder `0` over one default builder: the read succeeds, and the builder is not active
(its deposit epoch `0` is not below the finalized epoch `0`), so the bid rejects with the
caught assert. -/
private def pinBidBuilderInRangeRejectsAssert : Bool :=
  match bidRun 1 0 with
  | .error (.assert _) _ => true
  | _ => false
example : pinBidBuilderInRangeRejectsAssert = true := by native_decide

/-! ### 6. The builder flag conversions -/

/-- `convert_builder_index_to_validator_index(5)` sets bit `40`: `2^40 + 5`. -/
example : (convertBuilderIndexToValidatorIndex 5).toPlainNat = 1099511627781 := by native_decide

/-- `convert_validator_index_to_builder_index(2^40 + 5)` clears it again: `5`. -/
example : (toBuilderIndex 1099511627781).map (·.toPlainNat) = .ok 5 := by native_decide

/-- At `UINT64_MAX` the mixed `&` clears only bit `40`: `2^64 - 1 - 2^40`, in range. -/
example : (toBuilderIndex 18446744073709551615).map (·.toPlainNat) = .ok 18446742974197923839 := by
  native_decide

/-- `is_builder_index` tests bit `40`. -/
example : isBuilderIndex 1099511627781 = true ∧ isBuilderIndex 5 = false := by native_decide

end Gloas

end EthCLSpecs.Tests.IndexMigrationPins
