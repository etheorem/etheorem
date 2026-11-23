import EthCLSpecs.Fulu
import EthCLSpecs.Gloas
import EthCLSpecs.Heze

/-!
# `EthCLSpecs.Tests.PlainArithmeticPins`: the plain-integer formula pins

Behavior pins for the pyspec's plain-integer formulas: Python lengths, negative indices,
zero divisors, mixed `min` / `max`, and empty sums. Each failure pin pairs with a nearby
success that reaches the same operation, and the successes read back exact values. The pinned
pyspec gives the same class or value at every pin. Every failure pin fails under the pre-port
body, which the pin's own comment names.

1. `integer_squareroot(n: Uint64) -> Uint64`: the total checked-kind root, with the pinned
   special case at `UINT64_MAX`. Value pins.
2. `get_committee_count_per_slot`: the `Uint64` chain `Uint64(len(active)) // SLOTS_PER_EPOCH
   // TARGET_COMMITTEE_SIZE` raises `ZeroDivisionError` for a zero `TARGET_COMMITTEE_SIZE`.
   The old `Nat` formula returned `max(1, 0) = 1`.
3. `get_pending_partial_withdrawals` and `get_builder_withdrawals`: the `Uint64`
   `MAX_WITHDRAWALS_PER_PAYLOAD - 1` raises the range fault for a zero preset value. The old
   `Nat` subtraction floored at `0` and the call returned no withdrawals.
4. `withdrawals[-1]` (Fulu and Gloas `process_withdrawals`): the plain negative index reads
   the last element, behind the `len(withdrawals) != 0` guard and in the full-payload branch.
   Value pins: the old `[size - 1]!` read named the same element on a nonempty list.
5. `get_inclusion_list_committee` (Heze): `indices[index % len(indices)]` raises only when a
   position forms. With `INCLUSION_LIST_COMMITTEE_SIZE = 0` and no committee members the
   comprehension is empty and returns. The old body threw on the empty concatenation first.
6. `is_head_weak` (Fulu): each committee's equivocator `sum` runs before the add to
   `head_weight`. A committee whose first equivocator would overflow the running weight and
   whose second is past the justified registry raises `IndexError` inside the `sum`. The old
   fold added each balance to the running weight and raised the range fault first.
7. `process_eth1_data`: `count(...) * 2 > Uint64(EPOCHS_PER_ETH1_VOTING_PERIOD) *
   SLOTS_PER_EPOCH` forms the checked product, which raises past `2^64 - 1` for a generic
   preset. The old `Nat` product never raised.
8. `get_blob_parameters`: the blob limit is a plain value from the schedule or the Electra
   constant. Value pins.
9. `get_next_sync_committee_indices`: Fulu's loop has no `assert`, so an empty active set
   raises `ZeroDivisionError` on `i % active_validator_count`. Gloas and Heze draw through
   `compute_balance_weighted_selection` and raise the assert class. The old Fulu body
   shared the Gloas selection and raised the assert class. A four-validator Fulu draw pins
   the exact indices.

The pins hash through the FFI `Sha256` (`fastHasherTag`). The Fulu and Gloas states are
FFI-backed boxes, and the Heze state is the plain record. So `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.PlainArithmeticPins

/-- `2^64 - 1`, the largest checked value. -/
private def maxU64 : Nat := 18446744073709551615

/-- A capped array (an `SSZList`) built from `a` when `a` fits the cap, and the empty one
otherwise. The fixtures below check their sizes. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- Whether a run returned exactly `b`. The error types carry no decidable equality, so the
value pins compare through this `Bool`. -/
private def okIs {ε α : Type} [BEq α] (r : Except ε α) (b : α) : Bool :=
  match r with
  | .ok a => a == b
  | .error _ => false

/-! ### 1. `integer_squareroot` -/

/-- The root of `n`, read back as a `Nat`. -/
private def rootOf (n : Nat) : Nat :=
  match CLUint64.ofNat? n with
  | .ok v => v.integerSquareroot.toPlainNat
  | .error _ => 0

/-- Small values and a perfect square's neighbours, as the pinned body computes them. -/
example : (rootOf 0, rootOf 1, rootOf 15, rootOf 16, rootOf 17, rootOf 1000000)
    = (0, 1, 3, 4, 4, 1000) := by native_decide

/-- `UINT64_MAX - 1` runs Newton's iteration; `UINT64_MAX` takes the special case. Both give
`UINT64_MAX_SQRT = 4294967295`. -/
example : (rootOf (maxU64 - 1), rootOf maxU64) = (4294967295, 4294967295) := by native_decide

section Fulu
open EthCLSpecs.Fulu

/-- A validator active from epoch `0`, never exiting, with the given effective balance. -/
private def fuluValidator (P : Preset) (eb : Gwei) (active : Bool := true) : @Validator P :=
  letI : Preset := P
  { (default : Validator) with
    activationEpoch := if active then 0 else Const.farFutureEpoch
    effectiveBalance := eb
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- A Fulu state at slot `0` over `n` validators with the given effective balance. -/
private def fuluState (P : Preset) (n : Nat) (eb : Gwei := 32000000000) (active : Bool := true) :
    SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      validators := capped (Array.replicate n (fuluValidator P eb active))
      balances := capped (Array.replicate n 32000000000) }

/-! ### 2. `get_committee_count_per_slot` -/

/-- The minimal preset with `TARGET_COMMITTEE_SIZE` replaced, its range premise re-proved. -/
@[reducible] private def targetSize (t : Nat) (h : t < 2 ^ 64 := by decide) : Preset :=
  { minimal with targetCommitteeSize := t, targetCommitteeSizeLt := h }

/-- The count at epoch `0` over `n` active validators, read back as a `Nat`. -/
private def countOf (P : Preset) (n : Nat) : Except ArithFault Nat :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  (getCommitteeCountPerSlot (fuluState P n) 0).map (·.toPlainNat)

/-- `TARGET_COMMITTEE_SIZE = 0`: `... // TARGET_COMMITTEE_SIZE` raises `ZeroDivisionError`.
The old `Nat` division returned `0`, and `max(1, …)` gave a count of `1`. -/
private def pinCountZeroTargetRaises : Bool :=
  match countOf (targetSize 0) 9 with
  | .error f => f.cause == .zeroDivision
  | .ok _ => false
example : pinCountZeroTargetRaises = true := by native_decide

/-- The nearby successes: eight validators give `max(1, 8 // 8 // 4) = 1`, sixty-four give
`64 // 8 // 4 = 2`, and seventeen with `TARGET_COMMITTEE_SIZE = 1` give `17 // 8 // 1 = 2`. -/
example : (countOf minimal 8, countOf minimal 64, countOf (targetSize 1) 17)
    = (.ok 1, .ok 2, .ok 2) := by native_decide

/-! ### 3 and 4. Fulu withdrawals -/

/-- A Fulu state at slot `8` over `n` fully withdrawable validators (an `0x01` credential,
withdrawable at epoch `0`, balance `32 ETH`), `next_withdrawal_index = 5`. With `idle`, the
validators never become withdrawable. -/
private def withdrawState (P : Preset) (n : Nat) (idle : Bool := false) :
    SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  let epoch : Epoch := if idle then Const.farFutureEpoch else 0
  let v : Validator :=
    { (default : Validator) with
      withdrawalCredentials := Vector.ofFn (fun i => if i.val = 0 then 1 else 0)
      effectiveBalance := 32000000000, exitEpoch := epoch, withdrawableEpoch := epoch }
  SSZ.FastBox
    { (default : @BeaconState P) with
      slot := 8
      validators := capped (Array.replicate n v)
      balances := capped (Array.replicate n 32000000000)
      nextWithdrawalIndex := 5 }

/-- Fulu `get_expected_withdrawals`, reading back each withdrawal's index and validator. -/
private def fuluExpected (P : Preset) (n : Nat) :
    Except StateTransitionError (List (Nat × Nat)) :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st := withdrawState P n
  match (getExpectedWithdrawals st : EStateM StateTransitionError State _).run st with
  | .ok (ws, _) _ => .ok (ws.toList.map fun w => (w.index.toPlainNat, w.validatorIndex.toPlainNat))
  | .error e _ => .error e

/-- The minimal preset with `MAX_WITHDRAWALS_PER_PAYLOAD` replaced, its range premise
re-proved. -/
@[reducible] private def maxWithdrawals (m : Nat) (h : m < 2 ^ 64 := by decide) : Preset :=
  { minimal with maxWithdrawalsPerPayload := m, maxWithdrawalsPerPayloadLt := h }

/-- `MAX_WITHDRAWALS_PER_PAYLOAD = 0`: the pending-partials limit's `Uint64` subtraction
`MAX_WITHDRAWALS_PER_PAYLOAD - 1` raises (`SSZValueError` at the pin). The old `Nat`
subtraction floored at `0`, and the call returned no withdrawals. -/
private def pinFuluPartialLimitRaises : Bool :=
  match fuluExpected (maxWithdrawals 0) 2 with
  | .error (.arithmetic _) => true
  | _ => false
example : pinFuluPartialLimitRaises = true := by native_decide

/-- `MAX_WITHDRAWALS_PER_PAYLOAD = 1`: the limit is `0`, and the sweep queues one withdrawal. -/
example : okIs (fuluExpected (maxWithdrawals 1) 2) [(5, 0)] = true := by native_decide

/-- Fulu `process_withdrawals` with the payload carrying the expected withdrawals. Reads back
the number applied, `next_withdrawal_index`, and `next_withdrawal_validator_index`. -/
private def fuluProcess (n : Nat) (idle : Bool := false) :
    Except StateTransitionError (Nat × Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st := withdrawState minimal n idle
  match (getExpectedWithdrawals st : EStateM StateTransitionError State _).run st with
  | .error e _ => .error e
  | .ok (ws, _) _ =>
    let payload : ExecutionPayload := { (default : ExecutionPayload) with withdrawals := capped ws }
    match (processWithdrawals payload : EStateM StateTransitionError State Unit).run st with
    | .ok _ post =>
      .ok (ws.size, (sszGet post nextWithdrawalIndex).toPlainNat,
        (sszGet post nextWithdrawalValidatorIndex).toPlainNat)
    | .error e _ => .error e

/-- Two withdrawals at indices `5` and `6`: `withdrawals[-1].index + 1 = 7`. The short payload
advances the validator cursor to `(0 + 16) % 2 = 0`. -/
example : okIs (fuluProcess 2) (2, 7, 0) = true := by native_decide

/-- Five withdrawable validators fill the payload at four: `withdrawals[-1]` is validator `3`
at index `8`, so the cursor resumes at `(3 + 1) % 5 = 4` and the index at `9`. -/
example : okIs (fuluProcess 5) (4, 9, 4) = true := by native_decide

/-- Nothing to withdraw: the `len(withdrawals) != 0` guard keeps the index at `5`, and the
cursor advances to `(0 + 16) % 3 = 1`. -/
example : okIs (fuluProcess 3 (idle := true)) (0, 5, 1) = true := by native_decide

/-! ### 6. `is_head_weak` -/

/-- The minimal preset with `TARGET_COMMITTEE_SIZE = 2`: thirty-two active validators give
two committees of two at slot `0`. -/
@[reducible] private def pairs : Preset := targetSize 2

/-- The root under which the pins store the head block and the justified checkpoint. -/
private def pinRoot : Root := Vector.replicate 32 9

/-- The head state's two slot-`0` committees under `pairs`. The pinned pyspec gives
`[[26, 8], [6, 22]]`. -/
private def pairsCommittees : List (List Nat) :=
  letI : Preset := pairs
  letI : HasherTag := fastHasherTag
  [(0 : CommitteeIndex), 1].map fun i =>
    match getBeaconCommittee (fuluState pairs 32) 0 i with
    | .ok c => c.toList.map (·.toPlainNat)
    | .error _ => []
example : pairsCommittees = [[26, 8], [6, 22]] := by native_decide

/-- A store whose head state holds thirty-two active validators and whose justified state
holds twenty-two inactive validators with `UINT64_MAX` effective balance (so the reorg
threshold and the attestation score see no active balance). `equivocators` are the store's
equivocating indices. Returns `is_head_weak`'s answer, or its reject. -/
private def headWeak (equivocators : Array ValidatorIndex) :
    Except StoreTransitionError Bool :=
  letI : Preset := pairs
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let head := fuluState pairs 32
  let justified := fuluState pairs 22 (CLUint64.trustedOfUInt64 18446744073709551615) false
  let jc : Checkpoint := { epoch := 0, root := pinRoot }
  let store : @Store pairs treeMap fastHasherTag :=
    { timeMs := 0, genesisTimeMs := 0
      justifiedCheckpoint := jc, finalizedCheckpoint := jc
      unrealizedJustifiedCheckpoint := jc, unrealizedFinalizedCheckpoint := jc
      proposerBoostRoot := fcZeroRoot
      equivocatingIndices := equivocators
      blocks := FcMap.insert FcMap.empty pinRoot (default : BeaconBlock)
      blockStates := FcMap.insert FcMap.empty pinRoot head
      blockTimeliness := FcMap.empty
      checkpointStates := FcMap.insert FcMap.empty jc justified
      latestMessages := FcMap.empty
      unrealizedJustifications := FcMap.empty }
  match (isHeadWeak (map := treeMap) store pinRoot :
      EStateM StoreTransitionError (@Store pairs treeMap fastHasherTag) Bool).run store with
  | .ok b _ => .ok b
  | .error e _ => .error e

/-- Equivocators `8`, `6`, `22`: committee `0` sums validator `8` to `UINT64_MAX`, and
`head_weight` becomes `UINT64_MAX`. Committee `1` sums validator `6` to `UINT64_MAX`, then
reads validator `22`, past the twenty-two-validator justified registry: `IndexError`. The old
fold added validator `6`'s balance to the running weight first and raised the range fault. -/
private def pinHeadWeakSumBeforeAdd : Bool :=
  match headWeak #[8, 6, 22] with
  | .error (.transition (.outOfBounds _ _)) => true
  | _ => false
example : pinHeadWeakSumBeforeAdd = true := by native_decide

/-- Equivocators `8` and `6`: both committee sums reach `UINT64_MAX`, and the add of the second
to `head_weight` raises the range fault. -/
private def pinHeadWeakAddRaises : Bool :=
  match headWeak #[8, 6] with
  | .error (.transition (.arithmetic _)) => true
  | _ => false
example : pinHeadWeakAddRaises = true := by native_decide

/-- The nearby successes: equivocator `8` alone gives `head_weight = UINT64_MAX`, not below
the threshold; no equivocator gives `0`, which is below it. -/
example : (okIs (headWeak #[8]) false && okIs (headWeak #[]) true) = true := by native_decide

/-! ### 7. `process_eth1_data` -/

/-- Runs Fulu `process_eth1_data` on the default state with one vote for an `Eth1Data` of
deposit count `7`, reading back the state's `eth1_data.deposit_count`. -/
private def eth1Adopted (P : Preset) : Except StateTransitionError Nat :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let st : State := SSZ.FastBox (default : BeaconState)
  let body : BeaconBlockBody :=
    { (default : BeaconBlockBody) with eth1Data := { (default : Eth1Data) with depositCount := 7 } }
  match (processEth1Data body : EStateM StateTransitionError State Unit).run st with
  | .ok _ post => .ok (sszGet post eth1Data).depositCount.toPlainNat
  | .error e _ => .error e

/-- `EPOCHS_PER_ETH1_VOTING_PERIOD = 2^61`: the checked product
`Uint64(EPOCHS_PER_ETH1_VOTING_PERIOD) * SLOTS_PER_EPOCH` is `2^64` and raises
(`SSZValueError` at the pin). The old `Nat` product never raised, and the vote stayed
unadopted. -/
private def pinEth1PeriodProductRaises : Bool :=
  match eth1Adopted { minimal with
      epochsPerEth1VotingPeriod := 2305843009213693952,
      epochsPerEth1VotingPeriodLt := by decide } with
  | .error (.arithmetic _) => true
  | _ => false
example : pinEth1PeriodProductRaises = true := by native_decide

/-- The nearby successes: at `2^61 - 1` the product fits, and one vote does not reach it; with
one slot per epoch and a one-epoch period, one vote doubles past the product of `1` and is
adopted. -/
example :
    (okIs (eth1Adopted { minimal with
       epochsPerEth1VotingPeriod := 2305843009213693951,
       epochsPerEth1VotingPeriodLt := by decide }) 0 &&
     okIs (eth1Adopted { minimal with
       epochsPerEth1VotingPeriod := 1, epochsPerEth1VotingPeriodLt := by decide,
       slotsPerEpoch := 1, slotsPerEpochPos := by decide, slotsPerEpochLt := by decide }) 7)
      = true := by
  native_decide

/-! ### 8. `get_blob_parameters` -/

/-- The mainnet schedule's limits, read back as `Int`: the Electra fallback before the first
entry, then each entry from its epoch on. -/
private def mainnetBlobLimits : List (Option Int) :=
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  [0, 412672, 419071, 419072].map fun (e : Nat) =>
    match CLUint64.ofNat? e with
    | .ok epoch => some (getBlobParameters epoch).maxBlobsPerBlock.toPlainInt
    | .error _ => none
example : mainnetBlobLimits = [some 9, some 15, some 15, some 21] := by native_decide

/-! ### 9. `get_next_sync_committee_indices` (Fulu) -/

/-- Fulu's sync-committee draw at slot `0` over `n` active validators, read back as plain
indices. -/
private def fuluSyncIndices (n : Nat) : Except StateTransitionError (List Nat) :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  (getNextSyncCommitteeIndices (fuluState minimal n)).map (·.toList.map (·.toPlainNat))

/-- An empty active set: the loop's first `i % active_validator_count` raises
`ZeroDivisionError`. The old body went through `compute_balance_weighted_selection` and
raised the assert class on its `assert total > 0`, which Fulu's pyspec does not have. -/
private def pinFuluSyncEmptyRaises : Bool :=
  match fuluSyncIndices 0 with
  | .error (.zeroDivision _) => true
  | _ => false
example : pinFuluSyncEmptyRaises = true := by native_decide

/-- Four active validators: the pinned pyspec draws these 32 indices. -/
example : okIs (fuluSyncIndices 4)
    [2, 2, 0, 1, 1, 1, 1, 2, 1, 3, 2, 2, 0, 0, 3, 0, 3, 2, 1, 2, 3, 2, 3, 0, 3, 0, 1, 1, 3, 2,
      0, 2] = true := by native_decide

end Fulu

section Gloas
open EthCLSpecs.Gloas

/-- A Gloas state at slot `8` over `n` fully withdrawable validators, `next_withdrawal_index
= 5`. The default bid and the default latest block hash agree, so `process_withdrawals` runs.
With `idle`, the validators never become withdrawable. -/
private def gloasWithdrawState (P : Preset) (n : Nat) (idle : Bool := false) :
    SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  let epoch : Epoch := if idle then Const.farFutureEpoch else 0
  let v : Validator :=
    { (default : Validator) with
      withdrawalCredentials := Vector.ofFn (fun i => if i.val = 0 then 1 else 0)
      effectiveBalance := 32000000000, exitEpoch := epoch, withdrawableEpoch := epoch }
  SSZ.FastBox
    { (default : @BeaconState P) with
      slot := 8
      validators := ⟨Array.replicate n v⟩
      balances := ⟨Array.replicate n 32000000000⟩
      nextWithdrawalIndex := 5 }

/-- Gloas `process_withdrawals`: reads back the committed withdrawal count,
`next_withdrawal_index`, and `next_withdrawal_validator_index`. -/
private def gloasProcess (n : Nat) (idle : Bool := false) :
    Except StateTransitionError (Nat × Nat × Nat) :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  match (processWithdrawals : EStateM StateTransitionError State Unit).run
      (gloasWithdrawState minimal n idle) with
  | .ok _ post =>
    .ok ((sszGet post payloadExpectedWithdrawals).val.size,
      (sszGet post nextWithdrawalIndex).toPlainNat,
      (sszGet post nextWithdrawalValidatorIndex).toPlainNat)
  | .error e _ => .error e

/-- `withdrawals[-1]` after two withdrawals, after a full payload, and the guarded empty
case: the same values the Fulu pins read. -/
example : (okIs (gloasProcess 2) (2, 7, 0) && okIs (gloasProcess 5) (4, 9, 4) &&
    okIs (gloasProcess 3 (idle := true)) (0, 5, 1)) = true := by native_decide

/-- Gloas `get_builder_withdrawals` from index `5`, reading back the number queued. -/
private def builderWithdrawals (P : Preset) : Except StateTransitionError Nat :=
  letI : Preset := P
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.ffi
  let st := gloasWithdrawState P 1
  match (getBuilderWithdrawals 5 #[] : EStateM StateTransitionError State _).run st with
  | .ok (ws, _, _) _ => .ok ws.size
  | .error e _ => .error e

/-- `MAX_WITHDRAWALS_PER_PAYLOAD = 0`: `withdrawals_limit = MAX_WITHDRAWALS_PER_PAYLOAD - 1`
raises (`SSZValueError` at the pin). The old `Nat` subtraction floored at `0`. -/
private def pinGloasBuilderLimitRaises : Bool :=
  match builderWithdrawals
      { minimal with maxWithdrawalsPerPayload := 0, maxWithdrawalsPerPayloadLt := by decide } with
  | .error (.arithmetic _) => true
  | _ => false
example : pinGloasBuilderLimitRaises = true := by native_decide

/-- `MAX_WITHDRAWALS_PER_PAYLOAD = 1`: the limit is `0`, and the empty builder queue
yields no withdrawal. -/
example : okIs (builderWithdrawals
    { minimal with maxWithdrawalsPerPayload := 1, maxWithdrawalsPerPayloadLt := by decide }) 0
    = true := by
  native_decide

/-! ### 9. `get_next_sync_committee_indices` (Gloas) -/

/-- An empty active set: Gloas draws through `compute_balance_weighted_selection`, whose
`assert total > 0` raises the assert class. -/
private def pinGloasSyncEmptyAsserts : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match getNextSyncCommitteeIndices (SSZ.FastBox (default : BeaconState) : State) with
  | .error (.assert _) => true
  | _ => false
example : pinGloasSyncEmptyAsserts = true := by native_decide

end Gloas

section Heze
open EthCLSpecs.Heze

/-! ### 5. `get_inclusion_list_committee` -/

/-- `cyclicSample` over an empty source: the first position's `%` raises
`ZeroDivisionError`; with no positions, the comprehension is empty and returns. A nonempty
source wraps as `index % 3`. -/
private def pinCyclicSample : Bool :=
  (match cyclicSample (#[] : Array Nat) 3 with
    | .error (.zeroDivision _) => true
    | _ => false) &&
  okIs ((cyclicSample (#[] : Array Nat) 0).map (·.toList)) [] &&
  okIs ((cyclicSample #[10, 20, 30] 8).map (·.toList)) [10, 20, 30, 10, 20, 30, 10, 20]
example : pinCyclicSample = true := by native_decide

/-- `INCLUSION_LIST_COMMITTEE_SIZE = 0` over a zero-validator state: slot `0`'s committee is
empty, and the comprehension forms no position, so the accessor returns the empty committee.
The old body threw `ZeroDivisionError` on the empty concatenation before sampling. -/
private def pinEmptyCommitteeZeroSizeReturns : Bool :=
  letI : Preset := { minimal with inclusionListCommitteeSize := 0 }
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := (default : BeaconState)
  match (getInclusionListCommittee (StoreTransition := Except StoreTransitionError) state 0) with
  | .ok c => c.toList.isEmpty
  | .error _ => false
example : pinEmptyCommitteeZeroSizeReturns = true := by native_decide

/-! ### 9. `get_next_sync_committee_indices` (Heze) -/

/-- An empty active set: Heze inherits the Gloas draw, so the selection's
`assert total > 0` raises the assert class, as the pinned Heze pyspec does. -/
private def pinHezeSyncEmptyAsserts : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match getNextSyncCommitteeIndices (default : State) with
  | .error (.assert _) => true
  | _ => false
example : pinHezeSyncEmptyAsserts = true := by native_decide

end Heze

end EthCLSpecs.Tests.PlainArithmeticPins
