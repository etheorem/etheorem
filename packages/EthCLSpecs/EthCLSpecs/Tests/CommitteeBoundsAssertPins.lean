import EthCLSpecs.Fulu
import EthCLSpecs.Gloas
import EthCLSpecs.Heze

/-!
# `EthCLSpecs.Tests.CommitteeBoundsAssertPins`: the shuffled-index assert of `compute_committee`

Pins for the permutation read of `compute_committee` (`fulu/minimal.py:1310-1321`; Gloas and
Heze inherit the body). The comprehension calls `compute_shuffled_index` for each position of
`range(start, end)`, and that function asserts its bound first (`fulu/minimal.py:1278-1283`):

```python
def compute_shuffled_index(index: Uint64, index_count: Uint64, seed: Bytes32) -> Uint64:
    assert index < index_count
    return compute_shuffled_permutation(index_count, seed)[index]
```

A committee index at or past `count` with a nonempty range raises `AssertionError` at the
first position. The Lean body raises `.assert` there. Four pin groups run in every fork, at
both presets:

1. `compute_committee` over the indices `0 … 7` and a zero seed. Index `2` of count `2`
   raises the assert. Its pair, index `1 = count - 1`, returns the last committee. Index `16`
   of count `16` is out of range too, but its range `[8, 8)` is empty, so the call returns
   the empty committee and raises nothing.
2. Fault order: index `2^61 - 1` of count `1`. The stop product `8 * 2^61` raises the checked
   range fault before any position runs, so `.arithmetic` wins over the assert.
3. `get_beacon_committee` on a state with `SLOTS_PER_EPOCH` active validators, so each slot
   has one committee of one member and `count = SLOTS_PER_EPOCH`. Slot `0` with committee
   index `SLOTS_PER_EPOCH` raises the assert. Its pair, slot `SLOTS_PER_EPOCH - 1` with
   committee index `0`, reads the last committee (`count - 1`).
4. `get_attesting_indices`, the path a fork-choice attestation takes, on the same state. An
   attestation at slot `SLOTS_PER_EPOCH - 1` with committee bit `1` reaches committee index
   `count`, so it raises the assert. Its pair, committee bit `0`, returns the one member.

Every expected answer is the pinned pyspec's (1.7.0b4) on the same fixture. Under the
defaulting read that the assert replaces, every assert pin returns a committee instead
(`perm[i]!` past the end reads `0`), so each one fails there.
`State` is FFI-backed, so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.CommitteeBoundsAssertPins

/-- What a run surfaced: the committee members as plain numbers, or the reject class. The
class is the point of these pins, so the diagnostic string is dropped. -/
inductive Outcome where
  | members (vs : List Nat)
  | assert
  | arithmetic
  | other
  deriving DecidableEq

/-- Reads a run's result as an `Outcome`. -/
private def outcomeOf (r : Except StateTransitionError (Array CLUint64)) : Outcome :=
  match r with
  | .ok vs => .members (vs.toList.map (·.toPlainNat))
  | .error (.assert _) => .assert
  | .error (.arithmetic _) => .arithmetic
  | .error _ => .other

/-- A fixture `Nat` as a checked word. Every fixture value fits, so the `0` fallback never
fires. -/
private def u64 (n : Nat) : CLUint64 :=
  match CLUint64.ofNat? n with
  | .ok v => v
  | .error _ => 0

/-- The indices `0 … 7`. -/
private def indices8 : Array CLUint64 := (Array.range 8).map u64

/-- A capped array built from `a` when `a` fits the cap, and the empty one otherwise. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- `2^61 - 1`: `8 * (index + 1)` is `2^64`, one past the `Uint64` range. -/
private def orderIndex : Nat := 2305843009213693951

/-! ## Fulu -/

namespace Fulu

open EthCLSpecs.Fulu

/-- Runs Fulu `compute_committee` over `indices8` and a zero seed at preset `P`. -/
private def committee (P : Preset) (index count : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  outcomeOf (computeCommittee indices8 (Vector.replicate 32 0) (u64 index) (u64 count))

/-- An active `32 ETH` validator. -/
private def validator (P : Preset) : @Validator P :=
  letI : Preset := P
  { (default : @Validator P) with
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- A state at slot `0` with `SLOTS_PER_EPOCH` active validators. -/
private def fixture (P : Preset) : SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      validators := capped (Array.replicate Const.slotsPerEpoch (validator P))
      balances := capped (Array.replicate Const.slotsPerEpoch (u64 32000000000)) }

/-- Runs Fulu `get_beacon_committee` on the fixture at preset `P`. -/
private def beacon (P : Preset) (slot index : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  outcomeOf (getBeaconCommittee (fixture P) (u64 slot) (u64 index))

/-- Runs Fulu `get_attesting_indices` on the fixture at preset `P`: an attestation at slot
`SLOTS_PER_EPOCH - 1` with committee bit `bit` and one set aggregation bit. -/
private def attesting (P : Preset) (bit : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  let att : @Attestation P :=
    { (default : @Attestation P) with
      aggregationBits := capped #[true]
      data := { (default : @AttestationData P) with slot := u64 (Const.slotsPerEpoch - 1) }
      committeeBits := bitSet default bit true }
  outcomeOf (getAttestingIndices (fixture P) att)

/-! ### 1. `compute_committee` -/

/-- Index `2` of count `2`: the first position `8` is past the registry, so the assert raises. -/
example : committee minimal 2 2 = .assert := by native_decide
example : committee mainnet 2 2 = .assert := by native_decide

/-- Index `1 = count - 1`: the last committee, the slice `[4, 8)` of the shuffle. -/
example : committee minimal 1 2 = .members [6, 5, 3, 7] := by native_decide
example : committee mainnet 1 2 = .members [7, 2, 1, 5] := by native_decide

/-- Index `16` of count `16`: an empty range, so no position runs and nothing raises. -/
example : committee minimal 16 16 = .members [] := by native_decide
example : committee mainnet 16 16 = .members [] := by native_decide

/-! ### 2. Fault order -/

/-- The checked stop product raises before the first position's assert. -/
example : committee minimal orderIndex 1 = .arithmetic := by native_decide
example : committee mainnet orderIndex 1 = .arithmetic := by native_decide

/-! ### 3. `get_beacon_committee` -/

/-- Committee index `count` at slot `0`: the assert raises. -/
example : beacon minimal 0 8 = .assert := by native_decide
example : beacon mainnet 0 32 = .assert := by native_decide

/-- Committee index `count - 1` (the last slot's committee): one member. -/
example : beacon minimal 7 0 = .members [2] := by native_decide
example : beacon mainnet 31 0 = .members [28] := by native_decide

/-! ### 4. `get_attesting_indices` -/

/-- Committee bit `1` at the last slot reaches committee index `count`: the assert raises. -/
example : attesting minimal 1 = .assert := by native_decide
example : attesting mainnet 1 = .assert := by native_decide

/-- Committee bit `0` reaches committee index `count - 1`: its one member attests. -/
example : attesting minimal 0 = .members [2] := by native_decide
example : attesting mainnet 0 = .members [28] := by native_decide

end Fulu

/-! ## Gloas -/

namespace Gloas

open EthCLSpecs.Gloas

/-- Runs Gloas `compute_committee` over `indices8` and a zero seed at preset `P`. -/
private def committee (P : Preset) (index count : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  outcomeOf (computeCommittee indices8 (Vector.replicate 32 0) (u64 index) (u64 count))

/-- An active `32 ETH` validator. -/
private def validator (P : Preset) : @Validator P :=
  letI : Preset := P
  { (default : @Validator P) with
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- A state at slot `0` with `SLOTS_PER_EPOCH` active validators. The registry lists are
progressive, so they take the arrays without a cap. -/
private def fixture (P : Preset) : SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      validators := ⟨Array.replicate Const.slotsPerEpoch (validator P)⟩
      balances := ⟨Array.replicate Const.slotsPerEpoch (u64 32000000000)⟩ }

/-- Runs Gloas `get_beacon_committee` on the fixture at preset `P`. -/
private def beacon (P : Preset) (slot index : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  outcomeOf (getBeaconCommittee (fixture P) (u64 slot) (u64 index))

/-- Runs Gloas `get_attesting_indices`, as in the Fulu group. -/
private def attesting (P : Preset) (bit : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  let att : @Attestation P :=
    { (default : @Attestation P) with
      aggregationBits := ⟨#[true]⟩
      data := { (default : @AttestationData P) with slot := u64 (Const.slotsPerEpoch - 1) }
      committeeBits := bitSet default bit true }
  outcomeOf (getAttestingIndices (fixture P) att)

example : committee minimal 2 2 = .assert := by native_decide
example : committee mainnet 2 2 = .assert := by native_decide
example : committee minimal 1 2 = .members [6, 5, 3, 7] := by native_decide
example : committee mainnet 1 2 = .members [7, 2, 1, 5] := by native_decide
example : committee minimal 16 16 = .members [] := by native_decide
example : committee mainnet 16 16 = .members [] := by native_decide
example : committee minimal orderIndex 1 = .arithmetic := by native_decide
example : committee mainnet orderIndex 1 = .arithmetic := by native_decide
example : beacon minimal 0 8 = .assert := by native_decide
example : beacon mainnet 0 32 = .assert := by native_decide
example : beacon minimal 7 0 = .members [2] := by native_decide
example : beacon mainnet 31 0 = .members [28] := by native_decide
example : attesting minimal 1 = .assert := by native_decide
example : attesting mainnet 1 = .assert := by native_decide
example : attesting minimal 0 = .members [2] := by native_decide
example : attesting mainnet 0 = .members [28] := by native_decide

end Gloas

/-! ## Heze -/

namespace Heze

open EthCLSpecs.Heze

/-- Runs Heze `compute_committee` over `indices8` and a zero seed at preset `P`. -/
private def committee (P : Preset) (index count : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  outcomeOf (computeCommittee indices8 (Vector.replicate 32 0) (u64 index) (u64 count))

/-- An active `32 ETH` validator. -/
private def validator (P : Preset) : @Validator P :=
  letI : Preset := P
  { (default : @Validator P) with
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- A state at slot `0` with `SLOTS_PER_EPOCH` active validators, as in the Gloas group. -/
private def fixture (P : Preset) : SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      validators := ⟨Array.replicate Const.slotsPerEpoch (validator P)⟩
      balances := ⟨Array.replicate Const.slotsPerEpoch (u64 32000000000)⟩ }

/-- Runs Heze `get_beacon_committee` on the fixture at preset `P`. -/
private def beacon (P : Preset) (slot index : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  outcomeOf (getBeaconCommittee (fixture P) (u64 slot) (u64 index))

/-- Runs Heze `get_attesting_indices`, as in the Fulu group. -/
private def attesting (P : Preset) (bit : Nat) : Outcome :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  let att : @Attestation P :=
    { (default : @Attestation P) with
      aggregationBits := ⟨#[true]⟩
      data := { (default : @AttestationData P) with slot := u64 (Const.slotsPerEpoch - 1) }
      committeeBits := bitSet default bit true }
  outcomeOf (getAttestingIndices (fixture P) att)

example : committee minimal 2 2 = .assert := by native_decide
example : committee mainnet 2 2 = .assert := by native_decide
example : committee minimal 1 2 = .members [6, 5, 3, 7] := by native_decide
example : committee mainnet 1 2 = .members [7, 2, 1, 5] := by native_decide
example : committee minimal 16 16 = .members [] := by native_decide
example : committee mainnet 16 16 = .members [] := by native_decide
example : committee minimal orderIndex 1 = .arithmetic := by native_decide
example : committee mainnet orderIndex 1 = .arithmetic := by native_decide
example : beacon minimal 0 8 = .assert := by native_decide
example : beacon mainnet 0 32 = .assert := by native_decide
example : beacon minimal 7 0 = .members [2] := by native_decide
example : beacon mainnet 31 0 = .members [28] := by native_decide
example : attesting minimal 1 = .assert := by native_decide
example : attesting mainnet 1 = .assert := by native_decide
example : attesting minimal 0 = .members [2] := by native_decide
example : attesting mainnet 0 = .members [28] := by native_decide

end Heze

end EthCLSpecs.Tests.CommitteeBoundsAssertPins
