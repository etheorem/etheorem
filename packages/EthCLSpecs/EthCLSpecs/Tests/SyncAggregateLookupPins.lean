import EthCLSpecs.Fulu
import EthCLSpecs.Gloas
import EthCLSpecs.Heze

/-!
# `EthCLSpecs.Tests.SyncAggregateLookupPins`: the sync-committee participant lookup

Pins for the committee lookup of `process_sync_aggregate` (`fulu/minimal.py:4515-4518`; Gloas
and Heze restate the body unchanged). The pinned body builds the whole `committee_indices` list
before the reward loop:

```python
all_pubkeys = [validator.pubkey for validator in state.validators]
committee_indices = [
    ValidatorIndex(all_pubkeys.index(pubkey)) for pubkey in state.current_sync_committee.pubkeys
]
```

`list.index` raises a plain Python `ValueError` on a pubkey that no validator carries. The
Lean body raises `.notInList` there. Three pin groups run in every fork, at both presets:

1. Lookup miss: committee position `5` holds a pubkey that no validator carries. The run
   raises `.notInList`. Its pair, every committee pubkey present, applies the rewards.
2. Fault order: validator `0` holds `UINT64_MAX`, so its participant reward at position `0`
   overflows. The miss sits at the last position. The pinned body resolves every position
   first, so the lookup fault wins over the overflow. Its pair, the same state with every
   pubkey present, raises the overflow (`.arithmetic`, an `SSZValueError` at the pin).
3. Inheritance: Gloas and Heze `inherit processSyncAggregate`, so their pins give the same
   answers as Fulu's.

The fixture holds four active `32 ETH` validators with pubkeys `0x01…` to `0x04…`, at slot
`1`. Committee position `i` holds the pubkey of validator `i % 4`, and bit `i` is set when
`i % 3 = 0`. `CryptoBackend.verifyOff` accepts the aggregate signature. Every expected
answer is the pinned pyspec's (1.7.0b4) on the same fixture: `ValueError` for both miss
cases, `SSZValueError` for the overflow, and the balances below for the success.
`State` is FFI-backed, so `native_decide`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.SyncAggregateLookupPins

/-- The fixture variants. -/
inductive Case where
  /-- Every committee pubkey belongs to a validator. -/
  | present
  /-- Position `5` holds an unknown pubkey. -/
  | missing
  /-- Validator `0` holds `UINT64_MAX`, and the last position holds an unknown pubkey. -/
  | order
  /-- Validator `0` holds `UINT64_MAX`, and every committee pubkey is present. -/
  | overflow

/-- What a run surfaced: the post-state balances, or the reject class. The class is the
point of these pins, so the diagnostic string is dropped. -/
inductive Outcome where
  | balances (bs : List Nat)
  | notInList
  | arithmetic
  | other
  deriving DecidableEq

/-- The pubkey whose 48 bytes are all `b`. -/
private def pubkey (b : UInt8) : Vector UInt8 48 := Vector.replicate 48 b

/-- The pubkey byte at committee position `i` of `n`: validator `i % 4`, or the unknown `9`
at the position the case names. -/
private def committeeKeyByte (c : Case) (n i : Nat) : UInt8 :=
  match c with
  | .missing => if i = 5 then 9 else (i % 4 + 1).toUInt8
  | .order => if i + 1 = n then 9 else (i % 4 + 1).toUInt8
  | _ => (i % 4 + 1).toUInt8

/-- The balance of validator `i`: `UINT64_MAX` for validator `0` in the overflow cases,
`32 ETH` otherwise. -/
private def balanceOf (c : Case) (i : Nat) : Nat :=
  match c, i with
  | .order, 0 | .overflow, 0 => 18446744073709551615
  | _, _ => 32000000000

/-- The participation bits as a number: bit `i` is set when `i % 3 = 0`. -/
private def everyThirdBit (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => if i % 3 = 0 then acc ||| (1 <<< i) else acc) 0

/-- A fixture `Nat` as a checked word. Every fixture value fits, so the `0` fallback never
fires. -/
private def u64 (n : Nat) : CLUint64 :=
  match CLUint64.ofNat? n with
  | .ok v => v
  | .error _ => 0

/-- A capped array built from `a` when `a` fits the cap, and the empty one otherwise. -/
private def capped {α : Type} {cap : Nat} (a : Array α) : { xs : Array α // xs.size ≤ cap } :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩

/-! ## Fulu -/

namespace Fulu

open EthCLSpecs.Fulu

/-- Validator `b - 1`: active, `32 ETH` effective balance, pubkey `b`. -/
private def validator (P : Preset) (b : UInt8) : @Validator P :=
  letI : Preset := P
  { (default : @Validator P) with
    pubkey := pubkey b
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- The fixture state of case `c` at preset `P`. -/
private def fixture (P : Preset) (c : Case) : SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      slot := 1
      validators := capped ((#[1, 2, 3, 4] : Array UInt8).map (validator P))
      balances := capped ((Array.range 4).map fun i => u64 (balanceOf c i))
      currentSyncCommittee :=
        { pubkeys := Vector.ofFn fun i => pubkey (committeeKeyByte c Const.syncCommitteeSize i.val)
          aggregatePubkey := default } }

/-- Runs Fulu `process_sync_aggregate` on case `c` at preset `P` and config `C`. -/
private def run (P : Preset) (C : Config) (c : Case) : Outcome :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  let agg : @SyncAggregate P :=
    { syncCommitteeBits := ⟨BitVec.ofNat _ (everyThirdBit Const.syncCommitteeSize)⟩
      syncCommitteeSignature := default }
  match (processSyncAggregate agg : EStateM StateTransitionError
      (SSZ.Box Sha256 (@BeaconState P)) Unit).run (fixture P c) with
  | .ok _ post => .balances ((SSZ.Box.view post).balances.val.toList.map (·.toPlainNat))
  | .error (.notInList _) _ => .notInList
  | .error (.arithmetic _) _ => .arithmetic
  | .error _ _ => .other

/-! ### 1. Lookup miss -/

/-- An unknown pubkey at position `5` raises the lookup fault. -/
example : run minimal minimalConfig .missing = .notInList := by native_decide
example : run mainnet mainnetConfig .missing = .notInList := by native_decide

/-- Every committee pubkey present: the rewards apply. -/
example : run minimal minimalConfig .present =
    .balances [31999998799, 31999988820, 31999994410, 31999994410] := by native_decide
example : run mainnet mainnetConfig .present =
    .balances [31999999220, 31999998108, 31999998194, 31999998194] := by native_decide

/-! ### 2. Fault order -/

/-- The miss at the last position wins over the overflow at position `0`. -/
example : run minimal minimalConfig .order = .notInList := by native_decide
example : run mainnet mainnetConfig .order = .notInList := by native_decide

/-- Every pubkey present: position `0`'s overflow surfaces. -/
example : run minimal minimalConfig .overflow = .arithmetic := by native_decide
example : run mainnet mainnetConfig .overflow = .arithmetic := by native_decide

end Fulu

/-! ## Gloas -/

namespace Gloas

open EthCLSpecs.Gloas

/-- Validator `b - 1`: active, `32 ETH` effective balance, pubkey `b`. -/
private def validator (P : Preset) (b : UInt8) : @Validator P :=
  letI : Preset := P
  { (default : @Validator P) with
    pubkey := pubkey b
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- The fixture state of case `c` at preset `P`. The registry lists are progressive, so they
take the arrays without a cap. -/
private def fixture (P : Preset) (c : Case) : SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      slot := 1
      validators := ⟨(#[1, 2, 3, 4] : Array UInt8).map (validator P)⟩
      balances := ⟨(Array.range 4).map fun i => u64 (balanceOf c i)⟩
      currentSyncCommittee :=
        { pubkeys := Vector.ofFn fun i => pubkey (committeeKeyByte c Const.syncCommitteeSize i.val)
          aggregatePubkey := default } }

/-- Runs Gloas `process_sync_aggregate` on case `c` at preset `P` and config `C`. -/
private def run (P : Preset) (C : Config) (c : Case) : Outcome :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  let agg : @SyncAggregate P :=
    { syncCommitteeBits := ⟨BitVec.ofNat _ (everyThirdBit Const.syncCommitteeSize)⟩
      syncCommitteeSignature := default }
  match (processSyncAggregate agg : EStateM StateTransitionError
      (SSZ.Box Sha256 (@BeaconState P)) Unit).run (fixture P c) with
  | .ok _ post => .balances ((SSZ.Box.view post).balances.val.toList.map (·.toPlainNat))
  | .error (.notInList _) _ => .notInList
  | .error (.arithmetic _) _ => .arithmetic
  | .error _ _ => .other

example : run minimal minimalConfig .missing = .notInList := by native_decide
example : run mainnet mainnetConfig .missing = .notInList := by native_decide
example : run minimal minimalConfig .present =
    .balances [31999998799, 31999988820, 31999994410, 31999994410] := by native_decide
example : run mainnet mainnetConfig .present =
    .balances [31999999220, 31999998108, 31999998194, 31999998194] := by native_decide
example : run minimal minimalConfig .order = .notInList := by native_decide
example : run mainnet mainnetConfig .order = .notInList := by native_decide
example : run minimal minimalConfig .overflow = .arithmetic := by native_decide
example : run mainnet mainnetConfig .overflow = .arithmetic := by native_decide

end Gloas

/-! ## Heze -/

namespace Heze

open EthCLSpecs.Heze

/-- Validator `b - 1`: active, `32 ETH` effective balance, pubkey `b`. -/
private def validator (P : Preset) (b : UInt8) : @Validator P :=
  letI : Preset := P
  { (default : @Validator P) with
    pubkey := pubkey b
    effectiveBalance := 32000000000
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- The fixture state of case `c` at preset `P`. The registry lists are progressive, so they
take the arrays without a cap. -/
private def fixture (P : Preset) (c : Case) : SSZ.Box Sha256 (@BeaconState P) :=
  letI : Preset := P
  SSZ.FastBox
    { (default : @BeaconState P) with
      slot := 1
      validators := ⟨(#[1, 2, 3, 4] : Array UInt8).map (validator P)⟩
      balances := ⟨(Array.range 4).map fun i => u64 (balanceOf c i)⟩
      currentSyncCommittee :=
        { pubkeys := Vector.ofFn fun i => pubkey (committeeKeyByte c Const.syncCommitteeSize i.val)
          aggregatePubkey := default } }

/-- Runs Heze `process_sync_aggregate` on case `c` at preset `P` and config `C`. -/
private def run (P : Preset) (C : Config) (c : Case) : Outcome :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  let agg : @SyncAggregate P :=
    { syncCommitteeBits := ⟨BitVec.ofNat _ (everyThirdBit Const.syncCommitteeSize)⟩
      syncCommitteeSignature := default }
  match (processSyncAggregate agg : EStateM StateTransitionError
      (SSZ.Box Sha256 (@BeaconState P)) Unit).run (fixture P c) with
  | .ok _ post => .balances ((SSZ.Box.view post).balances.val.toList.map (·.toPlainNat))
  | .error (.notInList _) _ => .notInList
  | .error (.arithmetic _) _ => .arithmetic
  | .error _ _ => .other

example : run minimal minimalConfig .missing = .notInList := by native_decide
example : run mainnet mainnetConfig .missing = .notInList := by native_decide
example : run minimal minimalConfig .present =
    .balances [31999998799, 31999988820, 31999994410, 31999994410] := by native_decide
example : run mainnet mainnetConfig .present =
    .balances [31999999220, 31999998108, 31999998194, 31999998194] := by native_decide
example : run minimal minimalConfig .order = .notInList := by native_decide
example : run mainnet mainnetConfig .order = .notInList := by native_decide
example : run minimal minimalConfig .overflow = .arithmetic := by native_decide
example : run mainnet mainnetConfig .overflow = .arithmetic := by native_decide

end Heze

end EthCLSpecs.Tests.SyncAggregateLookupPins
