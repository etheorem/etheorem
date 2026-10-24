import EthCLSpecs.Fulu.Committees
import EthCLLib.Proofs.StoreRun

/-!
# `EthCLSpecs.Tests.FuluCommitteesPins`: the shuffle and committee pins

The pins for the Fulu shuffle, committee and selection bodies. Each pin states what the
pinned pyspec (`v1.7.0-alpha.11`, minimal preset) returns or raises on the same input. The
probe scripts that produced the pyspec side are `.tmp/spike/shuffle_edges_probe{,2}.py` and
`.tmp/spike/pin_values_probe.py` (local, not committed). The seed is 32 bytes of `0x01`
throughout.

Two kinds of pin:

* reject pins: the body raises where the pyspec raises, with the same reject kind;
* value pins: the body returns the pyspec's list for an ordinary input.

The value pins hash through the FFI SHA-256, so they close by `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluCommitteesPins

open EthCLSpecs.Fulu
open EthCLLib.Proofs (pureState)

/-- The result raised the uncaught-fault kind (`.arithmetic`). -/
private def isArith {α : Type} : Except StateTransitionError α → Bool
  | .error (.arithmetic _) => true
  | _ => false

/-- The result raised the expected-rejection kind (`.assert`). -/
private def isAssert {α : Type} : Except StateTransitionError α → Bool
  | .error (.assert _) => true
  | _ => false

/-- The result succeeded with exactly `xs`. -/
private def okList : Except StateTransitionError (Array UInt64) → List Nat → Bool
  | .ok a, xs => a.toList.map UInt64.toNat == xs
  | .error _, _ => false

private def seed : ByteArray := ⟨Array.replicate 32 1⟩

private def range (n : Nat) : Array UInt64 := (Array.range n).map UInt64.ofNat

/-! ## `compute_shuffled_permutation` -/

-- Value: pyspec returns [1, 3, 6, 9, 0, 8, 2, 5, 4, 7] for `index_count = 10`.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    okList (computeShuffledPermutation 10 seed) [1, 3, 6, 9, 0, 8, 2, 5, 4, 7]) = true := by
  native_decide

-- A: `index_count = 0` raises `ZeroDivisionError` (`.arithmetic`).
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (computeShuffledPermutation 0 seed)) = true := by native_decide

-- A, zero rounds: the loop never runs, so pyspec returns `[]` for `index_count = 0`.
example : (letI : Preset := { minimal with shuffleRoundCount := 0 }
    letI : HasherTag := fastHasherTag
    okList (computeShuffledPermutation 0 seed) []) = true := by native_decide

-- B: `index_count = 2 ^ 40 + 1` raises before it builds any array.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (computeShuffledPermutation (2 ^ 40 + 1) seed)) = true := by native_decide

-- C: 257 rounds raise at round 256 (pyspec: `OverflowError` with `index_count = 3`).
example : (letI : Preset := { minimal with shuffleRoundCount := 257 }
    letI : HasherTag := fastHasherTag
    isArith (computeShuffledPermutation 3 seed)) = true := by native_decide

/-! ## `compute_committee` -/

-- Value: pyspec returns [9, 38, 32, 42] for 64 indices, index 15, count 16.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    okList (computeCommittee (range 64) (bytesToRoot seed) 15 16) [9, 38, 32, 42]) = true := by
  native_decide

-- D: `count = 0` raises `ZeroDivisionError`, with entries and without.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (computeCommittee (range 4) (bytesToRoot seed) 0 0)) = true := by native_decide
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (computeCommittee #[] (bytesToRoot seed) 0 0)) = true := by native_decide

-- E: an index at the count fails `compute_shuffled_index`'s assert (divergence 3 input).
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isAssert (computeCommittee (range 64) (bytesToRoot seed) 16 16)) = true := by native_decide
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isAssert (computeCommittee (range 4) (bytesToRoot seed) 1 1)) = true := by native_decide

-- E: an empty slice makes no call, so pyspec returns `[]` for an empty index list.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    okList (computeCommittee #[] (bytesToRoot seed) 5 4) []) = true := by native_decide

-- G: the `uint64` products overflow and raise `ValueError`.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (computeCommittee (range 4) (bytesToRoot seed) (2 ^ 64 - 1) (2 ^ 64 - 1))) = true := by
  native_decide
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (computeCommittee (range 4) (bytesToRoot seed) (2 ^ 62) (2 ^ 64 - 1))) = true := by
  native_decide

/-! ## The balance-weighted selection loop

Five candidates with effective balances 32, 2048, 1, 640 and 0 ETH, `size = 6`. -/

private def effBals : Array Nat := #[32, 2048, 1, 640, 0].map (· * 10 ^ 9)

-- Value, shuffled: pyspec returns [1, 1, 1, 1, 1, 3].
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    match computeShuffledPermutation 5 seed with
    | .ok perm =>
      okList (cbwsAux #[0, 1, 2, 3, 4] effBals perm seed 5 6 true 0 ByteArray.empty #[])
        [1, 1, 1, 1, 1, 3]
    | .error _ => false) = true := by native_decide

-- Value, unshuffled: pyspec returns [1, 1, 3, 1, 1, 1].
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    okList (cbwsAux #[0, 1, 2, 3, 4] effBals #[] seed 5 6 false 0 ByteArray.empty #[])
      [1, 1, 3, 1, 1, 1]) = true := by native_decide

-- I: an effective balance of `2 ^ 63` overflows `effective_balance * MAX_RANDOM_VALUE`.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isArith (cbwsAux #[0] #[2 ^ 63] #[] seed 1 1 false 0 ByteArray.empty #[])) = true := by
  native_decide

/-- The preset of the site-i probe rows: `MAX_EFFECTIVE_BALANCE_ELECTRA = 2 ^ 60`. The
`Preset` holds the value twice, so the patch sets both fields. -/
@[reducible] private def bigMaxEbPreset : Preset :=
  { minimal with maxEffectiveBalanceElectra := 2 ^ 60, maxEffectiveBalanceElectraG := 2 ^ 60 }

/-- The seed of the site-i probe rows: 32 bytes `0xff`. -/
private def ffSeed : ByteArray := ⟨Array.replicate 32 0xff⟩

-- i, overflow: an effective balance of 32 ETH passes the weight product, and
-- `MAX_EFFECTIVE_BALANCE_ELECTRA * random_value` overflows (pyspec: `ValueError`).
example : (letI : Preset := bigMaxEbPreset; letI : HasherTag := fastHasherTag
    isArith (cbwsAux #[0] #[32 * 10 ^ 9] #[] ffSeed 1 1 false 0 ByteArray.empty #[])) = true := by
  native_decide

-- i, order: with an effective balance of `2 ^ 63`, the weight product raises first.
example : (letI : Preset := bigMaxEbPreset; letI : HasherTag := fastHasherTag
    match cbwsAux #[0] #[2 ^ 63] #[] ffSeed 1 1 false 0 ByteArray.empty #[] with
    | .error (.arithmetic d) => d == "compute_balance_weighted_selection: effective_balance * MAX_RANDOM_VALUE"
    | _ => false) = true := by
  native_decide

-- i, never reached: with `size = 0`, the loop does not run, and pyspec returns `[]`.
example : (letI : Preset := bigMaxEbPreset; letI : HasherTag := fastHasherTag
    okList (cbwsAux #[0] #[2 ^ 63] #[] ffSeed 1 0 false 0 ByteArray.empty #[]) []) = true := by
  native_decide

-- F: an empty candidate list fails `assert total > 0`, shuffled or not.
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isAssert (computeBalanceWeightedSelection (pureState (default : BeaconState)) #[] seed 1 true))
    = true := by native_decide
example : (letI : Preset := minimal; letI : HasherTag := fastHasherTag
    isAssert (computeBalanceWeightedSelection (pureState (default : BeaconState)) #[] seed 1 false))
    = true := by native_decide

end EthCLSpecs.Tests.FuluCommitteesPins
