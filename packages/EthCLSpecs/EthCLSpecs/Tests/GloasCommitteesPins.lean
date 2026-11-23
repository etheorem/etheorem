import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Tests.GloasCommitteesPins`: the empty-selection pins

The pins for `compute_balance_weighted_selection`'s `assert total > 0`
(`gloas/beacon-chain.md:1213`) and its `uint64` loop counter, which no conformance vector
reaches. The pins hash through the FFI `Sha256` (`fastHasherTag`), so `native_decide`. The
counter pin builds no `State`, so it runs as a `#guard`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasCommitteesPins

open EthCLSpecs.Gloas

/-- The pins' state-machine monad over the minimal preset. -/
private abbrev PinM := EStateM StateTransitionError (@State minimal)

/-- A minimal Gloas state with one active 32 ETH validator, slashed or not. -/
private def oneValidatorState (slashed : Bool) : @State minimal :=
  letI : Preset := minimal
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000, slashed,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
    validators := ⟨#[v]⟩, balances := ⟨#[32000000000]⟩ }

/-- An empty `indices` rejects with `.assert`. -/
private def pinSelectionEmptyRejects : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match computeBalanceWeightedSelection (oneValidatorState false) #[] ByteArray.empty 1 true with
  | .error (.assert _) => true
  | _ => false
example : pinSelectionEmptyRejects = true := by native_decide

/-- `process_proposer_lookahead` rejects with `.assert` when the only validator is slashed,
and passes when it is not. -/
private def pinProposerLookaheadAllSlashedRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let run (slashed : Bool) := (processProposerLookahead : PinM Unit).run (oneValidatorState slashed)
  (match run true with | .error (.assert _) _ => true | _ => false) &&
  (match run false with | .ok _ _ => true | _ => false)
example : pinProposerLookaheadAllSlashedRejects = true := by native_decide

/-- `process_ptc_window` rejects with `.assert` when a slot has no committee member. One
validator leaves all but one slot empty. -/
private def pinPtcWindowFewActiveRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match (processPtcWindow : PinM Unit).run (oneValidatorState false) with
  | .error (.assert _) _ => true
  | _ => false
example : pinPtcWindowFewActiveRejects = true := by native_decide

/-- `cbwsAux` mirrors the spec's loop order: the size check exits first, so a full selection
returns at any `i`, even the unreachable `i = 2**64`, which no driver-driven run reaches. The
tail increment is the spec's `i += 1`, so the last pass at `i = 2**64 - 1` throws on the
increment, whether or not it filled the selection. -/
private def pinSamplerCounterOverflow : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  -- A full selection returns even at `i = 2**64`: the size check precedes the increment,
  -- the spec's `while` order. No pass runs, so no hash is drawn.
  (match cbwsAux #[] #[] #[] ByteArray.empty 1 1 false UInt64.size ByteArray.empty #[7] with
    | .ok sel => sel == #[7] | _ => false) &&
  -- A full selection returns at the last counter value.
  (match cbwsAux #[] #[] #[] ByteArray.empty 1 1 false (UInt64.size - 1) ByteArray.empty #[7] with
    | .ok sel => sel == #[7] | _ => false) &&
  -- One 32 ETH validator and all-zero random bytes, so the last pass fills the selection
  -- and the increment throws. The arrays are well formed (one entry each for
  -- `total = 1`: the identity permutation and the 32 ETH effective balance), so no
  -- `!` read defaults: the `.arithmetic` fault comes from `checkedSucc` alone. An empty
  -- `effBals` fires the `effBals[0]!` panic default first, an input no real caller
  -- produces: `computeBalanceWeightedSelection` builds `effBals` with exactly `total`
  -- entries.
  (match cbwsAux #[3] #[0] #[32000000000] ByteArray.empty 1 1 false (UInt64.size - 1)
      (ByteArray.mk (Array.replicate 32 0)) #[] with
    | .error (.arithmetic _) => true | _ => false)
#guard pinSamplerCounterOverflow

end EthCLSpecs.Tests.GloasCommitteesPins
