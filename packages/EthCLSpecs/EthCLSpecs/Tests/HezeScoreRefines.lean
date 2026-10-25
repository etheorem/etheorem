import EthCLSpecs.Proofs.Heze.PayloadRaceRefines

/-!
# `EthCLSpecs.Tests.HezeScoreRefines`: the score and the race weight on one store

The store holds a block `r` at slot `0`, and the state holds three active validators with
balances 10, 20, and 40. Each validator has a slot-1 message for `r`. Validator 0 votes
FULL, validator 1 votes EMPTY, and validator 2 votes FULL but is an equivocator. The
examples pin the score of each child and the `sideWeight` of each side: FULL 10, EMPTY 20,
and `neither` 40, where the equivocator sits.

The last example puts two FULL votes of `2^63` on `r`. The sum passes `2^64`, and the score
raises an arithmetic fault, as pyspec's `Gwei(sum(...))` raises `ValueError`.

`State` is FFI-backed (`FastBox`), so the examples use `native_decide`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.HezeScoreRefines

open EthCLLib.Spec SizzLean SizzLean.Cache SizzLean.Hasher
open EthCLLib.Proofs (ForkChoiceStoreRun)
open EthCLSpecs.Proofs.Heze (raceValidators storeSide)
open EthCLSpecs.Proofs.Heze.PayloadRace (Side sideWeight)
open EthCLSpecs.Heze (Preset Config Store Root ForkChoiceNode ValidatorIndex LatestMessage
  minimal minimalConfig getAttestationScore)

/-- The root of the block. -/
private def tRoot : Root := Vector.replicate 32 9

/-- Three active validators with the balances `b0`, `b1`, and `b2`. -/
private def tState (b0 b1 b2 : UInt64) : @EthCLSpecs.Heze.BeaconState minimal :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let base := (default : @EthCLSpecs.Heze.BeaconState minimal)
  let v : EthCLSpecs.Heze.Validator :=
    { (default : EthCLSpecs.Heze.Validator) with exitEpoch := EthCLSpecs.Heze.Const.farFutureEpoch }
  { base with
    validators := EthCLLib.Spec.sszOfArray
      #[{ v with effectiveBalance := b0 }, { v with effectiveBalance := b1 },
        { v with effectiveBalance := b2 }] }

/-- A store with the default block (slot `0`) at `tRoot`, one slot-1 message for `tRoot` per
entry of `msgs` (the flag is `payloadPresent`), and the equivocators `equiv`. -/
private def tStore (msgs : List (ValidatorIndex × Bool)) (equiv : Array ValidatorIndex) :
    @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { time := 0, genesisTime := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := EthCLSpecs.Heze.fcZeroRoot
    equivocatingIndices := equiv
    blocks := FcMap.insert FcMap.empty tRoot default
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := msgs.foldl
      (fun m (p : ValidatorIndex × Bool) =>
        FcMap.insert m p.1 ({ slot := 1, root := tRoot, payloadPresent := p.2 } : LatestMessage))
      FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction := FcMap.empty
    inclusionListStore := EthCLSpecs.Heze.InclusionListStore.empty }

/-- What a score run gave: the value, an arithmetic fault, or another reject. -/
private inductive ScoreAnswer where
  | value (n : Nat)
  | arithmetic
  | otherReject
  deriving DecidableEq

/-- The score of `full tRoot` (`full = true`) or `empty tRoot`, run in the runner of the
theorems. -/
private def tScore (store : @Store minimal treeMap fastHasherTag)
    (state : @EthCLSpecs.Heze.BeaconState minimal) (full : Bool) : ScoreAnswer :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let node : ForkChoiceNode := if full then .full tRoot else .empty tRoot
  match (getAttestationScore (map := treeMap)
      (StoreTransition := ForkChoiceStoreRun (Store treeMap)) store node
      (SSZ.FastBox state)).run store with
  | .ok (w, _) => .value w.toNat
  | .error (.transition (.arithmetic _)) => .arithmetic
  | .error _ => .otherReject

/-- `sideWeight` of one side, over `raceValidators` and `storeSide`. -/
private def tSide (store : @Store minimal treeMap fastHasherTag)
    (state : @EthCLSpecs.Heze.BeaconState minimal) (side : Side) : Nat :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  sideWeight (raceValidators (SSZ.FastBox state) (fun _ => true) (fun _ _ => false))
    (fun v => storeSide store tRoot v.index) side

/-- The store of the module docstring. -/
private abbrev tVotes := tStore [(0, true), (1, false), (2, true)] #[2]

example : tScore tVotes (tState 10 20 40) true = .value 10 := by native_decide
example : tScore tVotes (tState 10 20 40) false = .value 20 := by native_decide
example : tSide tVotes (tState 10 20 40) .full = 10 := by native_decide
example : tSide tVotes (tState 10 20 40) .empty = 20 := by native_decide
example : tSide tVotes (tState 10 20 40) .neither = 40 := by native_decide

-- Two FULL votes of `2^63` pass `2^64`. A wrapping fold would return `0` here.
example : tScore (tStore [(0, true), (1, true)] #[]) (tState (2 ^ 63) (2 ^ 63) 0) true
    = .arithmetic := by native_decide

end EthCLSpecs.Tests.HezeScoreRefines
