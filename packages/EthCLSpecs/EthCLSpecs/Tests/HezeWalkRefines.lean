import EthCLSpecs.Proofs.Heze.PayloadTiebreak

/-!
# `EthCLSpecs.Tests.HezeWalkRefines`: the walk at `pending r` off the decision slot

The store is in a late slot. It holds a block `r` at slot `0` with a verified payload, and
a justified state with two active validators. Validator 0 votes FULL and validator 1 votes
EMPTY, both in slot 1. No block holds the proposer boost. So the weight of each child of
`pending r` is its score.

The examples run the `getHead` loop body at `pending r`. With balances 10 (FULL) and 20
(EMPTY), the walk goes to `empty r`. With 10 and 10, the weights tie and both roots are `r`.
The tiebreaker is the raw status, so the walk goes to `full r`. The second example pins the
strict lead: EMPTY needs more weight than FULL.

`State` is FFI-backed (`FastBox`), so the examples use `native_decide`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.HezeWalkRefines

open EthCLLib.Spec SizzLean SizzLean.Cache SizzLean.Hasher
open EthCLLib.Proofs (ForkChoiceStoreRun)
open EthCLSpecs.Proofs.Heze (headLoopBody)
open EthCLSpecs.Heze (Preset Config Store Root ForkChoiceNode ValidatorIndex LatestMessage
  minimal minimalConfig)

/-- The root of the block. -/
private def tRoot : Root := Vector.replicate 32 9

/-- Two active validators with the balances `b0` and `b1`. -/
private def tState (b0 b1 : UInt64) : @EthCLSpecs.Heze.BeaconState minimal :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let base := (default : @EthCLSpecs.Heze.BeaconState minimal)
  let v : EthCLSpecs.Heze.Validator :=
    { (default : EthCLSpecs.Heze.Validator) with exitEpoch := EthCLSpecs.Heze.Const.farFutureEpoch }
  { base with
    validators := EthCLLib.Spec.sszOfArray
      #[{ v with effectiveBalance := b0 }, { v with effectiveBalance := b1 }] }

/-- A store in a late slot with the default block (slot `0`) at `tRoot`, its payload
verified, and the justified state `state`. Validator 0 votes FULL and validator 1 votes
EMPTY, both in slot 1. No proposer boost. -/
private def tStore (state : @EthCLSpecs.Heze.BeaconState minimal) :
    @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { time := 100, genesisTime := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := EthCLSpecs.Heze.fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.insert FcMap.empty tRoot default
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.insert FcMap.empty default (SSZ.FastBox state)
    latestMessages := FcMap.insert
      (FcMap.insert FcMap.empty (0 : ValidatorIndex)
        ({ slot := 1, root := tRoot, payloadPresent := true } : LatestMessage))
      (1 : ValidatorIndex) ({ slot := 1, root := tRoot, payloadPresent := false } : LatestMessage)
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.insert FcMap.empty tRoot default
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction := FcMap.empty
    inclusionListStore := EthCLSpecs.Heze.InclusionListStore.empty }

/-- What the loop body at `pending tRoot` did: stepped to `empty tRoot`, to `full tRoot`,
to another node, stopped, or rejected. -/
private inductive StepAnswer where
  | empty
  | full
  | other
  | done
  | reject
  deriving DecidableEq

/-- The `getHead` loop body at `pending tRoot`, run in the runner of the theorems. -/
private def tStep (state : @EthCLSpecs.Heze.BeaconState minimal) : StepAnswer :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let store := tStore state
  match (headLoopBody store #[] (ForkChoiceNode.pending tRoot)).run store with
  | .ok (.next n, _) =>
    if n == ForkChoiceNode.empty tRoot then .empty
    else if n == ForkChoiceNode.full tRoot then .full
    else .other
  | .ok (.done _, _) => .done
  | .error _ => .reject

-- EMPTY (20) leads FULL (10): the walk goes to EMPTY.
example : tStep (tState 10 20) = .empty := by native_decide
-- A tie (10 against 10) goes to FULL off the decision slot.
example : tStep (tState 10 10) = .full := by native_decide

end EthCLSpecs.Tests.HezeWalkRefines
