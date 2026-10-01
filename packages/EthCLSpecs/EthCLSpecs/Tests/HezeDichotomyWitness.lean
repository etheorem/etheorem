import EthCLSpecs.Tests.HezeWitnessSeams

/-!
# `EthCLSpecs.Tests.HezeDichotomyWitness`: the dichotomy hypotheses have a witness

`inclusionList_dichotomy` (`Proofs/Heze/InclusionDichotomy.lean`) takes its hypotheses as
one `DichotomyHypotheses` bundle. `dichotomyHypotheses_witness` builds a store, an
envelope, and an honest inclusion list that meet every field, so the theorem is not
vacuous. `missingTx_recorded_false` then runs `inclusionList_missing_tx` on the witness:
the payload leaves out the one transaction of the list, and the handler records `false`.
`laterStore_witness` builds a `LaterStore` of the handler's result, so the `false` branch
gives `UnsatisfiedPayload` at a real store.

The witness uses the minimal preset, `treeMap`, and three seam instances:

- `strictEngine` (`HezeWitnessSeams.lean`), an `[ExecutionEngine]` that applies the
  EIP-7805 rule with no valid omission. It satisfies `LawfulInclusionList` with
  `isValidOmission := fun _ _ => False`. Its payload check `verifyAndNotifyNewPayload`
  accepts every payload.
- `CryptoBackend.verifyOff`, which accepts every BLS signature. The envelope carries no
  real signature.
- The optimistic `[DataAvailability]`, which answers `true` for every root.

The block state is at slot `1`, with one active validator per slot of the epoch. The
envelope is the self-build envelope that `verifyExecutionPayloadEnvelope` accepts for that
state. The store holds the block at slot `1` and its parent at slot `0`, so the shuffling
dependent root of the block for epoch `0` is the root of the parent. The honest list is
for slot `0` under that root: the key that the envelope handler reads. The witness
computes `htr` through the FFI hasher, so the checks use `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (ForkChoiceStoreRun LawfulFcMap LawfulInclusionList StateFree pureState)
open EthCLSpecs.Proofs.Heze

namespace EthCLSpecs.Tests.HezeDichotomyWitness

open EthCLSpecs.Heze (Preset Config Store State Root Slot BeaconState BeaconBlock Validator
  ExecutionPayload ExecutionRequests Transaction InclusionList SignedInclusionList
  InclusionListStore SignedExecutionPayloadEnvelope BeaconBlockHeader ValidatorIndex minimal
  minimalConfig verifyExecutionPayloadEnvelope getShufflingDependentRoot computeEpochAtSlot
  computeTimeAtSlot isDataAvailable)
open EthCLSpecs.Heze.Const (farFutureEpoch slotsPerEpoch builderIndexSelfBuild)

local instance : Preset := minimal
local instance : HasherTag := fastHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

open EthCLSpecs.Tests.HezeWitnessSeams (strictEngine_lawful)
open scoped EthCLSpecs.Tests.HezeWitnessSeams

/-- The one transaction of the honest list. -/
def tx : Transaction := ⟨#[1]⟩

/-- The block state: slot `1`, one active validator per slot of the epoch, and a cached
self-build bid that commits to the empty execution requests. -/
def blockValue : BeaconState :=
  let base := (default : BeaconState)
  let active : Validator := { (default : Validator) with exitEpoch := farFutureEpoch }
  let vals : ProgressiveList Validator := ⟨Array.replicate slotsPerEpoch active⟩
  let bid := { base.latestExecutionPayloadBid with
    builderIndex := builderIndexSelfBuild
    executionRequestsRoot := htr (default : ExecutionRequests) }
  { base with slot := 1, validators := vals, latestExecutionPayloadBid := bid }

/-- `blockState` is the uncached box of `blockValue`. `DichotomyHypotheses` asks the store
to hold this box. It is an `abbrev`, so a lookup that returns `blockState` matches
`some (pureState blockValue)`. -/
abbrev blockState : State := pureState blockValue

/-- The block root: the root of the latest block header with the state root filled in,
as `verifyExecutionPayloadEnvelope` computes it. -/
def blockRoot : Root :=
  htr ({ sszGet blockState latestBlockHeader with
    stateRoot := bytesToRoot (stateRoot blockState).1 } : BeaconBlockHeader)

/-- The payload time at slot `1`. -/
def payloadTime : UInt64 :=
  match computeTimeAtSlot (sszGet blockState genesisTime) 1 with
  | .ok t => t
  | .error _ => 0

/-- The self-build envelope for `blockState`. The payload carries no transactions. -/
def envelope : SignedExecutionPayloadEnvelope :=
  { message :=
      { payload := { (default : ExecutionPayload) with slotNumber := 1, timestamp := payloadTime }
        executionRequests := default
        builderIndex := builderIndexSelfBuild
        beaconBlockRoot := blockRoot
        parentBeaconBlockRoot := (sszGet blockState latestBlockHeader).parentRoot }
    signature := default }

/-- The block at `blockRoot`: a block at slot `1`, the slot of `blockState`. Its parent root
is the default root. -/
def rootBlock : BeaconBlock := { (default : BeaconBlock) with slot := 1 }

/-- The parent of `rootBlock`: the default block, at slot `0`, stored at the default root. -/
def parentBlock : BeaconBlock := default

/-- The honest list: validator `0`, for slot `0` under the parent root, with `tx`. -/
def il : InclusionList :=
  { slot := 0
    validatorIndex := 0
    dependentRoot := rootBlock.parentRoot
    transactions := ⟨#[tx]⟩ }

/-- The signed honest list. -/
def signedIl : SignedInclusionList := { message := il, signature := default }

/-- The store before the envelope: the two blocks, the block state at the block root, and
the IL store after one timely arrival of the honest list. Every other field is empty. -/
def pre : Store treeMap :=
  { timeMs := 0, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := default
    equivocatingIndices := #[]
    blocks := FcMap.insert (FcMap.insert FcMap.empty rootBlock.parentRoot parentBlock)
      blockRoot rootBlock
    blockStates := FcMap.insert FcMap.empty blockRoot blockState
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction := FcMap.empty
    inclusionListStore := ilStoreOfArrivals ([] ++ [(signedIl, true)]) }

/-- The envelope verification of `blockState` succeeds. -/
theorem verify_ok : (verifyExecutionPayloadEnvelope blockState envelope).isOk = true := by
  native_decide

/-- The dependent-root walk from the block, for the epoch of slot `0`, ends at the parent
root. The walk reads the store argument and no runner state, so the run keeps `pre`. -/
theorem dependent_ok :
    (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store treeMap)) pre
        blockRoot (computeEpochAtSlot (rootBlock.slot - 1))).run pre
      = .ok (rootBlock.parentRoot, pre) := by
  have hcheck :
      (match (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store treeMap))
          pre blockRoot (computeEpochAtSlot (rootBlock.slot - 1))).run pre with
        | .ok (r, _) => r == rootBlock.parentRoot
        | .error _ => false) = true := by
    native_decide
  have hfree : StateFree (getShufflingDependentRoot
      (StoreTransition := ForkChoiceStoreRun (Store treeMap)) pre blockRoot
      (computeEpochAtSlot (rootBlock.slot - 1))) := by
    unfold getShufflingDependentRoot EthCLSpecs.Heze.getAncestor
      EthCLSpecs.Heze.getParentPayloadStatus
    free_solve
  split at hcheck
  · rename_i r s hrun
    have hs := (hfree.run_eq hrun).1
    subst hs
    rw [hrun, beq_iff_eq.mp hcheck]
  · exact absurd hcheck Bool.false_ne_true

/-- `DichotomyHypotheses` holds for the witness, so `inclusionList_dichotomy` is not
vacuous. -/
theorem dichotomyHypotheses_witness :
    DichotomyHypotheses (map := treeMap) (fun _ _ => False) pre envelope blockValue rootBlock
      rootBlock.parentRoot pre [] [] signedIl il :=
  { el := strictEngine_lawful
    blockState := LawfulFcMap.lookup_insert_self _ _ _
    available := rfl
    verify := verify_ok
    blockLookup := LawfulFcMap.lookup_insert_self _ _ _
    slotNeZero := by decide
    dependent := dependent_ok
    key := rfl
    ils := rfl
    signedEq := rfl
    arrivals := ⟨by simp, by simp⟩ }

/-- On the witness, the payload leaves out `tx`, and `strictEngine` allows no omission.
So `inclusionList_missing_tx` gives a successful envelope handler that records `false`
at the block root. -/
theorem missingTx_recorded_false :
    ∃ post : Store treeMap,
      (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := treeMap)
          (StoreTransition := ForkChoiceStoreRun (Store treeMap)) envelope).run pre
        = .ok ((), post) ∧
      FcMap.lookup post.payloadInclusionListSatisfaction blockRoot = some false := by
  obtain ⟨post, hrun, hfalse, -⟩ := inclusionList_missing_tx rootBlock
    dichotomyHypotheses_witness (tx := tx) (by native_decide) (by native_decide) (fun hf => hf)
  exact ⟨post, hrun, hfalse⟩

/-- The `false` branch is not vacuous on the witness. The store `s` is the handler's `post`
with the clock in slot `2`, the slot after the block. It is a `LaterStore` of `post`, so
`UnsatisfiedPayload` holds at `s`. -/
theorem laterStore_witness :
    ∃ post s : Store treeMap,
      (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := treeMap)
          (StoreTransition := ForkChoiceStoreRun (Store treeMap)) envelope).run pre
        = .ok ((), post) ∧
      LaterStore s post blockRoot rootBlock ∧
      UnsatisfiedPayload s blockRoot rootBlock := by
  obtain ⟨post, hrun, hfalse⟩ := missingTx_recorded_false
  -- Minimal slots last 6000 ms, so `timeMs := 12000` with `genesisTimeMs := 0` is slot `2`.
  let s : Store treeMap :=
    { post with timeMs := 12000, genesisTimeMs := 0
                blocks := FcMap.insert post.blocks blockRoot rootBlock }
  have hlater : LaterStore s post blockRoot rootBlock := by
    refine ⟨LawfulFcMap.lookup_insert_self _ _ _, rfl, ?_, by decide⟩
    simp +zetaDelta [EthCLSpecs.Heze.getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis,
      EthCLSpecs.Heze.computeSlotAtTimeMs, checkedSub, EthCLSpecs.Heze.Const.slotDurationMs]
    -- The two sides differ only in the slot: `12000 / slotDurationMs` against
    -- `rootBlock.slot + 1`. The kernel evaluates both to `2`.
    exact congrArg (fun slot => (.ok (slot, _) : Except _ _)) (by decide +kernel)
  exact ⟨post, s, hrun, hlater, unsatisfiedPayload_of_recorded_false hlater hfalse⟩

end EthCLSpecs.Tests.HezeDichotomyWitness
