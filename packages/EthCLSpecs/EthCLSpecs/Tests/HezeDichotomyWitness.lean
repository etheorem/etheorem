import EthCLSpecs.Proofs.Heze.InclusionDichotomy

/-!
# `EthCLSpecs.Tests.HezeDichotomyWitness`: the dichotomy hypotheses have a witness

`inclusionList_dichotomy` (`Proofs/Heze/InclusionDichotomy.lean`) takes its hypotheses as
one `DichotomyHypotheses` bundle. `dichotomyHypotheses_witness` builds a store, an
envelope, and an honest inclusion list that meet every field, so the theorem is not
vacuous. `missingTx_recorded_false` then runs `inclusionList_missing_tx` on the witness:
the payload leaves out the one transaction of the list, and the handler records `false`.

The witness uses the minimal preset, `treeMap`, and three seam instances:

- `strictEngine`, an `[ExecutionEngine]` that applies the EIP-7805 rule with no valid
  omission. It satisfies `LawfulInclusionList` with `isValidOmission := fun _ _ => False`.
  Its payload check `verifyAndNotifyNewPayload` accepts every payload;
- `CryptoBackend.verifyOff`, which accepts every BLS signature. The envelope carries no
  real signature;
- the optimistic `[DataAvailability]`, which answers `true` for every root.

The block state is at slot `1`, with one active validator per slot of the epoch, so the
inclusion-list committee of slot `0` is not empty. The envelope is the self-build
envelope that `verifyExecutionPayloadEnvelope` accepts for that state. The witness
computes `htr` through the FFI hasher, so the checks use `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLSpecs.Proofs.Heze

namespace EthCLSpecs.Tests.HezeDichotomyWitness

open EthCLSpecs.Heze (Preset Config Store State Root BeaconState Validator ExecutionPayload
  ExecutionRequests Transaction InclusionList SignedInclusionList InclusionListStore
  SignedExecutionPayloadEnvelope BeaconBlockHeader ValidatorIndex minimal minimalConfig
  verifyExecutionPayloadEnvelope getInclusionListCommittee getInclusionListDueMs
  getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot cyclicSample
  computeTimeAtSlot isDataAvailable)
open EthCLSpecs.Heze.Const (farFutureEpoch slotsPerEpoch builderIndexSelfBuild
  inclusionListCommitteeSize maxTransactionsPerPayload)

local instance : Preset := minimal
local instance : HasherTag := fastHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

/-- The EIP-7805 rule with no valid omission: the answer is `true` exactly when every
listed transaction is in the payload. -/
local instance (priority := high) strictEngine :
    ExecutionEngine ExecutionPayload Transaction ExecutionRequests where
  isInclusionListSatisfied p ilTxs := ilTxs.all fun tx => p.transactions.toArray.contains tx
  verifyAndNotifyNewPayload _ _ _ _ := true

/-- `strictEngine` satisfies the rule with no valid omission. -/
theorem strictEngine_lawful :
    LawfulInclusionList ExecutionPayload Transaction ExecutionRequests
      (fun p => p.transactions.toArray) (fun _ _ => False) :=
  ⟨fun p ilTxs => by
    simp only [ExecutionEngine.isInclusionListSatisfied, Array.all_eq_true_iff_forall_mem,
      Array.contains_iff_mem, or_false]⟩

/-- The one transaction of the honest list. -/
def tx : Transaction := sszOfArray #[1]

/-- The block state: slot `1`, one active validator per slot of the epoch, and a cached
self-build bid that commits to the empty execution requests. -/
def blockState : State :=
  let base := (default : BeaconState)
  let active : Validator := { (default : Validator) with exitEpoch := farFutureEpoch }
  let vals := (Array.replicate slotsPerEpoch active).foldl (·.push ·) base.validators
  let bid := { base.latestExecutionPayloadBid with
    builderIndex := builderIndexSelfBuild
    executionRequestsRoot := htr (default : ExecutionRequests) }
  SSZ.FastBox { base with slot := 1, validators := vals, latestExecutionPayloadBid := bid }

/-- The block root: the root of the latest block header with the state root filled in,
as `verifyExecutionPayloadEnvelope` computes it. -/
def blockRoot : Root :=
  htr ({ sszGet blockState latestBlockHeader with
    stateRoot := bytesToRoot (stateRoot blockState).1 } : BeaconBlockHeader)

/-- The payload time at slot `1`. -/
def payloadTime : UInt64 :=
  match computeTimeAtSlot blockState 1 with
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

/-- The indices that `getInclusionListCommittee` samples for slot `0`, as
`getInclusionListCommittee_run_eq` spells them. -/
def committeeIndices : Array ValidatorIndex :=
  (Array.range (getCommitteeCountPerSlot blockState
      (computeEpochAtSlot (sszGet blockState slot - 1)))).foldl
    (fun acc i => acc ++ getBeaconCommittee blockState (sszGet blockState slot - 1) i)
    (#[] : Array ValidatorIndex)

/-- The inclusion-list committee of slot `0`. -/
def committee : Vector ValidatorIndex inclusionListCommitteeSize :=
  cyclicSample committeeIndices inclusionListCommitteeSize

/-- The honest list: validator `0`, under the key of `committee`, with `tx`. -/
def il : InclusionList :=
  { slot := 0
    validatorIndex := 0
    inclusionListCommitteeRoot := htr committee
    transactions := (default : SSZList Transaction maxTransactionsPerPayload).push tx }

/-- The signed honest list. -/
def signedIl : SignedInclusionList := { message := il, signature := default }

/-- The store before the envelope: the block state at the block root, and the IL store
after one timely arrival of the honest list. Every other field is empty. -/
def pre : Store treeMap :=
  { time := 0, genesisTime := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := default
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.insert FcMap.empty blockRoot blockState
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction := FcMap.empty
    inclusionListStore := ilStoreOfArrivals ([] ++ [(signedIl, 0)]) }

/-- The envelope verification of `blockState` succeeds. -/
theorem verify_ok : ∃ warm, verifyExecutionPayloadEnvelope blockState envelope = .ok warm := by
  have hb : (verifyExecutionPayloadEnvelope blockState envelope).toBool = true := by
    native_decide
  cases h : verifyExecutionPayloadEnvelope blockState envelope with
  | ok w => exact ⟨w, rfl⟩
  | error e => rw [h] at hb; simp [Except.toBool] at hb

/-- `DichotomyHypotheses` holds for the witness, so `inclusionList_dichotomy` is not
vacuous. -/
theorem dichotomyHypotheses_witness :
    ∃ warm : State,
      DichotomyHypotheses (map := treeMap) (fun _ _ => False) pre envelope blockState warm
        committee [] [] signedIl 0 il := by
  obtain ⟨warm, hverify⟩ := verify_ok
  refine ⟨warm, ⟨strictEngine_lawful, ?_, rfl, hverify, by native_decide, ?_, rfl, rfl, rfl,
    ⟨by simp, by simp, by simp⟩, by native_decide⟩⟩
  · exact LawfulFcMap.lookup_insert_self _ _ _
  · rw [getInclusionListCommittee_run_eq]
    show (if committeeIndices.size == 0 then _ else _) = _
    rw [if_neg (by native_decide)]
    rfl

/-- On the witness, the payload leaves out `tx`, and `strictEngine` allows no omission.
So `inclusionList_missing_tx` gives a successful envelope handler that records `false`
at the block root. -/
theorem missingTx_recorded_false :
    ∃ post : Store treeMap,
      (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := treeMap)
          (StoreTransition := ForkChoiceStoreRun (Store treeMap)) envelope).run pre
        = .ok ((), post) ∧
      FcMap.lookup post.payloadInclusionListSatisfaction blockRoot = some false := by
  obtain ⟨warm, h⟩ := dichotomyHypotheses_witness
  obtain ⟨post, hrun, hfalse, -⟩ := inclusionList_missing_tx (default : EthCLSpecs.Heze.BeaconBlock)
    h (tx := tx) (by native_decide) (by native_decide) (fun hf => hf)
  exact ⟨post, hrun, hfalse⟩

end EthCLSpecs.Tests.HezeDichotomyWitness
