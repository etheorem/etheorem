import EthCLSpecs.Tests.HezeWitnessSeams
import EthCLSpecs.Proofs.Heze.HonestDuties
import EthCLSpecs.Proofs.Heze.TraceRun

/-!
# `EthCLSpecs.Tests.HezeNetworkWitness`: the network theorem has a witness

`honestNodes_duties_avoid_full` (`Proofs/Heze/HonestDuties.lean`) states a result for
every honest node of a network. This module builds a network of two honest nodes, `A` and
`B`, at the minimal preset, and checks that it meets every hypothesis. So the theorem is
not vacuous.

## The scenario

The anchor is a genesis block at slot `0`. Block `r` has slot `1`. Its proposer builds the
payload itself, and the payload leaves out the one transaction `tx` of the honest
inclusion list `il` of slot `0`. Node `A` receives the envelope in slot `1` and records
`false` at `r`. Node `B` never receives it. Each node also receives four adversary lists:

1. a timely list from validator `1`, with another transaction;
2. two different timely lists from validator `2`, so validator `2` equivocates;
3. a late list from validator `3`, after the IL due time of slot `0`;
4. a list from validator `0`, the honest validator, under another committee root.

`B` receives the lists in another order and receives `il` later than `A` does.

At the first tick of slot `2`, `getHead` returns the EMPTY node of `r` at both nodes. That
check does not use the theorem.

## The seams

- `strictEngine` (`HezeWitnessSeams.lean`): the EIP-7805 rule with no valid omission.
- `CryptoBackend.verifyOff`: every BLS signature passes, so the blocks carry no real
  signatures.
- The optimistic `[DataAvailability]`: every root is available.
- `pureHasherTag`: the pure-Lean SHA-256 of `LeanSha256`. Its `combine` provably returns
  32 bytes, which is the hypothesis `hw` of the theorem. So the witness needs no FFI
  equivalence axiom. The checks run the compiled hasher through `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (LawfulFcMap)
open EthCLLib.Proofs (ForkChoiceStoreRun pureState)
open EthCLSpecs.Proofs.Heze

namespace EthCLSpecs.Tests.HezeNetworkWitness

open EthCLSpecs.Heze (Preset Config Store State Root BeaconState Validator BeaconBlock
  BeaconBlockBody BeaconBlockHeader SignedBeaconBlock ExecutionPayloadBid ExecutionPayload
  ExecutionRequests Transaction minimal minimalConfig getForkchoiceStore)
open EthCLSpecs.Heze.Const (farFutureEpoch slotsPerEpoch builderIndexSelfBuild
  g2PointAtInfinity)
open EthCLSpecs.Tests.HezeWitnessSeams (strictEngine_lawful)
open scoped EthCLSpecs.Tests.HezeWitnessSeams

local instance : Preset := minimal
local instance : HasherTag := pureHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

/-- The execution block hash of the genesis state. -/
def h1 : Vector UInt8 32 := Vector.replicate 32 1

/-- The execution block hash that the bid of `r` commits to. -/
def h2 : Vector UInt8 32 := Vector.replicate 32 2

/-- The genesis state: slot `0`, one active validator and one balance per slot of the
epoch, and a latest block header with the body root of the default body. The latest block
hash is `h1`, and the latest bid keeps its default block hash `0`. So the parent edge of a
block on the genesis block is EMPTY. The seed holds no payload, so `onBlock` rejects a
FULL parent edge there. -/
def genesisState : State :=
  let base := (default : BeaconState)
  let active : Validator := { (default : Validator) with exitEpoch := farFutureEpoch }
  let header : BeaconBlockHeader :=
    { (default : BeaconBlockHeader) with bodyRoot := htr (default : BeaconBlockBody) }
  pureState { base with
    validators := sszOfArray (Array.replicate slotsPerEpoch active)
    balances := sszOfArray (Array.replicate slotsPerEpoch 0)
    latestBlockHeader := header
    latestBlockHash := h1 }

/-- The genesis block: the default block with the root of the genesis state. `processSlot`
fills the state root of the latest header, so the header and this block have one root. -/
def genesisBlock : BeaconBlock :=
  { (default : BeaconBlock) with stateRoot := bytesToRoot (stateRoot genesisState).1 }

/-- The root of the genesis block. -/
def genesisRoot : Root := htr genesisBlock

/-- The self-build bid of `r`. Its parent hash is the latest block hash of the genesis
state, as `processExecutionPayloadBid` asserts. -/
def bidR : ExecutionPayloadBid :=
  { (default : ExecutionPayloadBid) with
    parentBlockHash := h1
    parentBlockRoot := genesisRoot
    blockHash := h2
    builderIndex := builderIndexSelfBuild
    slot := 1
    executionRequestsRoot := htr (default : ExecutionRequests) }

/-- Block `r` before its state root: slot `1`, proposer `0` (the default proposer
lookahead), on the genesis block. -/
def unsignedR : BeaconBlock :=
  { (default : BeaconBlock) with
    slot := 1
    proposerIndex := 0
    parentRoot := genesisRoot
    body := { (default : BeaconBlockBody) with
      signedExecutionPayloadBid := { message := bidR, signature := g2PointAtInfinity } } }

/-- The state transition of `r` on the genesis state, without the signature check and the
state-root check. -/
def postR : Except StateTransitionError State :=
  match (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun)
      { message := unsignedR, signature := default } false).run genesisState with
  | .ok ((), st) => .ok st
  | .error e => .error e

/-- The post-state of `r`. The `#guard` on `postR` below excludes the fallback. -/
def postState : State :=
  match postR with
  | .ok st => st
  | .error _ => genesisState

/-- Block `r` with the root of its post-state. -/
def blockR : BeaconBlock := { unsignedR with stateRoot := bytesToRoot (stateRoot postState).1 }

/-- The root of block `r`. -/
def rootR : Root := htr blockR

/-- The signed block `r`. The signature is empty, and `verifyOff` accepts it. -/
def signedR : SignedBeaconBlock := { message := blockR, signature := default }

/-- The seed of each node. -/
def seed : Except StoreTransitionError (Store treeMap) :=
  getForkchoiceStore genesisState genesisBlock

/-- `onTick 6` then `onBlock` on `r`, from the seed, succeed. -/
def blockRunOk : Bool :=
  match seed with
  | .error _ => false
  | .ok s0 => (runTrace s0 [.handler (.tick 6), .handler (.block signedR)]).toBool

-- The transition of `r` succeeds, and `onBlock` accepts `r` at the first tick of slot 1.
#guard postR.toBool
#guard blockRunOk

/-- The inclusion-list committee of slot `0`, as a state at `r` gives it. -/
def committee : Vector EthCLSpecs.Heze.ValidatorIndex
    EthCLSpecs.Heze.Const.inclusionListCommitteeSize :=
  (committeeOf postState 0).getD default

/-- The one transaction of the honest list. -/
def tx : Transaction := sszOfArray #[1]

/-- A signed list of slot `0` from `validator`, under the committee key `key`, with the
one transaction `t`. The signature is empty. -/
def mkList (validator : UInt64) (key : Root) (t : Transaction) :
    EthCLSpecs.Heze.SignedInclusionList :=
  { message :=
      { slot := 0, validatorIndex := validator, inclusionListCommitteeRoot := key
        transactions := sszOfArray #[t] }
    signature := default }

/-- The signed honest list: validator `0`, under the key of `committee`, with `tx`. -/
def signedIl : EthCLSpecs.Heze.SignedInclusionList := mkList 0 (htr committee) tx

/-- The honest list. -/
def il : EthCLSpecs.Heze.InclusionList := signedIl.message

/-- Adversary list 1: validator `1`, with another transaction. -/
def advX : EthCLSpecs.Heze.SignedInclusionList := mkList 1 (htr committee) (sszOfArray #[2])

/-- Adversary list 2, first copy: validator `2`. -/
def advY₁ : EthCLSpecs.Heze.SignedInclusionList := mkList 2 (htr committee) (sszOfArray #[3])

/-- Adversary list 2, second copy: validator `2` again, with another transaction. -/
def advY₂ : EthCLSpecs.Heze.SignedInclusionList := mkList 2 (htr committee) (sszOfArray #[4])

/-- Adversary list 3: validator `3`. The nodes receive it after the IL due time. -/
def advZ : EthCLSpecs.Heze.SignedInclusionList := mkList 3 (htr committee) (sszOfArray #[5])

/-- Adversary list 4: the honest validator under another committee root. -/
def advW : EthCLSpecs.Heze.SignedInclusionList := mkList 0 default (sszOfArray #[6])

/-- The self-build envelope of `r`. The payload carries no transactions, so it leaves out
`tx`. -/
def envelope : EthCLSpecs.Heze.SignedExecutionPayloadEnvelope :=
  { message :=
      { payload := { (default : ExecutionPayload) with
          slotNumber := 1, timestamp := 6, parentHash := h1, blockHash := h2 }
        executionRequests := default
        builderIndex := builderIndexSelfBuild
        beaconBlockRoot := rootR
        parentBeaconBlockRoot := genesisRoot }
    signature := default }

/-- The send time of `il`, in wall milliseconds. Genesis is at time `0`. -/
def tSend : Nat := 500

/-- The delivery bound of `il`, in milliseconds. -/
def Δ : Nat := 1000

/-- The trace of node `A`. Each event carries its wall time. `A` receives `il` at 600 and
the envelope in slot `1`. -/
def tevsA : List (TraceEvent × Nat) :=
  [ (.handler (.tick 0), 500), (.inclusionList signedIl, 600), (.inclusionList advX, 700),
    (.inclusionList advY₁, 800), (.inclusionList advY₂, 850), (.inclusionList advW, 900),
    (.handler (.tick 5), 5000), (.inclusionList advZ, 5000),
    (.handler (.tick 6), 6000), (.handler (.block signedR), 6000),
    (.handler (.tick 7), 7000), (.handler (.envelope envelope), 7000),
    (.handler (.tick 12), 12000) ]

/-- The trace of node `B`. `B` receives the lists in another order, and `il` at 1400. It
never receives the envelope. -/
def tevsB : List (TraceEvent × Nat) :=
  [ (.handler (.tick 0), 500), (.inclusionList advW, 600), (.inclusionList advX, 700),
    (.handler (.tick 1), 1400), (.inclusionList signedIl, 1400),
    (.inclusionList advY₂, 1500), (.inclusionList advY₁, 1500),
    (.handler (.tick 5), 5000), (.inclusionList advZ, 5000),
    (.handler (.tick 6), 6000), (.handler (.block signedR), 6000),
    (.handler (.tick 12), 12000) ]

/-- The hypotheses of `HonestView` that a computation decides, at the seed `s0` and the
trace `tevs`. The clock and the facts at `r` share one pass (`traceAll`). -/
def viewB (s0 : Store treeMap) (tevs : List (TraceEvent × Nat)) : Bool :=
  (runTrace s0 (tevs.map Prod.fst)).toBool &&
  decide (tevs.Pairwise (fun a b => a.2 ≤ b.2)) &&
  traceAll (rootFactsB rootR 1 committee) (fun x m => decide (ClockAt x.1 x.2 m)) tevs [] s0 &&
  (FcMap.lookup s0.blockStates rootR).isNone &&
  (FcMap.lookup s0.payloadInclusionListSatisfaction rootR).isNone &&
  (FcMap.lookup s0.payloads rootR).isNone &&
  honestListB tevs il tSend Δ &&
  handlersAll tevs (fun e => match e with
    | .envelope env =>
      !(env.message.beaconBlockRoot == rootR) ||
      !(env.message.payload.transactions.toArray.contains tx)
    | _ => true) &&
  handlersAll tevs (fun e => decide (e.NotAtAnchorParent genesisBlock)) &&
  !(genesisBlock.parentRoot == htr genesisBlock)

/-- The checks at both nodes, from the seed. -/
def nodeChecks : Bool :=
  match seed with
  | .ok s0 => viewB s0 tevsA && viewB s0 tevsB
  | .error _ => false

-- Both nodes meet every decidable hypothesis of `HonestView`.
#guard nodeChecks

/-- The seed exists. -/
theorem seed_ok : ∃ s0 : Store treeMap, seed = .ok s0 := by
  have hb : seed.toBool = true := by native_decide
  cases h : seed with
  | ok s0 => exact ⟨s0, rfl⟩
  | error e => rw [h] at hb; simp [Except.toBool] at hb

/-- `viewB` gives `HonestView` at the store where the trace ends. -/
theorem honestView_of_check {s0 : Store treeMap} (hseed : seed = .ok s0)
    {tevs : List (TraceEvent × Nat)} (h : viewB s0 tevs = true) :
    ∃ (arr : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)) (s : Store treeMap),
      runTrace s0 (tevs.map Prod.fst) = .ok (arr, s) ∧
      HonestView s0 s tevs arr rootR 1 committee il tSend Δ
        (fun p => p.transactions.toArray) (fun _ _ => False) tx genesisBlock := by
  simp only [viewB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hrun, hmono⟩, hpass⟩, hanchor⟩, hans⟩, hpay⟩, hlist⟩, homits⟩, hnap⟩,
    hparent⟩ := h
  cases hr : runTrace s0 (tevs.map Prod.fst) with
  | error e => rw [hr] at hrun; simp [Except.toBool] at hrun
  | ok res =>
    obtain ⟨arr, s⟩ := res
    refine ⟨arr, s, rfl, ?_⟩
    exact
      { clocked := ClockedTrace.of_check hr (of_decide_eq_true hmono) hpass
        seedIl := getForkchoiceStore_ilStore _ _ _ hseed
        root := RootFacts.of_check hanchor (BlockStatesPure.anchor _ _ _ hseed) hpass
        answer0 := Option.isNone_iff_eq_none.mp hans
        payload0 := Option.isNone_iff_eq_none.mp hpay
        list := HonestList.of_check hlist
        omits := fun env w hm hroot' => by
          have := handlersAll_spec homits _ w hm
          refine ⟨fun hmem => ?_, id⟩
          simp [hroot'] at this
          exact this hmem
        slotInv0 := SlotInv.anchor _ _ _ hseed (by simpa using hparent)
        noAnchorParent := fun e w hm => of_decide_eq_true (handlersAll_spec hnap e w hm) }

end EthCLSpecs.Tests.HezeNetworkWitness
