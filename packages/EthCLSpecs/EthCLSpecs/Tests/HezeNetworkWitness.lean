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
`false` at `r`. Node `B` never receives it. The IL committee of slot `0` is validators
`26`, `8`, `6`, and `22`, and `il` comes from validator `26`. Each node also receives three
adversary lists:

1. a timely list from validator `8`, with another transaction;
2. two different timely lists from validator `6`, so validator `6` equivocates;
3. a late list from validator `22`, after the IL due time of slot `0`.

`B` receives the lists in another order and receives `il` later than `A` does.

No list of slot `0` can name another dependent root. `on_inclusion_list` asserts that the
dependent block is known and is a possible dependent block for epoch `0`, and in slot `0`
the genesis block is the only one. A node rejects such a list, so no trace holds it.

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

-- The compiler specializes the Heze `state_transition` spine and `runTrace` at the concrete
-- instances of this module, and that needs more than the default heartbeats.
set_option maxHeartbeats 1000000

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

/-- The genesis state: slot `0`, four active validators and balances per slot of the
epoch, and a latest block header with the body root of the default body. So the beacon
committee of each slot has four members (`TARGET_COMMITTEE_SIZE`). The latest block
hash is `h1`, and the latest bid keeps its default block hash `0`. So the parent edge of a
block on the genesis block is EMPTY. The seed holds no payload, so `onBlock` rejects a
FULL parent edge there. -/
def genesisState : State :=
  let base := (default : BeaconState)
  let active : Validator := { (default : Validator) with exitEpoch := farFutureEpoch }
  let header : BeaconBlockHeader :=
    { (default : BeaconBlockHeader) with bodyRoot := htr (default : BeaconBlockBody) }
  pureState { base with
    validators := ⟨Array.replicate (4 * slotsPerEpoch) active⟩
    balances := ⟨Array.replicate (4 * slotsPerEpoch) 0⟩
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

/-- `postValue` is the post-state of `r` as a plain value. `HonestProposal` reads the
proposer's state as a value. The duties theorem runs `processParentExecutionPayload` on its
uncached box. -/
def postValue : BeaconState := postState.view

/-- Block `r` with the root of its post-state. -/
def blockR : BeaconBlock := { unsignedR with stateRoot := bytesToRoot (stateRoot postState).1 }

/-- The root of block `r`. -/
def rootR : Root := htr blockR

/-- The signed block `r`. The signature is empty, and `verifyOff` accepts it. -/
def signedR : SignedBeaconBlock := { message := blockR, signature := default }

/-- The seed of each node. -/
def seed : Except StoreTransitionError (Store treeMap) :=
  getForkchoiceStore genesisState genesisBlock

/-- `onTick 6000` then `onBlock` on `r`, from the seed, succeed. The genesis time is `0`,
and minimal slots last 6000 ms, so 6000 ms is the start of slot `1`. -/
def blockRunOk : Bool :=
  match seed with
  | .error _ => false
  | .ok s0 => (runTrace s0 [.handler (.tick 6000), .handler (.block signedR)]).toBool

-- The transition of `r` succeeds, and `onBlock` accepts `r` at the first tick of slot 1.
#guard postR.toBool
#guard blockRunOk

/-- The dependent root of the lists of slot `0`. The walk from `r` for epoch `0` reaches
the genesis block. The pass in `viewB` checks that every store of each trace agrees. -/
def dr : Root := genesisRoot

/-- The one transaction of the honest list. -/
def tx : Transaction := ⟨#[1]⟩

/-- A signed list of slot `0` from `validator`, under the dependent root `key`, with the
one transaction `t`. The signature is empty. -/
def mkList (validator : UInt64) (key : Root) (t : Transaction) :
    EthCLSpecs.Heze.SignedInclusionList :=
  { message :=
      { slot := 0, validatorIndex := validator, dependentRoot := key
        transactions := ⟨#[t]⟩ }
    signature := default }

/-- The signed honest list: validator `26`, under `dr`, with `tx`. -/
def signedIl : EthCLSpecs.Heze.SignedInclusionList := mkList 26 dr tx

/-- The honest list. -/
def il : EthCLSpecs.Heze.InclusionList := signedIl.message

/-- Adversary list 1: validator `8`, with another transaction. -/
def advX : EthCLSpecs.Heze.SignedInclusionList := mkList 8 dr ⟨#[2]⟩

/-- Adversary list 2, first copy: validator `6`. -/
def advY₁ : EthCLSpecs.Heze.SignedInclusionList := mkList 6 dr ⟨#[3]⟩

/-- Adversary list 2, second copy: validator `6` again, with another transaction. -/
def advY₂ : EthCLSpecs.Heze.SignedInclusionList := mkList 6 dr ⟨#[4]⟩

/-- Adversary list 3: validator `22`. The nodes receive it after the IL due time, 4000 ms
into slot `0`. -/
def advZ : EthCLSpecs.Heze.SignedInclusionList := mkList 22 dr ⟨#[5]⟩

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

/-- An event at the wall time `w`, after a tick to `w`. The store clock counts
milliseconds, so the node ticks to the wall time of each message. -/
def tickThen (w : Nat) (e : TraceEvent) : List (TraceEvent × Nat) :=
  [(.handler (.tick (UInt64.ofNat w)), w), (e, w)]

/-- The trace of node `A`. Each event carries its wall time. `A` receives `il` at 600 and
the envelope in slot `1`. -/
def tevsA : List (TraceEvent × Nat) :=
  tickThen 600 (.inclusionList signedIl) ++ tickThen 700 (.inclusionList advX) ++
  tickThen 800 (.inclusionList advY₁) ++ tickThen 850 (.inclusionList advY₂) ++
  tickThen 5000 (.inclusionList advZ) ++
  tickThen 6000 (.handler (.block signedR)) ++
  tickThen 7000 (.handler (.envelope envelope)) ++
  [(.handler (.tick 12000), 12000)]

/-- The trace of node `B`. `B` receives the lists in another order, and `il` at 1400. It
never receives the envelope. -/
def tevsB : List (TraceEvent × Nat) :=
  tickThen 700 (.inclusionList advX) ++ tickThen 1400 (.inclusionList signedIl) ++ tickThen 1500 (.inclusionList advY₂) ++
  tickThen 1500 (.inclusionList advY₁) ++ tickThen 5000 (.inclusionList advZ) ++
  tickThen 6000 (.handler (.block signedR)) ++ [(.handler (.tick 12000), 12000)]

/-- The facts that the queries need at the end of a trace. The store time is 12000 ms, the
start of slot `2`. The justified block has slot at most `1`. In the viable node list, the
FULL node of `r` comes only with its EMPTY node. `getHead` returns the EMPTY node of `r`,
and `shouldBuildOnFull` for slot `2` answers `false` at that head. The head check runs the
handlers only, so it does not depend on the theorem. -/
def queryB (m : Store treeMap) : Bool :=
  m.timeMs == 12000 &&
  (FcMap.lookup m.blocks m.justifiedCheckpoint.root).any (fun jb => decide (jb.slot ≤ 1)) &&
  emptyViableWithFullB m rootR &&
  match (EthCLSpecs.Heze.getHead (map := treeMap)
      (StoreTransition := ForkChoiceStoreRun (Store treeMap)) m).run m with
  | .ok (head, _) =>
    head.root == rootR && head.payloadStatus == EthCLSpecs.Heze.Const.payloadStatusEmpty &&
    match (EthCLSpecs.Heze.shouldBuildOnFull (map := treeMap)
        (StoreTransition := ForkChoiceStoreRun (Store treeMap)) m head 2).run m with
    | .ok (full, _) => !full
    | .error _ => false
  | .error _ => false

/-- The checks at one node, from the seed `s0` along the trace `tevs`: the query facts at
the end of the trace, and the hypotheses of `HonestView` that a computation decides. The
clock and the facts at `r` share one pass (`traceAll`). -/
def nodeB (s0 : Store treeMap) (tevs : List (TraceEvent × Nat)) : Bool :=
  (match runTrace s0 (tevs.map Prod.fst) with
    | .ok (_, m) => queryB m
    | .error _ => false) &&
  decide (tevs.Pairwise (fun a b => a.2 ≤ b.2)) &&
  traceAll (rootFactsB rootR 1 dr) (fun x m => decide (ClockAt x.1 x.2 m)) tevs [] s0 &&
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

/-- The checks at both nodes, and the genesis time of the seed. -/
def nodeChecks : Bool :=
  match seed with
  | .ok s0 => s0.genesisTimeMs == 0 && nodeB s0 tevsA && nodeB s0 tevsB
  | .error _ => false

/-- The seed exists. -/
theorem seed_ok : ∃ s0 : Store treeMap, seed = .ok s0 := by
  have hb : seed.toBool = true := by native_decide
  cases h : seed with
  | ok s0 => exact ⟨s0, rfl⟩
  | error e => rw [h] at hb; simp [Except.toBool] at hb

/-- `nodeB` gives the end of the trace, its query facts, and `HonestView` there. -/
theorem honestView_of_check {s0 : Store treeMap} (hseed : seed = .ok s0)
    {tevs : List (TraceEvent × Nat)} (h : nodeB s0 tevs = true) :
    ∃ (arr : List (EthCLSpecs.Heze.SignedInclusionList × Bool)) (s : Store treeMap),
      runTrace s0 (tevs.map Prod.fst) = .ok (arr, s) ∧ queryB s = true ∧
      HonestView s0 s tevs arr rootR 1 dr il tSend Δ
        (fun p => p.transactions.toArray) (fun _ _ => False) tx genesisBlock := by
  simp only [nodeB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hrun, hmono⟩, hpass⟩, hanchor⟩, hans⟩, hpay⟩, hlist⟩, homits⟩, hnap⟩,
    hparent⟩ := h
  cases hr : runTrace s0 (tevs.map Prod.fst) with
  | error e => rw [hr] at hrun; simp at hrun
  | ok res =>
    obtain ⟨arr, s⟩ := res
    rw [hr] at hrun
    refine ⟨arr, s, rfl, hrun, ?_⟩
    exact
      { clocked := ClockedTrace.of_check hr (of_decide_eq_true hmono) hpass
        seedIl := getForkchoiceStore_ilStore _ _ _ hseed
        root := RootFacts.of_check hanchor hpass
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

/-- The honest block of slot `2` on the head. Its parent is `r`. The parent hash of its bid
is the parent hash of the latest bid of the post-state of `r`, and it carries no parent
requests. -/
def blockS2 : BeaconBlock :=
  { (default : BeaconBlock) with
    slot := 2
    parentRoot := rootR
    body := { (default : BeaconBlockBody) with
      signedExecutionPayloadBid :=
        { message := { (default : ExecutionPayloadBid) with
            parentBlockHash := postValue.latestExecutionPayloadBid.parentBlockHash
            slot := 2 }
          signature := g2PointAtInfinity } } }

-- The latest bid of the post-state of `r` is the bid of `r`.
#guard sszGet postState latestExecutionPayloadBid == bidR

-- `processParentExecutionPayload` takes the EMPTY branch on `blockS2`. It succeeds and keeps
-- the state root. `State` has no decidable equality, so the check compares the roots.
#guard match (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
    blockS2).run postState with
  | .ok ((), st) => (stateRoot st).1 == (stateRoot postState).1
  | .error _ => false

/-- The `combine` of the pure-Lean hasher returns 32 bytes. -/
theorem combine_size (a b : ByteArray) :
    (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32 :=
  LeanSha256.combine_size_eq_32 a b

/-- The network of node `A` (`true`) and node `B` (`false`) meets every hypothesis of
`honestNodes_duties_avoid_full`. Node `v` runs its trace from the seed `s0` to the store
`m`, at the start of slot `2`. `getHead` on `m` returns the EMPTY node of `r`. The theorem
gives a root collision, or the three duties:

- the head avoids the FULL node of `r`;
- no honest vote is `(r, 1)`;
- `blockS2` does not extend `r`, or `processParentExecutionPayload` keeps the post-state
  of `r`, so it settles no builder payment.

The hasher is the pure-Lean one, so no FFI equivalence axiom enters. The proof still trusts
the compiler: `native_decide` evaluates `nodeChecks`, and `#print axioms` lists one axiom
per call. Kernel `decide` cannot replace it. The SSZ merkleizer `SSZType.hashTreeRoot`
compiles to well-founded recursion, so the kernel does not reduce any `htr`, not even of a
`UInt64`. -/
theorem networkWitness :
    ∀ v : Bool, ∃ (s0 m s' : Store treeMap)
      (arr : List (EthCLSpecs.Heze.SignedInclusionList × Bool))
      (head : EthCLSpecs.Heze.ForkChoiceNode),
      seed = .ok s0 ∧
      runTrace s0 ((if v then tevsA else tevsB).map Prod.fst) = .ok (arr, m) ∧
      (EthCLSpecs.Heze.getHead (map := treeMap)
        (StoreTransition := ForkChoiceStoreRun (Store treeMap)) m).run m = .ok (head, s') ∧
      head = .empty rootR ∧
      (RootCollision ∨
        (¬ NodeBelow m (.full rootR) head ∧
          (∀ headSlot currentSlot : EthCLSpecs.Heze.Slot,
            ¬ (head.root = rootR ∧ honestAttestationIndex head headSlot currentSlot = 1)) ∧
          (blockS2.parentRoot ≠ rootR ∨
            (head = .empty rootR ∧
              (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
                  blockS2).run (pureState postValue) = .ok ((), pureState postValue))))) := by
  obtain ⟨s0, hseed⟩ := seed_ok
  have hnodes : nodeChecks = true := by native_decide
  simp only [nodeChecks, hseed, Bool.and_eq_true] at hnodes
  obtain ⟨⟨hg, hA⟩, hB⟩ := hnodes
  obtain ⟨arrA, sA, hrunA, hqA, hvA⟩ := honestView_of_check hseed hA
  obtain ⟨arrB, sB, hrunB, hqB, hvB⟩ := honestView_of_check hseed hB
  -- The network: node `true` runs `tevsA`, and node `false` runs `tevsB`.
  let tevs : Bool → List (TraceEvent × Nat) := fun v => if v then tevsA else tevsB
  let arrs : Bool → List (EthCLSpecs.Heze.SignedInclusionList × Bool) :=
    fun v => if v then arrA else arrB
  let ss : Bool → Store treeMap := fun v => if v then sA else sB
  have hview : ∀ v : Bool, (fun _ => True) v → HonestView s0 (ss v) (tevs v) (arrs v) rootR 1
      dr il tSend Δ (fun p => p.transactions.toArray) (fun _ _ => False) tx
      genesisBlock := by
    intro v _
    cases v
    · exact hvB
    · exact hvA
  have hgenesis : ∀ _ : Bool, True → s0.genesisTimeMs = 0 :=
    fun _ _ => beq_iff_eq.mp hg
  -- The IL due time of the minimal preset: 6667 basis points of 6000 ms.
  have hthm := honestNodes_duties_avoid_full combine_size (Node := Bool) (fun _ => True)
    strictEngine_lawful (fun _ => s0) ss tevs arrs (fun _ => genesisBlock) hgenesis hview
    (due := 4000) rfl (by decide) (by decide) (by decide) rfl (by decide)
    (by native_decide) (by decide)
  intro v
  have hrunv : runTrace s0 ((tevs v).map Prod.fst) = .ok (arrs v, ss v) := by
    cases v
    · exact hrunB
    · exact hrunA
  have hq : queryB (ss v) = true := by
    cases v
    · exact hqB
    · exact hqA
  simp only [queryB, Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨⟨htime, hjb⟩, hev⟩, hhead⟩ := hq
  obtain ⟨jb, hjb, hjslot⟩ : ∃ jb, FcMap.lookup (ss v).blocks
      (ss v).justifiedCheckpoint.root = some jb ∧ decide (jb.slot ≤ 1) = true := by
    cases hlk : FcMap.lookup (ss v).blocks (ss v).justifiedCheckpoint.root with
    | none => simp [hlk] at hjb
    | some jb => exact ⟨jb, rfl, by simpa [hlk] using hjb⟩
  split at hhead
  · rename_i head runner hrunHead
    simp only [Bool.and_eq_true, beq_iff_eq] at hhead
    obtain ⟨⟨hroot, hstatus⟩, hbuild⟩ := hhead
    have hheq : head = .empty rootR := node_eq_of_root_status _ _ hroot hstatus
    split at hbuild
    · rename_i full runner' hrunBuild
      have hfull : full = false := by simpa using hbuild
      subst hfull
      refine ⟨s0, ss v, runner, arrs v, head, hseed, hrunv, hrunHead, hheq, ?_⟩
      rcases hthm v trivial (tevs v) [] (by simp) (arrs v) (ss v)
          (NodeTrace.of_runTrace hrunv) 12000 (by rw [htime]; rfl) (by decide) (by decide)
          jb hjb (of_decide_eq_true hjslot) (EmptyViableWithFull.of_check _ _ hev) (ss v)
          runner head hrunHead
        with hcol | ⟨havoid, hatt, hprop⟩
      · exact Or.inl hcol
      · refine Or.inr ⟨havoid, hatt, hprop postValue blockS2 ?_ (by native_decide)⟩
        exact
          { parent := by rw [hheq]; rfl
            build := ⟨false, 2, ss v, runner', hrunBuild, by simp [blockS2], by simp,
              fun _ => rfl⟩ }
    · simp at hbuild
  · simp at hhead

end EthCLSpecs.Tests.HezeNetworkWitness
