import EthCLSpecs.Proofs.Heze.RaceCheck
import EthCLSpecs.Tests.HezeWitnessSeams
import EthCLSpecs.Tests.HezeNetworkWitness

/-!
# `EthCLSpecs.Tests.HezeRaceWitness`: the composed race has a witness

`race_empty_persists_composed` (`Proofs/Heze/PayloadRaceDecision.lean`) states tier T2 under
`RaceSetting.Core`, `DecisionSetting`, and `RaceCommittees`. This module builds two honest
nodes, `A` and `B`, at the minimal preset, and checks every premise on them except
`QsortMem`. So the premises can hold together. `raceWitness` takes `QsortMem` as its one
hypothesis.

## The scenario

- **Genesis.** 32 active validators, each with the effective balance and the balance
  `32 ETH`. At the minimal preset, `get_committee_count_per_slot` is
  `max(1, min(4, 32 // 8 // 4)) = 1` (phase0 `beacon-chain.md:1080`). So each slot has one
  committee of 4.
- **Block `r`.** Slot `1`, self-built, and the payload leaves out the transaction `tx` of
  the honest list `il` of slot `0`. The first member of the IL committee sends `il`. Node `A`
  receives the envelope, and node `B` never receives it.
- **Votes.** `adv` is the first member of the committee of slot `2`, and every other
  validator is honest. In slot `2`, the three honest members vote for `empty r`, and `adv`
  votes for `full r`. A vote for `full r` needs the payload in the store
  (`gloas/fork-choice.md:875`), so only `A` receives it. In slot `3`, the four members vote
  for `empty r`. A vote counts from the slot after it (`gloas/fork-choice.md:885`), so each
  node receives the votes of a slot at the first tick of the next slot.
- **Head runs.** Each node runs `getHead` at the first tick of slots `2`, `3`, and `4`. The
  window is `[2, 4]`, with the vote slots `2` and `3`. Every validator runs on `A`.

In slot `2`, EMPTY holds the three honest votes and FULL holds the vote of `adv`. The
committee weight is `4 * 32 ETH`, so the proposer score is `51.2 ETH`. Then
`32 + 51.2 < 96` (in ETH) is the first condition of `RaceCommittees`.

## The checks

`raceChk` evaluates every premise that a computation decides. The checks of
`Proofs/Heze/RaceCheck.lean` and `Proofs/Heze/TraceRun.lean` turn it into the premises. The
checkpoint states of every store are those of the seed (`NodeTrace.checkpointStates_eq`), so
the justified state `jstOf s0` serves every head run. `committeesOf` is the committees of
that state, the first `get_committee_count_per_slot` of each slot and none above. `commChk`
checks that each of these committees of a vote slot exists (`.ok`). The
window `[2, 4)` of vote slots lies inside epoch `0`, so `EpochCommittees` holds, and
`RaceCommittees.of_epoch` gives the one-vote condition from the committee partition.

`headRunB` runs `getHead` at each of the six head runs and checks the answer `empty r`. That
check does not use the theorem.

The seams are those of `HezeNetworkWitness.lean`: `strictEngine`, `CryptoBackend.verifyOff`,
the optimistic `[DataAvailability]`, and `pureHasherTag`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (ForkChoiceStoreRun pureState)
open EthCLSpecs.Proofs.Heze
open EthCLSpecs.Proofs.Heze.PayloadRace (slotBalance)

namespace EthCLSpecs.Tests.HezeRaceWitness

open EthCLSpecs.Heze (Preset Config Store State Root BeaconState Validator BeaconBlock
  BeaconBlockBody BeaconBlockHeader SignedBeaconBlock ExecutionPayloadBid ExecutionPayload
  ExecutionRequests Transaction Attestation Checkpoint ValidatorIndex minimal minimalConfig
  getForkchoiceStore getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot
  getCommitteeIndices)
open EthCLSpecs.Heze.Const (farFutureEpoch builderIndexSelfBuild g2PointAtInfinity)
open EthCLSpecs.Tests.HezeWitnessSeams (strictEngine_lawful)
open EthCLSpecs.Tests.HezeNetworkWitness (h1 h2 tx tSend Δ combine_size)
open scoped EthCLSpecs.Tests.HezeWitnessSeams

local instance : Preset := minimal
local instance : HasherTag := pureHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

/-! ## The chain -/

/-- The balance of each validator: `32 ETH` in Gwei. -/
def ebal : UInt64 := 32000000000

/-- The genesis state: slot `0`, 32 active validators of balance `ebal`, and a latest block
header with the body root of the default body. The latest block hash is `h1`. -/
def genesisV : BeaconState :=
  let base := (default : BeaconState)
  let active : Validator :=
    { (default : Validator) with exitEpoch := farFutureEpoch, effectiveBalance := ebal }
  let header : BeaconBlockHeader :=
    { (default : BeaconBlockHeader) with bodyRoot := htr (default : BeaconBlockBody) }
  { base with
    validators := sszOfArray (Array.replicate 32 active)
    balances := sszOfArray (Array.replicate 32 ebal)
    latestBlockHeader := header
    latestBlockHash := h1 }

/-- The uncached box of the genesis state. -/
def genesisState : State := pureState genesisV

/-- The genesis block: the default block with the root of the genesis state. -/
def genesisBlock : BeaconBlock :=
  { (default : BeaconBlock) with stateRoot := bytesToRoot (stateRoot genesisState).1 }

/-- The root of the genesis block. -/
def genesisRoot : Root := htr genesisBlock

/-- The self-build bid of `r`, on the latest block hash of the genesis state. -/
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

/-- The signed block `r`. `verifyOff` accepts the empty signature. -/
def signedR : SignedBeaconBlock := { message := blockR, signature := default }

/-- The seed of each node. -/
def seed : Except StoreTransitionError (Store treeMap) :=
  getForkchoiceStore genesisState genesisBlock

-- The transition of `r` succeeds.
#guard postR.toBool

/-- The inclusion-list committee of slot `0`, as a state at `r` gives it. -/
def committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize :=
  (committeeOf postState 0).getD default

/-- The signed honest list of slot `0`: the first member of `committee`, with `tx`. -/
def signedIl : EthCLSpecs.Heze.SignedInclusionList :=
  { message :=
      { slot := 0, validatorIndex := committee[0], inclusionListCommitteeRoot := htr committee
        transactions := sszOfArray #[tx] }
    signature := default }

/-- The honest list. -/
def il : EthCLSpecs.Heze.InclusionList := signedIl.message

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

/-! ## The votes -/

/-- The committee of slot `t` at genesis. It is the one committee of the slot. The `#guard`
below excludes the fallback for the vote slots. -/
def comm (t : Nat) : Array ValidatorIndex :=
  (getBeaconCommittee genesisState (UInt64.ofNat t) 0).toOption.getD #[]

-- The committees of the vote slots exist at genesis.
#guard [2, 3].all fun t => (getBeaconCommittee genesisState (UInt64.ofNat t) 0).toBool

/-- Aggregation bits of length `n` with the one bit `pos`. -/
def bitsOne (n pos : Nat) : SizzLean.Repr.Bitlist
    (EthCLSpecs.Heze.Const.maxValidatorsPerCommittee * EthCLSpecs.Heze.Const.maxCommitteesPerSlot) :=
  let a := (Array.replicate n false).set! pos true
  if h : a.size ≤ _ then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- The genesis checkpoint. It is the justified checkpoint of the seed. -/
def target0 : Checkpoint := { epoch := 0, root := genesisRoot }

/-- The vote of the member at `pos` of the committee of slot `t`, for `r` with the payload
flag `index`, in committee `0`. -/
def vote (t pos : Nat) (index : UInt64) : Attestation :=
  { aggregationBits := bitsOne (comm t).size pos
    data := { slot := UInt64.ofNat t, index := index, beaconBlockRoot := rootR,
              source := target0, target := target0 }
    signature := default
    committeeBits := bitSet default 0 true }

/-- The adversarial validator: the first member of the committee of slot `2`. -/
def adv : ValidatorIndex := (comm 2)[0]!

/-- Every validator other than `adv` is honest. -/
def honestOf (i : ValidatorIndex) : Bool := i != adv

/-- An honest EMPTY vote of slot `2`, delivered at the first tick of slot `3`. -/
def att2 (pos : Nat) : TraceEvent × Nat := (.handler (.attestation (vote 2 pos 0) false), 18000)

/-- An honest EMPTY vote of slot `3`, delivered at the first tick of slot `4`. -/
def att3 (pos : Nat) : TraceEvent × Nat := (.handler (.attestation (vote 3 pos 0) false), 24000)

/-- The FULL vote of `adv` in slot `2`. -/
def advAtt : TraceEvent × Nat := (.handler (.attestation (vote 2 0 1) false), 18000)

/-! ## The traces -/

/-- The events of node `v` up to slot `2`. Both nodes receive `il` and `r`. Only `A`
(`true`) receives the envelope. -/
def pre12 (v : Bool) : List (TraceEvent × Nat) :=
  [ (.handler (.tick 0), 500), (.inclusionList signedIl, 600),
    (.handler (.tick 6), 6000), (.handler (.block signedR), 6000) ] ++
  (if v then [(.handler (.tick 7), 7000), (.handler (.envelope envelope), 7000)] else []) ++
  [ (.handler (.tick 12), 12000) ]

/-- The trace of node `v`: the votes of slot `2` at the tick of slot `3`, and the votes of
slot `3` at the tick of slot `4`. Only `A` receives the vote of `adv`. -/
def tevs (v : Bool) : List (TraceEvent × Nat) :=
  pre12 v ++
  [ (.handler (.tick 18), 18000), att2 1, att2 2, att2 3 ] ++
  (if v then [advAtt] else []) ++
  [ (.handler (.tick 24), 24000), att3 0, att3 1, att3 2, att3 3 ]

/-- The length of the prefix before the head run of slot `t` at node `v`. -/
def lenOf : Bool → Nat → Nat
  | true, 2 => 7 | true, 3 => 12 | true, _ => 17
  | false, 2 => 5 | false, 3 => 9 | false, _ => 14

/-- The index in the trace of node `v` of the first vote of slot `t`. -/
def baseOf : Bool → Nat → Nat
  | true, 2 => 7 | true, _ => 13 | false, 2 => 5 | false, _ => 10

/-- The index in the trace of node `v` of the vote of `i` in slot `t`. -/
def kOf (v : Bool) (t : Nat) (i : ValidatorIndex) : Nat :=
  baseOf v t + (comm t).toList.idxOf i

/-- Node `v` from the seed `s0`. The end of its trace is the run of the trace, or the seed
when the run fails. `raceChk` excludes the fallback. -/
def nodeOf (s0 : Store treeMap) (v : Bool) : NodeRun treeMap :=
  let res := (runTrace s0 ((tevs v).map Prod.fst)).toOption.getD ([], s0)
  ⟨genesisV, genesisBlock, s0, tevs v, res.1, res.2⟩

/-- The head run of slot `t` at node `v`, at the first millisecond of the slot, with the
head `empty r`. -/
def runOf (s0 : Store treeMap) (v : Bool) (t : Nat) : HeadRun treeMap :=
  let evs := (tevs v).take (lenOf v t)
  let res := (runTrace s0 (evs.map Prod.fst)).toOption.getD ([], s0)
  ⟨evs, res.1, res.2, 6000 * t, .empty rootR⟩

/-! ## The committees -/

/-- The justified state of the seed, as a plain value: the view of the stored box.
`raceChk` checks that the lookup succeeds. -/
def jstOf (s0 : Store treeMap) : BeaconState :=
  ((FcMap.lookup s0.checkpointStates s0.justifiedCheckpoint).getD genesisState).view

/-- The committee count of slot `t` in `jstOf s0`. -/
def countOf (s0 : Store treeMap) (t : Nat) : Nat :=
  getCommitteeCountPerSlot (pureState (jstOf s0)) (computeEpochAtSlot (UInt64.ofNat t))

/-- The committees of slot `t` in `jstOf s0`: the first `countOf s0 t`, and none above. A
committee is the `.ok` value of `getBeaconCommittee`. `commChk` excludes the fallback for the
vote slots. -/
def committeesOf (s0 : Store treeMap) (t ci : Nat) : Array ValidatorIndex :=
  if ci < countOf s0 t then
    (getBeaconCommittee (pureState (jstOf s0)) (UInt64.ofNat t) ci).toOption.getD #[]
  else #[]

/-- Each committee below the count of the vote slots `2` and `3` exists in `jstOf s0`. -/
def commChk (s0 : Store treeMap) : Bool :=
  [2, 3].all fun t => (List.range (countOf s0 t)).all fun ci =>
    (getBeaconCommittee (pureState (jstOf s0)) (UInt64.ofNat t) ci).toBool

/-- `committeeVotes` of `committeesOf s0`, as a computation (`committeeVotes_eq_any`). -/
def votesOf (s0 : Store treeMap) (i : ValidatorIndex) (t : Nat) : Bool :=
  (List.range (countOf s0 t)).any fun ci => (committeesOf s0 t ci).contains i

/-! ## The checks -/

/-- The check of one event at the store `m` before it. A vote targets the justified
checkpoint of the seed and finds it in `m`. A vote of slot `2` or `3` names only committees
below the count. When an attesting index is honest, the vote is for `empty r` with the index
of `honestAttestationIndex`. -/
def attB (s0 : Store treeMap) (e : TraceEvent) (m : Store treeMap) : Bool :=
  match e with
  | .handler (.attestation att _) =>
    decide (att.data.target = s0.justifiedCheckpoint) &&
    FcMap.contains m.checkpointStates att.data.target &&
    (!(decide (2 ≤ att.data.slot.toNat) && decide (att.data.slot.toNat < 4)) ||
      ((getCommitteeIndices att.committeeBits).all (fun ci =>
          decide (ci < getCommitteeCountPerSlot (pureState (jstOf s0))
            (computeEpochAtSlot att.data.slot))) &&
       match attIndicesB m att with
       | some A => !(A.any honestOf) ||
           (att.data.beaconBlockRoot == rootR &&
            att.data.index == honestAttestationIndex (.empty rootR) blockR.slot att.data.slot)
       | none => true))
  | _ => true

/-- Each honest member of a committee of slot `t` has its vote at `kOf v t i`, before the
head run of slot `s`, for the pairs `(s, t)` of the window. -/
def deliverChk (s0 : Store treeMap) (v : Bool) : Bool :=
  [(3, 2), (4, 2), (4, 3)].all fun p =>
    (List.range (countOf s0 p.2)).all fun ci => (committeesOf s0 p.2 ci).all fun i =>
      !honestOf i ||
        (decide (kOf v p.2 i < lenOf v p.1) && deliverAt s0 (tevs v) (kOf v p.2 i) p.2 i)

/-- The check of the head run of slot `t` at node `v`. -/
def runChk (s0 : Store treeMap) (v : Bool) (t : Nat) : Bool :=
  (runTrace s0 ((runOf s0 v t).events.map Prod.fst)).toBool &&
  headRunB (runOf s0 v t) rootR blockR t &&
  decide ((runOf s0 v t).store.justifiedCheckpoint = s0.justifiedCheckpoint)

/-- The checks at node `v`: the run of its trace, the clock, `RootFacts`, the votes, the
facts of the seed at `r`, the honest list, the envelopes, the anchor parent, no attester
slashing, the three head runs, and the deliveries. -/
def nodeChk (s0 : Store treeMap) (v : Bool) : Bool :=
  (runTrace s0 ((tevs v).map Prod.fst)).toBool &&
  decide ((tevs v).Pairwise (fun a b => a.2 ≤ b.2)) &&
  traceAll (rootFactsB rootR blockR.slot committee)
    (fun x m => decide (ClockAt x.1 x.2 m) && attB s0 x.1 m) (tevs v) [] s0 &&
  (FcMap.lookup s0.blockStates rootR).isNone &&
  (FcMap.lookup s0.payloadInclusionListSatisfaction rootR).isNone &&
  (FcMap.lookup s0.payloads rootR).isNone &&
  honestListB (tevs v) il tSend Δ &&
  handlersAll (tevs v) (fun e => match e with
    | .envelope env =>
      !(env.message.beaconBlockRoot == rootR) ||
      !(env.message.payload.transactions.toArray.contains tx)
    | _ => true) &&
  handlersAll (tevs v) (fun e => decide (e.NotAtAnchorParent genesisBlock)) &&
  noSlashingB (tevs v) &&
  [2, 3, 4].all (runChk s0 v) &&
  deliverChk s0 v

/-- The checks at both nodes, the justified state, the genesis time, the anchor, the
committees of the vote slots, and the two balance conditions of `RaceCommittees` over the
validators of `jstOf s0`. -/
def raceChk (s0 : Store treeMap) : Bool :=
  (FcMap.lookup s0.checkpointStates s0.justifiedCheckpoint).isSome &&
  s0.genesisTime == 0 &&
  !(genesisBlock.parentRoot == htr genesisBlock) &&
  commChk s0 &&
  nodeChk s0 true && nodeChk s0 false &&
  (let vs := raceValidators (pureState (jstOf s0)) honestOf (votesOf s0)
   decide (slotBalance vs false 2 + proposerScoreOf (pureState (jstOf s0))
     < slotBalance vs true 2) &&
   decide (slotBalance vs false 3 ≤ slotBalance vs true 3))

/-- `raceChk` at the seed. -/
def allChk : Bool :=
  match seed with
  | .ok s0 => raceChk s0
  | .error _ => false

/-! ## The witness -/

/-- The seed exists. -/
theorem seed_ok : ∃ s0 : Store treeMap, seed = .ok s0 := by
  have hb : seed.toBool = true := by native_decide
  cases h : seed with
  | ok s0 => exact ⟨s0, rfl⟩
  | error e => rw [h] at hb; simp [Except.toBool] at hb

/-- A successful run is its own fallback value. -/
theorem run_eq_getD {ε α β : Type} {x : Except ε (α × β)} (h : x.toBool = true) (d : α × β) :
    x = .ok ((x.toOption.getD d).1, (x.toOption.getD d).2) := by
  cases x <;> simp_all [Except.toBool, Except.toOption]

/-- A successful `Except` value is `.ok` of its `toOption.getD` value. -/
theorem ok_eq_getD {ε α : Type} {x : Except ε α} (h : x.toBool = true) (d : α) :
    x = .ok (x.toOption.getD d) := by
  cases x <;> simp_all [Except.toBool, Except.toOption]

/-- `commChk` gives each committee of a vote slot below the count as the `.ok` value. -/
theorem committeesOf_ok {s0 : Store treeMap} (hc : commChk s0 = true) {t ci : Nat}
    (h2 : 2 ≤ t) (h4 : t < 4) (hci : ci < countOf s0 t) :
    getBeaconCommittee (pureState (jstOf s0)) (UInt64.ofNat t) ci = .ok (committeesOf s0 t ci) := by
  have ht : t ∈ [2, 3] := by
    rcases (by omega : t = 2 ∨ t = 3) with rfl | rfl <;> simp
  have hb := List.all_eq_true.mp (List.all_eq_true.mp hc t ht) ci (List.mem_range.mpr hci)
  unfold committeesOf
  rw [if_pos hci]
  exact ok_eq_getD hb #[]

/-- The events of a head run are a prefix of the trace. -/
theorem runOf_events (s0 : Store treeMap) (v : Bool) (t : Nat) :
    (runOf s0 v t).events = (tevs v).take (lenOf v t) := rfl

/-- The window starts at slot `2`. -/
theorem raceLo_blockR : raceLo blockR = 2 := rfl

/-- The parts of `nodeChk`. -/
structure NodeParts (s0 : Store treeMap) (v : Bool) : Prop where
  /-- The trace runs. -/
  run : (runTrace s0 ((tevs v).map Prod.fst)).toBool = true
  /-- The wall times do not decrease. -/
  mono : decide ((tevs v).Pairwise (fun a b => a.2 ≤ b.2)) = true
  /-- The pass of `RootFacts`, the clock, and the votes. -/
  pass : traceAll (rootFactsB rootR blockR.slot committee)
    (fun x m => decide (ClockAt x.1 x.2 m) && attB s0 x.1 m) (tevs v) [] s0 = true
  /-- The seed holds no state at `r`. -/
  states0 : (FcMap.lookup s0.blockStates rootR).isNone = true
  /-- The seed holds no answer at `r`. -/
  answer0 : (FcMap.lookup s0.payloadInclusionListSatisfaction rootR).isNone = true
  /-- The seed holds no payload at `r`. -/
  payload0 : (FcMap.lookup s0.payloads rootR).isNone = true
  /-- The honest list. -/
  list : honestListB (tevs v) il tSend Δ = true
  /-- Every envelope for `r` omits `tx`. -/
  omits : handlersAll (tevs v) (fun e => match e with
    | .envelope env =>
      !(env.message.beaconBlockRoot == rootR) ||
      !(env.message.payload.transactions.toArray.contains tx)
    | _ => true) = true
  /-- No block at the parent root of the anchor. -/
  nap : handlersAll (tevs v) (fun e => decide (e.NotAtAnchorParent genesisBlock)) = true
  /-- No attester slashing. -/
  noSlash : noSlashingB (tevs v) = true
  /-- The three head runs. -/
  runs : [2, 3, 4].all (runChk s0 v) = true
  /-- The deliveries. -/
  deliver : deliverChk s0 v = true

/-- `nodeChk` gives its parts. -/
theorem NodeParts.of_check {s0 : Store treeMap} {v : Bool} (h : nodeChk s0 v = true) :
    NodeParts s0 v := by
  simp only [nodeChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hrun, hmono⟩, hpass⟩, h0⟩, ha⟩, hp⟩, hl⟩, ho⟩, hn⟩, hs⟩, hr⟩, hd⟩ := h
  exact ⟨hrun, hmono, hpass, h0, ha, hp, hl, ho, hn, hs, hr, hd⟩

/-- The checkpoint states of a store inside a trace are those of the seed. -/
theorem cps_eq {s0 : Store treeMap} {v : Bool} (hp : NodeParts s0 v) {n : Nat}
    {es1 rest : List TraceEvent} (hs : ((tevs v).take n).map Prod.fst = es1 ++ rest)
    {arr : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)} {mid : Store treeMap}
    (hm : NodeTrace s0 es1 arr mid) : mid.checkpointStates = s0.checkpointStates :=
  hm.checkpointStates_eq fun es1' es2' att fb arr' mid' hev hm' => by
    obtain ⟨w, hq⟩ := traceAll_take hp.pass (e := .handler (.attestation att fb))
      (es2 := es2' ++ rest) (by rw [hs, hev]; simp) hm'
    simp only [attB, Bool.and_eq_true] at hq
    exact hq.2.1.2

/-- The check of one vote of a prefix, read back. -/
theorem att_check {s0 : Store treeMap} {v : Bool} (hp : NodeParts s0 v) {n : Nat}
    {att : Attestation} {fb : Bool} {es1 es2 : List TraceEvent}
    (hs : ((tevs v).take n).map Prod.fst = es1 ++ .handler (.attestation att fb) :: es2)
    {arr : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)} {mid : Store treeMap}
    (hm : NodeTrace s0 es1 arr mid) :
    att.data.target = s0.justifiedCheckpoint ∧
    FcMap.contains mid.checkpointStates att.data.target = true ∧
    (2 ≤ att.data.slot.toNat → att.data.slot.toNat < 4 →
      (∀ ci ∈ getCommitteeIndices att.committeeBits,
        ci < getCommitteeCountPerSlot (pureState (jstOf s0)) (computeEpochAtSlot att.data.slot)) ∧
      ∀ A, attIndicesB mid att = some A → A.any honestOf = true →
        att.data.beaconBlockRoot = rootR ∧
        att.data.index = honestAttestationIndex (.empty rootR) blockR.slot att.data.slot) := by
  obtain ⟨w, hq⟩ := traceAll_take hp.pass hs hm
  simp only [attB, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨-, ⟨htgt, hcont⟩, hwin⟩ := hq
  refine ⟨htgt, hcont, fun hlo hhi => ?_⟩
  simp only [hlo, hhi, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hwin
  obtain ⟨hrange, hdata⟩ := hwin
  refine ⟨fun ci hci => of_decide_eq_true (Array.all_eq_true'.mp hrange ci hci), ?_⟩
  intro A hA hany
  rw [hA] at hdata
  simp only [hany, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hdata
  exact hdata

/-- The composed race holds on the two nodes, given `QsortMem`. At each head run of slots
`2`, `3`, and `4`, the head lies below `empty r` and not below `full r`, or a root collision
exists.

`native_decide` evaluates `allChk`, and the checks give `RaceSetting.Core`,
`DecisionSetting`, and `RaceCommittees`. Then `race_empty_persists_composed` applies. The
hasher is the pure-Lean one, so no FFI equivalence axiom enters. `#print axioms` lists one
compiler axiom per `native_decide` call. -/
theorem raceWitness (hsort : QsortMem) :
    ∃ s0 : Store treeMap, seed = .ok s0 ∧
      (RootCollision ∨ ∀ (v : Bool) (t : Nat), 2 ≤ t → t ≤ 4 →
        NodeBelow (runOf s0 v t).store (.empty rootR) (runOf s0 v t).head ∧
          ¬ NodeBelow (runOf s0 v t).store (.full rootR) (runOf s0 v t).head) := by
  obtain ⟨s0, hseed⟩ := seed_ok
  have hall : allChk = true := by native_decide
  simp only [allChk, hseed, raceChk, Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨hjs, hg⟩, hparent⟩, hcc⟩, hA⟩, hB⟩, hfirst, hlater⟩ := hall
  have parts : ∀ v, NodeParts s0 v := fun v => by
    cases v
    · exact NodeParts.of_check hB
    · exact NodeParts.of_check hA
  -- The seed holds only uncached boxes, so the justified state is the box of its view.
  obtain ⟨jv, hjv⟩ :=
    (StorePure.anchor genesisV genesisBlock s0 hseed).checkpointStates_some _ hjs
  have hjst : FcMap.lookup s0.checkpointStates s0.justifiedCheckpoint
      = some (pureState (jstOf s0)) := by
    unfold jstOf
    rw [hjv]
    rfl
  have hK : ∀ t ci, countOf s0 t ≤ ci → committeesOf s0 t ci = #[] := by
    intro t ci h
    unfold committeesOf
    rw [if_neg (by omega)]
  have hvotes : committeeVotes (committeesOf s0) = votesOf s0 :=
    committeeVotes_eq_any (committeesOf s0) (countOf s0) hK
  -- The head runs of the window.
  have runOk : ∀ v, (fun _ => True) v → ∀ t, raceLo blockR ≤ t → t ≤ 4 →
      (runOf s0 v t).Ok (nodeOf s0 v) rootR blockR (jstOf s0) t := by
    intro v _ t hlo hhi
    rw [raceLo_blockR] at hlo
    have hp := parts v
    have hrc : runChk s0 v t = true := List.all_eq_true.mp hp.runs t (by
      rcases (by omega : t = 2 ∨ t = 3 ∨ t = 4) with rfl | rfl | rfl <;> simp)
    simp only [runChk, Bool.and_eq_true, decide_eq_true_eq] at hrc
    obtain ⟨⟨hrun, hhb⟩, hjc⟩ := hrc
    have hrun' : runTrace s0 ((runOf s0 v t).events.map Prod.fst)
        = .ok ((runOf s0 v t).arrivals, (runOf s0 v t).store) := run_eq_getD hrun ([], s0)
    refine HeadRun.Ok.of_check ⟨(tevs v).drop (lenOf v t), (List.take_append_drop _ _).symm⟩
      hrun' rfl ?_ hhb
    rw [hjc, cps_eq hp (n := lenOf v t) (rest := []) (by rw [List.append_nil]; rfl)
      (NodeTrace.of_runTrace hrun'), hjst]
  have hset : RaceSetting.Core (fun _ : Bool => True) (nodeOf s0) (runOf s0) rootR blockR 4
      (jstOf s0) (fun _ => true) honestOf (committeesOf s0) :=
    { nodeOk := fun v _ => by
        have hp := parts v
        exact
          { anchorStore := hseed
            anchorSelf := by simpa using hparent
            anchorSlot := show genesisBlock.slot ≤ blockR.slot by decide
            clocked := ClockedTrace.of_check_and (run_eq_getD hp.run ([], s0))
              (of_decide_eq_true hp.mono) hp.pass
            noAnchorParent := fun e w hm => of_decide_eq_true (handlersAll_spec hp.nap e w hm) }
      runOk := runOk
      honestNode := fun _ _ => trivial
      committee := by
        intro v _ s _ _ att mid ⟨es1, es2, fb, arr, hev, hm⟩ hlo hhi cps s2 ts hrun hts
        rw [raceLo_blockR] at hlo
        rw [runOf_events] at hev
        have hp := parts v
        obtain ⟨htgt, hcont, hwin⟩ := att_check hp hev hm
        rw [storeTargetCheckpointState_run_of_contains mid mid _ hcont] at hrun
        injection hrun with hrun
        injection hrun with hrun
        have hcps : cps = mid.checkpointStates := (congrArg Store.checkpointStates hrun).symm
        rw [hcps, cps_eq hp hev hm, htgt, hjst] at hts
        injection hts with hts
        have hts' : jstOf s0 = ts := congrArg SizzLean.Cache.SSZ.Box.view hts
        subst hts'
        refine ⟨(hwin hlo hhi).1, fun ci => ?_⟩
        have hslot : UInt64.ofNat att.data.slot.toNat = att.data.slot := UInt64.ofNat_toNat
        split
        · rename_i hci
          have hok := committeesOf_ok hcc hlo hhi (ci := ci) (by unfold countOf; rwa [hslot])
          rwa [hslot] at hok
        · rename_i hci
          unfold committeesOf countOf
          rw [hslot, if_neg hci]
      attester := by
        intro v _ s _ _ i hi att mid ⟨es1, es2, fb, arr, hev, hm⟩ ⟨A, hA, hiA⟩ hlo hhi
        have hlo' := hlo
        rw [raceLo_blockR] at hlo'
        rw [runOf_events] at hev
        obtain ⟨-, -, hwin⟩ := att_check (parts v) hev hm
        have hany : A.any honestOf = true := Array.any_eq_true'.mpr ⟨i, hiA, hi⟩
        obtain ⟨hroot, hidx⟩ := (hwin hlo' hhi).2 A hA.eq_attIndicesB hany
        have hQ := runOk true trivial att.data.slot.toNat hlo (by omega)
        exact ⟨hroot, blockR, hQ.block, hidx⟩
      deliver := by
        intro v _ s hlos hs i hi t hlo hts hvote
        rw [raceLo_blockR] at hlo hlos
        rw [hvotes] at hvote
        simp only [votesOf, List.any_eq_true, List.mem_range, Array.contains_iff_mem] at hvote
        obtain ⟨ci, hci, hmem⟩ := hvote
        have hpair : (s, t) ∈ [(3, 2), (4, 2), (4, 3)] := by
          rcases (by omega : (s = 3 ∧ t = 2) ∨ (s = 4 ∧ t = 2) ∨ (s = 4 ∧ t = 3)) with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have h1 := List.all_eq_true.mp (parts v).deliver _ hpair
        have h2 := List.all_eq_true.mp h1 ci (List.mem_range.mpr hci)
        have h3 := Array.all_eq_true'.mp h2 i hmem
        simp only [hi, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h3
        rw [runOf_events]
        exact deliver_of_check h3.2 h3.1
      signer := fun v _ s _ _ i _ => honestSigner_of_check (parts v).noSlash (lenOf v s) i
      sort := hsort }
  have hdec : DecisionSetting (fun _ : Bool => True) (nodeOf s0) (runOf s0) rootR blockR 0
      committee il tSend Δ (fun p => p.transactions.toArray) (fun _ _ => False) tx :=
    { el := strictEngine_lawful
      genesis := fun _ _ => beq_iff_eq.mp hg
      root := fun v _ => RootFacts.of_check (parts v).states0
        (BlockStatesPure.anchor _ _ _ hseed) (parts v).pass
      answer0 := fun v _ => Option.isNone_iff_eq_none.mp (parts v).answer0
      payload0 := fun v _ => Option.isNone_iff_eq_none.mp (parts v).payload0
      list := fun v _ => HonestList.of_check (parts v).list
      omits := fun v _ env w hm hroot' => by
        have := handlersAll_spec (parts v).omits _ w hm
        refine ⟨fun hmem => ?_, id⟩
        simp [hroot'] at this
        exact this hmem
      key := rfl
      sendLo := by decide
      sendHi := by decide
      sendSec := by decide
      slotSec := by decide
      due := by decide
      listed := by native_decide
      wallSec := fun _ _ => by
        show 6000 * raceLo blockR / 1000 ≤ maxMsSeconds
        rw [raceLo_blockR]
        decide }
  -- `committeesOf s0` reads the uncached box of `jstOf s0`, as `EpochCommittees` does.
  -- `commChk` gives the `.ok` committee below the count.
  have hep : EpochCommittees (committeesOf s0) (jstOf s0) 0 2 4 :=
    { start := by decide
      stop := by decide
      fits := by decide
      limit := by decide
      rounds := by decide
      cap := by decide
      eq := fun t h2 h4 ci => by
        split
        · exact committeesOf_ok hcc h2 h4 ‹_›
        · exact if_neg ‹_› }
  have hcomm : RaceCommittees (jstOf s0) honestOf (committeesOf s0) (raceLo blockR) 4 := by
    rw [raceLo_blockR]
    refine RaceCommittees.of_epoch hep ?_ ?_
    · unfold raceVs
      rw [hvotes]
      exact of_decide_eq_true hfirst
    · intro t h2 h4
      obtain rfl : t = 3 := by omega
      unfold raceVs
      rw [hvotes]
      exact of_decide_eq_true hlater
  refine ⟨s0, hseed, ?_⟩
  rcases race_empty_persists_composed combine_size hset hdec hcomm with h | h
  · exact Or.inl h
  · exact Or.inr fun v t h2 h4 => h v trivial t (by rw [raceLo_blockR]; exact h2) h4

end EthCLSpecs.Tests.HezeRaceWitness
