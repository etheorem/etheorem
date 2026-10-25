import EthCLSpecs.Proofs.Heze.FinalityCheck
import EthCLSpecs.Tests.HezeWitnessSeams
import EthCLSpecs.Tests.HezeNetworkWitness
import EthCLSpecs.Tests.HezePaymentWitness

/-!
# `EthCLSpecs.Tests.HezeFinalityWitness`: the censored payload has a finality witness

`censored_payload_final` (`Proofs/Heze/FinalizationLiveness.lean`) takes `FinalitySetting`.
This module builds two honest nodes at the minimal preset and checks every premise of
`FinalitySetting` on them. So the premises can hold together, and the finality results apply
to a real run of the spec. `finalityWitness` takes `QsortMem` as its one hypothesis.

## The scenario

- **Genesis.** 32 active validators, each with the effective balance and the balance
  `32 ETH`. Each slot has one committee of 4. The validators `0` to `21` are honest, and the
  validators `22` to `31` are adversarial: more than two thirds of the stake is honest.
- **Block `r`.** Slot `24`, the first slot of epoch `3`, on the genesis block. Its builder
  builds it itself. The envelope of `r` carries no transaction. Node `A` receives the
  envelope, and node `B` never receives it.
- **The chain.** An honest proposer builds a block in each slot from `25` to `63`. Each block
  builds on the EMPTY edge of its parent, and it carries the votes of the honest members of
  the committee of the slot before it. The adversary does not vote.
- **The nodes.** Each node receives the block of slot `t` and the honest votes of slot `t - 1`
  at the first tick of slot `t`. Each node runs `getHead` after these events, in each slot of
  the window `[25, 64]`. The head of slot `t` is the block of slot `t`. Every validator runs
  on `A`.

`E₁` is `4`. The store finalizes epoch `4` at slot `64`, the first slot of epoch `8`.

## The checks

`allChk` evaluates every premise that a computation decides, with one `native_decide`
(`allChk_ok`). The lemmas of `Proofs/Heze/FinalityCheck.lean` and `Proofs/Heze/RaceCheck.lean`
turn it into the premises (`finalityWitness`). A store run of an honest store follows the
chain, so the premises over store runs reduce to checks over the states and the blocks of the
chain (`ChainStore`). `finalityWitness` also states that both stores finalize epoch `4` at
slot `64`. `finalityWitness_heads` applies `censored_payload_final`.

The check costs about four minutes and 3 GB at two cores.

The seams are those of `HezeNetworkWitness.lean`: `strictEngine`, `CryptoBackend.verifyOff`,
the optimistic `[DataAvailability]`, and `pureHasherTag`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure)
open EthCLSpecs.Proofs.Heze

namespace EthCLSpecs.Tests.HezeFinalityWitness

open EthCLSpecs.Heze (Preset Config Store State Root BeaconState Validator BeaconBlock
  BeaconBlockBody BeaconBlockHeader SignedBeaconBlock ExecutionPayloadBid ExecutionPayload
  Attestation Checkpoint ValidatorIndex ForkChoiceNode minimal minimalConfig getForkchoiceStore
  getBeaconCommittee getCommitteeCountPerSlot computeEpochAtSlot currentEpochOf
  getCommitteeIndices getHead getCurrentSlot getCheckpointBlock)
open EthCLSpecs.Heze.Const (farFutureEpoch builderIndexSelfBuild g2PointAtInfinity)
open EthCLSpecs.Tests.HezeWitnessSeams (strictEngine_lawful)
open EthCLSpecs.Tests.HezeNetworkWitness (h1 h2 combine_size)
open EthCLSpecs.Tests.HezePaymentWitness (bidFor)
open scoped EthCLSpecs.Tests.HezeWitnessSeams

local instance : Preset := minimal
local instance : HasherTag := pureHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

/-! ## The chain -/

/-- The balance of each validator: `32 ETH` in Gwei. -/
def ebal : UInt64 := 32000000000

/-- The genesis state: slot `0`, 32 active validators of balance `ebal`, the participation
lists and the inactivity scores of the registry, and a latest block header with the body root
of the default body. The latest block hash is `h1`. -/
def genesisV : BeaconState :=
  let base := (default : BeaconState)
  let active : Validator :=
    { (default : Validator) with
      exitEpoch := farFutureEpoch
      withdrawableEpoch := farFutureEpoch
      effectiveBalance := ebal }
  let header : BeaconBlockHeader :=
    { (default : BeaconBlockHeader) with bodyRoot := htr (default : BeaconBlockBody) }
  { base with
    validators := sszOfArray (Array.replicate 32 active)
    balances := sszOfArray (Array.replicate 32 ebal)
    previousEpochParticipation := sszOfArray (Array.replicate 32 0)
    currentEpochParticipation := sszOfArray (Array.replicate 32 0)
    inactivityScores := sszOfArray (Array.replicate 32 0)
    latestBlockHeader := header
    latestBlockHash := h1 }

/-- The uncached box of the genesis state. -/
def genesisState : State := pureState genesisV

/-- The genesis block: the default block with the root of the genesis state. -/
def genesisBlock : BeaconBlock :=
  { (default : BeaconBlock) with stateRoot := bytesToRoot (stateRoot genesisState).1 }

/-- The validators `0` to `21` are honest. -/
def honestOf (i : ValidatorIndex) : Bool := decide (i.toNat < 22)

/-- Aggregation bits with a bit for each honest member of the committee `c`. -/
def bitsOf (c : Array ValidatorIndex) : SizzLean.Repr.Bitlist
    (EthCLSpecs.Heze.Const.maxValidatorsPerCommittee * EthCLSpecs.Heze.Const.maxCommitteesPerSlot) :=
  let a := c.map honestOf
  if h : a.size ≤ _ then ⟨a, h⟩ else ⟨#[], by simp⟩

/-- The honest votes of the slot before `pre`, for the block of that slot, with the source and
the target that `process_attestation` reads at `pre`. When `getBeaconCommittee` fails, the
committee is empty and the slot has no vote. -/
def votesFor (pre : State) : Array Attestation :=
  let t := sszGet pre slot - 1
  let c := (getBeaconCommittee pre t 0).toOption.getD #[]
  if !(c.any honestOf) then #[] else
  let e := computeEpochAtSlot t
  let src := if e == currentEpochOf pre then sszGet pre currentJustifiedCheckpoint
    else sszGet pre previousJustifiedCheckpoint
  let tgt := match (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) pre e).run pre with
    | .ok (r, _) => r
    | .error _ => default
  #[{ aggregationBits := bitsOf c
      data := { slot := t, index := 0, beaconBlockRoot := htr (sszGet pre latestBlockHeader),
                source := src, target := { epoch := e, root := tgt } }
      signature := default
      committeeBits := bitSet default 0 true }]

/-- The attestation list of `xs`, empty when `xs` is over the limit. -/
def attList (xs : Array Attestation) :
    SSZList Attestation EthCLSpecs.Heze.Const.maxAttestationsElectra :=
  if h : xs.size ≤ _ then ⟨xs, h⟩ else ⟨#[], by simp⟩

/-- The self-built block of slot `n` on `st`, with the honest votes of slot `n - 1` when
`atts`, and the root of its post-state. -/
def blockAt (st : BeaconState) (n : Nat) (atts : Bool) :
    Option (BeaconState × SignedBeaconBlock) :=
  match (EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) (UInt64.ofNat n)).run
      (pureState st) with
  | .error _ => none
  | .ok ((), pre) =>
    let bid := { bidFor pre builderIndexSelfBuild 0 h2 with value := 0 }
    let unsigned : BeaconBlock :=
      { (default : BeaconBlock) with
        slot := UInt64.ofNat n
        proposerIndex := EthCLSpecs.Heze.getBeaconProposerIndex pre
        parentRoot := htr (sszGet pre latestBlockHeader)
        body := { (default : BeaconBlockBody) with
          attestations := attList (if atts then votesFor pre else #[])
          signedExecutionPayloadBid := { message := bid, signature := g2PointAtInfinity } } }
    match (blockStep { message := unsigned, signature := default } false).run pre with
    | .error _ => none
    | .ok ((), post) =>
      some (post.view,
        { message := { unsigned with stateRoot := bytesToRoot (stateRoot post).1 },
          signature := default })

/-- The blocks at the slots `ns` on `st`. The first block carries no votes. -/
def chainOf : List Nat → BeaconState → Option (BeaconState × List SignedBeaconBlock)
  | [], st => some (st, [])
  | n :: ns, st => do
    let (st1, b) ← blockAt st n (decide (24 < n))
    let (st2, bs) ← chainOf ns st1
    pure (st2, b :: bs)

/-- The end state and the blocks of slots `24` to `63`. -/
def chain : BeaconState × List SignedBeaconBlock :=
  (chainOf ((List.range 40).map (· + 24)) genesisV).getD (genesisV, [])

/-- The blocks of the chain. -/
def blocks : List SignedBeaconBlock := chain.2

/-- Block `r`, the block of slot `24`. -/
def blockR : BeaconBlock := (blocks.head?.map (·.message)).getD default

/-- The root of block `r`. -/
def rootR : Root := htr blockR

/-- The steps of the chain from genesis: slot steps to slot `24`, the block of each slot from
`24` to `63` with the result check, and a slot step to slot `64`. -/
def W : List ChainStep :=
  List.replicate 23 .slot ++ blocks.flatMap (fun b => [.slot, .block b true]) ++ [.slot]

/-- The block of slot `t`, for `t` from `24` to `63`. -/
def blockOf (t : Nat) : Option SignedBeaconBlock := blocks[t - 24]?

/-- The honest votes of slot `t`: the votes in the block of `t + 1`, or for slot `63` the votes
that a block of slot `64` would carry. -/
def gossip (t : Nat) : List Attestation :=
  if t = 63 then
    match (EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) 64).run
        (pureState chain.1) with
    | .ok ((), pre) => (votesFor pre).toList
    | .error _ => []
  else
    match blockOf (t + 1) with
    | some sb => sb.message.body.attestations.toArray.toList
    | none => []

/-- The self-build envelope of `r`. It carries no transaction. -/
def envelope : EthCLSpecs.Heze.SignedExecutionPayloadEnvelope :=
  { message :=
      { payload := { (default : ExecutionPayload) with
          slotNumber := 24, timestamp := 144, parentHash := h1, blockHash := h2,
          prevRandao := blockR.body.signedExecutionPayloadBid.message.prevRandao }
        executionRequests := default
        builderIndex := builderIndexSelfBuild
        beaconBlockRoot := rootR
        parentBeaconBlockRoot := blockR.parentRoot }
    signature := default }

/-! ## The traces -/

/-- The first group of node `v`: the genesis tick, block `r` at the first tick of slot `24`,
and for `A` (`true`) the envelope of `r` at second `147`. -/
def group0 (v : Bool) : List (TraceEvent × Nat) :=
  [ (.handler (.tick 0), 0), (.handler (.tick 144), 144000) ] ++
  ((blockOf 24).toList.map fun sb => (.handler (.block sb), 144000)) ++
  (if v then [(.handler (.tick 147), 147000), (.handler (.envelope envelope), 147000)] else [])

/-- The group of slot `t`: the tick, the block of `t`, and the honest votes of `t - 1`. -/
def groupAt (t : Nat) : List (TraceEvent × Nat) :=
  [(.handler (.tick (UInt64.ofNat (6 * t))), 6000 * t)] ++
  ((blockOf t).toList.map fun sb => (.handler (.block sb), 6000 * t)) ++
  (gossip (t - 1)).map fun a => (.handler (.attestation a false), 6000 * t)

/-- The groups of node `v`: the first group, then one group for each slot from `25` to `64`. -/
def groupsFor (v : Bool) : List (List (TraceEvent × Nat)) :=
  group0 v :: (List.range 40).map fun k => groupAt (25 + k)

/-- The groups of `A`. A closed constant, so the compiled checks build the groups once. -/
def groupsA : List (List (TraceEvent × Nat)) := groupsFor true

/-- The groups of `B`. -/
def groupsB : List (List (TraceEvent × Nat)) := groupsFor false

/-- The groups of node `v`. -/
def groups (v : Bool) : List (List (TraceEvent × Nat)) := if v then groupsA else groupsB

/-- The trace of `A`. -/
def tevsA : List (TraceEvent × Nat) := groupsA.flatten

/-- The trace of `B`. -/
def tevsB : List (TraceEvent × Nat) := groupsB.flatten

/-- The trace of node `v`. -/
def tevs (v : Bool) : List (TraceEvent × Nat) := if v then tevsA else tevsB

/-- The seed of each node. -/
def seed : Except StoreTransitionError (Store treeMap) :=
  getForkchoiceStore genesisState genesisBlock

/-- The arrivals and the store after each group of node `v`, from the seed. -/
abbrev Recs := List (List (EthCLSpecs.Heze.SignedInclusionList × UInt64) × Store treeMap)

/-- The records of node `v` from the seed, or none when the seed fails. -/
def recsFrom (v : Bool) : Recs :=
  match seed with
  | .ok s0 => (passFrom ([], s0) (groups v)).getD []
  | .error _ => []

/-- The records of `A`. A closed constant, so the compiled checks run the pass once. -/
def recsA : Recs := recsFrom true

/-- The records of `B`. -/
def recsB : Recs := recsFrom false

/-- The records of node `v`. -/
def recs (v : Bool) : Recs := if v then recsA else recsB

/-- The head that `getHead` returns on `st`, or the pending node of the zero root on an
error. -/
def headOf (st : Store treeMap) : ForkChoiceNode :=
  match (getHead (StoreTransition := ForkChoiceStoreRun (Store treeMap)) st).run st with
  | .ok (h, _) => h
  | .error _ => .pending default

/-- The head run of slot `t` at node `v`: the groups up to slot `t`, and the record after them.
-/
def runOf (s0 : Store treeMap) (v : Bool) (t : Nat) : HeadRun treeMap :=
  let r := ((recs v)[t - 24]?).getD ([], s0)
  ⟨((groups v).take (t - 23)).flatten, r.1, r.2, 6000 * t, headOf r.2⟩

/-- Node `v` from the seed `s0`. The end of its trace is the last record. -/
def nodeOf (s0 : Store treeMap) (v : Bool) : NodeRun treeMap :=
  let r := ((recs v)[40]?).getD ([], s0)
  ⟨genesisV, genesisBlock, s0, tevs v, r.1, r.2⟩

/-! ## The committees -/

/-- The target of the votes of epoch `e`: the block of the first slot of `e`. -/
def targetOf (e : Nat) : Checkpoint :=
  { epoch := UInt64.ofNat e, root := ((blockOf (8 * e)).map (htr ·.message)).getD default }

/-- The target state of the votes of epoch `e`, from the last store of `A`. -/
def tsOf (_s0 : Store treeMap) (e : Nat) : BeaconState :=
  ((recsA[40]?).bind fun r =>
    (FcMap.lookup r.2.checkpointStates (targetOf e)).map (·.view)).getD genesisV

/-- The committee count of slot `t` in the target state of its epoch. -/
def countOf (s0 : Store treeMap) (t : Nat) : Nat :=
  getCommitteeCountPerSlot (pureState (tsOf s0 (t / 8))) (computeEpochAtSlot (UInt64.ofNat t))

/-- The committees of slot `t`: those of the target state of its epoch, below the count. A
committee is the `.ok` value of `getBeaconCommittee`. `attTarget` excludes the fallback for the
slot of each vote. -/
def committeesOf (s0 : Store treeMap) (t ci : Nat) : Array ValidatorIndex :=
  if ci < countOf s0 t then
    (getBeaconCommittee (pureState (tsOf s0 (t / 8))) (UInt64.ofNat t) ci).toOption.getD #[]
  else #[]

/-- `committeeVotes` of `committeesOf s0`, as a computation (`committeeVotes_eq_any`). -/
def votesOf (s0 : Store treeMap) (i : ValidatorIndex) (t : Nat) : Bool :=
  (List.range (countOf s0 t)).any fun ci => (committeesOf s0 t ci).contains i

/-! ## The checks of one event -/

/-- The target check of the vote `att` at the store `m` before it. The target-state step
returns a state of the target. The vote names committees below the count. Below the count,
each committee of the target state is `.ok` with the value `committeesOf s0` at the vote slot.
`Except` has no `DecidableEq` instance here, so the check compares the `toOption` values. -/
def attTarget (s0 : Store treeMap) (att : Attestation) (m : Store treeMap) : Bool :=
  match (EthCLSpecs.Heze.storeTargetCheckpointState
      (StoreTransition := ForkChoiceStoreRun (Store treeMap)) m att.data.target).run m with
  | .ok (st, _) =>
    match FcMap.lookup st.checkpointStates att.data.target with
    | some ts =>
      decide (getCommitteeCountPerSlot ts (computeEpochAtSlot att.data.slot) =
        countOf s0 att.data.slot.toNat) &&
      (getCommitteeIndices att.committeeBits).all
        (fun ci => decide (ci < countOf s0 att.data.slot.toNat)) &&
      (List.range (countOf s0 att.data.slot.toNat)).all (fun ci =>
        decide ((getBeaconCommittee ts att.data.slot ci).toOption =
          some (committeesOf s0 att.data.slot.toNat ci)))
    | none => false
  | .error _ => false

/-- The data of the vote `att` is the honest data of the head run `q` (`HonestData`). -/
def honestDataQ (att : Attestation) (q : HeadRun treeMap) : Bool :=
  decide (att.data.beaconBlockRoot = q.head.root) &&
  (FcMap.lookup q.store.blocks q.head.root).any (fun hb =>
    decide (att.data.index = honestAttestationIndex q.head hb.slot att.data.slot))

/-- The data of the vote `att` is the honest data of `A` at the vote slot. -/
def honestDataB (s0 : Store treeMap) (att : Attestation) : Bool :=
  honestDataQ att (runOf s0 true att.data.slot.toNat)

/-- The index check of the vote `att` at the store `m` before it. When an attesting index is
honest, the vote has the honest data. Every honest member of the committees of the vote slot is
an attesting index. -/
def attHonest (s0 : Store treeMap) (att : Attestation) (m : Store treeMap) : Bool :=
  match attIndicesB m att with
  | some A =>
    (!(A.any honestOf) || honestDataB s0 att) &&
    (List.range (countOf s0 att.data.slot.toNat)).all (fun ci =>
      (committeesOf s0 att.data.slot.toNat ci).all fun i => !honestOf i || A.contains i)
  | none => false

/-- The check of one event at the store `m` before it: the two checks of a vote, and for a
block, a store slot no later than the block slot. -/
def evB (s0 : Store treeMap) (e : TraceEvent) (m : Store treeMap) : Bool :=
  match e with
  | .handler (.attestation att _) => attTarget s0 att m && attHonest s0 att m
  | .handler (.block sb) => decide (storeSlot m ≤ sb.message.slot.toNat)
  | _ => true

/-! ## The checks of the window -/

/-- The step bound of a walk up the node tree. A store holds at most 41 blocks, so a walk
passes at most `3 * 41` nodes. -/
def fuel : Nat := 200

/-- The states of the run of `W` from genesis, or the empty list when the run fails. A closed
constant, so the compiled checks run the chain once. -/
def Ls : List BeaconState := (runStates (2 ^ 64 - 1) W genesisV).getD []

/-- The justified state of the store of `q`, as a plain value. -/
def jstOf (q : HeadRun treeMap) : BeaconState :=
  ((FcMap.lookup q.store.checkpointStates q.store.justifiedCheckpoint).map (·.view)).getD
    genesisV

/-- `RaceCount` at slot `t` on the justified state `jst`, as a computation over `votesOf s0`. -/
def raceCountB (s0 : Store treeMap) (jst : BeaconState) (t : Nat) : Bool :=
  decide (PayloadRace.advVoted (raceValidators (pureState jst) honestOf (votesOf s0)) 25 t +
      proposerScoreOf (pureState jst) <
    PayloadRace.honestVoted (raceValidators (pureState jst) honestOf (votesOf s0)) 25 t)

/-- The two cases of `FinalitySetting.cases` at the head run `q` of slot `t`. The justified
block is later than `r`. Or it is no later than `r`, the store holds the justified state, and
after the first slot the race count holds. -/
def casesB (s0 : Store treeMap) (q : HeadRun treeMap) (t : Nat) : Bool :=
  (FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root).any
      (fun jb => decide (blockR.slot < jb.slot)) ||
    ((FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root).any
        (fun jb => decide (jb.slot ≤ blockR.slot)) &&
      (FcMap.lookup q.store.checkpointStates q.store.justifiedCheckpoint).isSome &&
      (decide (t ≤ 25) || raceCountB s0 (jstOf q) t))

/-- The checks of the head run `q` of slot `t`: `HeadRun.Base`, the two cases, and from the
first slot of `E₁` on, the checkpoint blocks of `early`. -/
def runQ (s0 : Store treeMap) (q : HeadRun treeMap) (t : Nat) : Bool :=
  baseB q rootR blockR t fuel && casesB s0 q t &&
  (!(decide (32 ≤ t) && decide (t < 64)) || earlyB q.store q.head.root blockR 4)

/-- The checks of the head run of slot `t` at node `v`. -/
def runChk (s0 : Store treeMap) (v : Bool) (t : Nat) : Bool := runQ s0 (runOf s0 v t) t

/-- A committee of slot `t` has an honest member. -/
def hasHonest (s0 : Store treeMap) (t : Nat) : Bool :=
  (List.range (countOf s0 t)).any fun ci => (committeesOf s0 t ci).any honestOf

/-- The index of the first vote of slot `t` in the trace of node `v`. -/
def vIdx (v : Bool) (t : Nat) : Nat :=
  ((tevs v).findIdx? fun x => match x.1 with
    | .handler (.attestation att _) => decide (att.data.slot.toNat = t)
    | _ => false).getD 0

/-- Event `k` of the trace of node `v` is a vote of slot `t`. -/
def voteAtB (v : Bool) (k t : Nat) : Bool :=
  match (tevs v)[k]? with
  | some (.handler (.attestation att _), _) => decide (att.data.slot.toNat = t)
  | _ => false

/-- Take a slot `t` with an honest committee member. A vote of `t` is an event of the head run
of each later slot `s` of the window. -/
def deliverChk (v : Bool) (s0 : Store treeMap) : Bool :=
  (List.range' 26 39).all fun s => (List.range' 25 (s - 25)).all fun t =>
    !hasHonest s0 t ||
      (voteAtB v (vIdx v t) t && decide (vIdx v t < ((groups v).take (s - 23)).flatten.length))

/-- The block step of slot `63` at the end of `W`, or the default block. -/
def sbLast : SignedBeaconBlock :=
  match W.drop (W.length - 2) with
  | [.block sb _, .slot] => sb
  | _ => default

/-- `W` ends with a block step and a slot step. -/
def tailB : Bool :=
  match W.drop (W.length - 2) with
  | [.block _ _, .slot] => true
  | _ => false

/-- The index of the block of slot `63` in the trace of node `v`. -/
def lastIdx (v : Bool) : Nat :=
  ((tevs v).findIdx? fun x => match x.1 with
    | .handler (.block sb) => decide (sb.message.slot.toNat = 63)
    | _ => false).getD 0

/-- Event `lastIdx v` of the trace of node `v` is the block `sbLast`. -/
def lastB (v : Bool) : Bool :=
  match (tevs v)[lastIdx v]? with
  | some (.handler (.block sb), _) => decide (sb = sbLast)
  | _ => false

/-- Every block event of the trace of node `v` is a block of `W`, with a nonzero state root. -/
def blocksB (v : Bool) : Bool :=
  handlersAll (tevs v) fun e => match e with
    | .block sb => (blocksOf W).any (fun b => decide (b = sb.message)) &&
        decide (sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    | _ => true

/-- The checks at node `v`: the records, the wall times, the pass of the event checks and the
clock, the anchor parent, no attester slashing, the blocks, the head runs of the window, the
first slot, the deliveries, the last block, and the finalized epoch at slot `64`. -/
def nodeChk (s0 : Store treeMap) (v : Bool) : Bool :=
  (recs v).length == 41 &&
  decide ((tevs v).Pairwise (fun a b => a.2 ≤ b.2)) &&
  traceAll (fun _ => true) (fun x m => decide (ClockAt x.1 x.2 m) && evB s0 x.1 m) (tevs v) [] s0 &&
  handlersAll (tevs v) (fun e => decide (e.NotAtAnchorParent genesisBlock)) &&
  noSlashingB (tevs v) &&
  blocksB v &&
  (List.range' 25 40).all (runChk s0 v) &&
  notBelowB (runOf s0 v 25).store fuel (.full rootR) (runOf s0 v 25).head &&
  deliverChk v s0 &&
  lastB v &&
  decide ((runOf s0 v 64).store.finalizedCheckpoint.epoch.toNat = 4)

/-- The checks over the chain: its states, the validated steps, the links and the roots of
its blocks, the totals and the stake bound at each state, the honest votes, `HonestChain`, and
the block of slot `63` before the last slot step. -/
def chainChk (s0 : Store treeMap) : Bool :=
  Ls.length == W.length + 1 &&
  validatedB W &&
  linkedB genesisBlock (blocksOf W) &&
  decide (chainRoots genesisBlock (blocksOf W)).Nodup &&
  Ls.all (fun u => decide (RunTotals u) && decide (RegFits u) &&
    decide (3 * advStakeB u honestOf <
      2 * (totBal u).toNat)) &&
  honestVotesB W (runOf s0 true) 25 64 &&
  honestChainB W Ls honestOf 4 &&
  (Ls[W.length]?).any (fun w => decide (epochOf w = 8)) &&
  tailB &&
  decide (sbLast.message.slot.toNat = 63) &&
  (Ls[W.length - 2]?).any (fun u => decide (u.slot.toNat = 63))

/-- The facts of the genesis state, the genesis block, block `r`, and the constants. -/
def genesisChk : Bool :=
  decide (genesisV.slot.toNat = 0) &&
  decide (genesisV.latestBlockHeader.slot.toNat = 0) &&
  (anchorCps genesisV).all (fun x => decide (x.epoch.toNat = 0) &&
    decide (x.root = genesisV.finalizedCheckpoint.root)) &&
  decide (genesisV.finalizedCheckpoint.epoch ≤ genesisV.previousJustifiedCheckpoint.epoch ∧
    genesisV.previousJustifiedCheckpoint.epoch ≤ genesisV.currentJustifiedCheckpoint.epoch ∧
    genesisV.currentJustifiedCheckpoint.epoch ≤ EthCLSpecs.Heze.previousEpochOf genesisState) &&
  decide ((filledHeader genesisV).stateRoot ≠ EthCLSpecs.Heze.zeroRoot) &&
  decide (filledHeader genesisV = headerOf genesisBlock) &&
  decide (htr (filledHeader genesisV) = htr genesisBlock) &&
  decide (genesisBlock.parentRoot ≠ htr genesisBlock) &&
  decide (blockR.slot.toNat = 24) &&
  decide (0 < EthCLSpecs.Heze.Const.minAttestationInclusionDelay.toNat) &&
  decide (1000 ∣ EthCLSpecs.Heze.Const.slotDurationMs.toNat) &&
  decide (0 < EthCLSpecs.Heze.Const.slotDurationMs.toNat) &&
  decide (2 * EthCLSpecs.Heze.Const.slotsPerEpoch ≤
    EthCLSpecs.Heze.Const.slotsPerHistoricalRoot) &&
  decide (EthCLSpecs.Heze.Const.slotsPerEpoch = 8)

/-- Every check at the seed. -/
def allChk : Bool :=
  match seed with
  | .ok s0 => genesisChk && chainChk s0 && nodeChk s0 true && nodeChk s0 false
  | .error _ => false

/-! ## The witness -/

/-- The seed exists. -/
theorem seed_ok : ∃ s0 : Store treeMap, seed = .ok s0 := by
  have hb : seed.toBool = true := by native_decide
  cases h : seed with
  | ok s0 => exact ⟨s0, rfl⟩
  | error e => rw [h] at hb; simp [Except.toBool] at hb

/-- Node `v` has 41 groups. -/
theorem groups_length (v : Bool) : (groups v).length = 41 := by
  cases v <;> simp only [groups, groupsA, groupsB, groupsFor, Bool.false_eq_true, ↓reduceIte,
    List.length_cons, List.length_map, List.length_range]

/-- The trace is the flattened groups. -/
theorem tevs_eq (v : Bool) : tevs v = (groups v).flatten := by
  cases v <;> simp only [tevs, groups, tevsA, tevsB, Bool.false_eq_true, ↓reduceIte]

/-- The events of a head run are the first groups. -/
theorem runOf_events (s0 : Store treeMap) (v : Bool) (t : Nat) :
    (runOf s0 v t).events = ((groups v).take (t - 23)).flatten := by
  simp only [runOf]

/-- The events of a head run are a prefix of the trace. -/
theorem runOf_prefix (s0 : Store treeMap) (v : Bool) (t : Nat) :
    tevs v = (runOf s0 v t).events ++ ((groups v).drop (t - 23)).flatten := by
  rw [tevs_eq, runOf_events, ← List.flatten_append, List.take_append_drop]

/-- The events of a head run are the first events of the trace. -/
theorem events_take (s0 : Store treeMap) (v : Bool) (t : Nat) :
    (runOf s0 v t).events = (tevs v).take (runOf s0 v t).events.length := by
  conv => rhs; rw [runOf_prefix s0 v t]
  rw [List.take_left]

/-- An event of a head run is an event of the trace. -/
theorem mem_tevs_of_runOf {s0 : Store treeMap} {v : Bool} {t : Nat} {e : TraceEvent}
    (h : e ∈ (runOf s0 v t).events.map Prod.fst) : ∃ w, (e, w) ∈ tevs v := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
  exact ⟨y.2, by rw [runOf_prefix s0 v t]; exact List.mem_append_left _ hy⟩

/-- The records of node `v` are the records of the pass from the seed. -/
theorem recs_eq {s0 : Store treeMap} (hseed : seed = .ok s0) (v : Bool) :
    recs v = (passFrom ([], s0) (groups v)).getD [] := by
  cases v <;> simp [recs, recsA, recsB, recsFrom, hseed, groups]

/-- The record of each slot of `[24, 64]` is the run of the trace up to the head run. -/
theorem runOf_run {s0 : Store treeMap} (hseed : seed = .ok s0) {v : Bool}
    (hlen : (recs v).length = 41) {t : Nat} (h1 : 24 ≤ t) (h2 : t ≤ 64) :
    runTrace s0 ((runOf s0 v t).events.map Prod.fst) =
      .ok ((runOf s0 v t).arrivals, (runOf s0 v t).store) := by
  have hrecs := recs_eq hseed v
  cases hp : passFrom ([], s0) (groups v) with
  | none =>
    rw [hrecs, hp] at hlen
    simp at hlen
  | some R =>
    rw [hp, Option.getD_some] at hrecs
    have hi : t - 24 < R.length := by rw [← hrecs, hlen]; omega
    have hr := passFrom_runTrace hp (List.getElem?_eq_getElem hi)
    rw [show t - 24 + 1 = t - 23 by omega] at hr
    simp only [runOf, hrecs, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hr

/-- The end of node `v` is the record of slot `64`. -/
theorem nodeOf_run {s0 : Store treeMap} (hseed : seed = .ok s0) {v : Bool}
    (hlen : (recs v).length = 41) :
    runTrace s0 ((tevs v).map Prod.fst) = .ok ((nodeOf s0 v).arrivals, (nodeOf s0 v).last) := by
  have h := runOf_run hseed hlen (t := 64) (by omega) (by omega)
  rw [runOf_events, List.take_of_length_le (by rw [groups_length]; decide), ← tevs_eq] at h
  exact h

/-- Event `k` of a list splits it. -/
theorem split_at {tevs : List (TraceEvent × Nat)} {k : Nat} {x : TraceEvent × Nat}
    (h : tevs[k]? = some x) :
    tevs.map Prod.fst = (tevs.take k).map Prod.fst ++ x.1 :: (tevs.drop (k + 1)).map Prod.fst := by
  obtain ⟨hk, hx⟩ := List.getElem?_eq_some_iff.mp h
  conv => lhs; rw [← List.take_append_drop k tevs, List.drop_eq_getElem_cons hk, hx]
  simp

/-- The parts of `nodeChk`. -/
structure NodeParts (s0 : Store treeMap) (v : Bool) : Prop where
  /-- The pass has a record for each group. -/
  len : (recs v).length = 41
  /-- The wall times do not decrease. -/
  mono : (tevs v).Pairwise (fun a b => a.2 ≤ b.2)
  /-- The pass of the event checks and the clock. -/
  pass : traceAll (fun _ => true) (fun x m => decide (ClockAt x.1 x.2 m) && evB s0 x.1 m)
    (tevs v) [] s0 = true
  /-- No block at the parent root of the anchor. -/
  nap : handlersAll (tevs v) (fun e => decide (e.NotAtAnchorParent genesisBlock)) = true
  /-- No attester slashing. -/
  noSlash : noSlashingB (tevs v) = true
  /-- The blocks. -/
  blocks : blocksB v = true
  /-- The head runs of the window. -/
  runs : (List.range' 25 40).all (runChk s0 v) = true
  /-- The heads of the first slot avoid `full r`. -/
  first : notBelowB (runOf s0 v 25).store fuel (.full rootR) (runOf s0 v 25).head = true
  /-- The deliveries. -/
  deliver : deliverChk v s0 = true
  /-- The block of slot `63`. -/
  last : lastB v = true
  /-- The finalized epoch at slot `64`. -/
  fin : (runOf s0 v 64).store.finalizedCheckpoint.epoch.toNat = 4

/-- `nodeChk` gives its parts. -/
theorem NodeParts.of_check {s0 : Store treeMap} {v : Bool} (h : nodeChk s0 v = true) :
    NodeParts s0 v := by
  simp only [nodeChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hmono⟩, hpass⟩, hnap⟩, hs⟩, hb⟩, hr⟩, hf⟩, hd⟩, hl⟩, hfin⟩ := h
  exact ⟨hlen, hmono, hpass, hnap, hs, hb, hr, hf, hd, hl, hfin⟩

/-- The check of one event of a head run, read back at the store before it. -/
theorem ev_check {s0 : Store treeMap} {v : Bool} (hp : NodeParts s0 v) {t : Nat}
    {es1 es2 : List TraceEvent} {e : TraceEvent}
    (hev : (runOf s0 v t).events.map Prod.fst = es1 ++ e :: es2)
    {arr : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)} {mid : Store treeMap}
    (hm : NodeTrace s0 es1 arr mid) : evB s0 e mid = true := by
  rw [events_take] at hev
  obtain ⟨w, hq⟩ := traceAll_take hp.pass hev hm
  simp only [Bool.and_eq_true] at hq
  exact hq.2

/-- The target check gives the conclusion of `RaceSetting.Fields.committee`. -/
theorem target_of_check {s0 : Store treeMap} {att : Attestation} {mid : Store treeMap}
    (h : attTarget s0 att mid = true) {cps : treeMap Checkpoint State} {s2 : Store treeMap}
    {ts : BeaconState}
    (hrun : (EthCLSpecs.Heze.storeTargetCheckpointState
      (StoreTransition := ForkChoiceStoreRun (Store treeMap)) mid att.data.target).run mid
        = .ok ({ mid with checkpointStates := cps }, s2))
    (hts : FcMap.lookup cps att.data.target = some (pureState ts)) :
    (∀ ci ∈ getCommitteeIndices att.committeeBits,
      ci < getCommitteeCountPerSlot (pureState ts) (computeEpochAtSlot att.data.slot)) ∧
    ∀ ci, if ci < getCommitteeCountPerSlot (pureState ts) (computeEpochAtSlot att.data.slot)
      then getBeaconCommittee (pureState ts) att.data.slot ci
        = .ok (committeesOf s0 att.data.slot.toNat ci)
      else committeesOf s0 att.data.slot.toNat ci = #[] := by
  unfold attTarget at h
  rw [hrun] at h
  simp only at h
  rw [hts] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hcount, hidx⟩, hcomm⟩ := h
  rw [hcount]
  refine ⟨fun ci hci => of_decide_eq_true (Array.all_eq_true'.mp hidx ci hci), fun ci => ?_⟩
  by_cases hci : ci < countOf s0 att.data.slot.toNat
  · rw [if_pos hci]
    -- `attTarget` compares the `toOption` values. Only an `.ok` value has a `some` value of
    -- `toOption`, so the committee is the `.ok` value `committeesOf s0`.
    have hc := hcomm ci hci
    cases hx : getBeaconCommittee (pureState ts) att.data.slot ci with
    | error e => rw [hx] at hc; simp [Except.toOption] at hc
    | ok c =>
      rw [hx] at hc
      simp only [Except.toOption, Option.some.injEq] at hc
      rw [hc]
  · rw [if_neg hci]
    unfold committeesOf
    rw [if_neg hci]

/-- The index check, read back for the attesting indices `A`. -/
theorem honest_of_check {s0 : Store treeMap} {att : Attestation} {mid : Store treeMap}
    (h : attHonest s0 att mid = true) {A : Array ValidatorIndex} (hA : AttIndices mid att A) :
    (A.any honestOf = true → honestDataB s0 att = true) ∧
    ∀ ci, ci < countOf s0 att.data.slot.toNat → ∀ i ∈ committeesOf s0 att.data.slot.toNat ci,
      honestOf i = true → i ∈ A := by
  unfold attHonest at h
  rw [hA.eq_attIndicesB] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hdata, hall⟩ := h
  refine ⟨fun hany => hdata.resolve_left (by rw [hany]; decide), fun ci hci i hi hh => ?_⟩
  have := Array.all_eq_true'.mp (hall ci hci) i hi
  simp only [hh, Bool.not_true, Bool.false_or] at this
  exact Array.contains_iff_mem.mp this

/-- The checkpoint states of a store of the trace are uncached boxes. -/
theorem storePure_runOf {s0 : Store treeMap} (hseed : seed = .ok s0) {v : Bool}
    (hlen : (recs v).length = 41) {t : Nat} (h1 : 24 ≤ t) (h2 : t ≤ 64) :
    StorePure (runOf s0 v t).store :=
  (NodeTrace.of_runTrace (runOf_run hseed hlen h1 h2)).storePure
    (StorePure.anchor genesisV genesisBlock s0 hseed)

set_option maxHeartbeats 0 in
/-- Every check passes. The compiled evaluation runs both traces, the chain, and every head
run of the window. Lean counts the allocations of that evaluation as heartbeats, so this one
declaration lifts the limit. -/
theorem allChk_ok : allChk = true := by native_decide

/-- The window from `raceLo r` to `finSlot 4` is `[25, 64]`. -/
theorem window {t : Nat} (hb : blockR.slot.toNat = 24) (hlo : raceLo blockR ≤ t)
    (hhi : t ≤ finSlot 4) : 25 ≤ t ∧ t ≤ 64 := by
  unfold raceLo at hlo
  have : finSlot 4 = 64 := rfl
  omega

/-- **The finality witness.** The two honest nodes meet `FinalitySetting` for block `r`, the
genesis anchor, and `E₁ = 4`, given `QsortMem`. Both stores finalize epoch `4` at slot `64`.

`native_decide` evaluates `allChk`, and the lemmas of `FinalityCheck.lean` and `RaceCheck.lean`
turn it into the premises. The hasher is the pure-Lean one, so no FFI equivalence axiom enters.
`#print axioms` lists one compiler axiom per `native_decide` call. -/
theorem finalityWitness (hsort : QsortMem) :
    ∃ s0 : Store treeMap, seed = .ok s0 ∧
      FinalitySetting (fun _ : Bool => True) (nodeOf s0) (runOf s0) rootR blockR genesisV
        genesisBlock 4 (fun _ => true) honestOf (committeesOf s0) ∧
      ∀ v, (runOf s0 v 64).store.finalizedCheckpoint.epoch.toNat = 4 := by
  obtain ⟨s0, hseed⟩ := seed_ok
  have hall := allChk_ok
  simp only [allChk, hseed, Bool.and_eq_true] at hall
  obtain ⟨⟨⟨hgen, hch⟩, hA⟩, hB⟩ := hall
  have parts : ∀ v, NodeParts s0 v := fun v => by
    cases v
    · exact NodeParts.of_check hB
    · exact NodeParts.of_check hA
  simp only [genesisChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hgen
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgslot, hghdr⟩, hgcps⟩, hgord⟩, hgfill⟩, hghead⟩, hgroot⟩, hgpar⟩, hbslot⟩,
    hdelay⟩, hsec⟩, hspos⟩, hsphr⟩, hspe⟩ := hgen
  simp only [chainChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hch
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hLlen, hval⟩, hlinked⟩, hnodup⟩, hstates⟩, hvotesB⟩, hhc⟩, hend⟩, htail⟩,
    hlastSlot⟩, hu63⟩ := hch
  -- The states of the chain.
  have hL : runStates (2 ^ 64 - 1) W genesisV = some Ls := by
    cases h : runStates (2 ^ 64 - 1) W genesisV with
    | none =>
      have : Ls = [] := by unfold Ls; rw [h]; rfl
      rw [this] at hLlen
      simp at hLlen
    | some L => unfold Ls; rw [h]; rfl
  -- The committees.
  have hK : ∀ t ci, countOf s0 t ≤ ci → committeesOf s0 t ci = #[] := by
    intro t ci h
    unfold committeesOf
    rw [if_neg (by omega)]
  have hvotes : committeeVotes (committeesOf s0) = votesOf s0 :=
    committeeVotes_eq_any (committeesOf s0) (countOf s0) hK
  have hraceLo : raceLo blockR = 25 := by unfold raceLo; omega
  have hfin : finSlot 4 = 64 := rfl
  -- Each store of the window is a store of chain blocks.
  have hcs : ∀ v t, 24 ≤ t → t ≤ 64 → ChainStore genesisV genesisBlock W Ls (runOf s0 v t).store :=
    fun v t h1 h2 => ChainStore.of_trace hseed
      (NodeTrace.of_runTrace (runOf_run hseed (parts v).len h1 h2))
      (fun sb hm => by
        obtain ⟨w, hw⟩ := mem_tevs_of_runOf hm
        have := handlersAll_spec (parts v).blocks _ w hw
        simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at this
        obtain ⟨⟨b, hb, rfl⟩, -⟩ := this
        exact hb)
      hL hlinked hnodup
  -- The head runs of the window.
  have hrunQ : ∀ v t, 25 ≤ t → t ≤ 64 → runChk s0 v t = true := fun v t h1 h2 =>
    List.all_eq_true.mp (parts v).runs t (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  have hbase : ∀ v t, 25 ≤ t → t ≤ 64 → (runOf s0 v t).Base (nodeOf s0 v) rootR blockR t :=
    fun v t h1 h2 => by
      have := hrunQ v t h1 h2
      simp only [runChk, runQ, Bool.and_eq_true] at this
      exact HeadRun.Base.of_check ⟨_, runOf_prefix s0 v t⟩
        (runOf_run hseed (parts v).len (by omega) h2) this.1.1
  refine ⟨s0, hseed, ?_, fun v => (parts v).fin⟩
  exact
    { fields :=
        { nodeOk := fun v _ =>
            { anchorStore := hseed
              anchorSelf := hgpar
              anchorSlot := by
                rw [UInt64.le_iff_toNat_le, hbslot]
                show (0 : UInt64).toNat ≤ 24
                decide
              clocked := ClockedTrace.of_check_and (nodeOf_run hseed (parts v).len)
                (parts v).mono (parts v).pass
              noAnchorParent := fun e w hm =>
                of_decide_eq_true (handlersAll_spec (parts v).nap e w hm) }
          honestNode := fun _ _ => trivial
          committee := by
            intro v _ s _ _ att mid ⟨es1, es2, fb, arr, hev, hm⟩ hlo hhi cps s2 ts hrun hts
            have he := ev_check (parts v) hev hm
            simp only [evB, Bool.and_eq_true] at he
            exact target_of_check he.1 hrun hts
          attester := by
            intro v _ s _ _ i hi att mid ⟨es1, es2, fb, arr, hev, hm⟩ ⟨A, hA, hiA⟩ hlo hhi
            have he := ev_check (parts v) hev hm
            simp only [evB, Bool.and_eq_true] at he
            have hany : A.any honestOf = true := Array.any_eq_true'.mpr ⟨i, hiA, hi⟩
            have hd := (honest_of_check he.2 hA).1 hany
            simp only [honestDataB, honestDataQ, Bool.and_eq_true, decide_eq_true_eq,
              Option.any_eq_true] at hd
            obtain ⟨hroot, hb, hlook, hidx⟩ := hd
            exact ⟨hroot, hb, hlook, hidx⟩
          deliver := by
            intro v _ s hlos hs i hi t hlo hts hvote
            rw [hraceLo] at hlo hlos
            rw [hfin] at hs
            rw [hvotes] at hvote
            simp only [votesOf, List.any_eq_true, List.mem_range, Array.contains_iff_mem] at hvote
            obtain ⟨ci, hci, hmem⟩ := hvote
            have hhon : hasHonest s0 t = true := List.any_eq_true.mpr
              ⟨ci, List.mem_range.mpr hci, Array.any_eq_true'.mpr ⟨i, hmem, hi⟩⟩
            have h1 := List.all_eq_true.mp (parts v).deliver s
              (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
            have h2 := List.all_eq_true.mp h1 t (List.mem_range'_1.mpr ⟨hlo, by omega⟩)
            simp only [hhon, Bool.not_true, Bool.false_or, Bool.and_eq_true,
              decide_eq_true_eq] at h2
            obtain ⟨hat, hk⟩ := h2
            unfold voteAtB at hat
            split at hat
            · rename_i att fb w hget
              have hsplit := split_at hget
              -- The events of the head run of `s` are the first events of the trace.
              have hev : (runOf s0 v s).events.map Prod.fst =
                  ((tevs v).take (vIdx v t)).map Prod.fst ++
                    TraceEvent.handler (.attestation att fb) ::
                      (((runOf s0 v s).events).drop (vIdx v t + 1)).map Prod.fst := by
                have hget' : ((runOf s0 v s).events)[vIdx v t]? =
                    some (TraceEvent.handler (.attestation att fb), w) := by
                  rw [events_take, List.getElem?_take_of_lt (by rw [runOf_events]; exact hk)]
                  exact hget
                rw [split_at hget', events_take s0 v s, List.take_take,
                  Nat.min_eq_left (Nat.le_of_lt (by rw [runOf_events]; exact hk))]
              refine ⟨_, _, att, fb, hev, of_decide_eq_true hat, fun arr mid hm A hA => ?_⟩
              have he := ev_check (parts v) hev hm
              simp only [evB, Bool.and_eq_true] at he
              have hslot := of_decide_eq_true hat
              have := (honest_of_check he.2 hA).2 ci (by rw [hslot]; exact hci) i
                (by rw [hslot]; exact hmem) hi
              exact this
            · cases hat
          signer := fun v _ s _ _ i _ => by
            rw [events_take]
            exact honestSigner_of_check (parts v).noSlash _ i
          sort := hsort }
      base := fun v _ t hlo hhi => by
        obtain ⟨h1, h2⟩ := window hbslot hlo hhi
        exact hbase v t h1 h2
      cases := fun v _ t hlo hhi => by
        obtain ⟨h1, h2⟩ := window hbslot hlo hhi
        have hq := hrunQ v t h1 h2
        simp only [runChk, runQ, Bool.and_eq_true] at hq
        have hc := hq.1.2
        simp only [casesB, Bool.or_eq_true, Bool.and_eq_true, Option.any_eq_true,
          decide_eq_true_eq] at hc
        rcases hc with ⟨jb, hjb, hlt⟩ | ⟨⟨⟨jb, hjb, hle⟩, hsome⟩, hcount⟩
        · exact .inr ⟨jb, hjb, hlt⟩
        · left
          obtain ⟨jv, hjv⟩ := (storePure_runOf hseed (parts v).len (by omega) h2).checkpointStates_some
            _ hsome
          have hjst : jstOf (runOf s0 v t) = jv := by
            unfold jstOf
            rw [hjv]
            rfl
          refine ⟨jv, ⟨hbase v t h1 h2, ⟨jb, hjb, hle⟩, hjv⟩, fun hlt => ?_⟩
          rw [hraceLo] at hlt ⊢
          have hr : raceCountB s0 jv t = true := by
            rcases hcount with h | h
            · exact absurd h (by omega)
            · rw [← hjst]
              exact h
          unfold raceCountB at hr
          unfold RaceCount raceVs
          rw [hvotes]
          exact of_decide_eq_true hr
      first := fun v _ => by
        rw [hraceLo]
        exact not_below_of_check (parts v).first
      anchorState := fun _ _ => rfl
      anchorBlock := fun _ _ => rfl
      stateRoots := fun v _ sb w hm => by
        have := handlersAll_spec (parts v).blocks _ w hm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      anchorRoot := hgroot
      anchorHeader := hghead
      anchorFilled := fun h => absurd h (by omega)
      aligned := by omega
      ord := hgord
      roots :=
        { filled := hgfill
          hdrLe := by omega
          roots := fun s _ hs _ => absurd hs (by omega) }
      cps :=
        { zero := fun x hx y hy _ _ => (hgcps x hx).2.trans (hgcps y hy).2.symm
          roots := fun x hx h1 => absurd (hgcps x hx).1 (by omega) }
      sphr := hsphr
      totals := fun v _ t hlo hhi => by
        obtain ⟨h1, h2⟩ := window hbslot hlo hhi
        exact StoreTotals.of_chain (hcs v t (by omega) h2) fun u hu => (hstates u hu).1.1
      late := by
        unfold epochOf
        rw [hgslot, hspe, hbslot]
        decide
      before := by rw [hbslot, hspe]; decide
      delay := hdelay
      seconds := hsec
      slotPos := hspos
      allChains := fun v _ t hlo hhi p q u hsr hp _ => by
        obtain ⟨h1, h2⟩ := window hbslot hlo hhi
        exact advStake_lt_of_chain (hcs v t (by omega) h2)
          (fun u hu => ⟨(hstates u hu).1.2, (hstates u hu).2⟩) hsr hp
      honestVotes := fun v _ t hlo hhi steps i d hsr _ hv hdlo hdhi => by
        obtain ⟨h1, h2⟩ := window hbslot hlo hhi
        rw [hfin] at hdhi
        rw [hraceLo] at hdlo
        exact honestVotes_of_check (hcs v t (by omega) h2) hvotesB hsr hv hdlo hdhi
      early := fun v _ t hlo hhi e c u u' he hck => by
        rw [hspe] at hlo
        rw [hfin] at hhi
        have hq := hrunQ v t (by omega) (by omega)
        simp only [runChk, runQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hq
        have he' := hq.2.resolve_left (by simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
        exact early_of_check he' he hck
      chain := by
        obtain ⟨st, hst⟩ := HonestChain.of_check combine_size hL hval
          ⟨hgfill, by omega, fun s _ hs _ => absurd hs (by omega)⟩
          ⟨fun x hx y hy _ _ => (hgcps x hx).2.trans (hgcps y hy).2.symm,
            fun x hx h1 => absurd (hgcps x hx).1 (by omega)⟩
          hgord hsphr (fun u hu => (hstates u hu).1.1) (by omega)
          (by unfold epochOf; rw [hgslot, Nat.zero_div]; omega)
          (by simpa using hend) hhc
        -- `W` ends with the block of slot `63` and a slot step.
        unfold tailB at htail
        split at htail
        · rename_i sb vb hd
          have hsb : sbLast = sb := by unfold sbLast; rw [hd]
          have hlen2 := congrArg List.length hd
          simp only [List.length_drop, List.length_cons, List.length_nil] at hlen2
          have hsplit : W = W.take (W.length - 2) ++ [.block sb vb, .slot] := by
            rw [← hd, List.take_append_drop]
          obtain ⟨u, hu, hrunp⟩ := runStates_take hL (W.length - 2) (by omega)
          obtain ⟨w, -, hrunb⟩ := runStates_take hL (W.length - 2 + 1) (by omega)
          have hWget : W[W.length - 2]? = some (.block sb vb) := by
            have := congrArg (·[0]?) hd
            simpa [List.getElem?_drop] using this
          have htk : W.take (W.length - 2 + 1) = W.take (W.length - 2) ++ [.block sb vb] := by
            rw [List.take_add_one, hWget]
            rfl
          rw [htk] at hrunb
          obtain ⟨m, hm, hrest⟩ := ChainRun.split hrunb
          rw [hm.det hrunp] at hrest
          cases hrest with
          | block _ _ hstep hnil =>
            cases hnil
            simp only [Option.any_eq_true, decide_eq_true_eq] at hu63
            obtain ⟨u', hu', hslot⟩ := hu63
            rw [hu] at hu'
            cases hu'
            refine ⟨_, W, st, regVals, hst, W.take (W.length - 2), [], sb, vb, u, _, hsplit,
              hrunp, hstep, by rw [hslot, hspe], by rw [hslot, hspe], fun v _ => ?_⟩
            -- The block of slot `63` in the trace of node `v`.
            have hl := (parts v).last
            unfold lastB at hl
            split at hl
            · rename_i sb' w' hget
              have hsb' : sb' = sb := (of_decide_eq_true hl).trans hsb
              subst hsb'
              have hev64 : (runOf s0 v 64).events = tevs v := by
                rw [runOf_events, List.take_of_length_le (by rw [groups_length]; decide), ← tevs_eq]
              rw [hfin]
              refine ⟨_, _, by rw [hev64]; exact split_at hget, fun arr mid hm => ?_⟩
              have he := ev_check (parts v) (t := 64) (by rw [hev64]; exact split_at hget) hm
              have hss : storeSlot mid ≤ sb'.message.slot.toNat := by simpa [evB] using he
              rw [← hsb] at hss
              omega
            · cases hl
        · cases htail }

/-- **The censored payload is final on the witness.** `censored_payload_final` applies to the
two nodes. Every head of the window avoids `full r`, or two blocks, headers or attestation data
share a root. -/
theorem finalityWitness_heads (hsort : QsortMem) :
    ∃ s0 : Store treeMap, seed = .ok s0 ∧
      (RootCollision ∨ HtrCollision EthCLSpecs.Heze.AttestationData ∨
        ∀ (v : Bool) (t : Nat), raceLo blockR ≤ t → t ≤ finSlot 4 →
          ¬ NodeBelow (runOf s0 v t).store (.full rootR) (runOf s0 v t).head) := by
  obtain ⟨s0, hseed, hset, -⟩ := finalityWitness hsort
  refine ⟨s0, hseed, ?_⟩
  rcases censored_payload_final combine_size hset with h | h | ⟨h, -⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr fun v t h1 h2 => h v trivial t h1 h2)

end EthCLSpecs.Tests.HezeFinalityWitness
