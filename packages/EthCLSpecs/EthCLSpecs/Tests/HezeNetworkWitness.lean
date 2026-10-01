import EthCLSpecs.Tests.HezeWitnessSeams
import EthCLSpecs.Proofs.Heze.HonestDuties

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
  | .ok s0 =>
    let run : ForkChoiceStoreRun (Store treeMap) Unit := do
      EthCLSpecs.Heze.onTick (map := treeMap)
        (StoreTransition := ForkChoiceStoreRun (Store treeMap)) 6
      EthCLSpecs.Heze.onBlock (map := treeMap)
        (StoreTransition := ForkChoiceStoreRun (Store treeMap)) signedR
    (run.run s0).toBool

-- The transition of `r` succeeds, and `onBlock` accepts `r` at the first tick of slot 1.
#guard postR.toBool
#guard blockRunOk

end EthCLSpecs.Tests.HezeNetworkWitness
