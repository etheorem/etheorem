import EthCLSpecs.Gloas.Transition
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLSpecs.Gloas.ForkChoice`: the EIP-7732 (ePBS) node-based fork choice

The Gloas fork choice (`specs/gloas/fork-choice.md`, v1.7.0-alpha.11) replaces the
phase0 root-walks with a `ForkChoiceNode = (root, payload_status)` abstraction: a
block's two payload realisations (empty / full) and an undecided pending node are
distinct fork-choice vertices, so `get_ancestor` / `is_ancestor` / `get_weight` /
`get_node_children` / `get_head` all thread a payload status through the DAG.

The shape mirrors `EthCLSpecs.Fulu.ForkChoice`: the `Store` is a `forkstruct` over the
map backing (`EthCLLib.Spec.FcMap`) and the Gloas boxed `State`, the section opens with
`fork_choice_section map`, and the wire handlers are monadic `StoreTransition` actions over
the typed `StoreTransitionError`. The ePBS surface adds `on_execution_payload_envelope`,
`on_payload_attestation_message`, the two per-block PTC vote maps, the parent-payload
assert, and `notify_ptc_messages` (the block's payload attestations replayed per validator
through `on_payload_attestation_message`, so the handler's rejects apply on the
block path too). `on_block` runs the Gloas `state_transition` through
`runNestedStateTransition`.

The `Ord (Vector UInt8 32)` instance is the framework's
(`EthCLLib.Spec.instOrdVectorUInt8`), which names no spec concept and so belongs
to no fork; the `Checkpoint` `Ord` / `BEq` / `Hashable` instances come from the
container derive.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Gloas

/-! ## The fork-choice node -/

/-- A fork-choice vertex (EIP-7732): a block root paired with the payload realisation
the vertex commits to (`PAYLOAD_STATUS_EMPTY` / `_FULL` / `_PENDING`). A pending node
is the undecided block; its empty and full children are the two payload outcomes. -/
forkstruct ForkChoiceNode where
  root : Root
  payloadStatus : UInt8

deriving instance BEq, Inhabited for ForkChoiceNode

/-! ## Store -/

/-- The latest attestation seen from a validator (Gloas): its slot, head vote, and
whether the vote was for the full (payload-present) realisation. The slot, not an
epoch, orders the messages; `payloadPresent` is `data.index == 1`. -/
forkstruct LatestMessage where
  slot : Slot
  root : Root
  payloadPresent : Bool

deriving instance Inhabited for LatestMessage

/-- The Gloas fork-choice store, a `forkstruct` over its map backing and (via the auto
`[Preset]`) the preset / hasher tag. Over the prior fork it adds the ePBS payload state:
the revealed `payloads`, the two per-block PTC vote arrays, and a two-element
`blockTimeliness` (the attestation-due and PTC-due deadlines). -/
forkstruct Store (map : MapKind) [HasherTag] where
  time                          : UInt64
  genesisTime                   : UInt64
  justifiedCheckpoint           : Checkpoint
  finalizedCheckpoint           : Checkpoint
  unrealizedJustifiedCheckpoint : Checkpoint
  unrealizedFinalizedCheckpoint : Checkpoint
  proposerBoostRoot             : Root
  equivocatingIndices           : Array ValidatorIndex
  blocks                        : map Root BeaconBlock
  blockStates                   : map Root State
  blockTimeliness               : map Root (Array Bool)
  checkpointStates              : map Checkpoint State
  latestMessages                : map ValidatorIndex LatestMessage
  unrealizedJustifications      : map Root Checkpoint
  payloads                      : map Root ExecutionPayloadEnvelope
  payloadTimelinessVote         : map Root (Array (Option Bool))
  payloadDataAvailabilityVote   : map Root (Array (Option Bool))

fork_choice_section map

/-! ### Node smart constructors

The fork choice builds a `ForkChoiceNode` at a fixed root in exactly one of the three ePBS
payload realisations. These name the realisation so a call site reads as its intent
(`ForkChoiceNode.pending root`) instead of spelling the `payloadStatus` constant; the constant
lives in one place and the `ForkChoiceNode` field order never leaks to the caller. They sit
inside the section so the `[Preset]` the `Const.payloadStatus…` projection needs is in scope
(auto-bound; they take no `map` / `FcMap`). -/

/-- A PENDING node at `root`: the undecided block, before either payload realisation is
committed. -/
def ForkChoiceNode.pending (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusPending }

/-- An EMPTY node at `root`: the realisation in which the block's payload is absent. -/
def ForkChoiceNode.empty (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusEmpty }

/-- A FULL node at `root`: the realisation in which the block's payload is present. -/
def ForkChoiceNode.full (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusFull }

/-- The all-zero root (an unset `proposer_boost_root`). -/
forkdef fcZeroRoot : Root := Vector.replicate 32 0

/-! ## Time / slot accessors -/

/-- `get_slots_since_genesis` (Gloas, ms-based): `(time - genesis_time) * 1000 //
SLOT_DURATION_MS`. Throwing: `time - genesis_time` (underflow) and `* 1000` (overflow) are
`uint64` ops that raise `ValueError`, uncaught by the runner, so `checkedSub` / `checkedMul`. -/
forkdef getSlotsSinceGenesis (store : Store map) : StoreTransition UInt64 := do
  let elapsed ← checkedSub store.time store.genesisTime "get_slots_since_genesis: time - genesis_time"
  let ms ← checkedMul elapsed 1000 "get_slots_since_genesis: (time - genesis_time) * 1000"
  pure (ms / Const.slotDurationMs)

/-- `get_current_slot`. `GENESIS_SLOT = 0`, so the `+` cannot overflow. -/
forkdef getCurrentSlot (store : Store map) : StoreTransition Slot := do
  pure (Const.genesisSlot + (← getSlotsSinceGenesis store))

/-- `get_current_store_epoch`. -/
forkdef getCurrentStoreEpoch (store : Store map) : StoreTransition Epoch := do
  pure (computeEpochAtSlot (← getCurrentSlot store))

/-- `time_into_slot`, in milliseconds: wall-clock elapsed since the slot start, modulo the slot
length, via the overflow-guarded `seconds_to_milliseconds` (shared with Fulu). Heze inherits. -/
forkdef timeIntoSlotMs (store : Store map) : StoreTransition UInt64 := do
  let seconds ← checkedSub store.time store.genesisTime "time_into_slot: time - genesis_time"
  pure (Fulu.secondsToMilliseconds seconds % Const.slotDurationMs)

/-- A basis-points deadline within a slot, in milliseconds: `bps * SLOT_DURATION_MS //
BASIS_POINTS`. Multiply before the `UInt64` truncating divide, so the floor lands on the full
`bps * SLOT_DURATION_MS` product. The product stays bare rather than `checkedMul`: both
factors are constants, so it peaks near `1.2e8` and cannot reach the `uint64` bound
(`Fulu.bpsDeadlineMs`). -/
forkdef bpsDeadlineMs (bps : UInt64) : UInt64 :=
  bps * Const.slotDurationMs / Const.basisPoints

/-! ## Parent payload status + node walks

The walks under this heading are `fuelLoop`-bounded rather than closed by `termination_by`,
the choice `SPECS_ARCHITECTURE.md` §7.2 asks each loop to justify: the reads raise, so the
walk is monadic, and a measure would have to be carried through a step that can reject. The
bounds are honest counts over a finite acyclic DAG, so fuel-out is unreachable.

`filterBlockTree` and `getHead` are the same kind of walk for the same reason, but they sit
under `Filtered block tree + head` below, so each carries the reason in its own docstring
rather than leaning on this heading.
-/

/-- `get_parent_payload_status(store, block)`: the parent edge is FULL when the
block's committed parent block hash matches the parent's own bid block hash, else
EMPTY. -/
forkdef getParentPayloadStatus (store : Store map) (block : BeaconBlock) : StoreTransition UInt8 := do
  -- The spec reads `store.blocks[block.parent_root]` (a plain `Dict`); a missing parent
  -- raises `KeyError`, so `getOrThrow` rather than the old default-EMPTY.
  let parent ← FcMap.getOrThrow store.blocks block.parentRoot
  let parentBlockHash := block.body.signedExecutionPayloadBid.message.parentBlockHash
  let messageBlockHash := parent.body.signedExecutionPayloadBid.message.blockHash
  pure (if parentBlockHash == messageBlockHash then Const.payloadStatusFull else Const.payloadStatusEmpty)

/-- `is_parent_node_full`: the parent edge of `block` is FULL. -/
forkdef isParentNodeFull (store : Store map) (block : BeaconBlock) : StoreTransition Bool := do
  let status ← getParentPayloadStatus store block
  pure (status == Const.payloadStatusFull)

/-- `get_ancestor(store, node, slot)`: walk parent edges (each edge carrying the
parent's payload status) until at/below `slot`. Fuel-bounded by the block count
(the DAG is finite and acyclic). The spec's `store.blocks[node.root]` is a plain `Dict`
read, so a missing root raises: `getOrThrow` in the monadic `fuelLoop` step (the fuel-out
value is unreachable, so `node` doubles as the `exhausted` sentinel). -/
forkdef getAncestor (store : Store map) (node : ForkChoiceNode) (slot : Slot) :
    StoreTransition ForkChoiceNode :=
  fuelLoop ((FcMap.keys store.blocks).length + 1) node node fun n => do
    let block ← FcMap.getOrThrow store.blocks n.root
    if block.slot > slot then
      let status ← getParentPayloadStatus store block
      pure (.next { root := block.parentRoot, payloadStatus := status })
    else pure (.done n)

/-- `is_ancestor(store, node, ancestor)`: `ancestor` is an ancestor of `node` when
the walk to the ancestor's slot lands on the ancestor's root with a matching payload
status (or the ancestor is PENDING, which matches either realisation). -/
forkdef isAncestor (store : Store map) (node ancestor : ForkChoiceNode) : StoreTransition Bool := do
  let block ← FcMap.getOrThrow store.blocks ancestor.root
  let nodeAncestor ← getAncestor store node block.slot
  if nodeAncestor.root != ancestor.root then pure false
  else pure (nodeAncestor.payloadStatus == ancestor.payloadStatus
    || ancestor.payloadStatus == Const.payloadStatusPending)

/-- `get_checkpoint_block(store, root, epoch)`: the root of the block at the epoch's
first slot, walking from a PENDING node. -/
forkdef getCheckpointBlock (store : Store map) (root : Root) (epoch : Epoch) :
    StoreTransition Root := do
  let node : ForkChoiceNode := .pending root
  let ancestor ← getAncestor store node (computeStartSlotAtEpoch epoch)
  pure ancestor.root

/-- `get_supported_node(store, message)`: the node a latest message supports. A
message for a strictly-earlier block slot decides the payload (full iff
`payload_present`); a same-slot message is PENDING. -/
forkdef getSupportedNode (store : Store map) (message : LatestMessage) :
    StoreTransition ForkChoiceNode := do
  let block ← FcMap.getOrThrow store.blocks message.root
  let payloadStatus :=
    if block.slot < message.slot then
      if message.payloadPresent then Const.payloadStatusFull else Const.payloadStatusEmpty
    else Const.payloadStatusPending
  pure { root := message.root, payloadStatus := payloadStatus }

/-- `get_dependent_root` (Gloas, node-based): the block root that determined the
current epoch's proposer shuffling. -/
forkdef getDependentRoot (store : Store map) (root : Root) : StoreTransition Root := do
  let epoch ← getCurrentStoreEpoch store
  if epoch ≤ Const.minSeedLookahead then pure fcZeroRoot
  else
    let node : ForkChoiceNode := .pending root
    let ancestor ← getAncestor store node (computeStartSlotAtEpoch (epoch - Const.minSeedLookahead) - 1)
    pure ancestor.root

/-! ## Payload-vote predicates -/

/-- `is_payload_verified(store, root)`: the block's payload envelope has been
revealed (`on_execution_payload_envelope` recorded it). -/
forkdef isPayloadVerified (store : Store map) (root : Root) : Bool :=
  FcMap.contains store.payloads root

/-- Tally a three-valued vote array against a flag: `none` matches neither `some
true` nor `some false` (Python's `vote is flag` identity). -/
forkdef voteCount (votes : Array (Option Bool)) (flag : Bool) : Nat :=
  (votes.filter (· == some flag)).size

/-- `payload_timeliness(store, root, timely)`: with no revealed payload the vote is
`not timely`; otherwise a majority of the PTC voted `timely`. -/
forkdef payloadTimeliness (store : Store map) (root : Root) (timely : Bool) : StoreTransition Bool := do
  -- The spec opens with `assert root in store.payload_timeliness_vote`, which fires even on
  -- the unverified early-return path, so it precedes the `is_payload_verified` branch. The
  -- later `[root]` read is then over a present key, so assert and read fuse into one
  -- `getOrAssert` (an `.assert` reject on a miss, the spec's own membership assert).
  let votes ← FcMap.getOrAssert store.payloadTimelinessVote root
    "root in store.payload_timeliness_vote"
  if !isPayloadVerified store root then pure (!timely)
  else pure (voteCount votes timely > Const.payloadTimelyThreshold)

/-- `payload_data_availability(store, root, available)`: the data-availability
counterpart of `payload_timeliness` (same fused assert-and-read, see there). -/
forkdef payloadDataAvailability (store : Store map) (root : Root) (available : Bool) :
    StoreTransition Bool := do
  let votes ← FcMap.getOrAssert store.payloadDataAvailabilityVote root
    "root in store.payload_data_availability_vote"
  if !isPayloadVerified store root then pure (!available)
  else pure (voteCount votes available > Const.dataAvailabilityTimelyThreshold)

/-- `is_previous_slot_payload_decision(store, node)`: the node is the previous
slot's block and carries a decided (EMPTY or FULL) payload status. -/
forkdef isPreviousSlotPayloadDecision (store : Store map) (node : ForkChoiceNode) :
    StoreTransition Bool := do
  -- The spec reads `store.blocks[node.root].slot` (plain `Dict`), raising on a missing root.
  let block ← FcMap.getOrThrow store.blocks node.root
  let currentSlot ← getCurrentSlot store
  let nextSlot ← checkedAdd block.slot 1 "is_previous_slot_payload_decision: blocks[root].slot + 1"
  let isPreviousSlot := nextSlot == currentSlot
  let isPayloadDecision :=
    node.payloadStatus == Const.payloadStatusEmpty || node.payloadStatus == Const.payloadStatusFull
  pure (isPreviousSlot && isPayloadDecision)

/-- `should_extend_payload(store, root)`: whether the FULL realisation of `root`
should win the payload-status tiebreak. -/
forkdef shouldExtendPayload (store : Store map) (root : Root) : StoreTransition Bool := do
  -- The spec opens with `assert store.blocks[root].slot + 1 == get_current_slot(store)`:
  -- read the block (raising on a missing root), then assert the slot equation.
  let rootBlock ← FcMap.getOrThrow store.blocks root
  let currentSlot ← getCurrentSlot store
  let nextSlot ← checkedAdd rootBlock.slot 1 "should_extend_payload: blocks[root].slot + 1"
  assert (nextSlot == currentSlot)
  if !isPayloadVerified store root then pure false
  else
    let proposerRoot := store.proposerBoostRoot
    let payloadIsTimely ← payloadTimeliness store root true
    let payloadDataIsAvailable ← payloadDataAvailability store root true
    -- Python's `or` short-circuits before the two `store.blocks[proposer_root]` reads,
    -- so those raise only when the boost root is set yet absent.
    if (payloadIsTimely && payloadDataIsAvailable) || proposerRoot == fcZeroRoot then
      pure true
    else
      let pb ← FcMap.getOrThrow store.blocks proposerRoot
      -- The final `or` short-circuits too: `is_parent_node_full` (whose
      -- `store.blocks[pb.parent_root]` read throws) never runs when
      -- `pb.parent_root != root` already decides the disjunction.
      if pb.parentRoot != root then pure true
      else isParentNodeFull store pb

/-- `get_payload_status_tiebreaker(store, node)`: the third `get_head` sort key. -/
forkdef getPayloadStatusTiebreaker (store : Store map) (node : ForkChoiceNode) :
    StoreTransition UInt8 := do
  if ← isPreviousSlotPayloadDecision store node then
    if node.payloadStatus == Const.payloadStatusEmpty then pure 1
    else if ← shouldExtendPayload store node.root then pure 2
    else pure 0
  else pure node.payloadStatus

/-! ## Reorg / committee-fraction helpers -/

/-- The per-slot committee weight: total active balance divided across the slots of an epoch
(`get_total_active_balance // SLOTS_PER_EPOCH`). The shared core of `calculateCommitteeFraction`
and `getProposerScore`. `UInt64` truncating division, so the floor is taken here once and both
callers inherit the same rounding. -/
forkdef committeeWeight (state : State) : Gwei :=
  getTotalActiveBalance state / UInt64.ofNat Const.slotsPerEpoch

/-- `calculate_committee_fraction(state, committee_percent)`. -/
forkdef calculateCommitteeFraction (state : State) (committeePercent : UInt64) : Gwei :=
  committeeWeight state * committeePercent / 100

/-- `get_proposer_score`. -/
forkdef getProposerScore (store : Store map) : StoreTransition Gwei := do
  -- `checkpoint_states` is `Checkpoint`-keyed, so `getOrThrowKey` with the checkpoint's
  -- own root as the (diagnostic) error key; the spec reads it as a plain `Dict`.
  let state ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  pure (committeeWeight state * UInt64.ofNat Const.proposerScoreBoost / 100)

/-- `get_attestation_score(store, node, state)`: the effective balance of the
unslashed active validators whose supported node is an ancestor of `node`. The validator
reads are at active-validator indices (in range by construction); the fold is monadic only
to bind `getSupportedNode` / `isAncestor`, which can reject. -/
forkdef getAttestationScore (store : Store map) (node : ForkChoiceNode) (state : State) :
    StoreTransition Gwei := do
  let active := getActiveValidatorIndices state (currentEpochOf state)
  let validators := sszGet state validators
  active.foldlM (init := 0) fun acc i => do
    let idx := i.toNat
    if (validators[idx]!).slashed then pure acc
    else match FcMap.lookup store.latestMessages i with
      | none => pure acc
      | some lm =>
        if store.equivocatingIndices.contains i then pure acc
        else
          let supported ← getSupportedNode store lm
          if ← isAncestor store supported node then pure (acc + (validators[idx]!).effectiveBalance)
          else pure acc

/-- `is_head_weak(store, head_root)`: the head's attestation weight, including the
equivocator weight from its slot's committees, is below the reorg threshold. -/
forkdef isHeadWeak (store : Store map) (headRoot : Root) : StoreTransition Bool := do
  let justifiedState ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let headState ← FcMap.getOrThrow store.blockStates headRoot
  let headBlock ← FcMap.getOrThrow store.blocks headRoot
  let reorgThreshold := calculateCommitteeFraction justifiedState Const.reorgHeadWeightThreshold
  let epoch := computeEpochAtSlot headBlock.slot
  let headNode : ForkChoiceNode := .pending headRoot
  let baseWeight ← getAttestationScore store headNode justifiedState
  let validators := sszGet justifiedState validators
  -- The equivocator read is `justified_state.validators[i]` with `i` drawn from the *head*
  -- state's committees, so a cross-branch registry skew can push it past the justified
  -- registry's end; the spec raises `IndexError` there, hence `sszGetIdx` (the wrapped
  -- `outOfBounds` reject) for this fold's validator reads, and `foldlM` to bind it. The
  -- sibling `getAttestationScore` fold keeps `validators[idx]!`: its indices come from
  -- `getActiveValidatorIndices` on the same state it reads, so they are in range.
  let headWeight ← (List.range (getCommitteeCountPerSlot headState epoch)).foldlM (init := baseWeight) fun acc index => do
    let committee := getBeaconCommittee headState headBlock.slot index
    committee.foldlM (init := acc) fun a i =>
      if store.equivocatingIndices.contains i then do
        let v ← sszGetIdx validators i.toNat
        pure (a + v.effectiveBalance)
      else pure a
  pure (headWeight < reorgThreshold)

/-- `is_parent_strong(store, root)`: the parent node's attestation weight exceeds the
reorg parent threshold. -/
forkdef isParentStrong (store : Store map) (root : Root) : StoreTransition Bool := do
  let justifiedState ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let block ← FcMap.getOrThrow store.blocks root
  let parentThreshold := calculateCommitteeFraction justifiedState Const.reorgParentWeightThreshold
  -- The spec scores the parent at PENDING "regardless of its payload status"
  -- (`ForkChoiceNode(root=block.parent_root, payload_status=PAYLOAD_STATUS_PENDING)`);
  -- it never calls `get_parent_payload_status` here, so no `blocks[parent_root]` read
  -- (and no throw) belongs on this path.
  let parentNode : ForkChoiceNode := .pending block.parentRoot
  let score ← getAttestationScore store parentNode justifiedState
  pure (score > parentThreshold)

/-- `should_apply_proposer_boost(store)`: gate the proposer boost. With an unset
boost root, no boost; with a far-enough-back parent or a non-weak parent head, boost;
otherwise boost only when no equivocating same-proposer sibling competes. -/
forkdef shouldApplyProposerBoost (store : Store map) : StoreTransition Bool := do
  if store.proposerBoostRoot == fcZeroRoot then pure false
  else
    let block ← FcMap.getOrThrow store.blocks store.proposerBoostRoot
    let parentRoot := block.parentRoot
    let parent ← FcMap.getOrThrow store.blocks parentRoot
    let slot := block.slot
    let parentNextSlot ← checkedAdd parent.slot 1 "is_proposer_equivocation: parent.slot + 1"
    if parentNextSlot < slot then pure true
    else if !(← isHeadWeak store parentRoot) then pure true
    else
      -- The spec's equivocation comprehension iterates `store.blocks.items()`
      -- (`gloas/fork-choice.md:501`), so the block comes from the iteration itself, not a
      -- separate read; fold over the `(root, block)` entries in hand. It then reads
      -- `store.block_timeliness[root][PTC_TIMELINESS_INDEX]` (`:503`): the outer `[root]` is a
      -- plain `Dict` (raises `KeyError`, `getOrThrow`), the inner `[PTC_TIMELINESS_INDEX]` a
      -- raising `list` index (`IndexError`, `arrGetIdx`). Both faithful throws.
      let entries : Array (Root × BeaconBlock) :=
        FcMap.fold (fun acc root b => acc.push (root, b)) #[] store.blocks
      let equivExists ← entries.foldlM (init := false) fun found (root, b) => do
        let tl ← FcMap.getOrThrow store.blockTimeliness root
        let timely ← arrGetIdx tl Const.ptcTimelinessIndex
        let bNextSlot ← checkedAdd b.slot 1 "is_proposer_equivocation: block.slot + 1"
        pure (found || (timely && b.proposerIndex == parent.proposerIndex
          && bNextSlot == slot && root != parentRoot))
      pure (!equivExists)

/-- `get_weight(store, node)`: zero for an undecided previous-slot payload; otherwise
the attestation score plus the (gated) proposer boost. -/
forkdef getWeight (store : Store map) (node : ForkChoiceNode) : StoreTransition Gwei := do
  if ← isPreviousSlotPayloadDecision store node then pure 0
  else
    let state ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
      store.justifiedCheckpoint.root
    let attestationScore ← getAttestationScore store node state
    if !(← shouldApplyProposerBoost store) then pure attestationScore
    else
      let proposerBoostNode : ForkChoiceNode := .pending store.proposerBoostRoot
      if ← isAncestor store proposerBoostNode node then
        let proposerScore ← getProposerScore store
        pure (attestationScore + proposerScore)
      else pure attestationScore

/-! ## Filtered block tree + head -/

/-- `get_voting_source(store, block_root)`. -/
forkdef getVotingSource (store : Store map) (blockRoot : Root) : StoreTransition Checkpoint := do
  -- The spec reads `store.blocks[block_root]`, then either
  -- `store.unrealized_justifications[block_root]` or `store.block_states[block_root]`, all
  -- plain `Dict`s that raise on a missing key.
  let block ← FcMap.getOrThrow store.blocks blockRoot
  let currentEpoch ← getCurrentStoreEpoch store
  if currentEpoch > computeEpochAtSlot block.slot then
    FcMap.getOrThrow store.unrealizedJustifications blockRoot
  else
    let hs ← FcMap.getOrThrow store.blockStates blockRoot
    pure (sszGet hs currentJustifiedCheckpoint)

/-- `filter_block_tree`: collect the viable branches into `acc` (a root set),
returning whether `blockRoot` is viable. Root-keyed (unchanged from phase0). The opening
`store.blocks[block_root]` read and the `get_voting_source` reads raise, so the descent is
fuel-bounded rather than closed by `termination_by` (§7.2), the same reason the node-walk
heading gives above. The bound is the block count (the DAG is finite and acyclic, so the
depth cannot exceed it), keeping the function total, no `partial def`; fuel-out is
unreachable and would return `(acc, false)`. -/
forkdef filterBlockTree (store : Store map) (blockRoot : Root) (acc : Array Root) :
    StoreTransition (Array Root × Bool) :=
  go ((FcMap.keys store.blocks).length + 1) blockRoot acc
where
  /-- The viability walk; `fuel` bounds the parent-to-child descent. -/
  go : Nat → Root → Array Root → StoreTransition (Array Root × Bool)
  | 0,        _,         acc => pure (acc, false)
  | fuel + 1, blockRoot, acc => do
    -- The spec opens with `block = store.blocks[block_root]`, a plain `Dict` read that
    -- raises on a missing root; fetch it up front (the fields are reached via the helpers).
    let _ ← FcMap.getOrThrow store.blocks blockRoot
    let children := FcMap.filterKeys store.blocks (fun _ b => b.parentRoot == blockRoot)
    if children.isEmpty then
      -- A leaf branch is viable when its voting source stays close to the justified
      -- checkpoint (genesis, the same epoch, or within two epochs of the current one).
      let currentEpoch ← getCurrentStoreEpoch store
      let votingSource ← getVotingSource store blockRoot
      -- Python's `or` short-circuits, so the `+ 2` runs only once the two cheap disjuncts
      -- fail; the guard keeps that order, since the add is a checked `uint64` op.
      let justifiedWithoutHorizon :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
      let correctJustified ← if justifiedWithoutHorizon then pure true else do
        let horizon ← checkedAdd votingSource.epoch 2 "filter_block_tree: voting_source.epoch + 2"
        pure (decide (horizon ≥ currentEpoch))

      -- The finalized checkpoint must also lie on this branch.
      let finalizedBlock ← getCheckpointBlock store blockRoot store.finalizedCheckpoint.epoch
      let correctFinalized :=
        store.finalizedCheckpoint.epoch == Const.genesisEpoch
          || store.finalizedCheckpoint.root == finalizedBlock
      if correctJustified && correctFinalized then pure (acc.push blockRoot, true) else pure (acc, false)
    else
      let (acc', anyViable) ← children.foldlM (init := (acc, false)) fun (a, viable) child => do
        let (a', v) ← go fuel child a
        pure (a', viable || v)
      if anyViable then pure (acc'.push blockRoot, true) else pure (acc', false)

/-- `get_filtered_block_tree`: the viable-root set rooted at the justified checkpoint. -/
forkdef getFilteredBlockTree (store : Store map) : StoreTransition (Array Root) := do
  let (roots, _) ← filterBlockTree store store.justifiedCheckpoint.root #[]
  pure roots

/-- `get_node_children(store, blocks, node)`: a pending node's children are its own
empty (always) and full (when the payload is verified) realisations; a decided node's
children are the pending nodes of the filtered child blocks whose parent edge matches
this node's status. -/
forkdef getNodeChildren (store : Store map) (blocks : Array Root) (node : ForkChoiceNode) :
    StoreTransition (Array ForkChoiceNode) := do
  if node.payloadStatus == Const.payloadStatusPending then
    let empty : ForkChoiceNode := .empty node.root
    if isPayloadVerified store node.root then
      pure #[empty, ForkChoiceNode.full node.root]
    else pure #[empty]
  else
    let mut result : Array ForkChoiceNode := #[]
    for root in blocks do
      -- The spec's comprehension (`get_node_children`, `gloas/fork-choice.md:547,560-561`) reads
      -- `blocks[root]` (a plain `Dict`), raising on a missing root; `getOrThrow` matches.
      -- Unreachable: `blocks` is `getFilteredBlockTree` output, a subset of `store.blocks`.
      let b ← FcMap.getOrThrow store.blocks root
      -- `get_parent_payload_status(store, blocks[root])` runs only after
      -- `blocks[root].parent_root == node.root` (Python `and` short-circuits), so guard the
      -- throwing helper the same way. It never fires for an unrelated block.
      if b.parentRoot == node.root then
        let parentStatus ← getParentPayloadStatus store b
        if node.payloadStatus == parentStatus then
          result := result.push (ForkChoiceNode.pending root)
    pure result

/-- `get_head`: the LMD-GHOST walk over the node DAG. The max at each step compares
`(get_weight, child.root, get_payload_status_tiebreaker)` in that priority order, ties
broken by the greater root then the greater tiebreaker. Fuel-bounded rather than closed by
`termination_by` (§7.2), because the `max` fold runs through the throwing `betterOf` and a
measure would have to be carried past that reject. Each step either descends to a new root
or flips a pending node to a decided child, so twice the block count bounds it. -/
forkdef getHead (store : Store map) : StoreTransition ForkChoiceNode := do
  let blocks ← getFilteredBlockTree store
  let head : ForkChoiceNode := .pending store.justifiedCheckpoint.root
  -- Monadic `fuelLoop`; the `exhausted` sentinel `head` is unreachable, and the `max` fold is
  -- a `foldlM` over the throwing `betterOf`.
  fuelLoop (2 * (FcMap.keys store.blocks).length + 2) head head fun head => do
    let children ← getNodeChildren store blocks head
    if children.isEmpty then pure (.done head)
    else
      let best ← children.foldlM (init := children[0]!) (betterOf store)
      pure (.next best)
where
  /-- The better of two candidate head nodes under the `(weight, root, tiebreaker)`
  ordering: greater weight wins, ties by greater root, further ties by the greater
  payload-status tiebreaker. The spec's `max(children, key=...)` builds the full key
  3-tuple *eagerly for every child*, so `get_payload_status_tiebreaker` (whose
  `payload_timeliness` membership assert throws) runs even when weight alone decides;
  both tiebreakers are therefore bound before any comparison, keeping a losing child's
  throw observable exactly where pyspec raises it.

  The `foldlM` re-evaluates the accumulator's key on every step, where `max` evaluates each
  child's key once. That leaves which reject surfaces unchanged. An accumulator reached its
  position by surviving an earlier step, so its key already succeeded and cannot throw on the
  re-run, and the first throw stays at the first child whose key raises, in index order, as
  under `max`. What the repetition does cost is a second `getWeight` walk per comparison. -/
  betterOf (store : Store map) (a b : ForkChoiceNode) : StoreTransition ForkChoiceNode := do
    let weightA ← getWeight store a
    let weightB ← getWeight store b
    let tieA ← getPayloadStatusTiebreaker store a
    let tieB ← getPayloadStatusTiebreaker store b
    if weightA > weightB then pure a
    else if weightB > weightA then pure b
    else match compare a.root b.root with
      | Ordering.gt => pure a
      | Ordering.lt => pure b
      | Ordering.eq => pure (if tieA > tieB then a else b)

/-! ## Checkpoint updates -/

/-- `update_checkpoints`. -/
forkdef updateCheckpoints (store : Store map) (j f : Checkpoint) : Store map :=
  let store := if j.epoch > store.justifiedCheckpoint.epoch then { store with justifiedCheckpoint := j } else store
  if f.epoch > store.finalizedCheckpoint.epoch then { store with finalizedCheckpoint := f } else store

/-- `update_unrealized_checkpoints`. -/
forkdef updateUnrealizedCheckpoints (store : Store map) (uj uf : Checkpoint) : Store map :=
  let store := if uj.epoch > store.unrealizedJustifiedCheckpoint.epoch then { store with unrealizedJustifiedCheckpoint := uj } else store
  if uf.epoch > store.unrealizedFinalizedCheckpoint.epoch then { store with unrealizedFinalizedCheckpoint := uf } else store

/-- `compute_pulled_up_tip`: pull up the block's post-state through
`process_justification_and_finalization`, record its unrealized justification, and
(for a prior-epoch block) realize it. The `block_states` / `blocks` reads raise on a
miss, and the pull-up itself propagates: pyspec runs `process_justification_and_finalization`
unguarded, so a reject aborts the surrounding `on_block`. -/
forkdef computePulledUpTip (blockRoot : Root) : StoreTransition Unit := do
  let store ← get
  let state ← FcMap.getOrThrow store.blockStates blockRoot
  let pulled ← runNestedStateTransition state processJustificationAndFinalization
  let cj := sszGet pulled currentJustifiedCheckpoint
  let fz := sszGet pulled finalizedCheckpoint
  set { store with
    unrealizedJustifications := FcMap.insert store.unrealizedJustifications blockRoot cj }
  set (updateUnrealizedCheckpoints (← get) cj fz)
  -- Only now does pyspec read the block and the store clock.
  let block ← FcMap.getOrThrow (← get).blocks blockRoot
  let currentEpoch ← getCurrentStoreEpoch (← get)
  if computeEpochAtSlot block.slot < currentEpoch then
    set (updateCheckpoints (← get) cj fz)

/-! ## on_tick -/

/-- `on_tick_per_slot`. Throwing: `get_current_slot` (before and after the `time` bump) can raise. -/
forkdef onTickPerSlot (store : Store map) (time : UInt64) : StoreTransition (Store map) := do
  let previousSlot ← getCurrentSlot store
  let store := { store with time := time }
  let currentSlot ← getCurrentSlot store
  let store := if currentSlot > previousSlot then { store with proposerBoostRoot := fcZeroRoot } else store
  pure <| if currentSlot > previousSlot && computeSlotsSinceEpochStart currentSlot == 0 then
    updateCheckpoints store store.unrealizedJustifiedCheckpoint store.unrealizedFinalizedCheckpoint
  else store
where
  -- The epoch-start slot is always `≤ slot`, so this `uint64` subtraction cannot underflow.
  computeSlotsSinceEpochStart (slot : Slot) : UInt64 := slot - computeStartSlotAtEpoch (computeEpochAtSlot slot)

/-- `on_tick`: advance the store clock to `time`. Each `on_tick_per_slot` commits before the
next iteration, because pyspec calls it against the live store and a raise partway through the
catch-up leaves the earlier per-slot boost resets and checkpoint updates applied. Threading a
local and committing once discarded them. Same rule as `aed053b`'s, at the site it did not
reach; the loop body can now throw, so the divergence is live in principle. -/
forkdef onTick (time : UInt64) : StoreTransition Unit := do
  let store ← get
  let elapsed ← checkedSub time store.genesisTime "on_tick: time - genesis_time"
  let tickMs ← checkedMul elapsed 1000 "on_tick: (time - genesis_time) * 1000"
  let tickSlot := tickMs / Const.slotDurationMs
  let cur ← getCurrentSlot store
  -- Fuel rather than a measure (§7.2): the body reads the store and can throw, so a decreasing
  -- `tickSlot - get_current_slot` would have to be carried past a rejecting step. The bound is a
  -- Lean artifact, not a spec op: a raw `-` here can only underflow to a huge ceiling when
  -- `tickSlot < cur`, and then the step `.done`s on its first iteration anyway. `fuelIterateM!`
  -- throws on fuel-out because the bound is exact only where `1000` divides `SLOT_DURATION_MS`.
  fuelIterateM! ((tickSlot - cur).toNat + 1) () "on_tick: per-slot catch-up" fun _ => do
    let cs ← getCurrentSlot (← get)
    if cs < tickSlot then
      let bumped ← checkedAdd cs 1 "on_tick: get_current_slot + 1"
      let scaled ← checkedMul bumped Const.slotDurationMs
        "on_tick: (get_current_slot + 1) * SLOT_DURATION_MS"
      let nextSlotTime ← checkedAdd store.genesisTime (scaled / 1000) "on_tick: genesis_time + …"
      set (← onTickPerSlot (← get) nextSlotTime)
      pure (.next ())
    else
      set (← onTickPerSlot (← get) time)
      pure (.done ())

/-! ## record_block_timeliness / update_proposer_boost_root -/

/-- `record_block_timeliness(store, root)`: the two deadlines (attestation-due and
PTC-due), each `is_current_slot ∧ time_into_slot_ms < threshold`. -/
forkdef recordBlockTimeliness (store : Store map) (root : Root) : StoreTransition (Store map) := do
  let block ← FcMap.getOrThrow store.blocks root
  let tis ← timeIntoSlotMs store
  let currentSlot ← getCurrentSlot store
  let isCurrentSlot := currentSlot == block.slot
  let timeliness : Array Bool := #[isCurrentSlot && tis < bpsDeadlineMs Const.attestationDueBpsGloas,
                                   isCurrentSlot && tis < bpsDeadlineMs Const.payloadAttestationDueBps]
  pure { store with blockTimeliness := FcMap.insert store.blockTimeliness root timeliness }

/-- `update_proposer_boost_root(store, head, root)`: boost a timely first block on the
same proposer-shuffling lineage as the pre-insertion head. -/
forkdef updateProposerBoostRoot (store : Store map) (head root : Root) :
    StoreTransition (Store map) := do
  let isFirstBlock := store.proposerBoostRoot == fcZeroRoot
  -- `store.block_timeliness[root][ATTESTATION_TIMELINESS_INDEX]` (`gloas/fork-choice.md:960`):
  -- the outer `[root]` is a plain `Dict` (raises `KeyError`, `getOrThrow`), the inner index a
  -- raising `list` index (`IndexError`, `arrGetIdx`). Both faithful throws.
  let timeliness ← FcMap.getOrThrow store.blockTimeliness root
  let isTimely ← arrGetIdx timeliness Const.attestationTimelinessIndex
  -- The spec's `get_dependent_root(store, root) == get_dependent_root(store, head)`
  -- evaluates left-to-right, so the *root* walk runs (and, when both would miss, throws)
  -- first; bind in that order so the surfaced `missingKey` names the same read.
  let depRoot ← getDependentRoot store root
  let depHead ← getDependentRoot store head
  let isSameDependentRoot := depHead == depRoot
  if isTimely && isFirstBlock && isSameDependentRoot then
    pure { store with proposerBoostRoot := root }
  else pure store

/-! ## PTC vote recording -/

/-- Write `payload_present` / `blob_data_available` at the given PTC positions for the
attested block (the shared core of `on_payload_attestation_message`'s vote write). The
two vote-map reads are plain `Dict` reads in the pinned spec
(`store.payload_timeliness_vote[data.beacon_block_root]`, fork-choice.md:1110-1111),
so a miss rejects with `missingKey` rather than defaulting. -/
forkdef recordPtcVotes (store : Store map) (data : PayloadAttestationData) (ptcIndices : Array Nat) :
    StoreTransition (Store map) := do
  let timelinessVote ← FcMap.getOrThrow store.payloadTimelinessVote data.beaconBlockRoot
  let availabilityVote ← FcMap.getOrThrow store.payloadDataAvailabilityVote data.beaconBlockRoot
  let (timelinessVote, availabilityVote) := ptcIndices.foldl (init := (timelinessVote, availabilityVote))
    fun (tv, av) i => (tv.set! i (some data.payloadPresent), av.set! i (some data.blobDataAvailable))
  pure { store with
    payloadTimelinessVote := FcMap.insert store.payloadTimelinessVote data.beaconBlockRoot timelinessVote
    payloadDataAvailabilityVote := FcMap.insert store.payloadDataAvailabilityVote data.beaconBlockRoot availabilityVote }

/-! ## on_payload_attestation_message -/

/-- `on_payload_attestation_message(store, ptc_message, is_from_block)` (the wire
handler, `is_from_block = false`): the attested block's state slot must match, the
validator must sit in its PTC, the message must be for the current slot, and its
signature must verify; then the votes are recorded. -/
forkdef onPayloadAttestationMessage (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    StoreTransition Unit := do
  let store ← get
  let data := msg.data
  let state ← FcMap.getOrAssert store.blockStates data.beaconBlockRoot
    "data.beacon_block_root in store.block_states"

  if !(data.slot == sszGet state slot) then pure ()
  else
    -- `get_ptc` asserts, and it is a state-file `forkdef`, so its `StateTransitionError`
    -- crosses `evalNestedStateTransition` to reach this store handler. The bind sits after the
    -- `data.slot == state.slot` guard that bounds the index.
    let ptc ← evalNestedStateTransition state (getPtc state data.slot)
    let ptcIndices := (Array.range Const.ptcSize).filter fun i => vget ptc i == msg.validatorIndex
    assert (ptcIndices.size > 0)
    if isFromBlock then set (← recordPtcVotes store data ptcIndices)
    else
      let currentSlot ← getCurrentSlot store
      assert (data.slot == currentSlot)
      let indexed : IndexedPayloadAttestation :=
        { attestingIndices := sszOfArray #[msg.validatorIndex], data := data, signature := msg.signature }
      assert (isValidIndexedPayloadAttestation state indexed)
      set (← recordPtcVotes store data ptcIndices)

/-- `notify_ptc_messages(store, state, payload_attestations)`: replay the block's
payload attestations as per-validator `on_payload_attestation_message`s
(`is_from_block = true`), exactly the pinned loop (fork-choice.md:217-237): each
attesting index becomes a `PayloadAttestationMessage` with an empty signature (never
verified on the block path) and runs through the wire handler. The handler's ungated
rejects apply on this path too, as in pyspec. An unknown `beacon_block_root` rejects with
the spec's `assert data.beacon_block_root in store.block_states` (a `getOrAssert` `.assert`),
and an attester outside the attested block's PTC rejects with
the `ptc_indices` assert. Either reject aborts the whole surrounding `on_block`.
`state` is the block's post-state, used only to resolve the attesting indices
(`get_indexed_payload_attestation`); the handler re-reads the attested block's own
state from the store, as the spec does. -/
forkdef notifyPtcMessages (state : State) (payloadAttestations : Array PayloadAttestation) :
    StoreTransition Unit := do
  if sszGet state slot == 0 then return
  for pa in payloadAttestations do
    -- Second bridge crossing: `get_indexed_payload_attestation` inherited `get_ptc`'s asserts,
    -- and this replay loop runs in the store machine.
    let indexed ← evalNestedStateTransition state (getIndexedPayloadAttestation state pa)
    for idx in indexed.attestingIndices do
      -- `(map := map)`: the handler takes no store argument, so the section's map backing
      -- is undetermined at this call site (the ambient `get`/`set` constraint alone leaves
      -- it a stuck metavariable); name it explicitly.
      onPayloadAttestationMessage (map := map) { validatorIndex := idx, data := pa.data, signature := default } true

/-! ## on_block -/

/-- `on_block`. Rejects (via `assert`) an unknown parent, a
full-but-unverified parent, a future block, or a finality conflict, and propagates a
failed `state_transition` through `runNestedStateTransition`. The ePBS additions over the
prior fork: the parent-full assert, the two per-block vote-map inits, and
`notify_ptc_messages`. -/
forkdef onBlock (signedBlock : SignedBeaconBlock) : StoreTransition Unit := do
  let store ← get
  let block := signedBlock.message
  let parentState ← FcMap.getOrAssert store.blockStates block.parentRoot
    "block.parent_root in store.block_states"

  -- Reject a full-but-unverified parent, a future block, or a finality conflict.
  let parentFull ← isParentNodeFull store block
  assert (!parentFull || isPayloadVerified store block.parentRoot)
  let currentSlot ← getCurrentSlot store
  assert (currentSlot ≥ block.slot)
  let finalizedSlot := computeStartSlotAtEpoch store.finalizedCheckpoint.epoch
  assert (block.slot > finalizedSlot)
  let finalizedBlock ← getCheckpointBlock store block.parentRoot store.finalizedCheckpoint.epoch
  assert (store.finalizedCheckpoint.root == finalizedBlock)

  -- Run the state transition, then snapshot the head before the block is added.
  let postState ← runNestedStateTransition parentState (stateTransition signedBlock)
  let blockRoot := htr block
  -- The head is taken BEFORE the new block is added (`update_proposer_boost_root`).
  let head ← getHead store

  -- Insert the block, its post-state, and the two empty per-block PTC vote maps.
  -- `set` before the replay: the routed `notify_ptc_messages` reads the ambient store,
  -- and pyspec's mutation order has these four writes precede it, so a replay reject
  -- leaves them in place.
  let emptyVotes : Array (Option Bool) := Array.replicate Const.ptcSize none
  set { store with
    blocks := FcMap.insert store.blocks blockRoot block
    blockStates := FcMap.insert store.blockStates blockRoot postState
    payloadTimelinessVote := FcMap.insert store.payloadTimelinessVote blockRoot emptyVotes
    payloadDataAvailabilityVote := FcMap.insert store.payloadDataAvailabilityVote blockRoot emptyVotes }

  -- Replay the block's PTC votes through the wire handler (`is_from_block = true`),
  -- then record timeliness, boost, and pull up the tip. `(map := map)` as in the replay
  -- itself: no store argument determines the backing.
  notifyPtcMessages (map := map) postState block.body.payloadAttestations.toArray
  let store ← get
  -- `set` at each pyspec statement boundary below: `update_proposer_boost_root`'s
  -- dependent-root walks can raise, and so does `compute_pulled_up_tip`'s pull-up, so
  -- each completed write must persist (in-place runner semantics).
  let store ← recordBlockTimeliness store blockRoot
  set store
  let store ← updateProposerBoostRoot store head.root blockRoot
  set store
  let store := updateCheckpoints store (sszGet postState currentJustifiedCheckpoint) (sszGet postState finalizedCheckpoint)
  set store
  -- `(map := map)`: no store argument, so the section's map backing is undetermined here
  -- (the ambient `get`/`set` constraint alone leaves it a stuck metavariable); name it.
  computePulledUpTip (map := map) blockRoot

/-! ## on_execution_payload_envelope -/

/-- `verify_execution_payload_envelope_signature`: the envelope is signed by the
builder's key (the proposer's, for a self-build) under `DOMAIN_BEACON_BUILDER`.

`state.validators[proposer_index]` / `state.builders[builder_index]` are bare indexed reads
with no guarding assert, and `builder_index` comes straight from the untrusted envelope, so an
out-of-range index is the spec's `IndexError`. `sszGetIdx` surfaces it as the wrapped
`.transition (.outOfBounds …)` reject where the former `[i]!` panicked, hence the
`Except StoreTransitionError Bool` signature; the caller binds the result before the `assert`. -/
forkdef verifyExecutionPayloadEnvelopeSignature (state : State) (signedEnv : SignedExecutionPayloadEnvelope) :
    Except StoreTransitionError Bool := do
  let builderIndex := signedEnv.message.builderIndex
  let pubkey ←
    if builderIndex == Const.builderIndexSelfBuild then do
      let validatorIndex := (sszGet state latestBlockHeader).proposerIndex
      let v ← sszGetIdx (sszGet state validators) validatorIndex.toNat
      pure v.pubkey
    else do
      let b ← sszGetIdx (sszGet state builders) builderIndex.toNat
      pure b.pubkey
  let signingRoot := computeSigningRoot signedEnv.message (getDomain state Const.domainBeaconBuilder (currentEpochOf state))
  pure (blsVerify pubkey signingRoot signedEnv.signature)

-- The envelope path crosses the execution layer twice: `verify_and_notify_new_payload`
-- inside the verification, and `is_data_available` at the handler. Both answers belong to
-- something outside the vector, so both enter through the framework seams in
-- `EthCLLib.Spec.Engine` (which carries the optimistic-default rationale for each) rather
-- than being written as constants here. Scoped to the two declarations that need them; at
-- file scope the binders would ride on every later declaration.
section EngineSeam
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- `verify_and_notify_new_payload(new_payload_request)` (`gloas/fork-choice.md:657-666`):
the EL's answer on the revealed payload. Reads the `[ExecutionEngine]` seam; the trust
boundary and the always-`true` default are documented on `EthCLLib.Spec.ExecutionEngine`,
including why the commitments reach it unmapped by
`kzg_commitment_to_versioned_hash`. -/
forkdef verifyAndNotifyNewPayload (payload : ExecutionPayload)
    (blobKzgCommitments : Array KZGCommitment) (parentBeaconBlockRoot : Root)
    (executionRequests : ExecutionRequests) : Bool :=
  -- The three class parameters are implicit on the projection and only `Payload` is
  -- recoverable from the value arguments (`Tx` appears in no argument of this method, and
  -- `Requests` is an `ExecutionRequests` the elaborator would have to guess a class instance
  -- for). Name all three, as the seam's own binder spells them.
  ExecutionEngine.verifyAndNotifyNewPayload (Payload := ExecutionPayload) (Tx := Transaction)
    (Requests := ExecutionRequests) payload blobKzgCommitments parentBeaconBlockRoot
    executionRequests

/-- `is_data_available(beacon_block_root)` (`gloas/fork-choice.md:243-257`): whether the
block's column sidecars retrieve and verify. Gloas modified the Fulu signature to take a
root and retrieve the sidecars itself, through a function the spec marks implementation
and context dependent, so the answer reads the `[DataAvailability]` seam. Fulu's own
`isDataAvailable` is unaffected: it is handed the columns the step lists and checks them
for real. -/
forkdef isDataAvailable (beaconBlockRoot : Root) : Bool :=
  DataAvailability.isDataAvailable beaconBlockRoot

/-- `verify_execution_payload_envelope`: the consensus-side envelope checks, closing with
the EL's `verify_and_notify_new_payload` answer. Returns the cache-warmed
state (the `hashTreeRoot` computed for the block-root check) in
`Except StoreTransitionError`; the handler stores it back so the warm tree is kept
rather than thrown away. -/
forkdef verifyExecutionPayloadEnvelope (state : State) (signedEnv : SignedExecutionPayloadEnvelope) :
    Except StoreTransitionError State := do
  let envelope := signedEnv.message
  let payload := envelope.payload

  -- Builder signature over the envelope.
  assert (← verifyExecutionPayloadEnvelopeSignature state signedEnv)

  -- Block-root binding: the envelope commits to this state's block header (warmed
  -- with its computed state root) and its parent.
  let (stateRootBytes, warm) := stateRoot state
  let header : BeaconBlockHeader := { sszGet state latestBlockHeader with stateRoot := bytesToRoot stateRootBytes }
  assert (envelope.beaconBlockRoot == htr header)
  assert (envelope.parentBeaconBlockRoot == (sszGet state latestBlockHeader).parentRoot)

  -- Bid consistency: the revealed payload matches the committed bid and the state.
  let bid := sszGet state latestExecutionPayloadBid
  assert (envelope.builderIndex == bid.builderIndex)
  assert (payload.prevRandao == bid.prevRandao)
  assert (payload.gasLimit == bid.gasLimit)
  assert (payload.blockHash == bid.blockHash)
  assert (htr envelope.executionRequests == bid.executionRequestsRoot)
  assert (payload.slotNumber == sszGet state slot)
  assert (payload.parentHash == sszGet state latestBlockHash)
  -- `compute_time_at_slot` (`Fulu/Time.lean`, inherited): `liftErr` wraps its `.arithmetic`
  -- fault as `.transition (.arithmetic …)`, the store machine's shape for the same fault.
  let expectedTime ← liftErr (computeTimeAtSlot state (sszGet state slot))
  assert (payload.timestamp == expectedTime)
  assert (htr payload.withdrawals == htr (sszGet state payloadExpectedWithdrawals))

  -- The EL answer, last as in the spec. `bid.blobKzgCommitments` supplies the request's
  -- versioned hashes (unmapped, see the seam's docstring); the parent root and the
  -- execution requests come off the envelope.
  assert (verifyAndNotifyNewPayload payload bid.blobKzgCommitments.toArray
    envelope.parentBeaconBlockRoot envelope.executionRequests)
  return warm

/-- `on_execution_payload_envelope`: verify the revealed payload envelope against the
committed bid and record it. The recorded payload flips the block's head node to FULL
and enables `is_payload_verified`. -/
forkdef onExecutionPayloadEnvelope (signedEnv : SignedExecutionPayloadEnvelope) : StoreTransition Unit := do
  let store ← get
  let envelope := signedEnv.message
  let state ← FcMap.getOrAssert store.blockStates envelope.beaconBlockRoot
    "envelope.beacon_block_root in store.block_states"
  -- `assert is_data_available(envelope.beacon_block_root)` (`gloas/fork-choice.md:1055`),
  -- between the block-state read and the verification, as the spec orders it.
  assert (isDataAvailable envelope.beaconBlockRoot)

  match verifyExecutionPayloadEnvelope state signedEnv with
  | .error e => throw e
  | .ok warm => set { store with
      blockStates := FcMap.insert store.blockStates envelope.beaconBlockRoot warm,
      payloads := FcMap.insert store.payloads envelope.beaconBlockRoot envelope }

end EngineSeam

/-! ## on_attestation -/

/-- `store_target_checkpoint_state`: cache the target's state, advancing to the
target epoch start if needed. The pinned `process_slots` call is unguarded, so a
rejected advance propagates (wrapped `.transition`) and nothing is cached, aborting
the surrounding `on_attestation` with the store unchanged. Reachable only from
degenerate near-zero-stake states. Caching the unadvanced base state instead would leave
a wrong-slot entry for later reads to consume. -/
forkdef storeTargetCheckpointState (store : Store map) (target : Checkpoint) :
    StoreTransition (Store map) := do
  if FcMap.contains store.checkpointStates target then pure store
  else
    -- `target not in store.checkpoint_states` is a membership guard (faithful), but the
    -- following `store.block_states[target.root]` is a plain `Dict` read that raises.
    let base ← FcMap.getOrThrow store.blockStates target.root
    let targetSlot := computeStartSlotAtEpoch target.epoch
    let advanced ←
      if (sszGet base slot) < targetSlot then
        runNestedStateTransition base (processSlots targetSlot)
      else pure base
    pure { store with checkpointStates := FcMap.insert store.checkpointStates target advanced }

/-- `validate_on_attestation` (Gloas): adds `index ∈ {0, 1}`, same-slot ⇒ index 0,
and full vote (index 1) ⇒ the head block's payload is verified. -/
forkdef validateOnAttestation (store : Store map) (att : Attestation) (isFromBlock : Bool) :
    StoreTransition Unit := do
  let target := att.data.target
  let currentEpoch ← getCurrentStoreEpoch store
  let previousEpoch := if currentEpoch > Const.genesisEpoch then currentEpoch - 1 else Const.genesisEpoch

  -- Target epoch in range and consistent with the attestation slot; both roots known.
  assert (isFromBlock || target.epoch == currentEpoch || target.epoch == previousEpoch)
  assert (target.epoch == computeEpochAtSlot att.data.slot)
  assert (FcMap.contains store.blocks target.root)
  assert (FcMap.contains store.blocks att.data.beaconBlockRoot)

  -- Head-block shape: the Gloas index/payload-presence rules and the checkpoint binding.
  let b ← FcMap.getOrThrow store.blocks att.data.beaconBlockRoot
  assert (b.slot ≤ att.data.slot)
  assert (att.data.index == 0 || att.data.index == 1)
  assert (!(b.slot == att.data.slot) || att.data.index == 0)
  assert (!(att.data.index == 1) || isPayloadVerified store att.data.beaconBlockRoot)
  let checkpointBlock ← getCheckpointBlock store att.data.beaconBlockRoot target.epoch
  assert (target.root == checkpointBlock)
  let currentSlot ← getCurrentSlot store
  -- `att.data.slot` is wire-controlled and the epoch-scope guard above is skipped when
  -- `is_from_block`, so a block-implied attestation reaches here with an arbitrary slot. The
  -- bare `+` wraps `0xFFFF…FFFF + 1` to `0`, `currentSlot ≥ 0` holds for every store, and the
  -- attestation is ACCEPTED into `latest_messages`, corrupting the head walk. pyspec
  -- (`phase0/fork-choice.md:813`) forms a checked `uint64` sum that raises `ValueError`, which
  -- `expect_assertion_error` does not catch. Sequenced after every preceding assert, matching
  -- Python's evaluation order.
  let attestationDeadline ← checkedAdd att.data.slot 1
    "on_attestation: attestation.data.slot + 1"
  assert (currentSlot ≥ attestationDeadline)

/-- `update_latest_messages` (Gloas): slot-ordered, carrying `payload_present`
(`data.index == 1`), skipping equivocators. -/
forkdef updateLatestMessages (store : Store map) (attestingIndices : Array ValidatorIndex)
    (att : Attestation) : Store map := Id.run do
  let slot := att.data.slot
  let beaconBlockRoot := att.data.beaconBlockRoot
  let payloadPresent := att.data.index == 1

  let mut lm := store.latestMessages
  for i in attestingIndices do
    if !store.equivocatingIndices.contains i then
      match FcMap.lookup lm i with
      | some prev => if slot > prev.slot then lm := FcMap.insert lm i { slot := slot, root := beaconBlockRoot, payloadPresent := payloadPresent }
      | none      => lm := FcMap.insert lm i { slot := slot, root := beaconBlockRoot, payloadPresent := payloadPresent }
  return { store with latestMessages := lm }

/-- `on_attestation`. `isFromBlock` distinguishes a wire attestation from a
block-implied one. -/
forkdef onAttestation (att : Attestation) (isFromBlock : Bool) : StoreTransition Unit := do
  validateOnAttestation (← get) att isFromBlock

  -- `store_target_checkpoint_state` mutates `checkpoint_states` before the
  -- indexed-attestation assert below can reject; `set` at the pyspec statement
  -- boundary so an expected rejection keeps the cache (in-place runner semantics).
  let store ← storeTargetCheckpointState (← get) att.data.target
  set store
  let targetState ← FcMap.getOrThrowKey store.checkpointStates att.data.target att.data.target.root
  let attesting := (← liftErr (getAttestingIndices targetState att)).qsort (· < ·)
  let indexedAttestation : IndexedAttestation := { attestingIndices := sszOfArray attesting, data := att.data, signature := att.signature }
  assert (isValidIndexedAttestation targetState indexedAttestation)

  set (updateLatestMessages store attesting att)

/-! ## on_attester_slashing -/

/-- `on_attester_slashing`: mark the intersection of the two attestations' indices as
equivocating. -/
forkdef onAttesterSlashing (asl : AttesterSlashing) : StoreTransition Unit := do
  assert (isSlashableAttestationData asl.attestation1.data asl.attestation2.data)
  let store ← get
  let state ← FcMap.getOrThrow store.blockStates store.justifiedCheckpoint.root
  assert (isValidIndexedAttestation state asl.attestation1)
  assert (isValidIndexedAttestation state asl.attestation2)

  let set2 := asl.attestation2.attestingIndices.toArray
  let inter := arrayInter asl.attestation1.attestingIndices.toArray set2
  let eq := arrayUnion store.equivocatingIndices inter
  set { store with equivocatingIndices := eq }

/-! ## get_forkchoice_store -/

/-- `get_forkchoice_store(anchor_state, anchor_block)` (Gloas,
`consensus-specs/specs/gloas/fork-choice.md:183-184`): `block_timeliness` seeds `[True, True]`
for the anchor, the three ePBS maps start empty, and the time uses the ms-based
`SLOT_DURATION_MS * slot // 1000` form. The pyspec opens with
`assert anchor_block.state_root == hash_tree_root(anchor_state)`, so the seed is a throwing
`Except StoreTransitionError` action rather than a total store literal (reject branch
vectorless; Heze's `pinAnchorRejects` locks the identical assert). -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) :
    Except StoreTransitionError (Store map) := do
  -- `anchor_block.state_root == hash_tree_root(anchor_state)`: the boxed state hashes
  -- through `stateRoot` (the cached-tree path), not `htr` (which wants a bare `SSZRepr`).
  assert (anchorBlock.stateRoot == bytesToRoot (stateRoot anchorState).1)
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }

  -- `uint64(anchor_state.genesis_time + SLOT_DURATION_MS * anchor_state.slot // 1000)`
  -- (`phase0/fork-choice.md:223`): both the product and the sum are checked. `anchor_state`
  -- comes straight off the wire, so a slot at or above `2^64 / SLOT_DURATION_MS` wraps and
  -- seeds the store with a wrong clock where pyspec errors.
  let elapsedMs ← checkedMul Const.slotDurationMs (sszGet anchorState slot)
    "get_forkchoice_store: SLOT_DURATION_MS * anchor_state.slot"
  let storeTime ← checkedAdd (sszGet anchorState genesisTime) (elapsedMs / 1000)
    "get_forkchoice_store: genesis_time + SLOT_DURATION_MS * slot // 1000"
  pure
    { time := storeTime
      genesisTime := sszGet anchorState genesisTime
      justifiedCheckpoint := cp, finalizedCheckpoint := cp
      unrealizedJustifiedCheckpoint := cp, unrealizedFinalizedCheckpoint := cp
      proposerBoostRoot := fcZeroRoot
      equivocatingIndices := #[]
      blocks := FcMap.insert FcMap.empty anchorRoot anchorBlock
      blockStates := FcMap.insert FcMap.empty anchorRoot anchorState
      blockTimeliness := FcMap.insert FcMap.empty anchorRoot #[true, true]
      checkpointStates := FcMap.insert FcMap.empty cp anchorState
      latestMessages := FcMap.empty
      unrealizedJustifications := FcMap.insert FcMap.empty anchorRoot cp
      payloads := FcMap.empty
      payloadTimelinessVote := FcMap.empty
      payloadDataAvailabilityVote := FcMap.empty }

end

end EthCLSpecs.Gloas
