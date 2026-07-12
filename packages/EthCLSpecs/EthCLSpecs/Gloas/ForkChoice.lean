import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Fulu.ForkChoice
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
assert, and `notify_ptc_messages` (the block's payload attestations replayed per
validator, a pure store transform). `on_block` runs the Gloas `state_transition` through
`runStateTransition`.

The `Ord (Vector UInt8 32)` instance and the `Checkpoint` `Ord` / `BEq` / `Hashable`
instances are the Fulu ones (`EthCLSpecs.Fulu.instOrdBytes32`), in scope through
`open EthCLSpecs.Fulu`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLSpecs.Fulu

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
SLOT_DURATION_MS`. -/
forkdef getSlotsSinceGenesis (store : Store map) : UInt64 :=
  ((store.time - store.genesisTime) * 1000) / Const.slotDurationMs

/-- `get_current_slot`. -/
forkdef getCurrentSlot (store : Store map) : Slot := Const.genesisSlot + getSlotsSinceGenesis store

/-- `get_current_store_epoch`. -/
forkdef getCurrentStoreEpoch (store : Store map) : Epoch := computeEpochAtSlot (getCurrentSlot store)

/-- `time_into_slot`, in milliseconds: wall-clock elapsed since the slot start, modulo the slot
length. -/
forkdef timeIntoSlotMs (store : Store map) : UInt64 :=
  ((store.time - store.genesisTime) * 1000) % Const.slotDurationMs

/-- A basis-points deadline within a slot, in milliseconds: `bps * SLOT_DURATION_MS //
BASIS_POINTS`. Multiply before the `UInt64` truncating divide, so the floor lands on the full
`bps * SLOT_DURATION_MS` product. -/
forkdef bpsDeadlineMs (bps : UInt64) : UInt64 :=
  bps * Const.slotDurationMs / Const.basisPoints

/-! ## Parent payload status + node walks -/

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
  let epoch := getCurrentStoreEpoch store
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
  let isPreviousSlot := block.slot + 1 == getCurrentSlot store
  let isPayloadDecision :=
    node.payloadStatus == Const.payloadStatusEmpty || node.payloadStatus == Const.payloadStatusFull
  pure (isPreviousSlot && isPayloadDecision)

/-- `should_extend_payload(store, root)`: whether the FULL realisation of `root`
should win the payload-status tiebreak. -/
forkdef shouldExtendPayload (store : Store map) (root : Root) : StoreTransition Bool := do
  -- The spec opens with `assert store.blocks[root].slot + 1 == get_current_slot(store)`:
  -- read the block (raising on a missing root), then assert the slot equation.
  let rootBlock ← FcMap.getOrThrow store.blocks root
  assert (rootBlock.slot + 1 == getCurrentSlot store)
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
      -- `store.blocks[pb.parent_root]` read now throws) never runs when
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
reads are at active-validator indices (in range by construction); this becomes monadic only
to bind the now-throwing `getSupportedNode` / `isAncestor`. -/
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
  -- `outOfBounds` reject) in place of the silent-default `[i.toNat]!`. The folds turn
  -- monadic (`foldlM`) only to bind that throwing read.
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
    if parent.slot + 1 < slot then pure true
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
        pure (found || (timely && b.proposerIndex == parent.proposerIndex
          && b.slot + 1 == slot && root != parentRoot))
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
  let currentEpoch := getCurrentStoreEpoch store
  if currentEpoch > computeEpochAtSlot block.slot then
    FcMap.getOrThrow store.unrealizedJustifications blockRoot
  else
    let hs ← FcMap.getOrThrow store.blockStates blockRoot
    pure (sszGet hs currentJustifiedCheckpoint)

/-- `filter_block_tree`: collect the viable branches into `acc` (a root set),
returning whether `blockRoot` is viable. Root-keyed (unchanged from phase0). The
recursion is fuel-bounded by the block count (the DAG is finite and acyclic, so the
depth cannot exceed it), keeping the function total, no `partial def`. -/
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
      let currentEpoch := getCurrentStoreEpoch store
      let votingSource ← getVotingSource store blockRoot
      let correctJustified :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
          || votingSource.epoch + 2 ≥ currentEpoch

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
      -- now-throwing helper the same way. It never fires for an unrelated block.
      if b.parentRoot == node.root then
        let parentStatus ← getParentPayloadStatus store b
        if node.payloadStatus == parentStatus then
          result := result.push (ForkChoiceNode.pending root)
    pure result

/-- `get_head`: the LMD-GHOST walk over the node DAG. The max at each step compares
`(get_weight, child.root, get_payload_status_tiebreaker)` in that priority order, ties
broken by the greater root then the greater tiebreaker. Fuel-bounded: each step either
descends to a new root or flips a pending node to a decided child. -/
forkdef getHead (store : Store map) : StoreTransition ForkChoiceNode := do
  let blocks ← getFilteredBlockTree store
  let head : ForkChoiceNode := .pending store.justifiedCheckpoint.root
  -- Monadic `fuelLoop` (the `exhausted` sentinel `head` is unreachable, matching the old
  -- `fuelIterate` fuel-out); the `max` fold becomes a `foldlM` over `betterOf`.
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
  throw observable exactly where pyspec raises it. -/
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
(for a prior-epoch block) realize it. Best-effort, so `EStateM.run`, not
`runStateTransition`. -/
forkdef computePulledUpTip (store : Store map) (blockRoot : Root) : StoreTransition (Store map) := do
  -- The spec reads `store.block_states[block_root]` and `store.blocks[block_root]`, both
  -- plain `Dict`s that raise on a miss. (The inner `processJustificationAndFinalization`
  -- stays best-effort — a separate discrepancy from the missing-key throws this sweep fixes.)
  let state ← FcMap.getOrThrow store.blockStates blockRoot
  let block ← FcMap.getOrThrow store.blocks blockRoot
  let act : EStateM StateTransitionError State Unit := processJustificationAndFinalization
  match act.run state with
  | .ok _ pulled =>
    let cj := sszGet pulled currentJustifiedCheckpoint
    let fz := sszGet pulled finalizedCheckpoint
    let store := { store with unrealizedJustifications := FcMap.insert store.unrealizedJustifications blockRoot cj }
    let store := updateUnrealizedCheckpoints store cj fz
    pure (if computeEpochAtSlot block.slot < getCurrentStoreEpoch store then updateCheckpoints store cj fz else store)
  | .error _ _ => pure store

/-! ## on_tick -/

/-- `on_tick_per_slot`. -/
forkdef onTickPerSlot (store : Store map) (time : UInt64) : Store map :=
  let previousSlot := getCurrentSlot store
  let store := { store with time := time }
  let currentSlot := getCurrentSlot store
  let store := if currentSlot > previousSlot then { store with proposerBoostRoot := fcZeroRoot } else store
  if currentSlot > previousSlot && computeSlotsSinceEpochStart currentSlot == 0 then
    updateCheckpoints store store.unrealizedJustifiedCheckpoint store.unrealizedFinalizedCheckpoint
  else store
where
  computeSlotsSinceEpochStart (slot : Slot) : UInt64 := slot - computeStartSlotAtEpoch (computeEpochAtSlot slot)

/-- `advance_store_time`: catch up slot-by-slot, then set the exact time (the pure core
of `on_tick`, ms-based). Fuel-bounded by the number of slots to advance. -/
forkdef advanceStoreTime (store : Store map) (time : UInt64) : Store map :=
  -- The slot `time` lands in. It is loop-invariant (only `time` and the fixed
  -- `genesisTime` feed it, and `onTickPerSlot` touches neither), so it doubles as
  -- the fuel bound and is read unchanged inside the sweep.
  let targetSlot := ((time - store.genesisTime) * 1000) / Const.slotDurationMs
  let fuel := (targetSlot - getCurrentSlot store).toNat + 1
  fuelIterate fuel store fun store =>
    if getCurrentSlot store < targetSlot then
      let nextSlotTime := store.genesisTime + (getCurrentSlot store + 1) * Const.slotDurationMs / 1000
      .next (onTickPerSlot store nextSlotTime)
    else .done (onTickPerSlot store time)

/-- `on_tick`: advance the store clock to `time`. -/
forkdef onTick (time : UInt64) : StoreTransition Unit := do
  modify fun store => advanceStoreTime store time

/-! ## record_block_timeliness / update_proposer_boost_root -/

/-- `record_block_timeliness(store, root)`: the two deadlines (attestation-due and
PTC-due), each `is_current_slot ∧ time_into_slot_ms < threshold`. -/
forkdef recordBlockTimeliness (store : Store map) (root : Root) : StoreTransition (Store map) := do
  let block ← FcMap.getOrThrow store.blocks root
  let tis := timeIntoSlotMs store
  let isCurrentSlot := getCurrentSlot store == block.slot
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
attested block (the shared core of `on_payload_attestation_message`'s vote write). -/
forkdef recordPtcVotes (store : Store map) (data : PayloadAttestationData) (ptcIndices : Array Nat) :
    Store map :=
  let timelinessVote := FcMap.lookupD store.payloadTimelinessVote data.beaconBlockRoot
  let availabilityVote := FcMap.lookupD store.payloadDataAvailabilityVote data.beaconBlockRoot
  let (timelinessVote, availabilityVote) := ptcIndices.foldl (init := (timelinessVote, availabilityVote))
    fun (tv, av) i => (tv.set! i (some data.payloadPresent), av.set! i (some data.blobDataAvailable))
  { store with
    payloadTimelinessVote := FcMap.insert store.payloadTimelinessVote data.beaconBlockRoot timelinessVote
    payloadDataAvailabilityVote := FcMap.insert store.payloadDataAvailabilityVote data.beaconBlockRoot availabilityVote }

/-- `notify_ptc_messages(store, state, payload_attestations)`: replay the block's
payload attestations as per-validator `on_payload_attestation_message`s
(`is_from_block = true`). The block-replay never asserts, so the per-message effect is
inlined as a pure store transform: apply the vote when the attested block's state slot
matches and the validator sits in its PTC, otherwise skip. -/
forkdef notifyPtcMessages (store : Store map) (state : State) (payloadAttestations : Array PayloadAttestation) :
    Store map := Id.run do
  if sszGet state slot == 0 then return store

  let mut store := store
  for pa in payloadAttestations do
    let indexed := getIndexedPayloadAttestation state pa
    for idx in indexed.attestingIndices do
      match FcMap.lookup store.blockStates pa.data.beaconBlockRoot with
      | none => pure ()
      | some attState =>
        if pa.data.slot == sszGet attState slot then
          let ptc := getPtc attState pa.data.slot
          let ptcIndices := (Array.range Const.ptcSize).filter fun i => vget ptc i == idx
          if ptcIndices.size > 0 then store := recordPtcVotes store pa.data ptcIndices
  return store

/-! ## on_block -/

/-- `on_block`. Rejects (via `assert`) an unknown parent, a
full-but-unverified parent, a future block, or a finality conflict, and propagates a
failed `state_transition` through `runStateTransition`. The ePBS additions over the
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
  assert (getCurrentSlot store ≥ block.slot)
  let finalizedSlot := computeStartSlotAtEpoch store.finalizedCheckpoint.epoch
  assert (block.slot > finalizedSlot)
  let finalizedBlock ← getCheckpointBlock store block.parentRoot store.finalizedCheckpoint.epoch
  assert (store.finalizedCheckpoint.root == finalizedBlock)

  -- Run the state transition, then snapshot the head before the block is added.
  let postState ← runStateTransition parentState (stateTransition signedBlock)
  let blockRoot := htr block
  -- The head is taken BEFORE the new block is added (`update_proposer_boost_root`).
  let head ← getHead store

  -- Insert the block, its post-state, and the two empty per-block PTC vote maps.
  let emptyVotes : Array (Option Bool) := Array.replicate Const.ptcSize none
  let store := { store with
    blocks := FcMap.insert store.blocks blockRoot block
    blockStates := FcMap.insert store.blockStates blockRoot postState
    payloadTimelinessVote := FcMap.insert store.payloadTimelinessVote blockRoot emptyVotes
    payloadDataAvailabilityVote := FcMap.insert store.payloadDataAvailabilityVote blockRoot emptyVotes }

  -- Replay the block's PTC votes, record timeliness, boost, and pull up the tip.
  let store := notifyPtcMessages store postState block.body.payloadAttestations.toArray
  let store ← recordBlockTimeliness store blockRoot
  let store ← updateProposerBoostRoot store head.root blockRoot
  let store := updateCheckpoints store (sszGet postState currentJustifiedCheckpoint) (sszGet postState finalizedCheckpoint)
  set (← computePulledUpTip store blockRoot)

/-! ## on_execution_payload_envelope -/

/-- `compute_time_at_slot(state, slot)`. -/
forkdef computeTimeAtSlot (state : State) (slot : Slot) : UInt64 :=
  (sszGet state genesisTime) + (slot - Const.genesisSlot) * Const.slotDurationMs / 1000

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

/-- `verify_execution_payload_envelope`: the consensus-side envelope checks. The EL
`verify_and_notify_new_payload` and `is_data_available` are modeled as always `true`
(no execution layer / data availability in the harness). Returns the cache-warmed
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
  assert (payload.timestamp == computeTimeAtSlot state (sszGet state slot))
  assert (htr payload.withdrawals == htr (sszGet state payloadExpectedWithdrawals))
  return warm

/-- `on_execution_payload_envelope`: verify the revealed payload envelope against the
committed bid and record it. The recorded payload flips the block's head node to FULL
and enables `is_payload_verified`. -/
forkdef onExecutionPayloadEnvelope (signedEnv : SignedExecutionPayloadEnvelope) : StoreTransition Unit := do
  let store ← get
  let envelope := signedEnv.message
  let state ← FcMap.getOrAssert store.blockStates envelope.beaconBlockRoot
    "envelope.beacon_block_root in store.block_states"

  match verifyExecutionPayloadEnvelope state signedEnv with
  | .error e => throw e
  | .ok warm => set { store with
      blockStates := FcMap.insert store.blockStates envelope.beaconBlockRoot warm,
      payloads := FcMap.insert store.payloads envelope.beaconBlockRoot envelope }

/-! ## on_payload_attestation_message -/

/-- `on_payload_attestation_message(store, ptc_message, is_from_block)` (the wire
handler, `is_from_block = false`): the attested block's state slot must match, the
validator must sit in its PTC, the message must be for the current slot, and its
signature must verify; then the votes are recorded. -/
forkdef onPayloadAttestationMessage (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    StoreTransition Unit := do
  let store ← get
  let data := msg.data
  let state ← FcMap.getOrThrow store.blockStates data.beaconBlockRoot

  if !(data.slot == sszGet state slot) then pure ()
  else
    let ptc := getPtc state data.slot
    let ptcIndices := (Array.range Const.ptcSize).filter fun i => vget ptc i == msg.validatorIndex
    assert (ptcIndices.size > 0)
    if isFromBlock then set (recordPtcVotes store data ptcIndices)
    else
      assert (data.slot == getCurrentSlot store)
      let indexed : IndexedPayloadAttestation :=
        { attestingIndices := sszOfArray #[msg.validatorIndex], data := data, signature := msg.signature }
      assert (isValidIndexedPayloadAttestation state indexed)
      set (recordPtcVotes store data ptcIndices)

/-! ## on_attestation -/

/-- `store_target_checkpoint_state`: cache the target's state, advancing to the
target epoch start if needed (best-effort, so `EStateM.run`). -/
forkdef storeTargetCheckpointState (store : Store map) (target : Checkpoint) :
    StoreTransition (Store map) := do
  if FcMap.contains store.checkpointStates target then pure store
  else
    -- `target not in store.checkpoint_states` is a membership guard (faithful), but the
    -- following `store.block_states[target.root]` is a plain `Dict` read that raises.
    let base ← FcMap.getOrThrow store.blockStates target.root
    let targetSlot := computeStartSlotAtEpoch target.epoch
    let advanced :=
      if (sszGet base slot) < targetSlot then
        runBestEffort (processSlots targetSlot) base
      else base
    pure { store with checkpointStates := FcMap.insert store.checkpointStates target advanced }

/-- `validate_on_attestation` (Gloas): adds `index ∈ {0, 1}`, same-slot ⇒ index 0,
and full vote (index 1) ⇒ the head block's payload is verified. -/
forkdef validateOnAttestation (store : Store map) (att : Attestation) (isFromBlock : Bool) :
    StoreTransition Unit := do
  let target := att.data.target
  let currentEpoch := getCurrentStoreEpoch store
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
  assert (getCurrentSlot store ≥ att.data.slot + 1)

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

  let store ← storeTargetCheckpointState (← get) att.data.target
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

/-- `get_forkchoice_store(anchor_state, anchor_block)` (Gloas): `block_timeliness`
seeds `[True, True]` for the anchor, the three ePBS maps start empty, and the time
uses the ms-based `SLOT_DURATION_MS * slot // 1000` form. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) : Store map :=
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }

  { time := (sszGet anchorState genesisTime) + Const.slotDurationMs * (sszGet anchorState slot) / 1000
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
