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
forkdef getParentPayloadStatus (store : Store map) (block : BeaconBlock) : UInt8 :=
  match FcMap.lookup store.blocks block.parentRoot with
  | none => Const.payloadStatusEmpty
  | some parent =>
    let parentBlockHash := block.body.signedExecutionPayloadBid.message.parentBlockHash
    let messageBlockHash := parent.body.signedExecutionPayloadBid.message.blockHash
    if parentBlockHash == messageBlockHash then Const.payloadStatusFull else Const.payloadStatusEmpty

/-- `is_parent_node_full`: the parent edge of `block` is FULL. -/
forkdef isParentNodeFull (store : Store map) (block : BeaconBlock) : Bool :=
  getParentPayloadStatus store block == Const.payloadStatusFull

/-- `get_ancestor(store, node, slot)`: walk parent edges (each edge carrying the
parent's payload status) until at/below `slot`. Fuel-bounded by the block count
(the DAG is finite and acyclic). -/
forkdef getAncestor (store : Store map) (node : ForkChoiceNode) (slot : Slot) : ForkChoiceNode :=
  fuelIterate ((FcMap.keys store.blocks).length + 1) node fun n =>
    match FcMap.lookup store.blocks n.root with
    | some block =>
      if block.slot > slot then
        .next { root := block.parentRoot, payloadStatus := getParentPayloadStatus store block }
      else .done n
    | none => .done n

/-- `is_ancestor(store, node, ancestor)`: `ancestor` is an ancestor of `node` when
the walk to the ancestor's slot lands on the ancestor's root with a matching payload
status (or the ancestor is PENDING, which matches either realisation). -/
forkdef isAncestor (store : Store map) (node ancestor : ForkChoiceNode) : Bool :=
  match FcMap.lookup store.blocks ancestor.root with
  | none => false
  | some block =>
    let nodeAncestor := getAncestor store node block.slot
    if nodeAncestor.root != ancestor.root then false
    else nodeAncestor.payloadStatus == ancestor.payloadStatus
      || ancestor.payloadStatus == Const.payloadStatusPending

/-- `get_checkpoint_block(store, root, epoch)`: the root of the block at the epoch's
first slot, walking from a PENDING node. -/
forkdef getCheckpointBlock (store : Store map) (root : Root) (epoch : Epoch) : Root :=
  let node : ForkChoiceNode := .pending root
  (getAncestor store node (computeStartSlotAtEpoch epoch)).root

/-- `get_supported_node(store, message)`: the node a latest message supports. A
message for a strictly-earlier block slot decides the payload (full iff
`payload_present`); a same-slot message is PENDING. -/
forkdef getSupportedNode (store : Store map) (message : LatestMessage) : ForkChoiceNode :=
  match FcMap.lookup store.blocks message.root with
  | none => ForkChoiceNode.pending message.root
  | some block =>
    let payloadStatus :=
      if block.slot < message.slot then
        if message.payloadPresent then Const.payloadStatusFull else Const.payloadStatusEmpty
      else Const.payloadStatusPending
    { root := message.root, payloadStatus := payloadStatus }

/-- `get_dependent_root` (Gloas, node-based): the block root that determined the
current epoch's proposer shuffling. -/
forkdef getDependentRoot (store : Store map) (root : Root) : Root :=
  let epoch := getCurrentStoreEpoch store
  if epoch ≤ Const.minSeedLookahead then fcZeroRoot
  else
    let node : ForkChoiceNode := .pending root
    (getAncestor store node (computeStartSlotAtEpoch (epoch - Const.minSeedLookahead) - 1)).root

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
forkdef payloadTimeliness (store : Store map) (root : Root) (timely : Bool) : Bool :=
  if !isPayloadVerified store root then !timely
  else
    let votes := FcMap.lookupD store.payloadTimelinessVote root
    voteCount votes timely > Const.payloadTimelyThreshold

/-- `payload_data_availability(store, root, available)`: the data-availability
counterpart of `payload_timeliness`. -/
forkdef payloadDataAvailability (store : Store map) (root : Root) (available : Bool) : Bool :=
  if !isPayloadVerified store root then !available
  else
    let votes := FcMap.lookupD store.payloadDataAvailabilityVote root
    voteCount votes available > Const.dataAvailabilityTimelyThreshold

/-- `is_previous_slot_payload_decision(store, node)`: the node is the previous
slot's block and carries a decided (EMPTY or FULL) payload status. -/
forkdef isPreviousSlotPayloadDecision (store : Store map) (node : ForkChoiceNode) : Bool :=
  match FcMap.lookup store.blocks node.root with
  | none => false
  | some block =>
    let isPreviousSlot := block.slot + 1 == getCurrentSlot store
    let isPayloadDecision :=
      node.payloadStatus == Const.payloadStatusEmpty || node.payloadStatus == Const.payloadStatusFull
    isPreviousSlot && isPayloadDecision

/-- `should_extend_payload(store, root)`: whether the FULL realisation of `root`
should win the payload-status tiebreak. -/
forkdef shouldExtendPayload (store : Store map) (root : Root) : Bool :=
  if !isPayloadVerified store root then false
  else
    let proposerRoot := store.proposerBoostRoot
    let payloadIsTimely := payloadTimeliness store root true
    let payloadDataIsAvailable := payloadDataAvailability store root true
    (payloadIsTimely && payloadDataIsAvailable)
      || proposerRoot == fcZeroRoot
      || (match FcMap.lookup store.blocks proposerRoot with
          | some pb => pb.parentRoot != root || isParentNodeFull store pb
          | none    => true)

/-- `get_payload_status_tiebreaker(store, node)`: the third `get_head` sort key. -/
forkdef getPayloadStatusTiebreaker (store : Store map) (node : ForkChoiceNode) : UInt8 :=
  if isPreviousSlotPayloadDecision store node then
    if node.payloadStatus == Const.payloadStatusEmpty then 1
    else if shouldExtendPayload store node.root then 2
    else 0
  else node.payloadStatus

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
forkdef getProposerScore (store : Store map) : Gwei :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint with
  | none => 0
  | some state =>
    committeeWeight state * UInt64.ofNat Const.proposerScoreBoost / 100

/-- `get_attestation_score(store, node, state)`: the effective balance of the
unslashed active validators whose supported node is an ancestor of `node`. -/
forkdef getAttestationScore (store : Store map) (node : ForkChoiceNode) (state : State) : Gwei :=
  let active := getActiveValidatorIndices state (currentEpochOf state)
  let validators := sszGet state validators
  active.foldl (init := 0) fun acc i =>
    let idx := i.toNat
    if (validators[idx]!).slashed then acc
    else match FcMap.lookup store.latestMessages i with
      | none => acc
      | some lm =>
        if store.equivocatingIndices.contains i then acc
        else if isAncestor store (getSupportedNode store lm) node then acc + (validators[idx]!).effectiveBalance
        else acc

/-- `is_head_weak(store, head_root)`: the head's attestation weight, including the
equivocator weight from its slot's committees, is below the reorg threshold. -/
forkdef isHeadWeak (store : Store map) (headRoot : Root) : Bool :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint,
        FcMap.lookup store.blockStates headRoot, FcMap.lookup store.blocks headRoot with
  | some justifiedState, some headState, some headBlock =>
    let reorgThreshold := calculateCommitteeFraction justifiedState Const.reorgHeadWeightThreshold
    let epoch := computeEpochAtSlot headBlock.slot
    let headNode : ForkChoiceNode := .pending headRoot
    let baseWeight := getAttestationScore store headNode justifiedState
    let validators := sszGet justifiedState validators
    let headWeight := (List.range (getCommitteeCountPerSlot headState epoch)).foldl (init := baseWeight) fun acc index =>
      let committee := getBeaconCommittee headState headBlock.slot index
      committee.foldl (init := acc) fun a i =>
        if store.equivocatingIndices.contains i then a + (validators[i.toNat]!).effectiveBalance else a
    headWeight < reorgThreshold
  | _, _, _ => false

/-- `is_parent_strong(store, root)`: the parent node's attestation weight exceeds the
reorg parent threshold. -/
forkdef isParentStrong (store : Store map) (root : Root) : Bool :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint,
        FcMap.lookup store.blocks root with
  | some justifiedState, some block =>
    let parentThreshold := calculateCommitteeFraction justifiedState Const.reorgParentWeightThreshold
    let parentPayloadStatus := getParentPayloadStatus store block
    let parentNode : ForkChoiceNode := { root := block.parentRoot, payloadStatus := parentPayloadStatus }
    getAttestationScore store parentNode justifiedState > parentThreshold
  | _, _ => false

/-- `should_apply_proposer_boost(store)`: gate the proposer boost. With an unset
boost root, no boost; with a far-enough-back parent or a non-weak parent head, boost;
otherwise boost only when no equivocating same-proposer sibling competes. -/
forkdef shouldApplyProposerBoost (store : Store map) : Bool :=
  if store.proposerBoostRoot == fcZeroRoot then false
  else match FcMap.lookup store.blocks store.proposerBoostRoot with
    | none => false
    | some block =>
      let parentRoot := block.parentRoot
      match FcMap.lookup store.blocks parentRoot with
      | none => false
      | some parent =>
        let slot := block.slot
        if parent.slot + 1 < slot then true
        else if !isHeadWeak store parentRoot then true
        else
          let equivocations := FcMap.filterKeys store.blocks fun root b =>
            match FcMap.lookup store.blockTimeliness root with
            | some tl =>
              (tl[Const.ptcTimelinessIndex]?.getD false)
                && b.proposerIndex == parent.proposerIndex
                && b.slot + 1 == slot
                && root != parentRoot
            | none => false
          equivocations.isEmpty

/-- `get_weight(store, node)`: zero for an undecided previous-slot payload; otherwise
the attestation score plus the (gated) proposer boost. -/
forkdef getWeight (store : Store map) (node : ForkChoiceNode) : Gwei :=
  if isPreviousSlotPayloadDecision store node then 0
  else match FcMap.lookup store.checkpointStates store.justifiedCheckpoint with
    | none => 0
    | some state =>
      let attestationScore := getAttestationScore store node state
      if !shouldApplyProposerBoost store then attestationScore
      else
        let proposerBoostNode : ForkChoiceNode := .pending store.proposerBoostRoot
        if isAncestor store proposerBoostNode node then attestationScore + getProposerScore store
        else attestationScore

/-! ## Filtered block tree + head -/

/-- `get_voting_source(store, block_root)`. -/
forkdef getVotingSource (store : Store map) (blockRoot : Root) : Checkpoint :=
  match FcMap.lookup store.blocks blockRoot with
  | none => store.justifiedCheckpoint
  | some block =>
    let currentEpoch := getCurrentStoreEpoch store
    if currentEpoch > computeEpochAtSlot block.slot then
      FcMap.lookupD store.unrealizedJustifications blockRoot
    else match FcMap.lookup store.blockStates blockRoot with
      | some hs => sszGet hs currentJustifiedCheckpoint
      | none    => store.justifiedCheckpoint

/-- `filter_block_tree`: collect the viable branches into `acc` (a root set),
returning whether `blockRoot` is viable. Root-keyed (unchanged from phase0). The
recursion is fuel-bounded by the block count (the DAG is finite and acyclic, so the
depth cannot exceed it), keeping the function total, no `partial def`. -/
forkdef filterBlockTree (store : Store map) (blockRoot : Root) (acc : Array Root) :
    Array Root × Bool :=
  go ((FcMap.keys store.blocks).length + 1) blockRoot acc
where
  /-- The viability walk; `fuel` bounds the parent-to-child descent. -/
  go : Nat → Root → Array Root → Array Root × Bool
  | 0,        _,         acc => (acc, false)
  | fuel + 1, blockRoot, acc =>
    let children := FcMap.filterKeys store.blocks (fun _ b => b.parentRoot == blockRoot)
    if children.isEmpty then
      -- A leaf branch is viable when its voting source stays close to the justified
      -- checkpoint (genesis, the same epoch, or within two epochs of the current one).
      let currentEpoch := getCurrentStoreEpoch store
      let votingSource := getVotingSource store blockRoot
      let correctJustified :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
          || votingSource.epoch + 2 ≥ currentEpoch

      -- The finalized checkpoint must also lie on this branch.
      let finalizedBlock := getCheckpointBlock store blockRoot store.finalizedCheckpoint.epoch
      let correctFinalized :=
        store.finalizedCheckpoint.epoch == Const.genesisEpoch
          || store.finalizedCheckpoint.root == finalizedBlock
      if correctJustified && correctFinalized then (acc.push blockRoot, true) else (acc, false)
    else
      let (acc', anyViable) := children.foldl (init := (acc, false)) fun (a, viable) child =>
        let (a', v) := go fuel child a
        (a', viable || v)
      if anyViable then (acc'.push blockRoot, true) else (acc', false)

/-- `get_filtered_block_tree`: the viable-root set rooted at the justified checkpoint. -/
forkdef getFilteredBlockTree (store : Store map) : Array Root :=
  (filterBlockTree store store.justifiedCheckpoint.root #[]).1

/-- `get_node_children(store, blocks, node)`: a pending node's children are its own
empty (always) and full (when the payload is verified) realisations; a decided node's
children are the pending nodes of the filtered child blocks whose parent edge matches
this node's status. -/
forkdef getNodeChildren (store : Store map) (blocks : Array Root) (node : ForkChoiceNode) :
    Array ForkChoiceNode :=
  if node.payloadStatus == Const.payloadStatusPending then
    let empty : ForkChoiceNode := .empty node.root
    if isPayloadVerified store node.root then
      #[empty, ForkChoiceNode.full node.root]
    else #[empty]
  else
    (blocks.filter fun root =>
      match FcMap.lookup store.blocks root with
      | some b => b.parentRoot == node.root && node.payloadStatus == getParentPayloadStatus store b
      | none   => false).map fun root =>
        ForkChoiceNode.pending root

/-- `get_head`: the LMD-GHOST walk over the node DAG. The max at each step compares
`(get_weight, child.root, get_payload_status_tiebreaker)` in that priority order, ties
broken by the greater root then the greater tiebreaker. Fuel-bounded: each step either
descends to a new root or flips a pending node to a decided child. -/
forkdef getHead (store : Store map) : ForkChoiceNode :=
  let blocks := getFilteredBlockTree store
  let head : ForkChoiceNode := .pending store.justifiedCheckpoint.root
  fuelIterate (2 * (FcMap.keys store.blocks).length + 2) head fun head =>
    let children := getNodeChildren store blocks head
    if children.isEmpty then .done head
    else .next (children.foldl (init := children[0]!) (betterOf store))
where
  /-- The better of two candidate head nodes under the `(weight, root, tiebreaker)`
  ordering: greater weight wins, ties by greater root, further ties by the greater
  payload-status tiebreaker. -/
  betterOf (store : Store map) (a b : ForkChoiceNode) : ForkChoiceNode :=
    let weightA := getWeight store a
    let weightB := getWeight store b
    if weightA > weightB then a
    else if weightB > weightA then b
    else match compare a.root b.root with
      | Ordering.gt => a
      | Ordering.lt => b
      | Ordering.eq => if getPayloadStatusTiebreaker store a > getPayloadStatusTiebreaker store b then a else b

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
forkdef computePulledUpTip (store : Store map) (blockRoot : Root) : Store map :=
  match FcMap.lookup store.blockStates blockRoot, FcMap.lookup store.blocks blockRoot with
  | some state, some block =>
    let act : EStateM StateTransitionError State Unit := processJustificationAndFinalization
    match act.run state with
    | .ok _ pulled =>
      let cj := sszGet pulled currentJustifiedCheckpoint
      let fz := sszGet pulled finalizedCheckpoint
      let store := { store with unrealizedJustifications := FcMap.insert store.unrealizedJustifications blockRoot cj }
      let store := updateUnrealizedCheckpoints store cj fz
      if computeEpochAtSlot block.slot < getCurrentStoreEpoch store then updateCheckpoints store cj fz else store
    | .error _ _ => store
  | _, _ => store

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
forkdef recordBlockTimeliness (store : Store map) (root : Root) : Store map :=
  match FcMap.lookup store.blocks root with
  | none => store
  | some block =>
    let tis := timeIntoSlotMs store
    let isCurrentSlot := getCurrentSlot store == block.slot
    let timeliness : Array Bool := #[isCurrentSlot && tis < bpsDeadlineMs Const.attestationDueBpsGloas,
                                     isCurrentSlot && tis < bpsDeadlineMs Const.payloadAttestationDueBps]
    { store with blockTimeliness := FcMap.insert store.blockTimeliness root timeliness }

/-- `update_proposer_boost_root(store, head, root)`: boost a timely first block on the
same proposer-shuffling lineage as the pre-insertion head. -/
forkdef updateProposerBoostRoot (store : Store map) (head root : Root) : Store map :=
  let isFirstBlock := store.proposerBoostRoot == fcZeroRoot
  let isTimely := (FcMap.lookupD store.blockTimeliness root)[Const.attestationTimelinessIndex]?.getD false
  let isSameDependentRoot := getDependentRoot store root == getDependentRoot store head
  if isTimely && isFirstBlock && isSameDependentRoot then { store with proposerBoostRoot := root } else store

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

/-- `on_block`. Rejects (via `assert` / `missingKey`) an unknown parent, a
full-but-unverified parent, a future block, or a finality conflict, and propagates a
failed `state_transition` through `runStateTransition`. The ePBS additions over the
prior fork: the parent-full assert, the two per-block vote-map inits, and
`notify_ptc_messages`. -/
forkdef onBlock (signedBlock : SignedBeaconBlock) : StoreTransition Unit := do
  let store ← get
  let block := signedBlock.message
  let parentState ← FcMap.getOrThrow store.blockStates block.parentRoot

  -- Reject a full-but-unverified parent, a future block, or a finality conflict.
  assert (!(isParentNodeFull store block) || isPayloadVerified store block.parentRoot)
  assert (getCurrentSlot store ≥ block.slot)
  let finalizedSlot := computeStartSlotAtEpoch store.finalizedCheckpoint.epoch
  assert (block.slot > finalizedSlot)
  assert (store.finalizedCheckpoint.root == getCheckpointBlock store block.parentRoot store.finalizedCheckpoint.epoch)

  -- Run the state transition, then snapshot the head before the block is added.
  let postState ← runStateTransition parentState (stateTransition signedBlock)
  let blockRoot := htr block
  -- The head is taken BEFORE the new block is added (`update_proposer_boost_root`).
  let head := getHead store

  -- Insert the block, its post-state, and the two empty per-block PTC vote maps.
  let emptyVotes : Array (Option Bool) := Array.replicate Const.ptcSize none
  let store := { store with
    blocks := FcMap.insert store.blocks blockRoot block
    blockStates := FcMap.insert store.blockStates blockRoot postState
    payloadTimelinessVote := FcMap.insert store.payloadTimelinessVote blockRoot emptyVotes
    payloadDataAvailabilityVote := FcMap.insert store.payloadDataAvailabilityVote blockRoot emptyVotes }

  -- Replay the block's PTC votes, record timeliness, boost, and pull up the tip.
  let store := notifyPtcMessages store postState block.body.payloadAttestations.toArray
  let store := recordBlockTimeliness store blockRoot
  let store := updateProposerBoostRoot store head.root blockRoot
  let store := updateCheckpoints store (sszGet postState currentJustifiedCheckpoint) (sszGet postState finalizedCheckpoint)
  set (computePulledUpTip store blockRoot)

/-! ## on_execution_payload_envelope -/

/-- `compute_time_at_slot(state, slot)`. -/
forkdef computeTimeAtSlot (state : State) (slot : Slot) : UInt64 :=
  (sszGet state genesisTime) + (slot - Const.genesisSlot) * Const.slotDurationMs / 1000

/-- `verify_execution_payload_envelope_signature`: the envelope is signed by the
builder's key (the proposer's, for a self-build) under `DOMAIN_BEACON_BUILDER`. -/
forkdef verifyExecutionPayloadEnvelopeSignature (state : State) (signedEnv : SignedExecutionPayloadEnvelope) : Bool :=
  let builderIndex := signedEnv.message.builderIndex
  let pubkey :=
    if builderIndex == Const.builderIndexSelfBuild then
      let validatorIndex := (sszGet state latestBlockHeader).proposerIndex
      (sszGet state validators[validatorIndex.toNat]!).pubkey
    else
      (sszGet state builders[builderIndex.toNat]!).pubkey
  let signingRoot := computeSigningRoot signedEnv.message (getDomain state Const.domainBeaconBuilder (currentEpochOf state))
  blsVerify pubkey signingRoot signedEnv.signature

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
  assert (verifyExecutionPayloadEnvelopeSignature state signedEnv)

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
  let state ← FcMap.getOrThrow store.blockStates envelope.beaconBlockRoot

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
forkdef storeTargetCheckpointState (store : Store map) (target : Checkpoint) : Store map :=
  if FcMap.contains store.checkpointStates target then store
  else match FcMap.lookup store.blockStates target.root with
    | none => store
    | some base =>
      let targetSlot := computeStartSlotAtEpoch target.epoch
      let advanced :=
        if (sszGet base slot) < targetSlot then
          runBestEffort (processSlots targetSlot) base
        else base
      { store with checkpointStates := FcMap.insert store.checkpointStates target advanced }

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
  assert (target.root == getCheckpointBlock store att.data.beaconBlockRoot target.epoch)
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

  let store := storeTargetCheckpointState (← get) att.data.target
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
