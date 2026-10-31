import EthCLSpecs.Fulu.Transition
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLSpecs.Fulu.ForkChoice`: the LMD-GHOST store and its handlers

The second state machine (`FRAMEWORK_ARCHITECTURE.md` §9): the fork-choice `Store`
and the `on_tick` / `on_block` / `on_attestation` / `on_attester_slashing`
handlers, plus `get_head` (the filtered-node-tree LMD-GHOST walk with proposer
boost). The store is a `forkstruct` (captured for inheritance); the section opens
with `fork_choice_section map`, so the handlers are monadic `StoreTransition` actions
over the typed `StoreTransitionError` (`assert` / `missingKey` / `todo`),
and the queries (`get_weight`, `get_head`, the reorg predicates) are pure functions
of the boxed store.

The handlers reuse the Fulu spine: `on_block` runs `state_transition` on a copy of
the parent post-state through `runNestedStateTransition` (the one-way bridge that wraps an
inner failure as `StoreTransitionError.transition`); `store_target_checkpoint_state`
runs `process_slots` and `compute_pulled_up_tip` runs
`process_justification_and_finalization`, each best-effort through `EStateM.run`.

The `Store` is parameterized by its finite-map backing (`EthCLLib.Spec.FcMap`); the
runner fixes it to `hashMap` over `Sha256` boxed states.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Fulu

/-! ## Store -/

/-- The latest attestation seen from a validator: its target epoch and head vote.
A `forkstruct`, so a child fork can `inherit` it. -/
forkstruct LatestMessage where
  epoch : Epoch
  root  : Root

deriving instance Inhabited for LatestMessage

/-- The fork-choice store, parameterized by its map backing and (via `forkstruct`'s
auto `[Preset]`) the preset / hasher tag. The boxed states reuse the transition
layer's `State` (`= SSZ.Box HasherTag.H BeaconState`). At v1.7.0-beta.4 the clock is in
milliseconds (`time_ms`, `genesis_time_ms`), so slot arithmetic needs no seconds-to-ms
conversion past `get_forkchoice_store`.

A node is its block root here: the phase0 `ForkChoiceNode` carries only `root`, so the
Fulu walks pass `Root` where the spec passes a node, and a membership test on nodes is a
membership test on roots. -/
forkstruct Store (map : MapKind) [HasherTag] where
  timeMs                        : UInt64
  genesisTimeMs                 : UInt64
  justifiedCheckpoint           : Checkpoint
  finalizedCheckpoint           : Checkpoint
  unrealizedJustifiedCheckpoint : Checkpoint
  unrealizedFinalizedCheckpoint : Checkpoint
  proposerBoostRoot             : Root
  equivocatingIndices           : Array ValidatorIndex
  blocks                        : map Root BeaconBlock
  blockStates                   : map Root State
  blockTimeliness               : map Root Bool
  checkpointStates              : map Checkpoint State
  latestMessages                : map ValidatorIndex LatestMessage
  unrealizedJustifications      : map Root Checkpoint

fork_choice_section map

/-- The all-zero root (an unset `proposer_boost_root`). -/
forkdef fcZeroRoot : Root := Vector.replicate 32 0

/-! ## Time / slot accessors

The millisecond clock helpers (`compute_slot_at_time_ms`, `compute_time_at_slot_ms`,
`seconds_to_milliseconds`) live in `Fulu/Time.lean` with the beacon-chain clock. They return
`Except StateTransitionError`, and `liftErr` lands their `.arithmetic` fault on this machine as
`.transition (.arithmetic …)`. -/

/-- `get_slots_since_genesis` (`phase0/fork-choice.md:254-255`):
`compute_slot_at_time_ms(store.genesis_time_ms, store.time_ms)`. Throwing: the clock's
`time_ms - genesis_time_ms` underflows when the store time predates genesis, a `uint64` fault
the reference runner does not catch. -/
forkdef getSlotsSinceGenesis (store : Store map) : StoreTransition Slot :=
  liftErr (computeSlotAtTimeMs store.genesisTimeMs store.timeMs)
/-- `get_current_slot` (`phase0/fork-choice.md:261-262`): the slots since genesis. At
v1.7.0-beta.4 the spec drops the `GENESIS_SLOT +` term (it is `0`). -/
forkdef getCurrentSlot (store : Store map) : StoreTransition Slot :=
  getSlotsSinceGenesis store
forkdef getCurrentStoreEpoch (store : Store map) : StoreTransition Epoch := do
  pure (computeEpochAtSlot (← getCurrentSlot store))

/-- `get_time_into_slot_ms` (`phase0/fork-choice.md:247-248`): the milliseconds elapsed since
the start of the current slot, `store.time_ms - compute_time_at_slot_ms(store.genesis_time_ms,
get_current_slot(store))`. Throwing: `get_current_slot` and `compute_time_at_slot_ms` can each
fault, and the subtraction is a checked `uint64` op. It cannot underflow once the current slot
is known, since that slot starts at or before `time_ms`. -/
forkdef getTimeIntoSlotMs (store : Store map) : StoreTransition UInt64 := do
  let currentSlot ← getCurrentSlot store
  let slotStartMs ← liftErr (computeTimeAtSlotMs store.genesisTimeMs currentSlot)
  checkedSub store.timeMs slotStartMs
    "get_time_into_slot_ms: time_ms - compute_time_at_slot_ms(genesis_time_ms, current_slot)"

/-- A basis-points deadline within a slot, in milliseconds: `get_slot_component_duration_ms`,
`bps * SLOT_DURATION_MS // BASIS_POINTS` (`phase0/fork-choice.md:573-577`). Multiply before
the `UInt64` truncating divide, so the floor lands on the full `bps * SLOT_DURATION_MS`
product. The product is bare rather than `checkedMul`, and stays that way: both factors are
constants (`bps ≤ BASIS_POINTS = 10000`, `SLOT_DURATION_MS` is 12000 at mainnet and 6000 at
minimal), so it peaks near `1.2e8` and cannot reach the `uint64` bound at any preset. -/
forkdef bpsDeadlineMs (bps : UInt64) : UInt64 :=
  bps * Const.slotDurationMs / Const.basisPoints

/-! ## DAG walks

The walks under this heading are `fuelLoop`-bounded rather than closed by `termination_by`,
which `SPECS_ARCHITECTURE.md` §7.2 asks each loop to justify. The reason: the reads raise, so
the walk is monadic, and a measure would have to be carried through a step that can reject.
The bounds are honest counts (the block count on a finite acyclic DAG), so fuel-out is
unreachable and each site names the sentinel it would return.

`filterNodeTree` and `getHead` are the same kind of walk for the same reason, but they sit
under `Weights and head` below, so each carries the reason in its own docstring rather than
leaning on this heading.
-/

/-- `get_ancestor(store, node, slot)`: walk parent links until at/below `slot`.
Fuel-bounded by the block count (the DAG is finite and acyclic). The spec's
`store.blocks[node.root]` is a plain `Dict` read, so a missing root raises:
`getOrThrow` in the monadic `fuelLoop` step (the fuel-out value is unreachable, so
`root` doubles as the `exhausted` sentinel). -/
forkdef getAncestor (store : Store map) (root : Root) (slot : Slot) : StoreTransition Root :=
  fuelLoop ((FcMap.keys store.blocks).length + 1) root root fun r => do
    let block ← FcMap.getOrThrow store.blocks r
    if block.slot > slot then pure (.next block.parentRoot)
    else pure (.done r)

/-- `get_checkpoint_block`. -/
forkdef getCheckpointBlock (store : Store map) (root : Root) (epoch : Epoch) :
    StoreTransition Root :=
  getAncestor store root (computeStartSlotAtEpoch epoch)

/-! ## Weights and head -/

/-- `calculate_committee_fraction(state, committee_percent)` (`phase0/fork-choice.md:300-307`):
a percentage of the per-slot committee weight. At v1.7.0-beta.4 the weight is the total
balance of the *unslashed* active validators (`get_total_balance`, floored at one increment)
divided across the slots of an epoch, where alpha.12 took `get_total_active_balance`, which
counts slashed validators too. `UInt64` truncating division, as the spec's `//`. -/
forkdef calculateCommitteeFraction (state : State) (committeePercent : UInt64) : Gwei :=
  let validators := sszGet state validators
  let unslashedAndActive := (getActiveValidatorIndices state (currentEpochOf state)).filter
    fun i => !(validators[i.toNat]!).slashed
  let committeeWeight := getTotalBalance state unslashedAndActive / UInt64.ofNat Const.slotsPerEpoch
  committeeWeight * committeePercent / 100

/-- `compute_proposer_score(state)` (`phase0/fork-choice.md:362-363`): the committee
fraction at `PROPOSER_SCORE_BOOST`. -/
forkdef computeProposerScore (state : State) : Gwei :=
  calculateCommitteeFraction state (UInt64.ofNat Const.proposerScoreBoost)

/-- `get_proposer_score` (`phase0/fork-choice.md:369-371`): `compute_proposer_score` over the
justified checkpoint state. -/
forkdef getProposerScore (store : Store map) : StoreTransition Gwei := do
  let state ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  pure (computeProposerScore state)

/-- `get_attestation_score(store, node, state)` (`phase0/fork-choice.md:338-356`): the
effective balance of the unslashed active validators whose latest message supports a
descendant of `root` (`is_ancestor(store, get_supported_node(...), node)`; a phase0 supported
node is the message's root). The fold is monadic only to bind `getAncestor` and the
`store.blocks[node.root]` read inside `is_ancestor`, both of which can reject.

The `and` chain short-circuits, so the block read runs only for a validator with a latest
message that is not equivocating. A store with no latest messages, exactly what
`get_forkchoice_store` hands back, therefore scores `0` without any read.
`validators[idx]!` stays unchecked: `idx` comes from `getActiveValidatorIndices` on the same
`state` the array belongs to, so it is in range by construction. The sum stays a bare `+`
because it is an operand of the weight path, which converts as one piece: `getTotalBalance`
underneath still wraps, so checking this alone would move a wrong number around instead of
catching it. -/
forkdef getAttestationScore (store : Store map) (root : Root) (state : State) :
    StoreTransition Gwei := do
  let active := getActiveValidatorIndices state (currentEpochOf state)
  let validators := sszGet state validators
  active.foldlM (init := (0 : Gwei)) fun acc i => do
    let idx := i.toNat
    if (validators[idx]!).slashed then pure acc
    else match FcMap.lookup store.latestMessages i with
      | none => pure acc
      | some lm =>
        if store.equivocatingIndices.contains i then pure acc
        else
          -- `is_ancestor(store, supported, node)` reads `store.blocks[node.root].slot`, then
          -- walks the supported node down to that slot.
          let block ← FcMap.getOrThrow store.blocks root
          let anc ← getAncestor store lm.root block.slot
          if anc == root then pure (acc + (validators[idx]!).effectiveBalance) else pure acc

/-- `get_weight(store, node)` (`phase0/fork-choice.md:377-391`): the attestation score, plus
the proposer score when `root` is an ancestor of the boosted block. With an unset boost root
the spec returns the attestation score and reads nothing more. The `checkpoint_states` /
`blocks` reads and the `is_ancestor` walk are plain `Dict` reads that raise, so the query is
monadic. -/
forkdef getWeight (store : Store map) (root : Root) : StoreTransition Gwei := do
  let state ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let attestationScore ← getAttestationScore store root state
  if store.proposerBoostRoot == fcZeroRoot then pure attestationScore
  else
    -- `is_ancestor(store, proposer_boost_node, node)`: read `store.blocks[node.root]`, then
    -- walk the boosted block down to that slot.
    let block ← FcMap.getOrThrow store.blocks root
    let anc ← getAncestor store store.proposerBoostRoot block.slot
    if anc == root then
      let proposerScore ← getProposerScore store
      pure (attestationScore + proposerScore)
    else pure attestationScore

/-- `get_voting_source(store, block_root)` (`phase0/fork-choice.md:397-410`): all three reads
(`blocks`, `unrealized_justifications`, `block_states`) are raising `Dict` reads. -/
forkdef getVotingSource (store : Store map) (blockRoot : Root) : StoreTransition Checkpoint := do
  let block ← FcMap.getOrThrow store.blocks blockRoot
  let currentEpoch ← getCurrentStoreEpoch store
  if currentEpoch > computeEpochAtSlot block.slot then
    FcMap.getOrThrow store.unrealizedJustifications blockRoot
  else
    let hs ← FcMap.getOrThrow store.blockStates blockRoot
    pure (sszGet hs currentJustifiedCheckpoint)

/-- `get_node_children(store, node)` (`phase0/fork-choice.md:416-421`): the roots of the
blocks whose parent is `root`. It iterates `store.blocks` and reads each entry it holds, so it
cannot raise; a pure filter. At v1.7.0-beta.4 it takes the whole store, where alpha.12 took
a filtered block map. -/
forkdef getNodeChildren (store : Store map) (root : Root) : Array Root :=
  (FcMap.filterKeys store.blocks (fun _ b => b.parentRoot == root)).toArray

/-- `filter_node_tree(store, node)` (`phase0/fork-choice.md:427-467`): the viable nodes under
`root`, each viable branch with its ancestors up to `root`, in the spec's order (a node's
viable descendants, then the node). A leaf is viable when its voting source stays close to the
justified checkpoint and its chain holds the finalized checkpoint.

v1.7.0-beta.4 replaces `filter_block_tree`. The new walk returns the node list rather than
filling a block map, and it reads `store.blocks[node.root]` only through `get_voting_source`
and `get_checkpoint_block` at a leaf; alpha.12 read it at every step. The reads raise, which
is why the descent is fuel-bounded rather than closed by `termination_by` (§7.2), the same
reason the `DAG walks` heading gives for the walks it heads. The bound is the block count on a
finite acyclic DAG, so fuel-out is unreachable; it would return no nodes. -/
forkdef filterNodeTree (store : Store map) (root : Root) : StoreTransition (Array Root) :=
  go ((FcMap.keys store.blocks).length + 1) root
where
  /-- The viability walk; `fuel` bounds the parent-to-child descent. -/
  go : Nat → Root → StoreTransition (Array Root)
  | 0,        _    => pure #[]
  | fuel + 1, root => do
    let children := getNodeChildren store root
    if !children.isEmpty then
      let viableNodes ← children.foldlM (init := (#[] : Array Root)) fun acc child => do
        pure (acc ++ (← go fuel child))
      if !viableNodes.isEmpty then pure (viableNodes.push root) else pure #[]
    else
      let currentEpoch ← getCurrentStoreEpoch store
      let votingSource ← getVotingSource store root
      let justifiedWithoutHorizon :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
      -- Python's `or` short-circuits, so it forms `voting_source.epoch + 2` only once the two
      -- earlier disjuncts fail. Bind it in that branch alone: an eager checked add would raise
      -- on a sum the reference never evaluates.
      -- `decide` because `≥` on `UInt64` is a `Prop`: in the original the comparison sat inside
      -- a `Bool` `||` chain, which drove the coercion; standalone under `pure` it needs saying.
      let correctJustified ← if justifiedWithoutHorizon then pure true else do
        let horizon ← checkedAdd votingSource.epoch 2 "filter_node_tree: voting_source.epoch + 2"
        pure (decide (horizon ≥ currentEpoch))
      let finalizedBlock ← getCheckpointBlock store root store.finalizedCheckpoint.epoch
      let correctFinalized :=
        store.finalizedCheckpoint.epoch == Const.genesisEpoch
          || store.finalizedCheckpoint.root == finalizedBlock
      if correctJustified && correctFinalized then pure #[root] else pure #[]

/-- `get_filtered_node_tree(store)` (`phase0/fork-choice.md:473-479`): the viable nodes rooted
at the justified checkpoint. -/
forkdef getFilteredNodeTree (store : Store map) : StoreTransition (Array Root) :=
  filterNodeTree store store.justifiedCheckpoint.root

/-- `get_head` (`phase0/fork-choice.md:485-496`): the LMD-GHOST walk from the justified root,
stepping to the heaviest child that is in the filtered node tree, ties broken by the
lexicographically greater root. Monadic `fuelLoop`; the `max` fold is `foldlM`, since
`betterOf` can reject, and that rejecting step is why the walk is fuel-bounded rather than
closed by `termination_by` (§7.2): `maxSlot - currentSlot` is a clean measure on paper but
would have to be carried past the reject. The bound is the block count, so fuel-out is
unreachable; the justified root doubles as the sentinel it would return. -/
forkdef getHead (store : Store map) : StoreTransition Root := do
  let nodes ← getFilteredNodeTree store
  fuelLoop ((FcMap.keys store.blocks).length + 1) store.justifiedCheckpoint.root
      store.justifiedCheckpoint.root fun head => do
    let children := (getNodeChildren store head).filter nodes.contains
    if children.isEmpty then pure (.done head)
    else
      let best ← children.foldlM (init := children[0]!) (betterOf store)
      pure (.next best)
where
  /-- The better of two candidate heads under the phase0 `(weight, root)` ordering:
  greater weight wins, ties by greater root. Phase0 `get_head`'s sort key is the
  2-tuple `(get_weight, child.root)`. The payload-status tiebreaker is a Gloas
  addition, so only the two weights bind here.

  The `foldlM` re-evaluates the accumulator's weight on every step, where `max` evaluates each
  child's key once, and the reject that surfaces is the same either way. An accumulator got
  there by surviving an earlier step, so its `getWeight` already succeeded and cannot throw on
  the re-run. See the Gloas twin, where the key carries a second throwing component. -/
  betterOf (store : Store map) (a b : Root) : StoreTransition Root := do
    let weightA ← getWeight store a
    let weightB ← getWeight store b
    if weightA > weightB then pure a
    else if weightB > weightA then pure b
    else if compare a b == Ordering.gt then pure a else pure b

/-! ## Proposer-head reorg logic (`get_proposer_head`) -/

/-- `is_head_late`: the head block did not arrive before the attestation deadline.
`store.block_timeliness[head_root]` is a raising `Dict` read. -/
forkdef isHeadLate (store : Store map) (headRoot : Root) : StoreTransition Bool := do
  let timely ← FcMap.getOrThrow store.blockTimeliness headRoot
  pure (!timely)

/-- `is_shuffling_stable(slot)` (`phase0/fork-choice.md:615-616`): not on an epoch boundary,
where the proposer shuffling could change. v1.7.0-beta.4 renames phase0's
`is_not_epoch_boundary` to this. The Fulu `get_proposer_head` no longer calls it (EIP-7917, see
there); it stays as the phase0 surface the Fulu spec still carries. -/
forkdef isShufflingStable (slot : Slot) : Bool := slot % UInt64.ofNat Const.slotsPerEpoch != 0

/-- `is_ffg_competitive`: head and parent carry the same unrealized justification.
Both `store.unrealized_justifications[...]` reads raise on a miss. -/
forkdef isFfgCompetitive (store : Store map) (headRoot parentRoot : Root) : StoreTransition Bool := do
  let h ← FcMap.getOrThrow store.unrealizedJustifications headRoot
  let p ← FcMap.getOrThrow store.unrealizedJustifications parentRoot
  pure (h == p)

/-- `is_finalization_ok`: the chain is finalizing within `REORG_MAX_EPOCHS_SINCE_FINALIZATION`.
pyspec (`phase0/fork-choice.md:631-633`) computes the epoch gap as a checked `uint64`
subtraction that raises `ValueError`. `on_tick_per_slot` sets `store.time_ms = time_ms` with no
monotonicity assert (`phase0/fork-choice.md:792-808`), so the spec permits a tick that moves
the clock back below the finalized epoch's start slot, where the subtraction underflows.
`checkedSub` rejects there. No conformance vector emits a backwards tick, so the path is
unreachable in the corpus and carries no pin. Throwing, so the caller binds it. -/
forkdef isFinalizationOk (store : Store map) (slot : Slot) : StoreTransition Bool := do
  let gap ← checkedSub (computeEpochAtSlot slot) store.finalizedCheckpoint.epoch
    "is_finalization_ok: compute_epoch_at_slot(slot) - finalized_checkpoint.epoch"
  pure (gap ≤ Const.reorgMaxEpochsSinceFinalization)

/-- `is_proposing_on_time` (`phase0/fork-choice.md:639-640`): the time into the slot is
within `get_proposer_reorg_cutoff_ms()`. Throwing only to bind `getTimeIntoSlotMs`. -/
forkdef isProposingOnTime (store : Store map) : StoreTransition Bool := do
  pure ((← getTimeIntoSlotMs store) ≤ bpsDeadlineMs Const.proposerReorgCutoffBps)

/-- `is_head_weak(store, head_root)` (`phase0/fork-choice.md:652-673`): the head's attestation
score, plus the effective balance of the equivocators in its slot's committees, is below the
reorg-head threshold. v1.7.0-beta.4 moves phase0 to this form, which Gloas already had: the
equivocator weight keeps the predicate monotonic, so more attestations can only turn it from
`true` to `false`.

The equivocator read is `justified_state.validators[i]` with `i` drawn from the *head* state's
committees, so a cross-branch registry skew can push it past the justified registry's end; the
spec raises `IndexError` there, hence `sszGetIdx` (the wrapped `outOfBounds` reject), and
`foldlM` to bind it. The `store.block_states[head_root]` / `store.blocks[head_root]` reads raise
on a miss. -/
forkdef isHeadWeak (store : Store map) (headRoot : Root) : StoreTransition Bool := do
  let justifiedState ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let reorgThreshold := calculateCommitteeFraction justifiedState Const.reorgHeadWeightThreshold
  let headState ← FcMap.getOrThrow store.blockStates headRoot
  let headBlock ← FcMap.getOrThrow store.blocks headRoot
  let epoch := computeEpochAtSlot headBlock.slot
  let baseWeight ← getAttestationScore store headRoot justifiedState
  let validators := sszGet justifiedState validators
  let headWeight ← (List.range (getCommitteeCountPerSlot headState epoch)).foldlM
      (init := baseWeight) fun acc index => do
    let committee := getBeaconCommittee headState headBlock.slot index
    committee.foldlM (init := acc) fun a i =>
      if store.equivocatingIndices.contains i then do
        let v ← sszGetIdx validators i.toNat
        pure (a + v.effectiveBalance)
      else pure a
  pure (headWeight < reorgThreshold)

/-- `is_parent_strong(store, root)` (`phase0/fork-choice.md:679-685`): the parent's
attestation score, over the justified state, exceeds the reorg-parent threshold. At
v1.7.0-beta.4 the parent is scored with `get_attestation_score` (no proposer boost), where
alpha.12 used `get_weight`. The `store.blocks[root]` read raises on a miss. -/
forkdef isParentStrong (store : Store map) (root : Root) : StoreTransition Bool := do
  let justifiedState ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let parentThreshold := calculateCommitteeFraction justifiedState Const.reorgParentWeightThreshold
  let b ← FcMap.getOrThrow store.blocks root
  let parentWeight ← getAttestationScore store b.parentRoot justifiedState
  pure (parentWeight > parentThreshold)

/-- `is_proposer_equivocation`: more than one block from the head's proposer at its
slot. `store.blocks[root]` raises on a miss. -/
forkdef isProposerEquivocation (store : Store map) (root : Root) : StoreTransition Bool := do
  let block ← FcMap.getOrThrow store.blocks root
  pure (((FcMap.values store.blocks).filter
    (fun b => b.proposerIndex == block.proposerIndex && b.slot == block.slot)).length > 1)

/-- `get_proposer_head` (Fulu, `fulu/fork-choice.md:28-80`): whether a proposer at `slot`
should reorg the current head (`head_root`) by building on its parent. Reorg the head when it
is late, weak, FFG-competitive, finalizing, proposed on time, exactly one slot back, and its
parent is strong; or, more aggressively, when the head is weak and the previous slot had a
proposer equivocation. Otherwise keep the head.

v1.7.0-beta.4 modifies the function in Fulu to drop phase0's `is_shuffling_stable(slot)`
guard (EIP-7917): the proposer lookahead fixes the proposer before the epoch boundary, so a
reorg of a late block at the end of the previous epoch cannot change this slot's proposer. -/
forkdef getProposerHead (store : Store map) (headRoot : Root) (slot : Slot) : StoreTransition Root := do
  -- `store.blocks[head_root]` / `store.blocks[parent_root]` are plain `Dict` reads that
  -- raise on a miss.
  let headBlock ← FcMap.getOrThrow store.blocks headRoot
  let parentRoot := headBlock.parentRoot
  let parentBlock ← FcMap.getOrThrow store.blocks parentRoot
  -- pyspec binds every predicate to a local before the two `all([...])` checks, so each
  -- (throwing) read runs unconditionally and in this order. A lazy `&&` would skip a raise
  -- the spec performs (e.g. `is_ffg_competitive`'s `unrealized_justifications` reads when
  -- `is_head_late` is already false), so bind them all eagerly to reject exactly where
  -- pyspec does.
  let headLate ← isHeadLate store headRoot
  let ffgCompetitive ← isFfgCompetitive store headRoot parentRoot
  let finalizationOk ← isFinalizationOk store slot
  let proposingOnTime ← isProposingOnTime store
  let parentNextSlot ← checkedAdd parentBlock.slot 1 "get_proposer_head: parent_block.slot + 1"
  let parentSlotOk := parentNextSlot == headBlock.slot
  let headNextSlot ← checkedAdd headBlock.slot 1 "get_proposer_head: head_block.slot + 1"
  let currentTimeOk := headNextSlot == slot
  let singleSlotReorg := parentSlotOk && currentTimeOk
  -- `assert proposer_boost_root != head_root` (the boost has worn off). Placed after the
  -- timing predicates and before the weight ones (`is_head_weak` / `is_parent_strong` /
  -- `is_proposer_equivocation`), matching the spec's statement order. Vectorless.
  assert (store.proposerBoostRoot != headRoot)
  let headWeak ← isHeadWeak store headRoot
  let parentStrong ← isParentStrong store headRoot
  let proposerEquivocation ← isProposerEquivocation store headRoot
  if headLate && ffgCompetitive && finalizationOk && proposingOnTime
      && singleSlotReorg && headWeak && parentStrong then pure parentRoot
  else if headWeak && currentTimeOk && proposerEquivocation then pure parentRoot
  else pure headRoot

/-! ## Checkpoint updates -/

forkdef updateCheckpoints (store : Store map) (j f : Checkpoint) : Store map :=
  let store := if j.epoch > store.justifiedCheckpoint.epoch then { store with justifiedCheckpoint := j } else store
  if f.epoch > store.finalizedCheckpoint.epoch then { store with finalizedCheckpoint := f } else store

forkdef updateUnrealizedCheckpoints (store : Store map) (uj uf : Checkpoint) : Store map :=
  let store := if uj.epoch > store.unrealizedJustifiedCheckpoint.epoch then { store with unrealizedJustifiedCheckpoint := uj } else store
  if uf.epoch > store.unrealizedFinalizedCheckpoint.epoch then { store with unrealizedFinalizedCheckpoint := uf } else store

/-- `compute_pulled_up_tip`: pull up the block's post-state through
`process_justification_and_finalization`, record its unrealized justification, and
(for a prior-epoch block) realize it. The `block_states` / `blocks` reads raise on a
miss, and the pull-up itself propagates: pyspec runs `process_justification_and_finalization`
unguarded, so a reject (e.g. the restored `get_block_root_at_slot` recency assert on a
degenerate epoch-boundary state) aborts the surrounding `on_block`, matching the Gloas
and Heze twins.

Each pyspec statement boundary gets its own `set`, the rule `aed053b` established for
`on_attestation` and `on_block`: the reference runner mutates in place and the harness
continues an expected rejection from the error-time store, so a write pyspec has already
applied must survive a later raise. One `set` at the end rolled back the
`unrealized_justifications` insert and the `update_unrealized_checkpoints` writes whenever
`get_current_store_epoch` rejected. The `store.blocks[block_root]` read moves below the
pull-up too, where pyspec performs it. -/
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

/-- `on_tick_per_slot(store, time_ms)` (`phase0/fork-choice.md:792-808`): set the clock,
reset the boost on a new slot, and pull up the unrealized checkpoints on a new epoch. -/
forkdef onTickPerSlot (store : Store map) (timeMs : UInt64) : StoreTransition (Store map) := do
  let previousSlot ← getCurrentSlot store
  let store := { store with timeMs := timeMs }
  let currentSlot ← getCurrentSlot store
  let store := if currentSlot > previousSlot then { store with proposerBoostRoot := fcZeroRoot } else store
  pure <| if currentSlot > previousSlot && computeSlotsSinceEpochStart currentSlot == 0 then
    updateCheckpoints store store.unrealizedJustifiedCheckpoint store.unrealizedFinalizedCheckpoint
  else store
where
  -- `slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot))`: the epoch-start slot is
  -- always `≤ slot`, so this `uint64` subtraction cannot underflow; a bare `-`, not `checkedSub`.
  computeSlotsSinceEpochStart (slot : Slot) : UInt64 := slot - computeStartSlotAtEpoch (computeEpochAtSlot slot)

/-- `on_tick(store, time_ms)` (`phase0/fork-choice.md:946-954`): advance the store clock to
`time_ms`, running `on_tick_per_slot` at the start of every slot the clock passes on the way.
Each `on_tick_per_slot` commits before the next iteration, because pyspec calls it against the
live store and a raise partway through the catch-up leaves the earlier per-slot boost resets
and checkpoint updates applied. Threading a local and committing once discarded them. Same
rule as `aed053b`'s, at the site it did not reach; the loop body can throw.

The clock is in milliseconds, so the slot-start times come from `compute_time_at_slot_ms` with
no seconds rounding, and the catch-up bound below is exact. -/
forkdef onTick (timeMs : UInt64) : StoreTransition Unit := do
  let store ← get
  let tickSlot ← liftErr (computeSlotAtTimeMs store.genesisTimeMs timeMs)
  let cur ← getCurrentSlot store
  -- Fuel rather than a measure (§7.2): the body reads the store and can throw, so a decreasing
  -- `tickSlot - get_current_slot` would have to be carried past a rejecting step. The bound is a
  -- Lean artifact, not a spec op: a raw `-` here can only underflow to a huge ceiling when
  -- `tickSlot < cur`, and then the step `.done`s on its first iteration anyway. Each pass of the
  -- loop moves the clock to the next slot start, so `tickSlot - cur + 1` passes suffice;
  -- `fuelIterateM!` throws on fuel-out rather than returning a wrong store.
  fuelIterateM! ((tickSlot - cur).toNat + 1) () "on_tick: per-slot catch-up" fun _ => do
    let cs ← getCurrentSlot (← get)
    if cs < tickSlot then
      let nextSlot ← checkedAdd cs 1 "on_tick: get_current_slot(store) + 1"
      let nextSlotTimeMs ← liftErr (computeTimeAtSlotMs (← get).genesisTimeMs nextSlot)
      set (← onTickPerSlot (← get) nextSlotTimeMs)
      pure (.next ())
    else
      set (← onTickPerSlot (← get) timeMs)
      pure (.done ())

/-! ## on_block helpers -/

/-- `record_block_timeliness(store, root)` (`phase0/fork-choice.md:890-896`): the block is
timely when it arrives in its own slot, before the attestation deadline. The
`store.blocks[root]` read raises on a miss. -/
forkdef recordBlockTimeliness (store : Store map) (root : Root) : StoreTransition (Store map) := do
  let block ← FcMap.getOrThrow store.blocks root
  let timeIntoSlotMs ← getTimeIntoSlotMs store
  let isBeforeAttestingInterval := timeIntoSlotMs < bpsDeadlineMs Const.attestationDueBps
  let currentSlot ← getCurrentSlot store
  let isTimely := currentSlot == block.slot && isBeforeAttestingInterval
  pure { store with blockTimeliness := FcMap.insert store.blockTimeliness root isTimely }

/-- `compute_shuffling_lookahead_start_slot(epoch)` (`phase0/fork-choice.md:902-904`): the
first slot of the epoch `MIN_SEED_LOOKAHEAD` before `epoch`, floored at genesis. Pure. -/
forkdef computeShufflingLookaheadStartSlot (epoch : Epoch) : Slot :=
  computeStartSlotAtEpoch (saturatingSub epoch Const.minSeedLookahead)

/-- `compute_shuffling_dependent_slot(epoch)` (`phase0/fork-choice.md:910-912`): the last slot
before the lookahead start, the slot whose block fixes `epoch`'s proposer shuffling. Floored
at genesis, so for the first `MIN_SEED_LOOKAHEAD + 1` epochs it is slot `0`. Pure. -/
forkdef computeShufflingDependentSlot (epoch : Epoch) : Slot :=
  saturatingSub (computeShufflingLookaheadStartSlot epoch) 1

/-- `get_shuffling_dependent_root(store, root, epoch)` (`phase0/fork-choice.md:918-921`): the
root of `root`'s ancestor at the shuffling dependent slot. At v1.7.0-beta.4 the genesis case
goes through the same walk, so an early epoch resolves to the slot-0 ancestor, where alpha.12
returned the zero root. Throwing, because `getAncestor` is. -/
forkdef getShufflingDependentRoot (store : Store map) (root : Root) (epoch : Epoch) :
    StoreTransition Root :=
  getAncestor store root (computeShufflingDependentSlot epoch)

/-- `update_proposer_boost_root(store, head, root)` (`phase0/fork-choice.md:927-938`): boost a
timely first block whose shuffling dependent root matches the pre-insertion head's. The spec
binds the head's dependent root first, then the block's, so when both walks would miss, the
surfaced `missingKey` names the head walk's read. -/
forkdef updateProposerBoostRoot (store : Store map) (head root : Root) :
    StoreTransition (Store map) := do
  let isFirstBlock := store.proposerBoostRoot == fcZeroRoot
  let isTimely ← FcMap.getOrThrow store.blockTimeliness root
  let epoch ← getCurrentStoreEpoch store
  let headDependentRoot ← getShufflingDependentRoot store head epoch
  let blockDependentRoot ← getShufflingDependentRoot store root epoch
  let isSameDependentRoot := headDependentRoot == blockDependentRoot
  if isTimely && isFirstBlock && isSameDependentRoot then
    pure { store with proposerBoostRoot := root }
  else pure store

/-! ## Data availability (PeerDAS, EIP-7594) -/

/-- `verify_data_column_sidecar` (`fulu/p2p-interface.md`): the structural gate. The index is
in range, the sidecar carries at least one commitment and no more than the blob limit at its
block's epoch (`get_blob_parameters`), and the column / commitment / proof list lengths agree. -/
forkdef verifyDataColumnSidecar (sidecar : DataColumnSidecar) : Bool :=
  let ncol := sidecar.column.size
  let ncomm := sidecar.kzgCommitments.size
  let epoch := computeEpochAtSlot sidecar.signedBlockHeader.message.slot
  if sidecar.index ≥ UInt64.ofNat Const.numberOfColumns then false
  else if ncomm == 0 then false
  else if ncomm > (getBlobParameters epoch).maxBlobsPerBlock then false
  else ncol == ncomm && ncol == sidecar.kzgProofs.size

/-- `verify_data_column_sidecar_kzg_proofs`: the KZG gate. Every cell index in the
batch is the sidecar's own column `index`; the cells are batch-verified against the
commitments and proofs through the `[CryptoBackend]` KZG seam. -/
forkdef verifyDataColumnSidecarKzgProofs (sidecar : DataColumnSidecar) : Bool :=
  CryptoBackend.kzgVerifyCellProofBatch
    (sidecar.kzgCommitments.map vecToBytes)
    (Array.replicate sidecar.column.size sidecar.index)
    (sidecar.column.map vecToBytes)
    (sidecar.kzgProofs.map vecToBytes)

/-- `is_data_available`: every supplied column sidecar passes both gates. The runner
feeds exactly the columns the step lists, mirroring the spec's
`retrieve_column_sidecars`.

The non-emptiness guard tracks the **test helper**, not the spec function. The spec's
`is_data_available` (`fulu/fork-choice.md:86-97`) returns `all([]) = True` on an empty
column set, because `retrieve_column_sidecars` is declared implementation-dependent and
left unmodeled. The pyspec harness monkeypatches it to raise
`AssertionError("Simulation: not all required columns have been sampled")` on an empty
set (`helpers/fork_choice.py:90-94`), which is the behaviour every vector observes, so
the guard reproduces the helper. -/
forkdef isDataAvailable (cols : Array DataColumnSidecar) : Bool :=
  !cols.isEmpty && cols.all (fun sidecar => verifyDataColumnSidecar sidecar && verifyDataColumnSidecarKzgProofs sidecar)

/-- `on_block` (Fulu, `fulu/fork-choice.md:108-159`). Returns early, with the store
unchanged, for a block it already holds. Otherwise it rejects (via `assert`) an unknown
parent, a future block, a finality conflict, or unavailable blob data, and propagates a failed
`state_transition` through `runNestedStateTransition`. `columns` are the block's PeerDAS
data-column sidecars (EIP-7594); the runner supplies exactly those the step lists. -/
forkdef onBlock (signedBlock : SignedBeaconBlock) (columns : Array DataColumnSidecar) :
    StoreTransition Unit := do
  let store ← get
  let block := signedBlock.message
  let blockRoot := htr block
  -- Return early if the block is already known (new at v1.7.0-beta.4).
  if FcMap.contains store.blocks blockRoot then return
  let parentState ← FcMap.getOrAssert store.blockStates block.parentRoot
    "block.parent_root in store.block_states"
  let currentSlot ← getCurrentSlot store
  assert (currentSlot ≥ block.slot)
  let finalizedSlot := computeStartSlotAtEpoch store.finalizedCheckpoint.epoch
  assert (block.slot > finalizedSlot)
  assert (store.finalizedCheckpoint.root == (← getCheckpointBlock store block.parentRoot store.finalizedCheckpoint.epoch))
  -- Data availability (EIP-7594). The spec's `on_block` calls `is_data_available(block_root)`
  -- unconditionally; the commitments short-circuit is ours, and it pairs with
  -- `isDataAvailable`'s non-emptiness guard. That guard reproduces the test helper, which
  -- raises on an empty column set, so without this clause a blob-free block would reject on a
  -- set the spec calls available. The one input shape that would tell the two apart is a block
  -- carrying blob commitments with no `columns` key in its step; the generator emits `columns`
  -- for every such block, so no vector produces it.
  assert (block.body.blobKzgCommitments.toArray.isEmpty || isDataAvailable columns)

  let postState ← runNestedStateTransition parentState (stateTransition signedBlock)
  -- The head is taken BEFORE the new block is added (`update_proposer_boost_root`).
  let head ← getHead store

  -- Insert the block and its post-state, then record its timeliness. `set` at each pyspec
  -- statement boundary: `record_block_timeliness`'s clock read, `update_proposer_boost_root`'s
  -- dependent-root walks, and `compute_pulled_up_tip`'s pull-up can each raise, so each
  -- completed write must persist (in-place runner semantics).
  set { store with
    blocks := FcMap.insert store.blocks blockRoot block
    blockStates := FcMap.insert store.blockStates blockRoot postState }
  set (← recordBlockTimeliness (← get) blockRoot)
  set (← updateProposerBoostRoot (← get) head blockRoot)
  set (updateCheckpoints (← get) (sszGet postState currentJustifiedCheckpoint) (sszGet postState finalizedCheckpoint))
  -- `(map := map)`: no store argument, so the section's map backing is undetermined here
  -- (the ambient `get`/`set` constraint alone leaves it a stuck metavariable); name it.
  computePulledUpTip (map := map) blockRoot

/-! ## on_attestation -/

/-- `store_target_checkpoint_state`: cache the target's state, advancing to the
target epoch start if needed. The pinned `process_slots` is unguarded, so a rejected
advance propagates (wrapped `.transition`) and nothing is cached, aborting
`on_attestation` with the store unchanged. Caching the unadvanced base state instead
would leave a wrong-slot entry for later reads to consume. -/
forkdef storeTargetCheckpointState (store : Store map) (target : Checkpoint) :
    StoreTransition (Store map) := do
  if FcMap.contains store.checkpointStates target then pure store
  else
    let base ← FcMap.getOrThrow store.blockStates target.root
    let targetSlot := computeStartSlotAtEpoch target.epoch
    let advanced ←
      if (sszGet base slot) < targetSlot then
        runNestedStateTransition base (processSlots targetSlot)
      else pure base
    pure { store with checkpointStates := FcMap.insert store.checkpointStates target advanced }

/-- `validate_target_epoch_against_current_time` (`phase0/fork-choice.md:816-823`): the
attestation's target is the current or the previous store epoch, where the previous epoch is
`saturating_sub(current_epoch, 1)`. -/
forkdef validateTargetEpochAgainstCurrentTime (store : Store map) (att : Attestation) :
    StoreTransition Unit := do
  let target := att.data.target
  let currentEpoch ← getCurrentStoreEpoch store
  let previousEpoch := saturatingSub currentEpoch 1
  assert (target.epoch == currentEpoch || target.epoch == previousEpoch)

/-- `validate_on_attestation`. The epoch-scope check is skipped for a block-implied
attestation (`is_from_block = true`); the rest always apply. -/
forkdef validateOnAttestation (store : Store map) (att : Attestation) (isFromBlock : Bool) : StoreTransition Unit := do
  let target := att.data.target
  if !isFromBlock then validateTargetEpochAgainstCurrentTime store att
  assert (target.epoch == computeEpochAtSlot att.data.slot)
  assert (FcMap.contains store.blocks target.root)
  assert (FcMap.contains store.blocks att.data.beaconBlockRoot)
  let b ← FcMap.getOrThrow store.blocks att.data.beaconBlockRoot
  assert (b.slot ≤ att.data.slot)
  assert (target.root == (← getCheckpointBlock store att.data.beaconBlockRoot target.epoch))
  let currentSlot ← getCurrentSlot store
  -- `att.data.slot` is wire-controlled and the epoch-scope guard above is skipped when
  -- `is_from_block`, so a block-implied attestation reaches here with an arbitrary slot. The
  -- bare `+` wraps `0xFFFF…FFFF + 1` to `0`, `currentSlot ≥ 0` holds for every store, and the
  -- attestation is ACCEPTED into `latest_messages`, corrupting the head walk. pyspec
  -- (`phase0/fork-choice.md:854`) forms a checked `uint64` sum that raises `ValueError`, which
  -- `expect_assertion_error` does not catch. Sequenced after every preceding assert, matching
  -- Python's evaluation order.
  let attestationDeadline ← checkedAdd att.data.slot 1
    "on_attestation: attestation.data.slot + 1"
  assert (currentSlot ≥ attestationDeadline)

/-- `update_latest_messages` for the attesting indices (skipping equivocators). -/
forkdef updateLatestMessages (store : Store map) (attestingIndices : Array ValidatorIndex)
    (att : Attestation) : Store map := Id.run do
  let target := att.data.target
  let mut lm := store.latestMessages
  for i in attestingIndices do
    if !store.equivocatingIndices.contains i then
      match FcMap.lookup lm i with
      | some prev => if target.epoch > prev.epoch then lm := FcMap.insert lm i { epoch := target.epoch, root := att.data.beaconBlockRoot }
      | none      => lm := FcMap.insert lm i { epoch := target.epoch, root := att.data.beaconBlockRoot }
  return { store with latestMessages := lm }

/-- `on_attestation`. `isFromBlock` distinguishes a wire attestation (the
`attestation` step) from a block-implied one. -/
forkdef onAttestation (att : Attestation) (isFromBlock : Bool) : StoreTransition Unit := do
  validateOnAttestation (← get) att isFromBlock

  -- `store_target_checkpoint_state` mutates `checkpoint_states` before the
  -- indexed-attestation assert below can reject; `set` at the pyspec statement
  -- boundary so an expected rejection keeps the cache (in-place runner semantics).
  let store ← storeTargetCheckpointState (← get) att.data.target
  set store
  let targetState ← FcMap.getOrThrowKey store.checkpointStates att.data.target att.data.target.root
  let attesting := (← liftErr (getAttestingIndices targetState att)).qsort (· < ·)
  let indexedAttestation : IndexedAttestation :=
    { attestingIndices := ← sszOfArrayM "attestingIndices" attesting, data := att.data,
      signature := att.signature }
  assert (isValidIndexedAttestation targetState indexedAttestation)

  set (updateLatestMessages store attesting att)

/-! ## on_attester_slashing -/

/-- `on_attester_slashing`: mark the intersection of the two attestations'
indices as equivocating. -/
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

/-- `get_forkchoice_store(anchor_state, anchor_block)` (`phase0/fork-choice.md:219-241`). The
pyspec opens with `assert anchor_block.state_root == hash_tree_root(anchor_state)`, the anchor's
self-consistency check, so the seed is a throwing `Except StoreTransitionError` action rather
than a total store literal. The reject branch is vectorless (the harness derives the anchor
block and state from one vector, so `state_root` always matches); Heze's `pinAnchorRejects`
locks the identical assert, and this Fulu constructor carries it verbatim. The anchor block's
root is computed from the (state-root-filled) anchor block.

At v1.7.0-beta.4 the clock seeds in milliseconds: `genesis_time_ms =
seconds_to_milliseconds(anchor_state.genesis_time)` (which caps at `UINT64_MAX` rather than raising) and
`time_ms = compute_time_at_slot_ms(genesis_time_ms, anchor_state.slot)`, whose product and sum
are checked. `anchor_state` comes straight off the wire, so a slot at or above
`2^64 / SLOT_DURATION_MS` faults where a bare product would wrap and seed a wrong clock. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) :
    Except StoreTransitionError (Store map) := do
  -- `anchor_block.state_root == hash_tree_root(anchor_state)`: the boxed state hashes
  -- through `stateRoot` (the cached-tree path), not `htr` (which wants a bare `SSZRepr`).
  assert (anchorBlock.stateRoot == bytesToRoot (stateRoot anchorState).1)
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }
  let genesisTimeMs := secondsToMilliseconds (sszGet anchorState genesisTime)
  let timeMs ← liftErr (computeTimeAtSlotMs genesisTimeMs (sszGet anchorState slot))
  pure
    { timeMs := timeMs
      genesisTimeMs := genesisTimeMs
      justifiedCheckpoint := cp, finalizedCheckpoint := cp
      unrealizedJustifiedCheckpoint := cp, unrealizedFinalizedCheckpoint := cp
      proposerBoostRoot := fcZeroRoot
      equivocatingIndices := #[]
      blocks := FcMap.insert FcMap.empty anchorRoot anchorBlock
      blockStates := FcMap.insert FcMap.empty anchorRoot anchorState
      blockTimeliness := FcMap.empty
      checkpointStates := FcMap.insert FcMap.empty cp anchorState
      latestMessages := FcMap.empty
      unrealizedJustifications := FcMap.insert FcMap.empty anchorRoot cp }

end

end EthCLSpecs.Fulu
