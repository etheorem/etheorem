import EthCLSpecs.Fulu.Transition
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLSpecs.Fulu.ForkChoice`: the LMD-GHOST store and its handlers

The second state machine (`FRAMEWORK_ARCHITECTURE.md` §9): the fork-choice `Store`
and the `on_tick` / `on_block` / `on_attestation` / `on_attester_slashing`
handlers, plus `get_head` (the filtered-block-tree LMD-GHOST walk with proposer
boost). The store is a `forkstruct` (captured for inheritance); the section opens
with `fork_choice_section map`, so the handlers are monadic `StoreTransition` actions
over the typed `StoreTransitionError` (`assert` / `missingKey` / `todo`),
and the queries (`get_weight`, `get_head`, the reorg predicates) are pure functions
of the boxed store.

The handlers reuse the Fulu spine: `on_block` runs `state_transition` on a copy of
the parent post-state through `runStateTransition` (the one-way bridge that wraps an
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

/-! ## Key instances for the map backing -/

/-- Lexicographic `Ord` on a 32-byte vector (`Root` / `Bytes32` / `Hash32`), so a
`Root`-keyed map satisfies `MapKind`'s `[Ord K]`. -/
instance instOrdBytes32 : Ord (Vector UInt8 32) where
  compare a b := Id.run do
    for i in [0:32] do
      let x := a.toArray[i]!
      let y := b.toArray[i]!
      if x < y then return .lt
      if x > y then return .gt
    return .eq

/-! ## Store -/

/-- The latest attestation seen from a validator: its target epoch and head vote.
A `forkstruct`, so a child fork can `inherit` it. -/
forkstruct LatestMessage where
  epoch : Epoch
  root  : Root

deriving instance Inhabited for LatestMessage

/-- The fork-choice store, parameterized by its map backing and (via `forkstruct`'s
auto `[Preset]`) the preset / hasher tag. The boxed states reuse the transition
layer's `State` (`= SSZ.Box HasherTag.H BeaconState`). -/
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
  blockTimeliness               : map Root Bool
  checkpointStates              : map Checkpoint State
  latestMessages                : map ValidatorIndex LatestMessage
  unrealizedJustifications      : map Root Checkpoint

fork_choice_section map

/-- The all-zero root (an unset `proposer_boost_root`). -/
forkdef fcZeroRoot : Root := Vector.replicate 32 0

/-! ## Time / slot accessors -/

forkdef getSlotsSinceGenesis (store : Store map) : UInt64 :=
  (store.time - store.genesisTime) / Const.secondsPerSlot
forkdef getCurrentSlot (store : Store map) : Slot := Const.genesisSlot + getSlotsSinceGenesis store
forkdef getCurrentStoreEpoch (store : Store map) : Epoch := computeEpochAtSlot (getCurrentSlot store)

/-- `time_into_slot`, in milliseconds: wall-clock elapsed since the slot start, modulo the
slot length. The store clock is in seconds, converted with `* 1000`. -/
forkdef timeIntoSlotMs (store : Store map) : UInt64 :=
  ((store.time - store.genesisTime) * 1000) % Const.slotDurationMs

/-- A basis-points deadline within a slot, in milliseconds: `bps * SLOT_DURATION_MS //
BASIS_POINTS`. Multiply before the `UInt64` truncating divide, so the floor lands on the full
`bps * SLOT_DURATION_MS` product. -/
forkdef bpsDeadlineMs (bps : UInt64) : UInt64 :=
  bps * Const.slotDurationMs / Const.basisPoints

/-! ## DAG walks -/

/-- `get_ancestor(store, root, slot)`: walk parent links until at/below `slot`.
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

/-- The per-slot committee weight: total active balance divided across the slots of an epoch
(`get_total_active_balance // SLOTS_PER_EPOCH`). The shared core of `getProposerScore` and
`calculateCommitteeFraction`. `UInt64` truncating division, so the floor is taken here once and
both callers inherit the same rounding. -/
forkdef committeeWeight (state : State) : Gwei :=
  getTotalActiveBalance state / UInt64.ofNat Const.slotsPerEpoch

/-- `get_proposer_score`. -/
forkdef getProposerScore (store : Store map) : StoreTransition Gwei := do
  let state ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  pure (committeeWeight state * UInt64.ofNat Const.proposerScoreBoost / 100)

/-- `get_weight(store, root)`: attestation balance for `root`, plus the proposer
boost if `root` is an ancestor of the boosted block. The `checkpoint_states` /
`blocks` reads and the inlined `is_ancestor` walks are plain `Dict` reads that
raise, so the query is monadic; the active-validator folds turn `foldlM` to bind
the throwing `getAncestor`. -/
forkdef getWeight (store : Store map) (root : Root) : StoreTransition Gwei := do
  let state ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let block ← FcMap.getOrThrow store.blocks root
  let active := getActiveValidatorIndices state (currentEpochOf state)
  let validators := sszGet state validators
  let attestationScore ← active.foldlM (init := (0 : Gwei)) fun acc i => do
    let idx := i.toNat
    if (validators[idx]!).slashed then pure acc
    else match FcMap.lookup store.latestMessages i with
      | none => pure acc
      | some lm =>
        if store.equivocatingIndices.contains i then pure acc
        else
          let anc ← getAncestor store lm.root block.slot
          if anc == root then pure (acc + (validators[idx]!).effectiveBalance) else pure acc
  if store.proposerBoostRoot == fcZeroRoot then pure attestationScore
  else
    let anc ← getAncestor store store.proposerBoostRoot block.slot
    if anc == root then
      let ps ← getProposerScore store
      pure (attestationScore + ps)
    else pure attestationScore

/-- `filter_block_tree`: collect the viable branches into `acc` (a key set),
returning whether `blockRoot` is viable. The recursion is fuel-bounded by the block
count. Monadic: the opening `store.blocks[block_root]` read and the `get_voting_source`
reads are plain `Dict`s that raise. -/
forkdef filterBlockTree (store : Store map) (blockRoot : Root) (acc : Array Root) :
    StoreTransition (Array Root × Bool) :=
  go ((FcMap.keys store.blocks).length + 1) blockRoot acc
where
  /-- `get_voting_source(store, block_root)`: all three reads (`blocks`,
  `unrealized_justifications`, `block_states`) are raising `Dict` reads. -/
  getVotingSource (store : Store map) (blockRoot : Root) : StoreTransition Checkpoint := do
    let block ← FcMap.getOrThrow store.blocks blockRoot
    let currentEpoch := getCurrentStoreEpoch store
    if currentEpoch > computeEpochAtSlot block.slot then
      FcMap.getOrThrow store.unrealizedJustifications blockRoot
    else
      let hs ← FcMap.getOrThrow store.blockStates blockRoot
      pure (sszGet hs currentJustifiedCheckpoint)
  /-- The viability walk; `fuel` bounds the parent-to-child descent. -/
  go : Nat → Root → Array Root → StoreTransition (Array Root × Bool)
  | 0,        _,         acc => pure (acc, false)
  | fuel + 1, blockRoot, acc => do
    let _ ← FcMap.getOrThrow store.blocks blockRoot
    let children := FcMap.filterKeys store.blocks (fun _ b => b.parentRoot == blockRoot)
    if children.isEmpty then
      let currentEpoch := getCurrentStoreEpoch store
      let votingSource ← getVotingSource store blockRoot
      let correctJustified :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
          || votingSource.epoch + 2 ≥ currentEpoch
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

/-- `get_head`: the filtered-block-tree LMD-GHOST walk, ties broken by the
lexicographically-greater root. Fuel-bounded. Monadic `fuelLoop`; the `max` fold is
`foldlM` over the now-throwing `betterOf`. -/
forkdef getHead (store : Store map) : StoreTransition Root := do
  let (viable, _) ← filterBlockTree store store.justifiedCheckpoint.root #[]
  fuelLoop ((FcMap.keys store.blocks).length + 1) store.justifiedCheckpoint.root
      store.justifiedCheckpoint.root fun head => do
    let children := viable.filter fun r =>
      match FcMap.lookup store.blocks r with
      | some b => b.parentRoot == head
      | none   => false
    if children.isEmpty then pure (.done head)
    else
      let best ← children.foldlM (init := children[0]!) (betterOf store)
      pure (.next best)
where
  /-- The better of two candidate heads under the phase0 `(weight, root)` ordering:
  greater weight wins, ties by greater root. Phase0 `get_head`'s sort key is the
  2-tuple `(get_weight, child.root)`. The payload-status tiebreaker is a Gloas
  addition, so only the two weights bind here. -/
  betterOf (store : Store map) (a b : Root) : StoreTransition Root := do
    let weightA ← getWeight store a
    let weightB ← getWeight store b
    if weightA > weightB then pure a
    else if weightB > weightA then pure b
    else if compare a b == Ordering.gt then pure a else pure b

/-! ## Proposer-head reorg logic (`get_proposer_head`) -/

/-- `calculate_committee_fraction`: a percentage of the per-slot committee weight. -/
forkdef calculateCommitteeFraction (state : State) (committeePercent : UInt64) : Gwei :=
  committeeWeight state * committeePercent / 100

/-- `is_head_late`: the head block did not arrive before the attestation deadline.
`store.block_timeliness[head_root]` is a raising `Dict` read. -/
forkdef isHeadLate (store : Store map) (headRoot : Root) : StoreTransition Bool := do
  let timely ← FcMap.getOrThrow store.blockTimeliness headRoot
  pure (!timely)

/-- `is_shuffling_stable`: not on an epoch boundary (where the shuffling could flip). -/
forkdef isShufflingStable (slot : Slot) : Bool := slot % UInt64.ofNat Const.slotsPerEpoch != 0

/-- `is_ffg_competitive`: head and parent carry the same unrealized justification.
Both `store.unrealized_justifications[...]` reads raise on a miss. -/
forkdef isFfgCompetitive (store : Store map) (headRoot parentRoot : Root) : StoreTransition Bool := do
  let h ← FcMap.getOrThrow store.unrealizedJustifications headRoot
  let p ← FcMap.getOrThrow store.unrealizedJustifications parentRoot
  pure (h == p)

/-- `is_finalization_ok`: the chain is finalizing within `REORG_MAX_EPOCHS_SINCE_FINALIZATION`. -/
forkdef isFinalizationOk (store : Store map) (slot : Slot) : Bool :=
  computeEpochAtSlot slot - store.finalizedCheckpoint.epoch ≤ Const.reorgMaxEpochsSinceFinalization

/-- `is_proposing_on_time`: within the reorg cutoff of the slot start (ms timing; the
store clock is seconds, converted via `* 1000`). -/
forkdef isProposingOnTime (store : Store map) : Bool :=
  timeIntoSlotMs store ≤ bpsDeadlineMs Const.proposerReorgCutoffBps

/-- `is_head_weak`: the head's weight is below the reorg-head threshold. -/
forkdef isHeadWeak (store : Store map) (headRoot : Root) : StoreTransition Bool := do
  let js ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let hw ← getWeight store headRoot
  pure (hw < calculateCommitteeFraction js Const.reorgHeadWeightThreshold)

/-- `is_parent_strong`: the head's parent weight exceeds the reorg-parent threshold.
Phase0 `is_parent_strong` reads `store.blocks[root].parent_root` (raising) and scores
the bare parent node, so the block read is faithful here. Gloas scores its parent at a
synthetic PENDING node with no block read, so no throw belongs on that path. -/
forkdef isParentStrong (store : Store map) (root : Root) : StoreTransition Bool := do
  let js ← FcMap.getOrThrowKey store.checkpointStates store.justifiedCheckpoint
    store.justifiedCheckpoint.root
  let b ← FcMap.getOrThrow store.blocks root
  let pw ← getWeight store b.parentRoot
  pure (pw > calculateCommitteeFraction js Const.reorgParentWeightThreshold)

/-- `is_proposer_equivocation`: more than one block from the head's proposer at its
slot. `store.blocks[root]` raises on a miss. -/
forkdef isProposerEquivocation (store : Store map) (root : Root) : StoreTransition Bool := do
  let block ← FcMap.getOrThrow store.blocks root
  pure (((FcMap.values store.blocks).filter
    (fun b => b.proposerIndex == block.proposerIndex && b.slot == block.slot)).length > 1)

/-- `get_proposer_head`: whether a proposer at `slot` should reorg the current head
(`head_root`) by building on its parent. Reorg the head when it is late, weak, on a
stable shuffling, FFG-competitive, finalizing, proposed on time, exactly one slot
back, and its parent is strong; or, more aggressively, when the head is weak and the
previous slot had a proposer equivocation. Otherwise keep the head. -/
forkdef getProposerHead (store : Store map) (headRoot : Root) (slot : Slot) : StoreTransition Root := do
  match FcMap.lookup store.blocks headRoot with
  | none => pure headRoot
  | some headBlock =>
    let parentRoot := headBlock.parentRoot
    match FcMap.lookup store.blocks parentRoot with
    | none => pure headRoot
    | some parentBlock =>
      let currentTimeOk := headBlock.slot + 1 == slot
      let singleSlotReorg := parentBlock.slot + 1 == headBlock.slot && currentTimeOk
      let headWeak ← isHeadWeak store headRoot
      -- The spec asserts `proposer_boost_root != head_root` (boost has worn off);
      -- modeled defensively as keeping the head rather than a raise (an optional
      -- helper; deliberate deviation, see the LANDED note). Only the Dict reads
      -- above convert to throwing.
      if store.proposerBoostRoot == headRoot then pure headRoot
      else if (← isHeadLate store headRoot) && isShufflingStable slot
          && (← isFfgCompetitive store headRoot parentRoot)
          && isFinalizationOk store slot && isProposingOnTime store && singleSlotReorg
          && headWeak && (← isParentStrong store headRoot) then pure parentRoot
      else if headWeak && currentTimeOk && (← isProposerEquivocation store headRoot) then pure parentRoot
      else pure headRoot

/-! ## Checkpoint updates -/

forkdef updateCheckpoints (store : Store map) (j f : Checkpoint) : Store map :=
  let store := if j.epoch > store.justifiedCheckpoint.epoch then { store with justifiedCheckpoint := j } else store
  if f.epoch > store.finalizedCheckpoint.epoch then { store with finalizedCheckpoint := f } else store

forkdef updateUnrealizedCheckpoints (store : Store map) (uj uf : Checkpoint) : Store map :=
  let store := if uj.epoch > store.unrealizedJustifiedCheckpoint.epoch then { store with unrealizedJustifiedCheckpoint := uj } else store
  if uf.epoch > store.unrealizedFinalizedCheckpoint.epoch then { store with unrealizedFinalizedCheckpoint := uf } else store

/-- `compute_pulled_up_tip`: pull up the block's post-state through
`process_justification_and_finalization`, record the unrealized justification, and
(for a prior-epoch block) realize it. The `block_states` / `blocks` reads are raising
`Dict`s, so monadic. The inner pull-up stays best-effort here — that swallow is a
separate discrepancy (F8) removed in its own commit. -/
forkdef computePulledUpTip (store : Store map) (blockRoot : Root) : StoreTransition (Store map) := do
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

/-- `advance_store_time`: catch up slot-by-slot, then set the exact time (the pure
core of `on_tick`). Fuel-bounded by the number of slots to advance. -/
forkdef advanceStoreTime (store : Store map) (time : UInt64) : Store map :=
  fuelIterate ((((time - store.genesisTime) / Const.secondsPerSlot) - getCurrentSlot store).toNat + 1) store fun store =>
    let tickSlot := (time - store.genesisTime) / Const.secondsPerSlot
    if getCurrentSlot store < tickSlot then
      let previousTime := store.genesisTime + (getCurrentSlot store + 1) * Const.secondsPerSlot
      .next (onTickPerSlot store previousTime)
    else .done (onTickPerSlot store time)

/-- `on_tick`: advance the store clock to `time`. -/
forkdef onTick (time : UInt64) : StoreTransition Unit := do
  modify fun store => advanceStoreTime store time

/-! ## on_block -/

/-- `get_dependent_root` (v1.7): the block root that determined the current epoch's
proposer shuffling. Monadic to bind the throwing `getAncestor`. -/
forkdef getDependentRoot (store : Store map) (root : Root) : StoreTransition Root := do
  let epoch := getCurrentStoreEpoch store
  if epoch ≤ Const.minSeedLookahead then pure fcZeroRoot
  else getAncestor store root (computeStartSlotAtEpoch (epoch - Const.minSeedLookahead) - 1)

/-! ## Data availability (PeerDAS, EIP-7594) -/

/-- `verify_data_column_sidecar`: the structural gate. The index is in range, the
column is non-empty and within the blob limit, and the column / commitment / proof
list lengths agree. -/
forkdef verifyDataColumnSidecar (sidecar : DataColumnSidecar) : Bool :=
  let ncol := sidecar.column.size
  let ncomm := sidecar.kzgCommitments.size
  if sidecar.index ≥ UInt64.ofNat Const.numberOfColumns then false
  else if ncomm == 0 then false
  else if ncomm > Const.maxBlobsPerBlockElectra then false
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
feeds exactly the columns the step lists (mirroring the spec's `retrieve_column_sidecars`),
so an empty set rejects (the spec raises when columns are missing). -/
forkdef isDataAvailable (cols : Array DataColumnSidecar) : Bool :=
  !cols.isEmpty && cols.all (fun sidecar => verifyDataColumnSidecar sidecar && verifyDataColumnSidecarKzgProofs sidecar)

/-- `on_block`. Rejects (via `assert`) an unknown parent, a future
block, a finality conflict, or unavailable blob data, and propagates a failed
`state_transition` through `runStateTransition`. `columns` are the block's PeerDAS
data-column sidecars (EIP-7594); the runner supplies exactly those the step lists. -/
forkdef onBlock (signedBlock : SignedBeaconBlock) (columns : Array DataColumnSidecar) :
    StoreTransition Unit := do
  let store ← get
  let block := signedBlock.message
  let parentState ← FcMap.getOrAssert store.blockStates block.parentRoot
    "block.parent_root in store.block_states"
  assert (getCurrentSlot store ≥ block.slot)
  let finalizedSlot := computeStartSlotAtEpoch store.finalizedCheckpoint.epoch
  assert (block.slot > finalizedSlot)
  assert (store.finalizedCheckpoint.root == (← getCheckpointBlock store block.parentRoot store.finalizedCheckpoint.epoch))
  -- Data availability (EIP-7594): only blocks carrying blob commitments need their
  -- columns sampled; a block with no blobs is trivially available.
  assert (block.body.blobKzgCommitments.toArray.isEmpty || isDataAvailable columns)

  let postState ← runStateTransition parentState (stateTransition signedBlock)
  let blockRoot := htr block
  -- The head is taken BEFORE the new block is added (v1.7 `update_proposer_boost_root`).
  let head ← getHead store
  let isTimely := getCurrentSlot store == block.slot && timeIntoSlotMs store < bpsDeadlineMs Const.attestationDueBps

  -- Insert the block, its post-state, and the timeliness flag. `set` before the boost
  -- computation: `update_proposer_boost_root`'s dependent-root walks can raise, and so
  -- does `compute_pulled_up_tip`'s pull-up, so each completed write must persist
  -- (in-place runner semantics).
  set { store with
    blocks := FcMap.insert store.blocks blockRoot block
    blockStates := FcMap.insert store.blockStates blockRoot postState
    blockTimeliness := FcMap.insert store.blockTimeliness blockRoot isTimely }
  let store ← get

  -- Boost only a timely first block on the same proposer-shuffling lineage as the
  -- pre-insertion head (v1.7 `is_same_dependent_root`). Root-then-head evaluation
  -- matches the pinned `get_dependent_root(store, root) == get_dependent_root(store, head)`.
  let depRoot ← getDependentRoot store blockRoot
  let depHead ← getDependentRoot store head
  let store := if isTimely && store.proposerBoostRoot == fcZeroRoot && depHead == depRoot then
    { store with proposerBoostRoot := blockRoot } else store
  set store
  let store := updateCheckpoints store (sszGet postState currentJustifiedCheckpoint) (sszGet postState finalizedCheckpoint)
  set store
  set (← computePulledUpTip store blockRoot)

/-! ## on_attestation -/

/-- `store_target_checkpoint_state`: cache the target's state, advancing to the
target epoch start if needed. The pinned `process_slots` is unguarded, so a rejected
advance propagates (wrapped `.transition`) and nothing is cached, aborting
`on_attestation` with the store unchanged. The pre-conversion `runBestEffort` cached
the UNADVANCED base state, a wrong-slot entry later reads would consume. -/
forkdef storeTargetCheckpointState (store : Store map) (target : Checkpoint) :
    StoreTransition (Store map) := do
  if FcMap.contains store.checkpointStates target then pure store
  else
    let base ← FcMap.getOrThrow store.blockStates target.root
    let targetSlot := computeStartSlotAtEpoch target.epoch
    let advanced ←
      if (sszGet base slot) < targetSlot then
        runStateTransition base (processSlots targetSlot)
      else pure base
    pure { store with checkpointStates := FcMap.insert store.checkpointStates target advanced }

/-- `validate_on_attestation`. The epoch-scope check is skipped for a block-implied
attestation (`is_from_block = true`); the rest always apply. -/
forkdef validateOnAttestation (store : Store map) (att : Attestation) (isFromBlock : Bool) : StoreTransition Unit := do
  let target := att.data.target
  let currentEpoch := getCurrentStoreEpoch store
  let previousEpoch := if currentEpoch > Const.genesisEpoch then currentEpoch - 1 else Const.genesisEpoch
  assert (isFromBlock || target.epoch == currentEpoch || target.epoch == previousEpoch)
  assert (target.epoch == computeEpochAtSlot att.data.slot)
  assert (FcMap.contains store.blocks target.root)
  assert (FcMap.contains store.blocks att.data.beaconBlockRoot)
  let b ← FcMap.getOrThrow store.blocks att.data.beaconBlockRoot
  assert (b.slot ≤ att.data.slot)
  assert (target.root == (← getCheckpointBlock store att.data.beaconBlockRoot target.epoch))
  assert (getCurrentSlot store ≥ att.data.slot + 1)

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
  let indexedAttestation : IndexedAttestation := { attestingIndices := sszOfArray attesting, data := att.data, signature := att.signature }
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

/-- `get_forkchoice_store(anchor_state, anchor_block)`
(`consensus-specs/specs/phase0/fork-choice.md:215-216`). The pyspec opens with
`assert anchor_block.state_root == hash_tree_root(anchor_state)`, the anchor's
self-consistency check, so the seed is a throwing `Except StoreTransitionError` action rather
than a total store literal. The reject branch is vectorless (the harness derives the anchor
block and state from one vector, so `state_root` always matches); Heze's `pinAnchorRejects`
locks the identical assert, and this Fulu constructor carries it verbatim. The anchor block's
root is computed from the (state-root-filled) anchor block. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) :
    Except StoreTransitionError (Store map) := do
  -- `anchor_block.state_root == hash_tree_root(anchor_state)`: the boxed state hashes
  -- through `stateRoot` (the cached-tree path), not `htr` (which wants a bare `SSZRepr`).
  assert (anchorBlock.stateRoot == bytesToRoot (stateRoot anchorState).1)
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }
  pure
    { time := (sszGet anchorState genesisTime) + Const.secondsPerSlot * (sszGet anchorState slot)
      genesisTime := sszGet anchorState genesisTime
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

/-! ### Build-enforced pins (vectorless): the Fulu fork-choice throws

These throw conversions' reject branches are unreachable by conformance vectors, so they
are locked here, the same pattern as the Gloas pins. `pinStore` mirrors the
`getForkchoiceStore` literal with every map empty. -/

/-- The pins' concrete fork-choice monad: the minimal preset over `treeMap` + FFI hasher. -/
private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

private def pinRoot : Root := Vector.replicate 32 9

/-- A minimal empty Fulu `Store`. -/
private def pinStore : @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { time := 0, genesisTime := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty }

/-- `getAncestor` rejects (`missingKey`) when the walk root is not in `store.blocks`,
the pinned plain-`Dict` read; the pre-conversion `fuelIterate` returned the root as a
silent `.done`. `FcMap`/hash-free, so kernel `#guard`. -/
private def pinGetAncestorThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match (getAncestor (map := treeMap) pinStore pinRoot 0 : PinM Root).run pinStore with
  | .error (.missingKey _) _ => true
  | _ => false
#guard pinGetAncestorThrows = true

/-- `getHead` rejects end-to-end when the justified-checkpoint root is unknown: the
`filter_block_tree` opening read misses. Locks the whole `getHead` monadic path.
`State`-free here (no checkpoint state read reached before the block miss), so `FcMap`
kernel `#guard`. -/
private def pinGetHeadThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let store := { pinStore with justifiedCheckpoint := { epoch := 0, root := pinRoot } }
  match (getHead (map := treeMap) store : PinM Root).run store with
  | .error (.missingKey _) _ => true
  | _ => false
#guard pinGetHeadThrows = true

/-- `storeTargetCheckpointState` propagates a `process_slots` reject. The fixture
state is `default` (zero validators, slot 0) carrying one queued `PendingConsolidation`:
advancing to epoch 1 reaches `process_pending_consolidations`, whose plain-list read
rejects (`outOfBounds`), and the unguarded pinned `process_slots` means the helper
re-throws it (`.transition`) with nothing cached. The consolidation carrier is
deliberate. A bare zero-validator advance grinds `cbwsAux`'s 10M fuel instead of
rejecting. `State` is FFI-backed, so `native_decide`. -/
private def pinTargetAdvanceRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let bs : @EthCLSpecs.Fulu.BeaconState minimal :=
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
      pendingConsolidations := sszOfArray #[{ sourceIndex := 0, targetIndex := 0 }] }
  let state : State := SSZ.FastBox bs
  let store := { pinStore with blockStates := FcMap.insert FcMap.empty pinRoot state }
  let target : Checkpoint := { epoch := 1, root := pinRoot }
  match (storeTargetCheckpointState (map := treeMap) store target : PinM (Store treeMap)).run store with
  | .error (.transition _) _ => true
  | _ => false
example : pinTargetAdvanceRejects = true := by native_decide

/-- `balanceAfterWithdrawals` rejects (`outOfBounds`) on an out-of-range validator
index: the pinned bare `state.balances[vi]` list read. A `default` state has zero
validators, so index 99 misses, where the pre-conversion `def` clamped
(`balances[vi]!` defaulting, `0` on underflow). `State` is FFI-backed, so
`native_decide`. -/
private def pinBalanceAfterWithdrawalsThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Fulu.BeaconState minimal)
  match (balanceAfterWithdrawals state 99 #[] : EStateM StateTransitionError State Gwei).run state with
  | .error (.outOfBounds _ _) _ => true
  | _ => false
example : pinBalanceAfterWithdrawalsThrows = true := by native_decide

/-- `balanceAfterWithdrawals` rejects (`.arithmetic`) a `uint64` underflow: a validator whose
queued withdrawals exceed its balance drives `balances[vi] - withdrawn` negative
(`capella/beacon-chain.md:378`), which pyspec raises as `ValueError`, uncaught by the reference
runner (`context.py:429-433`), so the Lean throws the uncaught `.arithmetic` reject rather than a
caught `.assert`. Fixture: balance 5 at index 0, a queued withdrawal of 10. `State` is FFI-backed,
so `native_decide`. -/
private def pinBalanceUnderflowThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let bs : @EthCLSpecs.Fulu.BeaconState minimal :=
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with balances := sszOfArray #[(5 : Gwei)] }
  let state : State := SSZ.FastBox bs
  let w : Withdrawal := { (default : Withdrawal) with validatorIndex := 0, amount := 10 }
  match (balanceAfterWithdrawals state 0 #[w] : EStateM StateTransitionError State Gwei).run state with
  | .error (.arithmetic _) _ => true
  | _ => false
example : pinBalanceUnderflowThrows = true := by native_decide
end EthCLSpecs.Fulu
