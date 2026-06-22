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
Fuel-bounded by the block count (the DAG is finite and acyclic). -/
forkdef getAncestor (store : Store map) (root : Root) (slot : Slot) : Root :=
  fuelIterate ((FcMap.keys store.blocks).length + 1) root fun r =>
    match FcMap.lookup store.blocks r with
    | some block => if block.slot > slot then .next block.parentRoot else .done r
    | none       => .done r

/-- `get_checkpoint_block`. -/
forkdef getCheckpointBlock (store : Store map) (root : Root) (epoch : Epoch) : Root :=
  getAncestor store root (computeStartSlotAtEpoch epoch)

/-! ## Weights and head -/

/-- The per-slot committee weight: total active balance divided across the slots of an epoch
(`get_total_active_balance // SLOTS_PER_EPOCH`). The shared core of `getProposerScore` and
`calculateCommitteeFraction`. `UInt64` truncating division, so the floor is taken here once and
both callers inherit the same rounding. -/
forkdef committeeWeight (state : State) : Gwei :=
  getTotalActiveBalance state / UInt64.ofNat Const.slotsPerEpoch

/-- `get_proposer_score`. -/
forkdef getProposerScore (store : Store map) : Gwei :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint with
  | none => 0
  | some state =>
    committeeWeight state * UInt64.ofNat Const.proposerScoreBoost / 100

/-- `get_weight(store, root)`: attestation balance for `root`, plus the proposer
boost if `root` is an ancestor of the boosted block. -/
forkdef getWeight (store : Store map) (root : Root) : Gwei :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint,
        FcMap.lookup store.blocks root with
  | some state, some block =>
    let active := getActiveValidatorIndices state (currentEpochOf state)
    let validators := sszGet state validators
    let attestationScore : Gwei := active.foldl (init := 0) fun acc i =>
      let idx := i.toNat
      if (validators[idx]!).slashed then acc
      else match FcMap.lookup store.latestMessages i with
        | some lm =>
          if store.equivocatingIndices.contains i then acc
          else if getAncestor store lm.root block.slot == root then acc + (validators[idx]!).effectiveBalance
          else acc
        | none => acc

    -- Add the proposer boost when `root` is an ancestor of the boosted block.
    if store.proposerBoostRoot == fcZeroRoot then attestationScore
    else if getAncestor store store.proposerBoostRoot block.slot == root then
      attestationScore + getProposerScore store
    else attestationScore
  | _, _ => 0

/-- `filter_block_tree`: collect the viable branches into `acc` (a key set),
returning whether `blockRoot` is viable. The recursion is fuel-bounded by the block
count (the block DAG is finite and acyclic, so the depth cannot exceed it), keeping
the function total, no `partial def`, per the framework's termination discipline. -/
forkdef filterBlockTree (store : Store map) (blockRoot : Root) (acc : Array Root) :
    Array Root × Bool :=
  go ((FcMap.keys store.blocks).length + 1) blockRoot acc
where
  /-- `get_voting_source(store, block_root)`. -/
  getVotingSource (store : Store map) (blockRoot : Root) : Checkpoint :=
    match FcMap.lookup store.blocks blockRoot with
    | none => store.justifiedCheckpoint
    | some block =>
      let currentEpoch := getCurrentStoreEpoch store
      if currentEpoch > computeEpochAtSlot block.slot then
        FcMap.lookupD store.unrealizedJustifications blockRoot
      else match FcMap.lookup store.blockStates blockRoot with
        | some hs => sszGet hs currentJustifiedCheckpoint
        | none    => store.justifiedCheckpoint
  /-- The viability walk; `fuel` bounds the parent-to-child descent. -/
  go : Nat → Root → Array Root → Array Root × Bool
  | 0,        _,         acc => (acc, false)
  | fuel + 1, blockRoot, acc =>
    let children := FcMap.filterKeys store.blocks (fun _ b => b.parentRoot == blockRoot)
    if children.isEmpty then
      let currentEpoch := getCurrentStoreEpoch store
      let votingSource := getVotingSource store blockRoot
      let correctJustified :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
          || votingSource.epoch + 2 ≥ currentEpoch
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

/-- `get_head`: the filtered-block-tree LMD-GHOST walk, ties broken by the
lexicographically-greater root. Fuel-bounded by the block count. -/
forkdef getHead (store : Store map) : Root :=
  let (viable, _) := filterBlockTree store store.justifiedCheckpoint.root #[]
  fuelIterate ((FcMap.keys store.blocks).length + 1) store.justifiedCheckpoint.root fun head =>
    let children := viable.filter fun r =>
      match FcMap.lookup store.blocks r with
      | some b => b.parentRoot == head
      | none   => false
    if children.isEmpty then .done head
    else .next (children.foldl (init := children[0]!) (betterOf store))
where
  /-- The better of two candidate heads under the `(weight, root)` ordering: greater
  weight wins, ties broken by the greater root. -/
  betterOf (store : Store map) (a b : Root) : Root :=
    let weightA := getWeight store a
    let weightB := getWeight store b
    if weightA > weightB then a
    else if weightB > weightA then b
    else if compare a b == Ordering.gt then a else b

/-! ## Proposer-head reorg logic (`get_proposer_head`) -/

/-- `calculate_committee_fraction`: a percentage of the per-slot committee weight. -/
forkdef calculateCommitteeFraction (state : State) (committeePercent : UInt64) : Gwei :=
  committeeWeight state * committeePercent / 100

/-- `is_head_late`: the head block did not arrive before the attestation deadline. -/
forkdef isHeadLate (store : Store map) (headRoot : Root) : Bool := !(FcMap.lookupD store.blockTimeliness headRoot)

/-- `is_shuffling_stable`: not on an epoch boundary (where the shuffling could flip). -/
forkdef isShufflingStable (slot : Slot) : Bool := slot % UInt64.ofNat Const.slotsPerEpoch != 0

/-- `is_ffg_competitive`: head and parent carry the same unrealized justification. -/
forkdef isFfgCompetitive (store : Store map) (headRoot parentRoot : Root) : Bool :=
  FcMap.lookup store.unrealizedJustifications headRoot == FcMap.lookup store.unrealizedJustifications parentRoot

/-- `is_finalization_ok`: the chain is finalizing within `REORG_MAX_EPOCHS_SINCE_FINALIZATION`. -/
forkdef isFinalizationOk (store : Store map) (slot : Slot) : Bool :=
  computeEpochAtSlot slot - store.finalizedCheckpoint.epoch ≤ Const.reorgMaxEpochsSinceFinalization

/-- `is_proposing_on_time`: within the reorg cutoff of the slot start (ms timing; the
store clock is seconds, converted via `* 1000`). -/
forkdef isProposingOnTime (store : Store map) : Bool :=
  timeIntoSlotMs store ≤ bpsDeadlineMs Const.proposerReorgCutoffBps

/-- `is_head_weak`: the head's weight is below the reorg-head threshold. -/
forkdef isHeadWeak (store : Store map) (headRoot : Root) : Bool :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint with
  | some js => getWeight store headRoot < calculateCommitteeFraction js Const.reorgHeadWeightThreshold
  | none    => false

/-- `is_parent_strong`: the head's parent weight exceeds the reorg-parent threshold. -/
forkdef isParentStrong (store : Store map) (root : Root) : Bool :=
  match FcMap.lookup store.checkpointStates store.justifiedCheckpoint, FcMap.lookup store.blocks root with
  | some js, some b => getWeight store b.parentRoot > calculateCommitteeFraction js Const.reorgParentWeightThreshold
  | _, _            => false

/-- `is_proposer_equivocation`: more than one block from the head's proposer at its slot. -/
forkdef isProposerEquivocation (store : Store map) (root : Root) : Bool :=
  match FcMap.lookup store.blocks root with
  | none       => false
  | some block =>
    ((FcMap.values store.blocks).filter
      (fun b => b.proposerIndex == block.proposerIndex && b.slot == block.slot)).length > 1

/-- `get_proposer_head`: whether a proposer at `slot` should reorg the current head
(`head_root`) by building on its parent. Reorg the head when it is late, weak, on a
stable shuffling, FFG-competitive, finalizing, proposed on time, exactly one slot
back, and its parent is strong; or, more aggressively, when the head is weak and the
previous slot had a proposer equivocation. Otherwise keep the head. -/
forkdef getProposerHead (store : Store map) (headRoot : Root) (slot : Slot) : Root :=
  match FcMap.lookup store.blocks headRoot with
  | none => headRoot
  | some headBlock =>
    let parentRoot := headBlock.parentRoot
    match FcMap.lookup store.blocks parentRoot with
    | none => headRoot
    | some parentBlock =>
      let currentTimeOk := headBlock.slot + 1 == slot
      let singleSlotReorg := parentBlock.slot + 1 == headBlock.slot && currentTimeOk
      let headWeak := isHeadWeak store headRoot
      -- The spec asserts `proposer_boost_root != head_root` (boost has worn off);
      -- model defensively as keeping the head rather than a panic.
      if store.proposerBoostRoot == headRoot then headRoot
      else if isHeadLate store headRoot && isShufflingStable slot && isFfgCompetitive store headRoot parentRoot
          && isFinalizationOk store slot && isProposingOnTime store && singleSlotReorg
          && headWeak && isParentStrong store headRoot then parentRoot
      else if headWeak && currentTimeOk && isProposerEquivocation store headRoot then parentRoot
      else headRoot

/-! ## Checkpoint updates -/

forkdef updateCheckpoints (store : Store map) (j f : Checkpoint) : Store map :=
  let store := if j.epoch > store.justifiedCheckpoint.epoch then { store with justifiedCheckpoint := j } else store
  if f.epoch > store.finalizedCheckpoint.epoch then { store with finalizedCheckpoint := f } else store

forkdef updateUnrealizedCheckpoints (store : Store map) (uj uf : Checkpoint) : Store map :=
  let store := if uj.epoch > store.unrealizedJustifiedCheckpoint.epoch then { store with unrealizedJustifiedCheckpoint := uj } else store
  if uf.epoch > store.unrealizedFinalizedCheckpoint.epoch then { store with unrealizedFinalizedCheckpoint := uf } else store

/-- `compute_pulled_up_tip`: pull up the block's post-state through
`process_justification_and_finalization`, record the unrealized justification, and
(for a prior-epoch block) realize it. The pull-up is best-effort (an inner failure
leaves the store unchanged), so it stays an `EStateM.run`, not `runStateTransition`. -/
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
proposer shuffling. Used by the proposer-boost gate so a block on a different
shuffling lineage than the current head is not boosted. -/
forkdef getDependentRoot (store : Store map) (root : Root) : Root :=
  let epoch := getCurrentStoreEpoch store
  if epoch ≤ Const.minSeedLookahead then fcZeroRoot
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

/-- `on_block`. Rejects (via `assert` / `missingKey`) an unknown parent, a future
block, a finality conflict, or unavailable blob data, and propagates a failed
`state_transition` through `runStateTransition`. `columns` are the block's PeerDAS
data-column sidecars (EIP-7594); the runner supplies exactly those the step lists. -/
forkdef onBlock (signedBlock : SignedBeaconBlock) (columns : Array DataColumnSidecar) :
    StoreTransition Unit := do
  let store ← get
  let block := signedBlock.message
  let parentState ← FcMap.getOrThrow store.blockStates block.parentRoot
  assert (getCurrentSlot store ≥ block.slot)
  let finalizedSlot := computeStartSlotAtEpoch store.finalizedCheckpoint.epoch
  assert (block.slot > finalizedSlot)
  assert (store.finalizedCheckpoint.root == getCheckpointBlock store block.parentRoot store.finalizedCheckpoint.epoch)
  -- Data availability (EIP-7594): only blocks carrying blob commitments need their
  -- columns sampled; a block with no blobs is trivially available.
  assert (block.body.blobKzgCommitments.toArray.isEmpty || isDataAvailable columns)

  let postState ← runStateTransition parentState (stateTransition signedBlock)
  let blockRoot := htr block
  -- The head is taken BEFORE the new block is added (v1.7 `update_proposer_boost_root`).
  let head := getHead store
  let isTimely := getCurrentSlot store == block.slot && timeIntoSlotMs store < bpsDeadlineMs Const.attestationDueBps

  let store := { store with
    blocks := FcMap.insert store.blocks blockRoot block
    blockStates := FcMap.insert store.blockStates blockRoot postState
    blockTimeliness := FcMap.insert store.blockTimeliness blockRoot isTimely }

  -- Boost only a timely first block on the same proposer-shuffling lineage as the
  -- pre-insertion head (v1.7 adds the `is_same_dependent_root` gate).
  let isSameDependentRoot := getDependentRoot store blockRoot == getDependentRoot store head
  let store := if isTimely && store.proposerBoostRoot == fcZeroRoot && isSameDependentRoot then
    { store with proposerBoostRoot := blockRoot } else store
  let store := updateCheckpoints store (sszGet postState currentJustifiedCheckpoint) (sszGet postState finalizedCheckpoint)
  set (computePulledUpTip store blockRoot)

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
  assert (target.root == getCheckpointBlock store att.data.beaconBlockRoot target.epoch)
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

  let store := storeTargetCheckpointState (← get) att.data.target
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

/-- `get_forkchoice_store(anchor_state, anchor_block)`. The anchor block's root is
computed from the (state-root-filled) anchor block. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) : Store map :=
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }
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

end EthCLSpecs.Fulu
