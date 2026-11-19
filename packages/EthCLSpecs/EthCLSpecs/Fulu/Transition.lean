import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Fulu.Withdrawals
import EthCLSpecs.Fulu.EpochProcessing

/-!
# `EthCLSpecs.Fulu.Transition`: the state-transition spine

The top of the Fulu state transition: `process_slot` / `process_slots` (with
`process_epoch` at epoch boundaries), the block-level steps that do not belong to
a dedicated module (`process_block_header`, `process_randao`, `process_eth1_data`,
`process_sync_aggregate`, `process_execution_payload`), and the `process_block` /
`state_transition` wiring. The heavy sub-pipelines live in `EpochProcessing`,
`Operations`, and `Withdrawals`.

`state_transition` is monad-generic (`StateTransition Unit`): the runner discharges
it at the fast `EStateM` config, a future proof at the pure config. A reject is a
`throw`; the discharger decides the fate of the discarded post-state.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- The all-zero `Root` (an empty `state_root` sentinel in `latest_block_header`). -/
forkdef zeroRoot : Root := Vector.replicate 32 0

/-! ### Slot processing -/

/-- `process_slot` (`fulu/mainnet.py:1696-1706`): cache the state root, fill the latest
header's empty state root, then cache the block root, all at
`slot % SLOTS_PER_HISTORICAL_ROOT`. The ring index is the checked slot reduced by the
proved-total divisor view (`SPEC_ARITHMETIC.md` §4.2); `toPlainNat` names the structural
vector index the result narrows to (`SPEC_ARITHMETIC.md` §4.5). -/
forkdef processSlot : StateTransition Unit :=
  modifyState fun state => Id.run do
    let (prevStateRootBytes, state) := stateRoot state
    let mut state := state
    let prevStateRoot : Root := bytesToRoot prevStateRootBytes
    let idx := ((sszGet state slot) % Const.slotsPerHistoricalRootDiv).toPlainNat
    state := sszUpdate state with stateRoots[idx]! := prevStateRoot

    -- Fill the latest header's empty state root with the one just cached.
    let latestHeader := sszGet state latestBlockHeader
    let latestHeader := if latestHeader.stateRoot == zeroRoot then { latestHeader with stateRoot := prevStateRoot } else latestHeader
    state := sszUpdate state with latestBlockHeader := latestHeader

    let blockRoot := htr (sszGet state latestBlockHeader)
    state := sszUpdate state with blockRoots[idx]! := blockRoot
    return state

/-- `process_epoch` (Fulu ordering). -/
forkdef processEpoch : StateTransition Unit := do
  processJustificationAndFinalization
  processInactivityUpdates
  processRewardsAndPenalties
  processRegistryUpdates
  processSlashings
  processEth1DataReset
  processPendingDeposits
  processPendingConsolidations
  processEffectiveBalanceUpdates
  processSlashingsReset
  processRandaoMixesReset
  processHistoricalSummariesUpdate
  processParticipationFlagUpdates
  processSyncCommitteeUpdates
  processProposerLookahead

/-- `process_slots` (`fulu/mainnet.py:1686-1693`): advance to `slot`, running `process_slot`
(and `process_epoch` at each epoch boundary) for every intervening slot. The loop fuel is
the spec's `while` distance, the checked difference bound once and narrowed with
`toPlainNat` (`SPEC_ARITHMETIC.md` §4.5; the assert above puts it above zero, so the
subtraction cannot fault). `(state.slot + 1) % SLOTS_PER_EPOCH` binds the checked add where
Python forms it, then the modulo takes the proved-total divisor view; the store's
`state.slot = state.slot + 1` re-forms the sum as Python does. -/
forkdef processSlots (target : Slot) : StateTransition Unit := do
  assert ((sszGet (← get) slot) < target)
  let diff ← target - (sszGet (← get) slot)
  for _ in [0:diff.toPlainNat] do
    processSlot
    let next ← (sszGet (← get) slot) + 1
    let atBoundary : Slot := next % Const.slotsPerEpochDiv
    if atBoundary == 0 then processEpoch
    let nextSlot ← (sszGet (← get) slot) + 1
    modifyState fun state => sszUpdate state with slot := nextSlot

/-! ### Block-level steps -/

/-- `process_block_header`. -/
forkdef processBlockHeader (block : BeaconBlock) : StateTransition Unit := do
  let state ← get
  assert (block.slot == sszGet state slot)
  assert (block.slot > (sszGet state latestBlockHeader).slot)
  assert (block.proposerIndex == getBeaconProposerIndex state)
  assert (block.parentRoot == htr (sszGet state latestBlockHeader))

  let newHeader : BeaconBlockHeader :=
    { slot := block.slot, proposerIndex := block.proposerIndex, parentRoot := block.parentRoot,
      stateRoot := zeroRoot, bodyRoot := htr block.body }
  -- `proposer = state.validators[block.proposer_index]` (`fulu/minimal.py`,
  -- `process_block_header`): a raising list read, so an out-of-range proposer rejects
  -- with `IndexError`'s class.
  let proposer ← sszGetIdx (sszGet state validators) block.proposerIndex
  assert (!proposer.slashed)

  modifyState fun state => sszUpdate state with latestBlockHeader := newHeader

/-- `process_randao`: verify the proposer's RANDAO reveal and mix it into the
current epoch's mix. -/
forkdef processRandao (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let epoch := currentEpochOf state
  let proposer ← sszGetIdx (sszGet state validators) (getBeaconProposerIndex state)
  let signingRoot := computeSigningRoot epoch (getDomain state Const.domainRandao epoch)
  assert (blsVerify proposer.pubkey signingRoot body.randaoReveal)

  -- Mix the reveal's hash into the current epoch's mix, then write it back. The mix slot
  -- is `epoch % EPOCHS_PER_HISTORICAL_VECTOR`: the read rides the checked value's word
  -- through the proved-total `vmodGet` route, whose bound is the mod itself
  -- (`SPEC_ARITHMETIC.md` §4.5).
  let mix := vmodGet (sszGet state randaoMixes) epoch.val Const.epochsPerHistoricalVector
  let digest := sha body.randaoReveal
  let newMix : Bytes32 := Vector.ofFn (fun i : Fin 32 => mix[i] ^^^ digest.get! i.val)
  -- The write slot `epoch % EPOCHS_PER_HISTORICAL_VECTOR` is the checked `Epoch` modulo,
  -- formed after the value, as Python evaluates an assignment's right side first. The
  -- remainder is below the vector length, so `toPlainNat` names an in-range position (§4.5).
  let idx ← epoch % Const.epochsPerHistoricalVectorC
  modifyState fun state =>
    sszUpdate state with randaoMixes[idx.toPlainNat]! := newMix

/-- `process_eth1_data` (`fulu/minimal.py:1972-1978`): append the vote and adopt it once it
has a majority over the voting period. `eth1_data_votes.count(...) * 2` is a plain `int`
formula, a `CLInt`. `Uint64(EPOCHS_PER_ETH1_VOTING_PERIOD) * SLOTS_PER_EPOCH` is the checked
product, formed after the plain side as Python evaluates it, so it raises past `2^64 - 1`
for a generic preset. The comparison never raises; `int(x)` carries the product into the
plain kind. -/
forkdef processEth1Data (body : BeaconBlockBody) : StateTransition Unit := do
  appendState eth1DataVotes body.eth1Data

  let state ← get
  let target := htr body.eth1Data
  let voteCount : CLInt := (sszGet state eth1DataVotes).foldl
    (fun acc e => if htr e == target then acc + 1 else acc) 0
  let doubled := voteCount * 2
  let periodSlots ← Const.epochsPerEth1VotingPeriodC * Const.slotsPerEpochC
  if doubled > periodSlots.toCLInt then
    modifyState fun state => sszUpdate state with eth1Data := body.eth1Data

/-- `process_sync_aggregate`: verify the aggregate signature over the previous
slot's block root, then apply participant / proposer rewards and non-participant
penalties. The participant pubkey list is the bit-selected committee keys, and
`eth_fast_aggregate_verify` aggregates them. The spec's all-participate and
majority-subtraction branches start from the cached `aggregate_pubkey` instead, so the
answers agree whenever that aggregate is the sum of the committee's `pubkeys`, as
`get_next_sync_committee` builds it. The crypto seam has no point addition or negation to
model those branches; `IMPLEMENTATION_NOTES.md` records the divergence. -/
forkdef processSyncAggregate (agg : SyncAggregate) : StateTransition Unit := do
  let state ← get

  -- Verify the aggregate over the previous slot's block root from the bit-selected keys.
  let syncCommittee := sszGet state currentSyncCommittee
  let bits := agg.syncCommitteeBits
  let participantKeys : Array BLSPubkey :=
    (Bitvector.trueIndices bits).map (fun i => syncCommittee.pubkeys[i]!)
  let previousSlot := (sszGet state slot).saturatingSub 1
  let previousBlockRoot ← getBlockRootAtSlot state previousSlot
  let signingRoot := computeSigningRoot previousBlockRoot
    (getDomain state Const.domainSyncCommittee (computeEpochAtSlot previousSlot))
  assert (blsEthFastAggregateVerify participantKeys signingRoot agg.syncCommitteeSignature)

  -- Per-participant and per-proposer reward amounts (`fulu/mainnet.py`,
  -- `process_sync_aggregate`). The chain is the checked `Gwei` surface:
  -- the increment division, the base-reward product, the reward-quotient chain,
  -- and the per-participant split each bind where the pyspec forms it. The
  -- `slotsPerEpoch` divisor is the proved-total `PositiveDivisor` view, since the
  -- preset value is positive (`SPEC_ARITHMETIC.md` §4.2).
  let totalActiveBalance ← liftErr (getTotalActiveBalance state)
  let totalActiveIncrements ← totalActiveBalance / Const.effectiveBalanceIncrementG
  let basePerIncrement ← liftErr (getBaseRewardPerIncrement state)
  let totalBaseRewards ← basePerIncrement * totalActiveIncrements
  let maxParticipantRewards ← totalBaseRewards * Const.syncRewardWeight / Const.weightDenominator
  let maxParticipantRewards := maxParticipantRewards / Const.slotsPerEpochDiv
  let participantReward ← maxParticipantRewards / Const.syncCommitteeSize
  let proposerReward ← participantReward * Const.proposerWeight / (Const.weightDenominator - Const.proposerWeight)
  let proposerIdx := getBeaconProposerIndex state
  let validators := (sszGet state validators).toArray

  -- Reward participants (and the proposer), penalize non-participants.
  let mut state := state
  for h : i in [0:Const.syncCommitteeSize] do
    let pk := syncCommittee.pubkeys[i]
    match validators.findIdx? (·.pubkey == pk) with
    | some pIdx =>
      -- `ValidatorIndex(all_pubkeys.index(pubkey))`: the pyspec's checked cast.
      let participantIndex ← CLUint64.ofNat? pIdx
      if bitGet bits i then
        state ← increaseBalance state participantIndex participantReward
        state ← increaseBalance state proposerIdx proposerReward
      else
        state ← decreaseBalance state participantIndex participantReward
    | none => pure ()
  set state

/-- `process_execution_payload` (Fulu, `fulu/beacon-chain.md`, "Modified
`process_execution_payload`"): the consistency checks against the previous header and the
current RANDAO / slot time, the EIP-7892 bound on the blob commitments
(`get_blob_parameters(current_epoch).max_blobs_per_block`), then cache the new header. The
execution-engine `verify_and_notify_new_payload` is the consumer's responsibility: the
operations runner asserts the vector's `execution_valid` answer, and the block runners take
it as valid. -/
forkdef processExecutionPayload (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let payload := body.executionPayload
  assert (payload.parentHash == (sszGet state latestExecutionPayloadHeader).blockHash)
  let epoch := currentEpochOf state
  let mix := vmodGet (sszGet state randaoMixes) epoch.val Const.epochsPerHistoricalVector
  assert (payload.prevRandao == mix)
  -- `compute_time_at_slot(state.genesis_time, state.slot)` (`Fulu/Time.lean`). It can fault, so
  -- it binds through the arithmetic lift, which lands the fault on this machine unwrapped.
  let expectedTimestamp ← computeTimeAtSlot (sszGet state genesisTime) (sszGet state slot)
  -- TEMPORARY CROSSING (removed in Stage 7.1b): `payload.timestamp` is still the raw `UInt64`
  -- field, so the checked time compares through its native word. The pinned `Uint64.__eq__`
  -- compares by value, so the answer is the same.
  assert (payload.timestamp == expectedTimestamp.val)
  -- [Modified in Fulu:EIP7892] the commitments are under the scheduled blob limit: the plain
  -- `len(...)` against the plain limit, a comparison that never raises.
  assert (len body.blobKzgCommitments ≤ (getBlobParameters epoch).maxBlobsPerBlock)

  let header : ExecutionPayloadHeader :=
    { parentHash := payload.parentHash, feeRecipient := payload.feeRecipient,
      stateRoot := payload.stateRoot, receiptsRoot := payload.receiptsRoot,
      logsBloom := payload.logsBloom, prevRandao := payload.prevRandao,
      blockNumber := payload.blockNumber, gasLimit := payload.gasLimit,
      gasUsed := payload.gasUsed, timestamp := payload.timestamp, extraData := payload.extraData,
      baseFeePerGas := payload.baseFeePerGas, blockHash := payload.blockHash,
      transactionsRoot := htr payload.transactions, withdrawalsRoot := htr payload.withdrawals,
      blobGasUsed := payload.blobGasUsed, excessBlobGas := payload.excessBlobGas }
  modifyState fun state => sszUpdate state with latestExecutionPayloadHeader := header

/-! ### Block + transition -/

/-- `process_block` (Fulu ordering). -/
forkdef processBlock (block : BeaconBlock) : StateTransition Unit := do
  processBlockHeader block
  processWithdrawals block.body.executionPayload
  processExecutionPayload block.body
  processRandao block.body
  processEth1Data block.body
  processOperations block.body
  processSyncAggregate block.body.syncAggregate

/-- `verify_block_signature`. -/
forkdef verifyBlockSignature (state : State) (signedBlock : SignedBeaconBlock) : Bool :=
  let block := signedBlock.message
  -- The pyspec's `state.validators[block.proposer_index]` raises `IndexError` for an
  -- out-of-range proposer. This body returns `false` on the `getAt` miss, and the caller's
  -- `assert` raises the assert class; the runner catches both.
  match getAt (sszGet state validators) block.proposerIndex with
  | .error _ => false
  | .ok proposer =>
    let signingRoot := computeSigningRoot block (getDomain state Const.domainBeaconProposer (currentEpochOf state))
    blsVerify proposer.pubkey signingRoot signedBlock.signature

/-- `state_transition`: advance to the block's slot, verify the block signature,
apply the block, and check the claimed post-state root, all under `validateResult`. -/
forkdef stateTransition (signedBlock : SignedBeaconBlock) (validateResult : Bool := true) :
    StateTransition Unit := do
  let block := signedBlock.message
  processSlots block.slot
  if validateResult then assert (verifyBlockSignature (← get) signedBlock)
  processBlock block
  if validateResult then
    let root ← getStateRoot
    assert (block.stateRoot == bytesToRoot root)

end

end EthCLSpecs.Fulu
