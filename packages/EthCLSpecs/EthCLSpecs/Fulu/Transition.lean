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

/-- `process_slot`: cache the state root, fill the latest header's empty state root,
then cache the block root, all at `slot % SLOTS_PER_HISTORICAL_ROOT`. -/
forkdef processSlot : StateTransition Unit :=
  modifyState fun state => Id.run do
    let (prevStateRootBytes, state) := stateRoot state
    let mut state := state
    let prevStateRoot : Root := bytesToRoot prevStateRootBytes
    let idx := umodIdx (sszGet state slot) Const.slotsPerHistoricalRoot
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

/-- `process_slots`: advance to `slot`, running `process_slot` (and `process_epoch`
at each epoch boundary) for every intervening slot. -/
forkdef processSlots (target : Slot) : StateTransition Unit := do
  assert ((sszGet (← get) slot) < target)
  for _ in [0:(target - (sszGet (← get) slot)).toNat] do
    processSlot
    if ((sszGet (← get) slot) + 1) % UInt64.ofNat Const.slotsPerEpoch == 0 then processEpoch
    modifyState fun state => sszUpdate state with slot := (sszGet state slot) + 1

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
  -- `state.validators[block.proposer_index]` raises `IndexError` past the registry.
  let proposer ← sszGetIdx (sszGet state validators) block.proposerIndex.toNat
  assert (!proposer.slashed)

  modifyState fun state => sszUpdate state with latestBlockHeader := newHeader

/-- `process_randao`: verify the proposer's RANDAO reveal and mix it into the
current epoch's mix. -/
forkdef processRandao (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let epoch := currentEpochOf state
  let proposer ← sszGetIdx (sszGet state validators) (getBeaconProposerIndex state).toNat
  let signingRoot := computeSigningRoot epoch (getDomain state Const.domainRandao epoch)
  assert (blsVerify proposer.pubkey signingRoot body.randaoReveal)

  -- Mix the reveal's hash into the current epoch's mix, then write it back.
  let mix := vmodGet (sszGet state randaoMixes) epoch Const.epochsPerHistoricalVector
  let digest := sha body.randaoReveal
  let newMix : Bytes32 := Vector.ofFn (fun i : Fin 32 => mix[i] ^^^ digest.get! i.val)
  modifyState fun state =>
    sszUpdate state with randaoMixes[umodIdx epoch Const.epochsPerHistoricalVector]! := newMix

/-- `process_eth1_data`: append the vote and adopt it once it has a majority over
the voting period. pyspec evaluates `votes.count(...) * 2`, then
`EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH`. `count` returns a Python `int`, so
`count * 2` is exact, and the body keeps it in `Nat`. The period product multiplies two
`uint64` constants, so it is a checked product (`.arithmetic`). -/
forkdef processEth1Data (body : BeaconBlockBody) : StateTransition Unit := do
  appendState eth1DataVotes body.eth1Data

  let state ← get
  let target := htr body.eth1Data
  let cnt := (sszGet state eth1DataVotes).foldl
    (fun acc e => if htr e == target then acc + 1 else acc) 0
  let votingSlots ← checkedMul (UInt64.ofNat Const.epochsPerEth1VotingPeriod)
    (UInt64.ofNat Const.slotsPerEpoch)
    "process_eth1_data: EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH"
  if cnt * 2 > votingSlots.toNat then
    modifyState fun state => sszUpdate state with eth1Data := body.eth1Data

/-- `process_sync_aggregate`: verify the aggregate signature over the previous
slot's block root, then apply participant / proposer rewards and non-participant
penalties.

The verify gets the keys the spec chooses by the number of set bits:

- All bits set: the stored `aggregate_pubkey`, unchanged. The body does not compare it with
  the committee keys.
- More than half set: the G1 difference of the stored aggregate and the aggregate of the
  non-participant keys. `ValueError` (`.arithmetic`) when the stored aggregate or a
  non-participant key does not decode as a G1 point, or when a non-participant key fails
  `KeyValidate`.
- Half set or fewer: the participant keys.

The pyspec chooses the keys before it reads the block root. So a key fault raises before a
fault in `get_block_root_at_slot`.

Before any reward, the pyspec finds the registry position of every committee key
(`all_pubkeys.index`). A key that is not in the registry raises `ValueError`
(`.arithmetic`). -/
forkdef processSyncAggregate (agg : SyncAggregate) : StateTransition Unit := do
  let state ← get

  -- Choose the verification keys by the number of set bits.
  let syncCommittee := sszGet state currentSyncCommittee
  let bits := agg.syncCommitteeBits
  let participantCount := (Bitvector.trueIndices bits).size
  let participantKeys : Array BLSPubkey ←
    if participantCount == Const.syncCommitteeSize then
      pure #[syncCommittee.aggregatePubkey]
    else if participantCount > Const.syncCommitteeSize / 2 then do
      let nonParticipantKeys : Array BLSPubkey :=
        ((Array.range Const.syncCommitteeSize).filter (fun i => !bitGet bits i)).map
          (fun i => syncCommittee.pubkeys[i]!)
      let nonParticipantAggregate ← liftErr (blsAggregatePubkeysChecked nonParticipantKeys)
      let negated ← liftErr (blsG1Neg nonParticipantAggregate)
      pure #[← liftErr (blsG1Add syncCommittee.aggregatePubkey negated)]
    else
      pure ((Bitvector.trueIndices bits).map (fun i => syncCommittee.pubkeys[i]!))

  -- Verify the signature over the previous slot's block root.
  let previousSlot := (umax (sszGet state slot) 1) - 1
  let previousBlockRoot ← getBlockRootAtSlot state previousSlot
  let signingRoot := computeSigningRoot previousBlockRoot
    (getDomain state Const.domainSyncCommittee (computeEpochAtSlot previousSlot))
  assert (blsEthFastAggregateVerify participantKeys signingRoot agg.syncCommitteeSignature)

  -- Per-participant and per-proposer reward amounts.
  let totalActiveIncrements := (← liftErr (getTotalActiveBalance state)).toNat / Const.effectiveBalanceIncrement
  let totalBaseRewards := (← liftErr (getBaseRewardPerIncrement state)).toNat * totalActiveIncrements
  let maxParticipantRewards := totalBaseRewards * Const.syncRewardWeight / Const.weightDenominator / Const.slotsPerEpoch
  let participantReward : Gwei := UInt64.ofNat (maxParticipantRewards / Const.syncCommitteeSize)
  let proposerReward : Gwei :=
    UInt64.ofNat (participantReward.toNat * Const.proposerWeight / (Const.weightDenominator - Const.proposerWeight))
  let proposerIdx := getBeaconProposerIndex state

  -- `committee_indices`: the first registry position of each committee key.
  let validators := (sszGet state validators).toArray
  let committeeIndices : Array ValidatorIndex ← syncCommittee.pubkeys.toArray.mapM fun pk =>
    match validators.findIdx? (·.pubkey == pk) with
    | some pIdx => pure (UInt64.ofNat pIdx)
    | none => throwArithmetic "process_sync_aggregate: all_pubkeys.index(pubkey)"

  -- Reward participants (and the proposer), penalize non-participants.
  let mut state := state
  for h : i in [0:committeeIndices.size] do
    let pIdx := committeeIndices[i]
    if bitGet bits i then
      state ← increaseBalance state pIdx participantReward
      state ← increaseBalance state proposerIdx proposerReward
    else
      state ← decreaseBalance state pIdx participantReward
  set state

/-- `process_execution_payload`: the consistency checks against the previous
header and the current RANDAO / slot time, then cache the new header. The
execution-engine `verify_and_notify_new_payload` is the consumer's responsibility
(valid for `sanity/blocks`). The blob commitments must fit the blob limit of the
current epoch (EIP-7892). -/
forkdef processExecutionPayload (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let payload := body.executionPayload
  assert (payload.parentHash == (sszGet state latestExecutionPayloadHeader).blockHash)
  let epoch := currentEpochOf state
  let mix := vmodGet (sszGet state randaoMixes) epoch Const.epochsPerHistoricalVector
  assert (payload.prevRandao == mix)
  -- `compute_time_at_slot(state, state.slot)` (`Fulu/Time.lean`). It can fault, so it arrives
  -- through `liftErr`, which lands the `.arithmetic` fault on this machine unwrapped.
  let expectedTimestamp ← liftErr (computeTimeAtSlot state (sszGet state slot))
  assert (payload.timestamp == expectedTimestamp)
  assert (body.blobKzgCommitments.size ≤ (getBlobParameters epoch).maxBlobsPerBlock.toNat)

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

/-- `verify_block_signature`. The pyspec reads `state.validators[proposer_index]` first, and
that read raises `IndexError` past the registry. The body reads through `sszGetIdx`
(`.outOfBounds`), so the result is an `Except`. -/
forkdef verifyBlockSignature (state : State) (signedBlock : SignedBeaconBlock) :
    Except StateTransitionError Bool := do
  let block := signedBlock.message
  let proposer ← sszGetIdx (sszGet state validators) block.proposerIndex.toNat
  let signingRoot := computeSigningRoot block (getDomain state Const.domainBeaconProposer (currentEpochOf state))
  pure (blsVerify proposer.pubkey signingRoot signedBlock.signature)

/-- `state_transition`: advance to the block's slot, verify the block signature,
apply the block, and check the claimed post-state root, all under `validateResult`. -/
forkdef stateTransition (signedBlock : SignedBeaconBlock) (validateResult : Bool := true) :
    StateTransition Unit := do
  let block := signedBlock.message
  processSlots block.slot
  if validateResult then assert (← liftErr (verifyBlockSignature (← get) signedBlock))
  processBlock block
  if validateResult then
    let root ← getStateRoot
    assert (block.stateRoot == bytesToRoot root)

end

end EthCLSpecs.Fulu
