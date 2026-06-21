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
def zeroRoot : Root := Vector.replicate 32 0

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
  let hb ← assertH (block.proposerIndex.toNat < (sszGet state validators).size)
  let proposer := (sszGet state validators)[block.proposerIndex.toNat]'hb.down
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
  let mix := vmodGet (sszGet state randaoMixes) epoch Const.epochsPerHistoricalVector
  let digest := sha body.randaoReveal
  let newMix : Bytes32 := Vector.ofFn (fun i : Fin 32 => mix[i] ^^^ digest.get! i.val)
  modifyState fun state =>
    sszUpdate state with randaoMixes[umodIdx epoch Const.epochsPerHistoricalVector]! := newMix

/-- `process_eth1_data`: append the vote and adopt it once it has a majority over
the voting period. -/
forkdef processEth1Data (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let votes := (sszGet state eth1DataVotes).push body.eth1Data
  let target := htr body.eth1Data
  let cnt := votes.foldl (fun acc e => if htr e == target then acc + 1 else acc) 0
  modifyState fun state => Id.run do
    let mut state := state
    state := sszUpdate state with eth1DataVotes := votes
    if cnt * 2 > Const.epochsPerEth1VotingPeriod * Const.slotsPerEpoch then
      state := sszUpdate state with eth1Data := body.eth1Data
    return state

/-- `process_sync_aggregate`: verify the aggregate signature over the previous
slot's block root, then apply participant / proposer rewards and non-participant
penalties. The participant pubkey list is the bit-selected committee keys;
`eth_fast_aggregate_verify` aggregates them, so the all-participate /
majority-subtraction optimizations the spec describes are unnecessary and the
verification result is identical. -/
forkdef processSyncAggregate (agg : SyncAggregate) : StateTransition Unit := do
  let state ← get
  let syncCommittee := sszGet state currentSyncCommittee
  let bits := agg.syncCommitteeBits
  let participantKeys : Array BLSPubkey :=
    (Bitvector.trueIndices bits).map (fun i => syncCommittee.pubkeys[i]!)
  let previousSlot := (umax (sszGet state slot) 1) - 1
  let signingRoot := computeSigningRoot (getBlockRootAtSlot state previousSlot)
    (getDomain state Const.domainSyncCommittee (computeEpochAtSlot previousSlot))
  assert (blsEthFastAggregateVerify participantKeys signingRoot agg.syncCommitteeSignature)
  let totalActiveIncrements := (getTotalActiveBalance state).toNat / Const.effectiveBalanceIncrement
  let totalBaseRewards := getBaseRewardPerIncrement state * totalActiveIncrements
  let maxParticipantRewards := totalBaseRewards * Const.syncRewardWeight / Const.weightDenominator / Const.slotsPerEpoch
  let participantReward : Gwei := UInt64.ofNat (maxParticipantRewards / Const.syncCommitteeSize)
  let proposerReward : Gwei :=
    UInt64.ofNat (participantReward.toNat * Const.proposerWeight / (Const.weightDenominator - Const.proposerWeight))
  let proposerIdx := getBeaconProposerIndex state
  let validators := (sszGet state validators).toArray
  modifyState fun state => Id.run do
    let mut state := state
    for h : i in [0:Const.syncCommitteeSize] do
      let pk := syncCommittee.pubkeys[i]
      match validators.findIdx? (·.pubkey == pk) with
      | some pIdx =>
        if bitGet bits i then
          state := increaseBalance state (UInt64.ofNat pIdx) participantReward
          state := increaseBalance state proposerIdx proposerReward
        else
          state := decreaseBalance state (UInt64.ofNat pIdx) participantReward
      | none => pure ()
    return state

/-- `process_execution_payload`: the consistency checks against the previous
header and the current RANDAO / slot time, then cache the new header. The
execution-engine `verify_and_notify_new_payload` is the consumer's responsibility
(valid for `sanity/blocks`); the blob-parameter bound is enforced where the
operation format supplies it. -/
forkdef processExecutionPayload (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let payload := body.executionPayload
  assert (payload.parentHash == (sszGet state latestExecutionPayloadHeader).blockHash)
  let epoch := currentEpochOf state
  let mix := vmodGet (sszGet state randaoMixes) epoch Const.epochsPerHistoricalVector
  assert (payload.prevRandao == mix)
  assert (payload.timestamp == (sszGet state genesisTime) + (sszGet state slot) * Const.secondsPerSlot)
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
  if block.proposerIndex.toNat ≥ (sszGet state validators).size then false
  else
    let proposer := sszGet state validators[block.proposerIndex.toNat]!
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
