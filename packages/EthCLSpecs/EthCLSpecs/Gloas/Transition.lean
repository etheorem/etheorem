import EthCLSpecs.Gloas.Withdrawals

/-!
# `EthCLSpecs.Gloas.Transition`: the EIP-7732 state-transition spine

Gloas reshapes the block spine. `process_slot` additionally clears the next slot's
payload-availability bit; `process_epoch` inserts `process_builder_pending_payments`
and ends with `process_ptc_window`; and `process_block` drops `process_execution_payload`,
prepends `process_parent_execution_payload`, makes `process_withdrawals` payload-free,
and adds `process_execution_payload_bid` and the in-body `process_payload_attestation`s.
`process_randao` / `process_eth1_data` / `process_sync_aggregate` / `process_block_header`
/ `verify_block_signature` are unchanged and inherited over the Gloas types; the
slot-loop and `state_transition` are restated so their sub-calls bind to the Gloas
spine.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

state_section

-- Block-level steps EIP-7732 leaves unchanged, inherited over the Gloas types.
inherit processRandao
inherit processEth1Data
inherit verifyBlockSignature

/-- `process_slot` (Gloas): Fulu's state/header/block-root caching, plus clearing the
next slot's `execution_payload_availability` bit (a payload starts unavailable). -/
forkdef processSlot : StateTransition Unit :=
  modifyState fun state => Id.run do
    let (prevStateRootBytes, state) := stateRoot state
    let mut state := state
    let prevStateRoot : Root := bytesToRoot prevStateRootBytes
    let idx := umodIdx (sszGet state slot) Const.slotsPerHistoricalRoot

    -- Cache the previous state root, backfill it into the latest header, then cache that
    -- header's block root.
    state := sszUpdate state with stateRoots[idx]! := prevStateRoot
    let latestHeader := sszGet state latestBlockHeader
    let latestHeader := if latestHeader.stateRoot == Fulu.zeroRoot then { latestHeader with stateRoot := prevStateRoot } else latestHeader
    state := sszUpdate state with latestBlockHeader := latestHeader
    let blockRoot := htr (sszGet state latestBlockHeader)
    state := sszUpdate state with blockRoots[idx]! := blockRoot

    -- Gloas addition: the next slot's payload starts unavailable.
    let nextIdx := umodIdx ((sszGet state slot) + 1) Const.slotsPerHistoricalRoot
    state := sszUpdate state with executionPayloadAvailability :=
      bitSet (sszGet state executionPayloadAvailability) nextIdx false
    return state

/-- `process_epoch` (Gloas ordering): `process_builder_pending_payments` after the
pending-consolidations step, and `process_ptc_window` last (EIP-7732). -/
forkdef processEpoch : StateTransition Unit := do
  processJustificationAndFinalization
  processInactivityUpdates
  processRewardsAndPenalties
  processRegistryUpdates
  processSlashings
  processEth1DataReset
  processPendingDeposits
  processPendingConsolidations
  processBuilderPendingPayments
  processEffectiveBalanceUpdates
  processSlashingsReset
  processRandaoMixesReset
  processHistoricalSummariesUpdate
  processParticipationFlagUpdates
  processSyncCommitteeUpdates
  processProposerLookahead
  processPtcWindow

/-- `process_slots`: restated so its `process_slot` / `process_epoch` calls bind to
the Gloas spine. -/
forkdef processSlots (target : Slot) : StateTransition Unit := do
  assert ((sszGet (← get) slot) < target)
  for _ in [0:(target - (sszGet (← get) slot)).toNat] do
    processSlot
    if ((sszGet (← get) slot) + 1) % UInt64.ofNat Const.slotsPerEpoch == 0 then processEpoch
    modifyState fun state => sszUpdate state with slot := (sszGet state slot) + 1

/-- `process_operations` (Gloas, EIP-7732, `gloas/beacon-chain.md:2228-2263`): no in-block
deposits, no execution-request loops (those run in `process_parent_execution_payload`), and
the new `payload_attestations` loop. v1.7.0-beta.4 adds the `parent_slot` parameter, which the
attestation loop passes to `process_attestation`. -/
forkdef processOperations (body : BeaconBlockBody) (parentSlot : Slot) : StateTransition Unit := do
  assert (body.deposits.size == 0)
  -- EIP-7688: the operation lists are progressive, so the old SSZ caps are asserts.
  assert (body.proposerSlashings.size ≤ Const.maxProposerSlashings)
  assert (body.attesterSlashings.size ≤ Const.maxAttesterSlashingsElectra)
  assert (body.attestations.size ≤ Const.maxAttestationsElectra)
  assert (body.voluntaryExits.size ≤ Const.maxVoluntaryExits)
  assert (body.blsToExecutionChanges.size ≤ Const.maxBlsToExecutionChanges)
  assert (body.payloadAttestations.size ≤ Const.maxPayloadAttestations)
  for op in body.proposerSlashings do processProposerSlashing op
  for op in body.attesterSlashings do processAttesterSlashing op
  for op in body.attestations do processAttestation op parentSlot
  for op in body.voluntaryExits do processVoluntaryExit op
  for op in body.blsToExecutionChanges do processBlsToExecutionChange op
  for op in body.payloadAttestations do processPayloadAttestation op

/-- `process_block` (Gloas ordering, EIP-7732, `gloas/beacon-chain.md:1754-1772`). The parent
block's slot is read first, before `process_block_header` replaces the latest header, and
reaches `process_operations` (new at v1.7.0-beta.4). -/
forkdef processBlock (block : BeaconBlock) : StateTransition Unit := do
  let parentSlot := (sszGet (← get) latestBlockHeader).slot
  processParentExecutionPayload block
  processBlockHeader block
  processWithdrawals
  processExecutionPayloadBid block.body.signedExecutionPayloadBid
  processRandao block.body
  processEth1Data block.body
  processOperations block.body parentSlot
  processSyncAggregate block.body.syncAggregate

/-- `state_transition`: restated so its spine sub-calls bind to the Gloas copies. -/
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

end EthCLSpecs.Gloas
