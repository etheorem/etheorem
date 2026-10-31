import EthCLSpecs.Heze.Withdrawals

/-!
# `EthCLSpecs.Heze.Transition`: the state-transition spine (Gloas over Heze, EIP-8015)

EIP-7805 (FOCIL) leaves the EIP-7732 block spine unchanged. EIP-8015 (new at v1.7.0-beta.4)
removes the eth1 deposit machinery, which touches three spine steps: `process_epoch` drops
`process_eth1_data_reset`, `process_block` drops `process_eth1_data`, and `process_operations`
drops the `assert len(body.deposits) == 0` (the body has no `deposits` field). Those three are
restated here. `process_slot` / `process_slots` / `state_transition` and the unchanged
`process_randao` / `verify_block_signature` are `inherit`ed over Heze state. When `inherit`
replays each definition here, its unqualified callee names resolve to the Heze versions
declared in the files above, the transition "spine", and never to the Gloas originals.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

state_section

inherit processRandao
inherit verifyBlockSignature
inherit processSlot

/-- `process_epoch` (Heze, `heze/beacon-chain.md:318-336`): the Gloas order without
`process_eth1_data_reset` (EIP-8015). -/
forkdef processEpoch : StateTransition Unit := do
  processJustificationAndFinalization
  processInactivityUpdates
  processRewardsAndPenalties
  processRegistryUpdates
  processSlashings
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

inherit processSlots

/-- `process_operations` (Heze, `heze/beacon-chain.md:367-384`): the Gloas loops and caps,
without the `assert len(body.deposits) == 0` (EIP-8015 removes the `deposits` field). The
attestation loop passes `parent_slot` on to `process_attestation`, as in Gloas. -/
forkdef processOperations (body : BeaconBlockBody) (parentSlot : Slot) : StateTransition Unit := do
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

/-- `process_block` (Heze, `heze/beacon-chain.md:346-357`): the Gloas order without
`process_eth1_data` (EIP-8015). The parent block's slot is read first, before
`process_block_header` replaces the latest header. -/
forkdef processBlock (block : BeaconBlock) : StateTransition Unit := do
  let parentSlot := (sszGet (← get) latestBlockHeader).slot
  processParentExecutionPayload block
  processBlockHeader block
  processWithdrawals
  processExecutionPayloadBid block.body.signedExecutionPayloadBid
  processRandao block.body
  processOperations block.body parentSlot
  processSyncAggregate block.body.syncAggregate

inherit stateTransition

end

end EthCLSpecs.Heze
