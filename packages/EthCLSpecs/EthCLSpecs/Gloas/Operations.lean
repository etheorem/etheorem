import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Fulu.Transition

/-!
# `EthCLSpecs.Gloas.Operations`: the inherited (non-ePBS) operation handlers

EIP-7732 leaves most block operations untouched. The Gloas `beacon-chain.md`
overrides only `process_proposer_slashing` (builder-payment cleanup),
`process_attestation` (payload-aware participation), `process_withdrawals` (builder
withdrawals), and adds `process_payload_attestation` / the execution-bid /
envelope steps. Everything else, the slashing-evidence and deposit / exit /
change / execution-request handlers and `process_sync_aggregate`, is unchanged, so
it is `inherit`ed verbatim and re-elaborated over `Gloas.State`, with the helper
dependencies already in the Gloas namespace from `EpochProcessing`.

The ePBS-modified and ePBS-new handlers are the Gloas-specific port (not here).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

state_section

-- Operation-level validity helpers (no committee dependency).
inherit isSlashableAttestationData
inherit isValidIndexedAttestation
inherit isValidSwitchToCompoundingRequest
-- Attesting-set helper: now inheritable since the Gloas committee layer is in scope
-- (its `getBeaconCommittee` / `getCommitteeIndices` calls bind to the Gloas copies).
inherit getAttestingIndices

-- Handlers EIP-7732 does not change, inherited verbatim over `Gloas.State`.
inherit processAttesterSlashing
inherit processBlockHeader
inherit processBlsToExecutionChange
inherit processWithdrawalRequest
inherit processConsolidationRequest
-- alpha.11 reverted the Gloas `process_deposit_request` and `process_voluntary_exit`
-- overrides: builder onboarding / exit moved to the dedicated EIP-8282
-- `process_builder_deposit_request` / `process_builder_exit_request`, so a `DepositRequest`
-- is just queued and a builder-index `VoluntaryExit` is rejected by the inherited handlers.
inherit processDepositRequest
inherit processVoluntaryExit
inherit processSyncAggregate

/-! ## Builder-registry helpers (EIP-7732) -/

/-- `is_builder_index`: the `BUILDER_INDEX_FLAG` bit marks a builder index. -/
forkdef isBuilderIndex (vi : ValidatorIndex) : Bool := (vi &&& Const.builderIndexFlag) != 0
/-- `convert_validator_index_to_builder_index`. -/
forkdef toBuilderIndex (vi : ValidatorIndex) : BuilderIndex := vi &&& (~~~ Const.builderIndexFlag)
/-- `is_active_builder`. -/
forkdef isActiveBuilder (state : State) (builderIndex : BuilderIndex) : Bool :=
  let builder := sszGet state builders[builderIndex.toNat]!
  builder.depositEpoch < (sszGet state finalizedCheckpoint).epoch && builder.withdrawableEpoch == Const.farFutureEpoch
/-- `get_pending_balance_to_withdraw_for_builder`: pending builder withdrawals plus
queued builder payments for `builderIndex`. -/
forkdef getPendingBalanceToWithdrawForBuilder (state : State) (builderIndex : BuilderIndex) : Gwei :=
  let w := (sszGet state builderPendingWithdrawals).foldl
    (fun acc x => if x.builderIndex == builderIndex then acc + x.amount else acc) 0
  (sszGet state builderPendingPayments).toArray.foldl
    (fun acc p => if p.withdrawal.builderIndex == builderIndex then acc + p.withdrawal.amount else acc) w
/-- `builderPaymentIndex`: the ring slot for `slot`'s `BuilderPendingPayment`, given whether
`slot` falls in the *current* epoch (`current = true`) versus the previous one.
`builderPendingPayments` is a `2 * SLOTS_PER_EPOCH` ring whose lower half holds the previous
epoch and whose upper half holds the current epoch, so the index is `slot % SLOTS_PER_EPOCH` with
a `SLOTS_PER_EPOCH` offset added only for the current epoch. The epoch test is the caller's
(`process_proposer_slashing` / `apply_parent_execution_payload` compare `compute_epoch_at_slot`,
`process_attestation` keys off `data.target.epoch`); this helper names only the offset
arithmetic. -/
forkdef builderPaymentIndex (slot : Slot) (current : Bool) : Nat :=
  (if current then Const.slotsPerEpoch else 0) + umodIdx slot Const.slotsPerEpoch
/-- `is_builder_withdrawal_credential`. -/
forkdef isBuilderWithdrawalCredential (wc : Bytes32) : Bool := credPrefix wc == Const.builderWithdrawalPrefix
/-- `is_pending_validator`: among `pendingDeposits`, a deposit for `pubkey` with a
valid proof-of-possession. The queue is passed explicitly so callers can probe the
state's queue (`process_deposit_request`) or an in-progress accumulator
(`onboard_builders_from_pending_deposits`). -/
forkdef isPendingValidator (pendingDeposits : Array PendingDeposit) (pubkey : BLSPubkey) : Bool :=
  pendingDeposits.any fun d =>
    d.pubkey == pubkey && isValidDepositSignature d.pubkey d.withdrawalCredentials d.amount d.signature
/-- `initiate_builder_exit`. The EL-triggered builder exit, called by
`process_builder_exit_request` (alpha.11 moved builder exits off `process_voluntary_exit`
to this path). -/
forkdef initiateBuilderExit (builderIndex : BuilderIndex) : StateTransition Unit := do
  let epoch := currentEpochOf (← get)
  modifyState fun state =>
    sszModify state builders[builderIndex.toNat]! as b => { b with withdrawableEpoch := epoch + Const.minBuilderWithdrawabilityDelay }
/-- `get_index_for_new_builder`: a recyclable slot (withdrawable + zero balance) or the end. -/
forkdef getIndexForNewBuilder (state : State) : BuilderIndex := Id.run do
  let bs := (sszGet state builders).toArray
  let epoch := currentEpochOf state
  for i in [0:bs.size] do
    if (bs[i]?.getD default).withdrawableEpoch ≤ epoch && (bs[i]?.getD default).balance == 0 then return UInt64.ofNat i
  return UInt64.ofNat bs.size
/-- `withdrawal_credentials[12:]` as a 20-byte execution address. -/
private def addressOfCred (wc : Bytes32) : ExecutionAddress := Vector.ofFn (fun i : Fin 20 => wc[12 + i.val])

/-- `add_builder_to_registry` (EIP-8282): set-or-append a `Builder` at the recyclable
index with the supplied `version` / `executionAddress`. -/
forkdef addBuilderToRegistry (pubkey : BLSPubkey) (version : UInt8) (executionAddress : ExecutionAddress)
    (amount : Gwei) (slot : Slot) : StateTransition Unit := do
  let state ← get
  let idx := (getIndexForNewBuilder state).toNat
  let b : Builder :=
    { pubkey, version, executionAddress, balance := amount,
      depositEpoch := computeEpochAtSlot slot, withdrawableEpoch := Const.farFutureEpoch }
  modifyState fun state =>
    if idx < (sszGet state builders).size then
      sszUpdate state with builders[idx]! := b
    else sszAppend state builders b
/-- `apply_deposit_for_builder` (retained as a helper; the spec inlines it into
`onboard_builders_from_pending_deposits`): top up an existing builder, or add a new one
with a valid proof-of-possession, stamped `PAYLOAD_BUILDER_VERSION`. -/
forkdef applyDepositForBuilder (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei)
    (sig : BLSSignature) (slot : Slot) : StateTransition Unit := do
  let state ← get
  match (sszGet state builders).findIdx? (·.pubkey == pubkey) with
  | some builderIndex => modifyState fun state =>
      sszModify state builders[builderIndex]! as b => { b with balance := b.balance + amount }
  | none =>
    if isValidDepositSignature pubkey wc amount sig then
      addBuilderToRegistry pubkey Const.payloadBuilderVersion (addressOfCred wc) amount slot

/-- `onboard_builders_from_pending_deposits`: at the fork, drain the pending-deposit
queue, applying builder deposits (existing builder pubkey, or a builder-credential
deposit) to the registry and keeping validator deposits (and valid new-validator
deposits) queued. The builder-pubkey set is reread each iteration because
`applyDepositForBuilder` can append a builder. -/
forkdef onboardBuildersFromPendingDeposits : StateTransition Unit := do
  let state ← get
  let validatorPubkeys := (sszGet state validators).map (·.pubkey)
  let mut kept : Array PendingDeposit := #[]

  for d in (sszGet state pendingDeposits) do
    let state ← get
    let builderPubkeys := (sszGet state builders).map (·.pubkey)
    let keep :=
      validatorPubkeys.contains d.pubkey ||
      (!builderPubkeys.contains d.pubkey &&
        (!isBuilderWithdrawalCredential d.withdrawalCredentials || isPendingValidator kept d.pubkey))
    if keep then
      kept := kept.push d
    else
      applyDepositForBuilder d.pubkey d.withdrawalCredentials d.amount d.signature d.slot

  modifyState fun state => sszUpdate state with pendingDeposits := sszOfArray kept

/-! ## EIP-8282 builder-request handlers

The EL-triggered builder onboarding / exit path (alpha.11). `apply_parent_execution_payload`
runs these over the parent payload's `ExecutionRequests.builder_deposits` /
`builder_exits` lists, after the validator deposit / withdrawal / consolidation requests. -/

/-- `is_valid_builder_deposit_signature`: the builder-deposit proof-of-possession.
Like `is_valid_deposit_signature`, the domain is fixed (`compute_domain(DOMAIN_BUILDER_DEPOSIT)`
over the genesis fork version and a zero `genesis_validators_root`), so verification is a
single BLS gate through the `[CryptoBackend]` seam. -/
forkdef isValidBuilderDepositSignature (request : BuilderDepositRequest) : Bool :=
  let msg : DepositMessage :=
    { pubkey := request.pubkey, withdrawalCredentials := request.withdrawalCredentials, amount := request.amount }
  let domain := computeDomain Const.domainBuilderDeposit Const.genesisForkVersion (Vector.replicate 32 0)
  blsVerify request.pubkey (computeSigningRoot msg domain) request.signature

/-- `process_builder_deposit_request` (EIP-8282): for a new builder pubkey with a valid
proof-of-possession, onboard it (the `version` byte and execution address come from the
withdrawal credentials, stamped at `state.slot`); for an existing builder, top up its
balance and, if it had already initiated exit, push its withdrawable epoch back out. -/
forkdef processBuilderDepositRequest (request : BuilderDepositRequest) : StateTransition Unit := do
  let state ← get
  match (sszGet state builders).findIdx? (·.pubkey == request.pubkey) with
  | none =>
    if isValidBuilderDepositSignature request then
      addBuilderToRegistry request.pubkey (credPrefix request.withdrawalCredentials)
        (addressOfCred request.withdrawalCredentials) request.amount (sszGet state slot)
  | some builderIndex =>
    let epoch := currentEpochOf state
    modifyState fun state =>
      sszModify state builders[builderIndex]! as b =>
        { b with
          balance := b.balance + request.amount,
          withdrawableEpoch :=
            if b.withdrawableEpoch != Const.farFutureEpoch
            then epoch + Const.minBuilderWithdrawabilityDelay
            else b.withdrawableEpoch }

/-- `process_builder_exit_request` (EIP-8282): an EL-triggered builder exit. A no-op
unless the pubkey names an active builder whose registered execution address matches the
request's `source_address` and that has no pending balance to withdraw; otherwise it
initiates the builder's exit. -/
forkdef processBuilderExitRequest (request : BuilderExitRequest) : StateTransition Unit := do
  let state ← get
  match (sszGet state builders).findIdx? (·.pubkey == request.pubkey) with
  | none => pure ()
  | some idx =>
    let builderIndex : BuilderIndex := UInt64.ofNat idx
    let builder := sszGet state builders[idx]!
    if isActiveBuilder state builderIndex
        && builder.executionAddress == request.sourceAddress
        && getPendingBalanceToWithdrawForBuilder state builderIndex == 0 then
      initiateBuilderExit builderIndex

/-! ## Gloas-modified operations -/

/-- `process_proposer_slashing` (Gloas): Fulu's checks and `slash_validator`, plus
the EIP-7732 step that voids the slashed proposal's `BuilderPendingPayment` if it
is still in the two-epoch payment window. -/
forkdef processProposerSlashing (ps : ProposerSlashing) : StateTransition Unit := do
  let state ← get
  let h1 := ps.signedHeader1.message
  let h2 := ps.signedHeader2.message

  assert (h1.slot == h2.slot)
  assert (h1.proposerIndex == h2.proposerIndex)
  assert (htr h1 != htr h2)
  let hb ← assertH (h1.proposerIndex.toNat < (sszGet state validators).size)
  let proposer := (sszGet state validators)[h1.proposerIndex.toNat]'hb.down
  assert (isSlashableValidator proposer (currentEpochOf state))
  assert (blsVerifySigned proposer.pubkey h1
    (getDomain state Const.domainBeaconProposer (computeEpochAtSlot h1.slot)) ps.signedHeader1.signature)
  assert (blsVerifySigned proposer.pubkey h2
    (getDomain state Const.domainBeaconProposer (computeEpochAtSlot h2.slot)) ps.signedHeader2.signature)

  -- Void the slashed proposal's pending payment only if it is still in the two-epoch
  -- window AND the recorded payment belongs to this proposer (EIP-8282). `default` is
  -- the all-zero `BuilderPendingPayment`, so this clears the slot without restating it.
  let empty : BuilderPendingPayment := default
  let proposalEpoch := computeEpochAtSlot h1.slot
  if proposalEpoch == currentEpochOf state then
    let idx := builderPaymentIndex h1.slot true
    if ((sszGet state builderPendingPayments)[idx]!).proposerIndex == h1.proposerIndex then
      modifyState fun state => sszUpdate state with builderPendingPayments[idx]! := empty
  else if proposalEpoch == previousEpochOf state then
    let idx := builderPaymentIndex h1.slot false
    if ((sszGet state builderPendingPayments)[idx]!).proposerIndex == h1.proposerIndex then
      modifyState fun state => sszUpdate state with builderPendingPayments[idx]! := empty

  slashValidator h1.proposerIndex

/-! ## Attestation (payload-aware) + payload-timeliness committee (EIP-7732) -/

/-- `is_attestation_same_slot`: the attestation votes for the block proposed at its
own slot (head matches this slot's block root but differs from the previous slot's).
The `slot == 0` guard avoids the `slot - 1` `UInt64` underflow. -/
forkdef isAttestationSameSlot (state : State) (data : AttestationData) : Bool :=
  if data.slot == 0 then true
  else
    let blockroot := data.beaconBlockRoot
    blockroot == getBlockRootAtSlot state data.slot && blockroot != getBlockRootAtSlot state (data.slot - 1)

/-- `get_attestation_participation_flag_indices` (Gloas, EIP-7732): adds the
payload-matching constraint to `is_matching_head`. A same-slot attestation must have
`data.index == 0` (a second reject, surfaced as `none`); otherwise `payload_matches`
compares `data.index` to this slot's `execution_payload_availability` bit. `none`
also covers the `is_matching_source` reject (as in Fulu). -/
forkdef getAttestationParticipationFlagIndices (state : State) (data : AttestationData)
    (inclusionDelay : UInt64) : Option (Array Nat) := Id.run do
  let justified := if data.target.epoch == currentEpochOf state then sszGet state currentJustifiedCheckpoint
                   else sszGet state previousJustifiedCheckpoint
  let isMatchingSource := data.source.epoch == justified.epoch && data.source.root == justified.root
  if !isMatchingSource then return none

  let isMatchingTarget := data.target.root == getBlockRoot state data.target.epoch
  let sameSlot := isAttestationSameSlot state data
  if sameSlot && data.index != 0 then return none
  let payloadMatches : Bool :=
    if sameSlot then true
    else
      let bit := bitGet (sszGet state executionPayloadAvailability) (data.slot.toNat % Const.slotsPerHistoricalRoot)
      data.index == (if bit then (1 : UInt64) else 0)
  let isMatchingHead := isMatchingTarget && data.beaconBlockRoot == getBlockRootAtSlot state data.slot && payloadMatches

  let mut flags : Array Nat := #[]
  if inclusionDelay ≤ UInt64.ofNat (isqrt Const.slotsPerEpoch) then flags := flags.push Const.timelySourceFlagIndex
  if isMatchingTarget then flags := flags.push Const.timelyTargetFlagIndex
  if isMatchingHead && inclusionDelay == Const.minAttestationInclusionDelay then flags := flags.push Const.timelyHeadFlagIndex
  return some flags

/-- `process_attestation` (Gloas, EIP-7732): Fulu's flag/reward processing, with
`assert data.index < 2` (a payload-presence bit rides the committee index) and the
new builder-payment weight accounting. For same-slot attestations whose builder
payment is non-empty, each validator that sets a new flag adds its effective balance
to the slot's `BuilderPendingPayment.weight`, contributing once per slot. -/
forkdef processAttestation (att : Attestation) : StateTransition Unit := do
  let state ← get
  let data := att.data

  -- Reject on shape: target epoch, slot timing, and the payload-presence bit.
  assert (data.target.epoch == previousEpochOf state || data.target.epoch == currentEpochOf state)
  assert (data.target.epoch == computeEpochAtSlot data.slot)
  assert (data.slot + Const.minAttestationInclusionDelay ≤ sszGet state slot)
  assert (data.index < 2)

  -- Every committee index is valid and non-empty; the bitfield covers them all.
  let count := getCommitteeCountPerSlot state data.target.epoch
  let (ok, offset) := verifyCommitteeCoverage state data att count
  assert ok
  assert (att.aggregationBits.size == offset)

  -- Resolve the participation flags, then validate the aggregate signature.
  let flagIndices ← match getAttestationParticipationFlagIndices state data ((sszGet state slot) - data.slot) with
    | some f => pure f
    | none   => throw (StateTransitionError.assert "attestation participation flags")
  let indexedAttestation : IndexedAttestation :=
    { attestingIndices := sszOfArray ((← liftErr (getAttestingIndices state att)).qsort (· < ·)),
      data := att.data, signature := att.signature }
  assert (isValidIndexedAttestation state indexedAttestation)

  -- Apply participation flags and accumulate the builder-payment weight.
  let currentTarget := data.target.epoch == currentEpochOf state
  let sameSlot := isAttestationSameSlot state data
  let paymentIdx := builderPaymentIndex data.slot currentTarget
  let payment0 := vget (sszGet state builderPendingPayments) paymentIdx
  let mut stateAcc := state
  let mut proposerNum := 0
  let mut weight := payment0.weight
  for vi in (← liftErr (getAttestingIndices state att)) do
    let i := vi.toNat
    let mut willSet := false
    for flagIndex in [0:3] do
      -- `i` is a data-derived attesting-validator index; read the participation flag
      -- through `sszGetIdx` so an out-of-range index rejects with `outOfBounds` rather
      -- than masking as a default flag (the matching `[i]!` write is then in range).
      let flag ← if currentTarget then sszGetIdx (sszGet stateAcc currentEpochParticipation) i
                 else sszGetIdx (sszGet stateAcc previousEpochParticipation) i
      if flagIndices.contains flagIndex && !hasFlag flag flagIndex then
        stateAcc := if currentTarget then
                   sszUpdate stateAcc with currentEpochParticipation[i]! := addFlag flag flagIndex
                 else
                   sszUpdate stateAcc with previousEpochParticipation[i]! := addFlag flag flagIndex
        proposerNum := proposerNum + (← liftErr (getBaseReward state vi)) * Const.participationFlagWeights[flagIndex]!
        willSet := true
    if willSet && sameSlot && payment0.withdrawal.amount > 0 then
      let attester ← sszGetIdx (sszGet state validators) i
      weight := weight + attester.effectiveBalance

  -- Write back the (possibly weight-updated) payment, as the spec does unconditionally.
  stateAcc := sszUpdate stateAcc with builderPendingPayments[paymentIdx]! := { payment0 with weight := weight }
  let proposerDenom := (Const.weightDenominator - Const.proposerWeight) * Const.weightDenominator / Const.proposerWeight
  stateAcc := increaseBalance stateAcc (getBeaconProposerIndex stateAcc) (UInt64.ofNat (proposerNum / proposerDenom))
  set stateAcc
where
  /-- Walk the committee bits: each referenced committee index is in range and
  attested by at least one bit, and the running `offset` totals their sizes (the
  aggregation bitfield must match it exactly). Returns `(valid?, totalSize)`. -/
  verifyCommitteeCoverage (state : State) (data : AttestationData) (att : Attestation) (count : Nat) : Bool × Nat :=
    (getCommitteeIndices att.committeeBits).foldl
      (fun (acc : Bool × Nat) ci => Id.run do
        let (okAcc, off) := acc
        if (UInt64.ofNat ci).toNat ≥ count then return (false, off)
        let committee := getBeaconCommittee state data.slot ci
        let attesters := (List.range committee.size).foldl
          (fun a i => if att.aggregationBits[off + i]! then a + 1 else a) 0
        return (okAcc && attesters > 0, off + committee.size))
      (true, 0)

/-- `get_ptc` (v1.7.0-alpha.11): read the cached PTC for `slot` from `ptc_window`.
For a slot in the previous epoch the window's first `SLOTS_PER_EPOCH` entries hold
it; otherwise an `(epoch - state_epoch + 1) * SLOTS_PER_EPOCH` offset applies. The
spec asserts the slot is within `[state_epoch-1, state_epoch + MIN_SEED_LOOKAHEAD]`;
callers (`process_payload_attestation`) guarantee this via `data.slot + 1 ==
state.slot`, so the index is always in range. -/
forkdef getPtc (state : State) (slot : Slot) : Vector ValidatorIndex Const.ptcSize :=
  let epoch := computeEpochAtSlot slot
  let stateEpoch := currentEpochOf state
  let spe := UInt64.ofNat Const.slotsPerEpoch
  if epoch < stateEpoch then vmodGet (sszGet state ptcWindow) slot Const.slotsPerEpoch
  -- The else index `(epoch - stateEpoch + 1) * spe + slot % spe` is in range only under the
  -- caller's slot-range guarantee (`process_payload_attestation`'s `data.slot + 1 ==
  -- state.slot`), which is not in scope here, so it stays a total read.
  else vget (sszGet state ptcWindow) (((epoch - stateEpoch + 1) * spe + slot % spe).toNat)

/-- `get_indexed_payload_attestation`: resolve the PTC bits to the (sorted) attesting
validator set. The `aggregation_bits` index into the `PTC_SIZE`-length PTC. -/
forkdef getIndexedPayloadAttestation (state : State) (pa : PayloadAttestation) : IndexedPayloadAttestation :=
  let ptc := getPtc state pa.data.slot
  let attesting := (Array.range Const.ptcSize).foldl
    (fun acc i => if bitGet pa.aggregationBits i then acc.push (vget ptc i) else acc) (#[] : Array ValidatorIndex)
  { attestingIndices := sszOfArray (attesting.qsort (· < ·)), data := pa.data, signature := pa.signature }

/-- `is_valid_indexed_payload_attestation`: non-empty, *non-strictly* sorted indices
(the PTC can repeat a validator), in range, with a valid `DOMAIN_PTC_ATTESTER`
aggregate signature over the `PayloadAttestationData`. -/
forkdef isValidIndexedPayloadAttestation (state : State) (a : IndexedPayloadAttestation) : Bool :=
  let idx := a.attestingIndices.toArray
  let nonStrictSorted := (Array.range (idx.size - 1)).all (fun i => idx[i]?.getD default ≤ idx[i+1]?.getD default)
  if idx.size == 0 || !nonStrictSorted then false
  else
    let validators := sszGet state validators
    if !idx.all (·.toNat < validators.size) then false
    else
      let pubkeys := idx.map (fun i => (validators[i.toNat]!).pubkey)
      blsFastAggregateVerify pubkeys
        (computeSigningRoot a.data (getDomain state Const.domainPtcAttester (computeEpochAtSlot a.data.slot)))
        a.signature

/-- `process_payload_attestation` (NEW, EIP-7732): the attestation is for the parent
block and the previous slot, with a valid indexed signature. Pure validation, no
state change on success. -/
forkdef processPayloadAttestation (pa : PayloadAttestation) : StateTransition Unit := do
  let state ← get
  let data := pa.data
  assert (data.beaconBlockRoot == (sszGet state latestBlockHeader).parentRoot)
  assert (data.slot + 1 == sszGet state slot)
  assert (isValidIndexedPayloadAttestation state (getIndexedPayloadAttestation state pa))

/-! ## Execution payload bid + parent-payload application (EIP-7732) -/

/-- `convert_builder_index_to_validator_index`: set the `BUILDER_INDEX_FLAG` bit. -/
forkdef convertBuilderIndexToValidatorIndex (builderIndex : BuilderIndex) : ValidatorIndex := builderIndex ||| Const.builderIndexFlag

/-- `can_builder_cover_bid`: the builder's balance, after reserving `MIN_DEPOSIT_AMOUNT`
plus its already-pending withdrawals, covers the bid value. -/
forkdef canBuilderCoverBid (state : State) (builderIndex : BuilderIndex) (bidAmount : Gwei) : Bool :=
  let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
  let minBalance := Const.minDepositAmountG + getPendingBalanceToWithdrawForBuilder state builderIndex
  if builderBalance < minBalance then false else builderBalance - minBalance ≥ bidAmount

/-- `verify_execution_payload_bid_signature`: the bid is signed by the builder's key
under `DOMAIN_BEACON_BUILDER` at the current epoch. -/
forkdef verifyExecutionPayloadBidSignature (state : State) (signedBid : SignedExecutionPayloadBid) : Bool :=
  let builder := sszGet state builders[signedBid.message.builderIndex.toNat]!
  blsVerifySigned builder.pubkey signedBid.message
    (getDomain state Const.domainBeaconBuilder (currentEpochOf state)) signedBid.signature

/-- `settle_builder_payment`: queue the pending payment's withdrawal (if non-zero)
and clear the payment slot. No quorum check at this layer (that lives in the epoch
substep `process_builder_pending_payments`). -/
forkdef settleBuilderPayment (paymentIndex : Nat) : StateTransition Unit := do
  let state ← get
  assert (paymentIndex < 2 * Const.slotsPerEpoch)
  let payment := vget (sszGet state builderPendingPayments) paymentIndex

  if payment.withdrawal.amount > 0 then
    appendState builderPendingWithdrawals payment.withdrawal

  let empty : BuilderPendingPayment := default
  modifyState fun state =>
    sszUpdate state with builderPendingPayments[paymentIndex]! := empty

/-- `process_execution_payload_bid` (EIP-7732, alpha.11 signature): validate the signed
bid (self-build sentinel, or an active, payload-builder-versioned, funded, correctly-signed
builder), check it commits to the current slot / parent / randao, record the
`BuilderPendingPayment`, and cache the bid. alpha.11 takes the `SignedExecutionPayloadBid`
directly (not a `BeaconBlock`) and reads the slot / parent root from state. -/
forkdef processExecutionPayloadBid (signedBid : SignedExecutionPayloadBid) : StateTransition Unit := do
  let state ← get
  let bid := signedBid.message
  let builderIndex := bid.builderIndex
  let amount := bid.value

  -- A self-build sentinel carries no value or signature; a real builder must be active,
  -- a payload builder (`PAYLOAD_BUILDER_VERSION`), funded, and the signer of the bid.
  if builderIndex == Const.builderIndexSelfBuild then
    assert (amount == 0)
    assert (signedBid.signature == Const.g2PointAtInfinity)
  else
    assert (isActiveBuilder state builderIndex)
    assert ((sszGet state builders[builderIndex.toNat]!).version == Const.payloadBuilderVersion)
    assert (canBuilderCoverBid state builderIndex amount)
    assert (verifyExecutionPayloadBidSignature state signedBid)

  assert (bid.blobKzgCommitments.size ≤ Const.maxBlobsPerBlockElectra)
  assert (bid.slot == sszGet state slot)
  assert ((sszGet state slot) > Const.genesisSlot)
  assert (bid.parentBlockHash == sszGet state latestBlockHash)
  assert (bid.parentBlockRoot == getBlockRootAtSlot state ((sszGet state slot) - 1))
  let randaoMix ← getRandaoMix (currentEpochOf state)
  assert (bid.prevRandao == randaoMix)

  if amount > 0 then
    let pending : BuilderPendingPayment :=
      { weight := 0,
        withdrawal := { feeRecipient := bid.feeRecipient, amount := amount, builderIndex := builderIndex },
        proposerIndex := getBeaconProposerIndex state }
    modifyState fun state =>
      sszUpdate state with builderPendingPayments[builderPaymentIndex bid.slot true]! := pending

  modifyState fun state => sszUpdate state with latestExecutionPayloadBid := bid

/-- `apply_parent_execution_payload`: process the parent payload's execution requests
(at the child's slot), settle or evict the parent's builder payment, then mark the
parent slot's payload available and adopt its block hash. -/
forkdef applyParentExecutionPayload (requests : ExecutionRequests) : StateTransition Unit := do
  let state ← get
  let parentBid := sszGet state latestExecutionPayloadBid
  let parentSlot := parentBid.slot
  let parentEpoch := computeEpochAtSlot parentSlot

  for d in requests.deposits do processDepositRequest d
  for w in requests.withdrawals do processWithdrawalRequest w
  for c in requests.consolidations do processConsolidationRequest c
  for bd in requests.builderDeposits do processBuilderDepositRequest bd
  for be in requests.builderExits do processBuilderExitRequest be

  -- Settle the parent's payment if it is still in the two-epoch window; outside it,
  -- queue any remaining value directly as a builder withdrawal.
  if parentEpoch == currentEpochOf state then
    settleBuilderPayment (builderPaymentIndex parentSlot true)
  else if parentEpoch == previousEpochOf state then
    settleBuilderPayment (builderPaymentIndex parentSlot false)
  else if parentBid.value > 0 then
    appendState builderPendingWithdrawals
      { feeRecipient := parentBid.feeRecipient, amount := parentBid.value, builderIndex := parentBid.builderIndex }

  modifyState fun state => sszUpdate state with executionPayloadAvailability :=
    bitSet (sszGet state executionPayloadAvailability) (umodIdx parentSlot Const.slotsPerHistoricalRoot) true
  modifyState fun state => sszUpdate state with latestBlockHash := parentBid.blockHash

/-- `process_parent_execution_payload` (NEW, EIP-7732): if the bid's parent hash does
not match the cached bid, the parent was empty (no requests expected); otherwise the
parent was full, so verify the requests commitment and apply them. -/
forkdef processParentExecutionPayload (block : BeaconBlock) : StateTransition Unit := do
  let state ← get
  let bid := block.body.signedExecutionPayloadBid.message
  let parentBid := sszGet state latestExecutionPayloadBid
  let requests := block.body.parentExecutionRequests
  if bid.parentBlockHash != parentBid.blockHash then
    assert (htr requests == htr (default : ExecutionRequests))
  else
    assert (htr requests == parentBid.executionRequestsRoot)
    applyParentExecutionPayload requests

end

end EthCLSpecs.Gloas
