import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Gloas.Operations`: the inherited (non-ePBS) operation handlers

EIP-7732 leaves most block operations untouched. The Gloas `beacon-chain.md`
overrides only `process_attestation` (payload-aware participation, keyed at the parent
block's slot), `process_withdrawals` (builder withdrawals), and adds
`process_payload_attestation` / the execution-bid / envelope steps. At v1.7.0-beta.4 the
builder-payment cleanup moves from `process_proposer_slashing` into `slash_validator`
(`Gloas/EpochProcessing.lean`), so `process_proposer_slashing` is Fulu's again. Everything
else, the slashing-evidence and deposit / exit / change / execution-request handlers and
`process_sync_aggregate`, is unchanged, so it is `inherit`ed verbatim and re-elaborated over
`Gloas.State`, with the helper dependencies already in the Gloas namespace from
`EpochProcessing`.

The ePBS-modified and ePBS-new handlers are the Gloas-specific port (not here).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

state_section

-- Operation-level validity helpers (no committee dependency).
inherit strictlySorted zeroRoot
inherit isSlashableAttestationData
inherit isValidSwitchToCompoundingRequest

/-- `is_valid_indexed_attestation` (Gloas, EIP-7688, `gloas/beacon-chain.md:1022-1041`).
Fulu's checks, plus the cap that used to live on the list type:
`len(indices) > MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT` returns `False`. The
pyspec then reads `state.validators[index].pubkey` for each index, in order, and a read past
the registry raises `IndexError`. The body raises `.outOfBounds` at the first such index, so
the result is an `Except`, as in Fulu. Declared before the inherited slashings handlers so
their calls bind here. -/
forkdef isValidIndexedAttestation (state : State) (a : IndexedAttestation) :
    Except StateTransitionError Bool := do
  let validators := sszGet state validators
  let idx := a.attestingIndices.toArray
  let cap := Const.maxValidatorsPerCommittee * Const.maxCommitteesPerSlot
  if idx.size == 0 || idx.size > cap || !strictlySorted idx then return false
  -- The pyspec reads the indices in order, so the first one past the registry raises.
  if let some i := idx.find? (fun i => validators.size ≤ i.toNat) then
    throw (.outOfBounds i.toNat validators.size)
  let pubkeys := idx.map (fun i => (validators[i.toNat]!).pubkey)
  pure (blsFastAggregateVerify pubkeys
    (computeSigningRoot a.data (getDomain state Const.domainBeaconAttester a.data.target.epoch))
    a.signature)
-- Attesting-set helper: now inheritable since the Gloas committee layer is in scope
-- (its `getBeaconCommittee` / `getCommitteeIndices` calls bind to the Gloas copies).
inherit getAttestingIndices
inherit attestationCommitteeOffset

-- Handlers EIP-7732 does not change, inherited verbatim over `Gloas.State`.
inherit processAttesterSlashing
-- v1.7.0-beta.4 drops the Gloas `process_proposer_slashing` override: the builder-payment
-- cleanup lives in `slash_validator` now, which this replay late-binds to.
inherit processProposerSlashing
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
/-- `is_active_builder` (`gloas/beacon-chain.md:1054-1064`). The pyspec reads
`state.builders[builder_index]`, and that read raises `IndexError` past the registry. The body
reads through `sszGetIdx` (`.outOfBounds`), so the result is an `Except`. -/
forkdef isActiveBuilder (state : State) (builderIndex : BuilderIndex) :
    Except StateTransitionError Bool := do
  let builder ← sszGetIdx (sszGet state builders) builderIndex.toNat
  pure (builder.depositEpoch < (sszGet state finalizedCheckpoint).epoch
    && builder.withdrawableEpoch == Const.farFutureEpoch)
/-- `get_scheduled_gas_limit(epoch)` (EIP-8261, new at v1.7.0-beta.4,
`gloas/beacon-chain.md:1155-1162`): the gas limit of the latest `GAS_LIMIT_SCHEDULE` entry at
or before `epoch`, or `none` when no entry applies. The schedule's epochs are distinct, so the
descending sort has no ties to break. No modeled path calls it; its callers are the validator
and builder duties. Pure. -/
forkdef getScheduledGasLimit (epoch : Epoch) : Option UInt64 :=
  let descending := Const.gasLimitSchedule.toArray.qsort (fun a b => a.1 > b.1)
  (descending.find? (fun entry => epoch ≥ entry.1)).map (·.2)

/-- `get_pending_balance_to_withdraw_for_builder` (`gloas/beacon-chain.md:1168-1178`): the
pending builder withdrawals plus the queued builder payments for `builderIndex`, summed in
that order into one `balance`.

The pyspec starts `balance` at `Gwei(0)` and adds with `+=` on `uint64` values, so an addition
past `2 ^ 64 - 1` raises a `ValueError`. The body mirrors that: one accumulator, folded first
over the withdrawals and then over the payments, each addition a `checkedAdd`. The reject is
`.arithmetic`. -/
forkdef getPendingBalanceToWithdrawForBuilder (state : State) (builderIndex : BuilderIndex) :
    Except StateTransitionError Gwei := do
  let afterWithdrawals ← (sszGet state builderPendingWithdrawals).val.foldlM
    (fun acc w => if w.builderIndex == builderIndex then
        checkedAdd acc w.amount
          "get_pending_balance_to_withdraw_for_builder: balance += withdrawal.amount"
      else pure acc) 0
  (sszGet state builderPendingPayments).toArray.foldlM
    (fun acc p => if p.withdrawal.builderIndex == builderIndex then
        checkedAdd acc p.withdrawal.amount
          "get_pending_balance_to_withdraw_for_builder: balance += payment.withdrawal.amount"
      else pure acc) afterWithdrawals
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
/-- `get_index_for_new_builder`: a recyclable slot (withdrawable + zero balance) or the end.
Both returns cast a position with `BuilderIndex(...)`, which raises at `2 ^ 64` or above. -/
forkdef getIndexForNewBuilder (state : State) : Except StateTransitionError BuilderIndex := do
  let bs := (sszGet state builders).toArray
  let epoch := currentEpochOf state
  for i in [0:bs.size] do
    if (bs[i]?.getD default).withdrawableEpoch ≤ epoch && (bs[i]?.getD default).balance == 0 then
      return (← checkedIndex i "get_index_for_new_builder: BuilderIndex(index)")
  checkedIndex bs.size "get_index_for_new_builder: BuilderIndex(len(state.builders))"
/-- `withdrawal_credentials[12:]` as a 20-byte execution address. -/
forkdef addressOfCred (wc : Bytes32) : ExecutionAddress := Vector.ofFn (fun i : Fin 20 => wc[12 + i.val])

/-- `add_builder_to_registry` (EIP-8282): set-or-append a `Builder` at the recyclable
index with the supplied `version` / `executionAddress`. -/
forkdef addBuilderToRegistry (pubkey : BLSPubkey) (version : UInt8) (executionAddress : ExecutionAddress)
    (amount : Gwei) (slot : Slot) : StateTransition Unit := do
  let state ← get
  let b : Builder :=
    { pubkey, version, executionAddress, balance := amount,
      depositEpoch := computeEpochAtSlot slot, withdrawableEpoch := Const.farFutureEpoch }
  setOrAppendState builders (← liftErr (getIndexForNewBuilder state)).toNat b
/-- `apply_deposit_for_builder` (retained as a helper; the spec inlines it into
`onboard_builders_from_pending_deposits`): top up an existing builder, or add a new one
with a valid proof-of-possession, stamped `PAYLOAD_BUILDER_VERSION`. -/
forkdef applyDepositForBuilder (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei)
    (sig : BLSSignature) (slot : Slot) : StateTransition Unit := do
  let state ← get
  match (sszGet state builders).findIdx? (·.pubkey == pubkey) with
  | some builderIndex =>
    -- `BuilderIndex(builder_pubkeys.index(deposit.pubkey))` raises at `2 ^ 64` or above, and
    -- `balance += deposit.amount` is a checked `uint64` add (`gloas/fork.md:116-117`).
    let _ ← checkedIndex builderIndex
      "onboard_builders_from_pending_deposits: BuilderIndex(builder_pubkeys.index(deposit.pubkey))"
    let builder := sszGet state builders[builderIndex]!
    let balance ← checkedAdd builder.balance amount
      "onboard_builders_from_pending_deposits: builder.balance + deposit.amount"
    modifyState fun state => sszModify state builders[builderIndex]! as b => { b with balance }
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

  -- `pendingDeposits` is a progressive list at alpha.12: the kept deposits go back
  -- whole, with no `PENDING_DEPOSITS_LIMIT` cap and no `.listFull` raise.
  let keptList : ProgressiveList PendingDeposit := ⟨kept⟩
  modifyState fun state => sszUpdate state with pendingDeposits := keptList

/-- `initialize_ptc_window(state)` (`gloas/fork.md:37-56`): the cached PTC window that seeds
a Gloas state at the fork. The first `SLOTS_PER_EPOCH` entries (the previous epoch, which has
no Gloas PTC) hold zeroed committees; the next `1 + MIN_SEED_LOOKAHEAD` epochs hold
`compute_ptc` for each slot. `MIN_SEED_LOOKAHEAD` is `1`, so the window is
`3 * SLOTS_PER_EPOCH` long, the `ptc_window` field's declared length.

At v1.7.0-beta.4 `upgrade_to_gloas` computes it over the Gloas post-state, with Gloas's own
`compute_ptc`; alpha.12 computed it over the Fulu pre-state. The registry, balances, and
RANDAO mixes the committee reads carry over unchanged, so the window is the same, but the
function is now this fork's own. Each entry is an `Except` carrying its own two faults: the
spec's per-entry `current_epoch + e` (the delta confined to `0` and `1`; `+0` cannot
overflow, `+1` raises the `.arithmetic` fault at `current_epoch = UINT64_MAX`, where
eth-ssz-specs raises Python `ValueError`) binds `checkedAdd` before the entry's `compute_ptc`
read, and `compute_ptc` itself rejects a slot with no committee members.
`completeUpgradeToGloas` maps the entries in index order, so the first rejecting slot
surfaces, matching the spec's list comprehension. -/
forkdef initializePtcWindow (state : State) :
    Vector (Except StateTransitionError (Vector ValidatorIndex Const.ptcSize))
      (3 * Const.slotsPerEpoch) :=
  let currentEpoch := currentEpochOf state
  let emptyCommittee : Vector ValidatorIndex Const.ptcSize := Vector.replicate Const.ptcSize 0
  Vector.ofFn fun i : Fin (3 * Const.slotsPerEpoch) =>
    if i.val < Const.slotsPerEpoch then pure emptyCommittee
    else do
      let j := i.val - Const.slotsPerEpoch
      let epoch ← checkedAdd currentEpoch (UInt64.ofNat (j / Const.slotsPerEpoch))
        "initialize_ptc_window: current_epoch + e"
      let startSlot ← computeStartSlotAtEpoch epoch
      computePtc state (startSlot + UInt64.ofNat (j % Const.slotsPerEpoch))

/-- The state-side close of `upgrade_to_gloas` (`gloas/fork.md:227-230`): fill the post-state's
`ptc_window` with `initialize_ptc_window(post)`, then onboard the builders from the pending
deposits. `upgradeToGloas` (`Gloas/Upgrade.lean`) builds the post-state's fields from the Fulu
pre-state; these two steps read and write the Gloas state, so they run on it, in the spec's
order. -/
forkdef completeUpgradeToGloas : StateTransition Unit := do
  let window ← liftErr ((initializePtcWindow (← get)).mapM id)
  modifyState fun state => sszUpdate state with ptcWindow := window
  onboardBuildersFromPendingDeposits

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

/-- `process_builder_deposit_request` (EIP-8282, alpha.12): ignore a deposit whose
withdrawal-credential prefix is not the builder prefix. A new pubkey with a valid
proof-of-possession is onboarded at `PAYLOAD_BUILDER_VERSION`. An existing builder
is topped up; if it has exited and its balance is already zero, its withdrawable
epoch is pushed back out before the balance increases (`gloas/beacon-chain.md:2334-2360`).
The two `uint64` adds, `epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY` on the reset and
`builder.balance += request.amount`, raise past `2 ^ 64` in that order, so both are checked. -/
forkdef processBuilderDepositRequest (request : BuilderDepositRequest) : StateTransition Unit := do
  if !isBuilderWithdrawalCredential request.withdrawalCredentials then return
  let state ← get
  match (sszGet state builders).findIdx? (·.pubkey == request.pubkey) with
  | none =>
    if isValidBuilderDepositSignature request then
      addBuilderToRegistry request.pubkey Const.payloadBuilderVersion
        (addressOfCred request.withdrawalCredentials) request.amount (sszGet state slot)
  | some builderIndex =>
    -- `builderIndex` comes from `findIdx?` over the registry, so the read is in range. The
    -- spec's `BuilderIndex(...)` cast of it raises at `2 ^ 64` or above.
    let _ ← checkedIndex builderIndex
      "process_builder_deposit_request: BuilderIndex(builder_pubkeys.index(request.pubkey))"
    let builder := sszGet state builders[builderIndex]!
    let reset := builder.withdrawableEpoch != Const.farFutureEpoch && builder.balance == 0
    let withdrawableEpoch ← if reset then
        checkedAdd (currentEpochOf state) Const.minBuilderWithdrawabilityDelay
          "process_builder_deposit_request: epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY"
      else pure builder.withdrawableEpoch
    let balance ← checkedAdd builder.balance request.amount
      "process_builder_deposit_request: builder.balance + request.amount"
    modifyState fun state =>
      sszModify state builders[builderIndex]! as b => { b with balance, withdrawableEpoch }

/-- `process_builder_exit_request` (EIP-8282): an EL-triggered builder exit. A no-op
unless the pubkey names an active builder whose registered execution address matches the
request's `source_address` and that has no pending balance to withdraw; otherwise it
initiates the builder's exit.

The pyspec returns early at each check, in order, so it computes the pending balance only for
an active builder with a matching address. The body binds the pending balance after the first
two checks for the same reason: its sum can fault, and the fault must fire only where the spec
computes it. -/
forkdef processBuilderExitRequest (request : BuilderExitRequest) : StateTransition Unit := do
  let state ← get
  match (sszGet state builders).findIdx? (·.pubkey == request.pubkey) with
  | none => pure ()
  | some idx =>
    let builderIndex : BuilderIndex ← checkedIndex idx
      "process_builder_exit_request: BuilderIndex(builder_pubkeys.index(request.pubkey))"
    let builder := sszGet state builders[idx]!
    if !(← liftErr (isActiveBuilder state builderIndex)) then return
    if builder.executionAddress != request.sourceAddress then return
    let pending ← liftErr (getPendingBalanceToWithdrawForBuilder state builderIndex)
    if pending == 0 then
      initiateBuilderExit builderIndex

/-! ## Attestation (payload-aware) + payload-timeliness committee (EIP-7732) -/

/-- `is_attestation_same_slot`: the attestation votes for the block proposed at its
own slot (head matches this slot's block root but differs from the previous slot's).
The `slot == 0` guard avoids the `slot - 1` `UInt64` underflow. -/
forkdef isAttestationSameSlot (state : State) (data : AttestationData) : StateTransition Bool := do
  if data.slot == 0 then pure true
  else
    let blockroot := data.beaconBlockRoot
    let slotRoot ← getBlockRootAtSlot state data.slot
    let prevRoot ← getBlockRootAtSlot state (data.slot - 1)
    pure (blockroot == slotRoot && blockroot != prevRoot)

/-- `get_attestation_participation_flag_indices` (Gloas, EIP-7732,
`gloas/beacon-chain.md:1339-1386`): adds the payload-matching constraint to `is_matching_head`.
A same-slot attestation must have `data.index == 0`; otherwise `payload_matches` compares
`data.index` to the `execution_payload_availability` bit at `parent_slot`.

v1.7.0-beta.4 adds the `parent_slot` parameter, the slot of the parent of the block being
processed, and reads the payload bit there rather than at `data.slot`. The timely head flag
needs both the minimum inclusion delay and a head root that matches the block root at the
attestation slot, so only an attestation to the parent block can earn it, and the parent's
payload availability is recorded at `parent_slot` even when `data.slot` is a skipped slot.

The pyspec order is: the target root read, the same-slot test (two root reads), the
`data.index == 0` assert, the head root read, and the `is_matching_source` assert last. A
root read can fault, and the body keeps that order, so the fault kind matches. -/
forkdef getAttestationParticipationFlagIndices (state : State) (data : AttestationData)
    (inclusionDelay : UInt64) (parentSlot : Slot) : StateTransition (Array Nat) := do
  let justified := if data.target.epoch == currentEpochOf state then sszGet state currentJustifiedCheckpoint
                   else sszGet state previousJustifiedCheckpoint
  let isMatchingSource := data.source.epoch == justified.epoch && data.source.root == justified.root

  let targetRoot ← getBlockRoot state data.target.epoch
  let isMatchingTarget := isMatchingSource && data.target.root == targetRoot
  let sameSlot ← isAttestationSameSlot state data
  if sameSlot then assert (data.index == 0)
  let payloadMatches : Bool :=
    if sameSlot then true
    else
      let bit := bitGet (sszGet state executionPayloadAvailability) (parentSlot.toNat % Const.slotsPerHistoricalRoot)
      data.index == (if bit then (1 : UInt64) else 0)
  let headRoot ← getBlockRootAtSlot state data.slot
  let isMatchingHead := isMatchingTarget && data.beaconBlockRoot == headRoot && payloadMatches
  assert isMatchingSource

  let mut flags : Array Nat := #[]
  if inclusionDelay ≤ UInt64.ofNat (isqrt Const.slotsPerEpoch) then flags := flags.push Const.timelySourceFlagIndex
  if isMatchingTarget then flags := flags.push Const.timelyTargetFlagIndex
  if isMatchingHead && inclusionDelay == Const.minAttestationInclusionDelay then flags := flags.push Const.timelyHeadFlagIndex
  return flags

/-- `process_attestation` (Gloas, EIP-7732, `gloas/beacon-chain.md:2396-2480`): Fulu's
flag/reward processing, with `assert data.index < 2` (the committee
index carries a payload-presence bit) and the builder-payment weight accounting. For a same-slot attestation
whose builder payment is non-empty, a validator adds its effective balance to the slot's
`BuilderPendingPayment.weight` when it sets a new flag and held no flag before this
attestation, so each validator contributes once.

v1.7.0-beta.4 adds the `parent_slot` parameter, which reaches
`get_attestation_participation_flag_indices`, and the `had_no_participation` gate on the
weight: alpha.12 credited any validator that set a new flag. -/
forkdef processAttestation (att : Attestation) (parentSlot : Slot) : StateTransition Unit := do
  let state ← get
  let data := att.data

  -- Reject on shape: target epoch, slot timing, and the payload-presence bit.
  assert (data.target.epoch == previousEpochOf state || data.target.epoch == currentEpochOf state)
  assert (data.target.epoch == computeEpochAtSlot data.slot)
  -- `data.slot` is wire-controlled and `MIN_ATTESTATION_INCLUSION_DELAY` is 1, so the bare `+`
  -- wraps `0xFFFF…FFFF + 1` to `0` and `0 ≤ state.slot` bypasses the guard for every state: a
  -- false ACCEPT, the state-transition twin of `on_attestation`'s. pyspec's checked `uint64` add
  -- raises `ValueError`, which `process_attestation` does not catch, so the driver scores it
  -- `uncaughtFault`. Sequenced after the two epoch asserts above, matching Python's order.
  let inclusionSlot ← checkedAdd data.slot Const.minAttestationInclusionDelay
    "process_attestation: data.slot + MIN_ATTESTATION_INCLUSION_DELAY"
  assert (inclusionSlot ≤ sszGet state slot)
  assert (data.index < 2)

  -- Every committee index is valid and non-empty; the bitfield covers them all.
  let offset ← liftErr (attestationCommitteeOffset state att)
  assert (att.aggregationBits.size == offset)

  -- Resolve the participation flags, then validate the aggregate signature.
  let flagIndices ← getAttestationParticipationFlagIndices state data
    ((sszGet state slot) - data.slot) parentSlot
  let indexedAttestation : IndexedAttestation :=
    { attestingIndices := ⟨(← liftErr (getAttestingIndices state att)).qsort (· < ·)⟩,
      data := att.data, signature := att.signature }
  assert (← liftErr (isValidIndexedAttestation state indexedAttestation))

  -- Apply participation flags and accumulate the builder-payment weight.
  let currentTarget := data.target.epoch == currentEpochOf state
  let sameSlot ← isAttestationSameSlot state data
  let paymentIdx := builderPaymentIndex data.slot currentTarget
  let payment0 := vget (sszGet state builderPendingPayments) paymentIdx
  let mut stateAcc := state
  let mut proposerNum : Gwei := 0
  let mut weight := payment0.weight
  for vi in (← liftErr (getAttestingIndices state att)) do
    let i := vi.toNat
    -- `i` is a data-derived attesting-validator index; read the participation flag
    -- through `sszGetIdx` so an out-of-range index rejects with `outOfBounds` rather
    -- than masking as a default flag (the matching `[i]!` writes are then in range).
    -- [New in Gloas:EIP7732] the flags this validator held before this attestation.
    let flags0 ← if currentTarget then sszGetIdx (sszGet stateAcc currentEpochParticipation) i
                 else sszGetIdx (sszGet stateAcc previousEpochParticipation) i
    let hadNoParticipation := flags0 == 0
    let mut willSet := false
    for flagIndex in [0:3] do
      -- Python's `and` reads `epoch_participation[index]` only for a flag in the set. The
      -- `had_no_participation` read above already succeeded at `i`, so this read cannot
      -- fault, and the `[i]!` write below is in range.
      if flagIndices.contains flagIndex then
        let flag ← if currentTarget then sszGetIdx (sszGet stateAcc currentEpochParticipation) i
                   else sszGetIdx (sszGet stateAcc previousEpochParticipation) i
        if !hasFlag flag flagIndex then
          stateAcc := if currentTarget then
                     sszUpdate stateAcc with currentEpochParticipation[i]! := addFlag flag flagIndex
                   else
                     sszUpdate stateAcc with previousEpochParticipation[i]! := addFlag flag flagIndex
          -- `get_base_reward(state, index) * weight` is a `Gwei` product, and the numerator a
          -- `Gwei` sum, so both are checked `uint64` ops.
          let reward ← checkedMul (← liftErr (getBaseReward state vi))
            (UInt64.ofNat Const.participationFlagWeights[flagIndex]!)
            "process_attestation: get_base_reward(state, index) * weight"
          proposerNum ← checkedAdd proposerNum reward
            "process_attestation: proposer_reward_numerator + reward"
          willSet := true
    if willSet && hadNoParticipation && sameSlot && payment0.withdrawal.amount > 0 then
      let attester ← sszGetIdx (sszGet state validators) i
      -- `payment.weight += effective_balance` is a checked `uint64` add.
      weight ← checkedAdd weight attester.effectiveBalance
        "process_attestation: payment.weight + effective_balance"

  -- Reward the proposer, then write back the (possibly weight-updated) payment, which the
  -- spec does unconditionally and in this order.
  let proposerDenom := (Const.weightDenominator - Const.proposerWeight) * Const.weightDenominator / Const.proposerWeight
  stateAcc ← increaseBalance stateAcc (getBeaconProposerIndex stateAcc)
    (proposerNum / UInt64.ofNat proposerDenom)
  stateAcc := sszUpdate stateAcc with builderPendingPayments[paymentIdx]! := { payment0 with weight := weight }
  set stateAcc

/-- `get_ptc` (`gloas/beacon-chain.md:1392-1404`): read the cached PTC for `slot` from
`ptc_window`. For a slot in the previous epoch the window's first `SLOTS_PER_EPOCH` entries
hold it; otherwise an `(epoch - state_epoch + 1) * SLOTS_PER_EPOCH` offset applies.

The spec opens with `assert epoch >= GLOAS_FORK_EPOCH` (new at v1.7.0-beta.4): a slot before
the fork has no PTC. The window's previous-epoch entries are zero-filled at the upgrade, so
without the assert a payload attestation for the last pre-fork slot would resolve to
validator 0 and could verify. `GLOAS_FORK_EPOCH` is a config value; the runner applies a
vector's override of it (`0` for a vector that activates Gloas at genesis, the `fork_epoch`
for a transition vector).

The two branch asserts, `epoch + 1 == state_epoch` on the past-epoch side and
`epoch <= state_epoch + MIN_SEED_LOOKAHEAD` on the other, are what bound the index:
`MIN_SEED_LOOKAHEAD` is 1, so the else branch's `epoch - state_epoch` is 0 or 1, the scaled
offset is one or two epochs, and the read lands inside the `3 * SLOTS_PER_EPOCH` window by
construction. That is why the total `vget` is sound once the asserts are in place, and why the
spec's own `IndexError` on this subscript is unreachable rather than unmodeled. Throwing, so
`get_indexed_payload_attestation` and the fork-choice handler bind it. -/
forkdef getPtc (state : State) (slot : Slot) :
    StateTransition (Vector ValidatorIndex Const.ptcSize) := do
  let epoch := computeEpochAtSlot slot
  assert (epoch ≥ Const.gloasForkEpoch)
  let stateEpoch := currentEpochOf state
  let spe := UInt64.ofNat Const.slotsPerEpoch
  if epoch < stateEpoch then
    let nextEpoch ← checkedAdd epoch 1 "get_ptc: epoch + 1"
    assert (nextEpoch == stateEpoch)
    pure (vmodGet (sszGet state ptcWindow) slot Const.slotsPerEpoch)
  else
    let lookaheadBound ← checkedAdd stateEpoch Const.minSeedLookahead
      "get_ptc: state_epoch + MIN_SEED_LOOKAHEAD"
    assert (epoch ≤ lookaheadBound)
    let offset ← checkedSub epoch stateEpoch "get_ptc: epoch - state_epoch"
    let windowed ← checkedAdd offset 1 "get_ptc: (epoch - state_epoch) + 1"
    let scaled ← checkedMul windowed spe "get_ptc: (epoch - state_epoch + 1) * SLOTS_PER_EPOCH"
    let idx ← checkedAdd scaled (slot % spe) "get_ptc: … + slot % SLOTS_PER_EPOCH"
    pure (vget (sszGet state ptcWindow) idx.toNat)

/-- `get_indexed_payload_attestation`: resolve the PTC bits to the (sorted) attesting
validator set. The `aggregation_bits` index into the `PTC_SIZE`-length PTC. Throwing,
because `get_ptc` is. -/
forkdef getIndexedPayloadAttestation (state : State) (pa : PayloadAttestation) :
    StateTransition IndexedPayloadAttestation := do
  let ptc ← getPtc state pa.data.slot
  let attesting := (Array.range Const.ptcSize).foldl
    (fun acc i => if bitGet pa.aggregationBits i then acc.push (vget ptc i) else acc) (#[] : Array ValidatorIndex)
  pure { attestingIndices := ← sszOfArrayM "attestingIndices" (attesting.qsort (· < ·)),
         data := pa.data, signature := pa.signature }

/-- `is_valid_indexed_payload_attestation`: non-empty, *non-strictly* sorted indices
(the PTC can repeat a validator), with a valid `DOMAIN_PTC_ATTESTER` aggregate signature over
the `PayloadAttestationData`. The pyspec tests the shape first and returns `False` on a bad
one. It then reads `state.validators[i].pubkey` for each index, and a read past the registry
raises `IndexError`. The body finds the first index past the registry and raises
`.outOfBounds` there, so the result is an `Except`. -/
forkdef isValidIndexedPayloadAttestation (state : State) (a : IndexedPayloadAttestation) :
    Except StateTransitionError Bool := do
  let idx := a.attestingIndices.toArray
  let nonStrictSorted := (Array.range (idx.size - 1)).all (fun i => idx[i]?.getD default ≤ idx[i+1]?.getD default)
  if idx.size == 0 || !nonStrictSorted then return false
  let validators := sszGet state validators
  -- The pyspec reads the indices in order, so the first one past the registry raises.
  if let some i := idx.find? (fun i => validators.size ≤ i.toNat) then
    throw (.outOfBounds i.toNat validators.size)
  let pubkeys := idx.map (fun i => (validators[i.toNat]!).pubkey)
  pure (blsFastAggregateVerify pubkeys
    (computeSigningRoot a.data (getDomain state Const.domainPtcAttester (computeEpochAtSlot a.data.slot)))
    a.signature)

/-- `process_payload_attestation` (NEW, EIP-7732): the attestation is for the parent
block and the previous slot, with a valid indexed signature. Pure validation, no
state change on success. -/
forkdef processPayloadAttestation (pa : PayloadAttestation) : StateTransition Unit := do
  let state ← get
  let data := pa.data
  assert (data.beaconBlockRoot == (sszGet state latestBlockHeader).parentRoot)
  -- Only satisfiable by wrap when `state.slot == 0`, which block processing cannot reach — but
  -- it is the sole path by which `get_ptc`'s asserts could ever be reached, so it is
  -- checked rather than argued about. pyspec's `data.slot + 1` is a checked `uint64` add.
  let attestedSlot ← checkedAdd data.slot 1 "process_payload_attestation: data.slot + 1"
  assert (attestedSlot == sszGet state slot)
  -- The bind stays after the slot assert: that assert is what bounds `get_ptc`'s index, and the
  -- spec's order is `beacon_block_root`, then `data.slot + 1 == state.slot`, then the indexed
  -- signature check.
  let indexed ← getIndexedPayloadAttestation state pa
  assert (← liftErr (isValidIndexedPayloadAttestation state indexed))

/-! ## Execution payload bid + parent-payload application (EIP-7732) -/

/-- `convert_builder_index_to_validator_index`: set the `BUILDER_INDEX_FLAG` bit. -/
forkdef convertBuilderIndexToValidatorIndex (builderIndex : BuilderIndex) : ValidatorIndex := builderIndex ||| Const.builderIndexFlag

/-- `can_builder_cover_bid`: the builder's balance, after reserving `MIN_DEPOSIT_AMOUNT`
plus its already-pending withdrawals, covers the bid value (`gloas/beacon-chain.md:661`).

Two steps can fault, as in the pyspec: the pending-balance sums, and
`MIN_DEPOSIT_AMOUNT + pending_withdrawals_amount`. Each rejects with `.arithmetic`. The final
subtraction cannot fault, because the `if` rules out `builder_balance < min_balance`. -/
forkdef canBuilderCoverBid (state : State) (builderIndex : BuilderIndex) (bidAmount : Gwei) :
    Except StateTransitionError Bool := do
  let builderBalance := (sszGet state builders[builderIndex.toNat]!).balance
  let pending ← getPendingBalanceToWithdrawForBuilder state builderIndex
  let minBalance ← checkedAdd Const.minDepositAmountG pending
    "can_builder_cover_bid: MIN_DEPOSIT_AMOUNT + pending_withdrawals_amount"
  pure (if builderBalance < minBalance then false else builderBalance - minBalance ≥ bidAmount)

/-- `verify_execution_payload_bid_signature`: the bid is signed by the builder's key
under `DOMAIN_BEACON_BUILDER` at the current epoch. -/
forkdef verifyExecutionPayloadBidSignature (state : State) (signedBid : SignedExecutionPayloadBid) : Bool :=
  let builder := sszGet state builders[signedBid.message.builderIndex.toNat]!
  blsVerifySigned builder.pubkey signedBid.message
    (getDomain state Const.domainBeaconBuilder (currentEpochOf state)) signedBid.signature

/-- `verify_execution_payload_envelope_signature` (`gloas/beacon-chain.md:2107-2121`): the
envelope is signed by the builder's key (the proposer's, for a self-build) under
`DOMAIN_BEACON_BUILDER` at the current epoch. v1.7.0-beta.4 moves it from the fork-choice
document into the beacon-chain one; its one caller is still the fork-choice envelope check.

`state.validators[proposer_index]` / `state.builders[builder_index]` are bare indexed reads
with no guarding assert, and `builder_index` comes straight from the untrusted envelope, so an
out-of-range index is the spec's `IndexError`. `sszGetIdx` surfaces it as the `outOfBounds`
reject, hence the `Except StateTransitionError Bool` signature; the fork-choice caller lifts it
with `liftErr` and binds the result before its `assert`. -/
forkdef verifyExecutionPayloadEnvelopeSignature (state : State)
    (signedEnvelope : SignedExecutionPayloadEnvelope) : Except StateTransitionError Bool := do
  let builderIndex := signedEnvelope.message.builderIndex
  let pubkey ←
    if builderIndex == Const.builderIndexSelfBuild then do
      let validatorIndex := (sszGet state latestBlockHeader).proposerIndex
      let v ← sszGetIdx (sszGet state validators) validatorIndex.toNat
      pure v.pubkey
    else do
      let b ← sszGetIdx (sszGet state builders) builderIndex.toNat
      pure b.pubkey
  let signingRoot := computeSigningRoot signedEnvelope.message
    (getDomain state Const.domainBeaconBuilder (currentEpochOf state))
  pure (blsVerify pubkey signingRoot signedEnvelope.signature)

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

/-- `process_execution_payload_bid` (EIP-7732, `gloas/beacon-chain.md:2162-2215`): validate the
signed bid (self-build sentinel, or an active, payload-builder-versioned, funded,
correctly-signed builder), check it commits to the current slot / parent / randao and names a
block hash other than its parent's (`bid.block_hash != bid.parent_block_hash`, new at
v1.7.0-beta.4), record the `BuilderPendingPayment`, and cache the bid. It takes the
`SignedExecutionPayloadBid` directly (not a `BeaconBlock`, since alpha.11) and reads the
slot / parent root from state. -/
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
    assert (← liftErr (isActiveBuilder state builderIndex))
    assert ((sszGet state builders[builderIndex.toNat]!).version == Const.payloadBuilderVersion)
    assert (← liftErr (canBuilderCoverBid state builderIndex amount))
    assert (verifyExecutionPayloadBidSignature state signedBid)

  assert (bid.blobKzgCommitments.size ≤ (getBlobParameters (currentEpochOf state)).maxBlobsPerBlock)
  assert (bid.slot == sszGet state slot)
  assert ((sszGet state slot) > Const.genesisSlot)
  assert (bid.parentBlockHash == sszGet state latestBlockHash)
  -- [New at v1.7.0-beta.4] the bid's block hash must differ from its parent's.
  assert (bid.blockHash != bid.parentBlockHash)
  let parentBlockRoot ← getBlockRootAtSlot state ((sszGet state slot) - 1)
  assert (bid.parentBlockRoot == parentBlockRoot)
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

/-- `apply_parent_execution_payload` (`gloas/beacon-chain.md:1784-1830`): settle the parent's
builder payment (or queue its value directly once the payment entry is evicted), then process
the parent payload's execution requests at the child's slot, then mark the parent slot's
payload available and adopt its block hash.

v1.7.0-beta.4 changes two things. The parent slot is `state.latest_block_header.slot`, the
parent block's own slot; alpha.12 read the cached bid's slot. And the payment settles before
the requests, so a builder exit request in the same payload is rejected while the payment is
still pending. -/
forkdef applyParentExecutionPayload (requests : ExecutionRequests) : StateTransition Unit := do
  let state ← get
  let parentBid := sszGet state latestExecutionPayloadBid
  let parentSlot := (sszGet state latestBlockHeader).slot
  let parentEpoch := computeEpochAtSlot parentSlot

  assert (requests.withdrawals.size ≤ Const.maxWithdrawalRequestsPerPayload)
  assert (requests.consolidations.size ≤ Const.maxConsolidationRequestsPerPayload)
  assert (requests.builderDeposits.size ≤ Const.maxBuilderDepositRequestsPerPayload)
  assert (requests.builderExits.size ≤ Const.maxBuilderExitRequestsPerPayload)

  -- Settle the parent's payment if it is still in the two-epoch window; outside it,
  -- queue any remaining value directly as a builder withdrawal.
  if parentEpoch == currentEpochOf state then
    settleBuilderPayment (builderPaymentIndex parentSlot true)
  else if parentEpoch == previousEpochOf state then
    settleBuilderPayment (builderPaymentIndex parentSlot false)
  else if parentBid.value > 0 then
    appendState builderPendingWithdrawals
      { feeRecipient := parentBid.feeRecipient, amount := parentBid.value, builderIndex := parentBid.builderIndex }

  for d in requests.deposits do processDepositRequest d
  for w in requests.withdrawals do processWithdrawalRequest w
  for c in requests.consolidations do processConsolidationRequest c
  for bd in requests.builderDeposits do processBuilderDepositRequest bd
  for be in requests.builderExits do processBuilderExitRequest be

  modifyState fun state => sszUpdate state with executionPayloadAvailability :=
    bitSet (sszGet state executionPayloadAvailability) (umodIdx parentSlot Const.slotsPerHistoricalRoot) true
  modifyState fun state => sszUpdate state with latestBlockHash := parentBid.blockHash

/-- `process_parent_execution_payload` (NEW, EIP-7732): if the bid's parent hash does
not match the cached bid, the parent was empty (no requests expected); otherwise the
parent was full, so verify the requests commitment and apply them. On the empty edge the
pyspec's `requests == ExecutionRequests.empty()` compares fields, so the body compares
`requests` with the empty value by the derived `BEq`. On the full edge the pyspec compares
`hash_tree_root(requests)` with the bid's root, and so does the body. -/
forkdef processParentExecutionPayload (block : BeaconBlock) : StateTransition Unit := do
  let state ← get
  let bid := block.body.signedExecutionPayloadBid.message
  let parentBid := sszGet state latestExecutionPayloadBid
  let requests := block.body.parentExecutionRequests
  if bid.parentBlockHash != parentBid.blockHash then
    assert (requests == (default : ExecutionRequests))
  else
    assert (htr requests == parentBid.executionRequestsRoot)
    applyParentExecutionPayload requests

end

end EthCLSpecs.Gloas
