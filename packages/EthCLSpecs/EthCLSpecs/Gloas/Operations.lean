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

/-- `is_valid_indexed_attestation` (Gloas, EIP-7688). Fulu's checks, plus the
cap that used to live on the list type:
`len(indices) > MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT`
rejects. The pyspec's pubkey read `state.validators[i]` raises `IndexError` for an index
past the registry. This body is a pure `Bool`, so it returns `false` there, and the caller's
`assert` raises the assert class. The runner catches both classes. Declared before the inherited slashings handlers so their calls bind here. -/
forkdef isValidIndexedAttestation (state : State) (a : IndexedAttestation) : Bool :=
  let validators := state.validators
  let idx := a.attestingIndices.toArray
  let cap := Const.maxValidatorsPerCommittee * Const.maxCommitteesPerSlot
  if idx.size == 0 || idx.size > cap || !strictlySorted idx then false
  else match idx.mapM (fun i => getAt validators i) with
    | .error _ => false
    | .ok attesters =>
      blsFastAggregateVerify (attesters.map (·.pubkey))
        (computeSigningRoot a.data (getDomain state Const.domainBeaconAttester a.data.target.epoch))
        a.signature
-- Attesting-set helper: now inheritable since the Gloas committee layer is in scope
-- (its `getBeaconCommittee` / `getCommitteeIndices` calls bind to the Gloas copies).
inherit getAttestingIndices

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

/-- `is_builder_index` (`gloas/minimal.py:7657-7658`): the `BUILDER_INDEX_FLAG` bit marks a
builder index. `validator_index & BUILDER_INDEX_FLAG` is the same-width `&` of two checked
values, total (`SPEC_ARITHMETIC.md` §5.1). -/
forkdef isBuilderIndex (vi : ValidatorIndex) : Bool := (vi &&& Const.builderIndexFlag) != 0
/-- `convert_validator_index_to_builder_index` (`gloas/minimal.py:7732-7733`):
`BuilderIndex(validator_index & ~BUILDER_INDEX_FLAG)`. `~BUILDER_INDEX_FLAG` is a plain `int`
(`SPEC_ARITHMETIC.md` §3.1), so the `&` is the mixed route with its range test, and the
result is `Checked`. The test never fires on a checked index (`hand_invert_eq` proves the
value), and the `BuilderIndex(...)` cast of that in-range value is the same value. -/
forkdef toBuilderIndex (vi : ValidatorIndex) : Checked BuilderIndex :=
  vi &&& Const.builderIndexFlag.invert
/-- `is_active_builder` (`gloas/minimal.py:7661-7671`). `state.builders[builder_index]` is a
bare list index, so an out-of-range index raises `IndexError` through `getAt`. -/
forkdef isActiveBuilder (state : State) (builderIndex : BuilderIndex) :
    Except StateTransitionError Bool := do
  let builder ← liftErr (getAt state.builders builderIndex)
  pure (builder.depositEpoch < state.finalizedCheckpoint.epoch &&
    builder.withdrawableEpoch == Const.farFutureEpoch)
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
that order. The accumulator is a `Gwei` and each `balance += …amount` is the checked `Gwei`
add (`SPEC_ARITHMETIC.md` §3.2, the `sum` row), so the fold carries its fault. -/
forkdef getPendingBalanceToWithdrawForBuilder (state : State) (builderIndex : BuilderIndex) :
    Checked Gwei := do
  let w ← state.builderPendingWithdrawals.val.foldlM
    (fun acc x => if x.builderIndex == builderIndex then acc + x.amount else pure acc) (0 : Gwei)
  state.builderPendingPayments.toArray.foldlM
    (fun acc p => if p.withdrawal.builderIndex == builderIndex then acc + p.withdrawal.amount else pure acc) w
/-- `builderPaymentIndex`: the ring slot for `slot`'s `BuilderPendingPayment`, given whether
`slot` falls in the *current* epoch (`current = true`) versus the previous one.
`builderPendingPayments` is a `2 * SLOTS_PER_EPOCH` ring whose lower half holds the previous
epoch and whose upper half holds the current epoch, so the index is `slot % SLOTS_PER_EPOCH` with
a `SLOTS_PER_EPOCH` offset added only for the current epoch. The epoch test is the caller's
(`apply_parent_execution_payload` compares `compute_epoch_at_slot`, `process_attestation` keys
off `data.target.epoch`, and `process_execution_payload_bid` always takes the current epoch);
this helper names only the offset arithmetic.

The pinned `SLOTS_PER_EPOCH + slot % SLOTS_PER_EPOCH` is a checked `Uint64` add, and the
structural `Nat` sum here equals it. The add cannot raise: the remainder is below
`SLOTS_PER_EPOCH`, so the sum is below `2 * SLOTS_PER_EPOCH`. The pinned module forms that
product as the `BuilderPendingPayments` length when it loads, so it is below `2^64` on every
preset the pyspec accepts. The `%` takes the proved-total divisor view (`SPEC_ARITHMETIC.md`
§4.2). -/
forkdef builderPaymentIndex (slot : Slot) (current : Bool) : Nat :=
  (if current then Const.slotsPerEpoch else 0) + (slot % Const.slotsPerEpochDiv).toPlainNat
/-- `is_builder_withdrawal_credential`. -/
forkdef isBuilderWithdrawalCredential (wc : Bytes32) : Bool := credPrefix wc == Const.builderWithdrawalPrefix
/-- `is_pending_validator`: among `pendingDeposits`, a deposit for `pubkey` with a
valid proof-of-possession. The queue is passed explicitly so callers can probe the
state's queue (`process_deposit_request`) or an in-progress accumulator
(`onboard_builders_from_pending_deposits`). -/
forkdef isPendingValidator (pendingDeposits : Array PendingDeposit) (pubkey : BLSPubkey) : Bool :=
  pendingDeposits.any fun d =>
    d.pubkey == pubkey && isValidDepositSignature d.pubkey d.withdrawalCredentials d.amount d.signature
/-- `initiate_builder_exit` (`gloas/mainnet.py:7901-7907`). The EL-triggered builder exit,
called by `process_builder_exit_request` (alpha.11 moved builder exits off
`process_voluntary_exit` to this path). Python reads `state.builders[builder_index]`
before the withdrawability sum, so this body reads the builder first, in the pinned
order: the read goes through `sszGetIdx`, so an out-of-range index rejects with
`outOfBounds` (the spec's `IndexError`) before any arithmetic runs. The
`get_current_epoch(state) + MIN_BUILDER_WITHDRAWABILITY_DELAY` sum is the pyspec's
checked `Epoch` addition, so it binds (`SPEC_ARITHMETIC.md` §4.3) and raises past
`2^64 - 1` before the store records it. -/
forkdef initiateBuilderExit (builderIndex : BuilderIndex) : StateTransition Unit := do
  let state ← get
  let _builder ← sszGetIdx state.builders builderIndex
  let epoch := currentEpochOf state
  let withdrawableEpoch ← epoch + Const.minBuilderWithdrawabilityDelay
  -- `toPlainNat`: the raising read above proved `builderIndex` in range for this list.
  modifyState fun state =>
    sszModify state builders[builderIndex.toPlainNat]! as b => { b with withdrawableEpoch := withdrawableEpoch }
/-- `get_index_for_new_builder` (`gloas/minimal.py:8203-8207`): a recyclable slot
(withdrawable + zero balance) or the end. Each return is the `BuilderIndex(...)` cast of a
plain position, the pyspec's checked narrowing, so the result is `Checked`. -/
forkdef getIndexForNewBuilder (state : State) : Checked BuilderIndex := do
  let bs := state.builders.toArray
  let epoch := currentEpochOf state
  for i in [0:bs.size] do
    if (bs[i]?.getD default).withdrawableEpoch ≤ epoch && (bs[i]?.getD default).balance == 0 then
      return ← CLUint64.ofNat? i
  CLUint64.ofNat? bs.size
/-- `withdrawal_credentials[12:]` as a 20-byte execution address. -/
forkdef addressOfCred (wc : Bytes32) : ExecutionAddress := Vector.ofFn (fun i : Fin 20 => wc[12 + i.val])

/-- `add_builder_to_registry` (EIP-8282): set-or-append a `Builder` at the recyclable
index with the supplied `version` / `executionAddress`. -/
forkdef addBuilderToRegistry (pubkey : BLSPubkey) (version : UInt8) (executionAddress : ExecutionAddress)
    (amount : Gwei) (slot : Slot) : StateTransition Unit := do
  let state ← get
  -- `set_or_append_list(state.builders, get_index_for_new_builder(state), Builder(...))`:
  -- the index argument forms first, with its `BuilderIndex(...)` cast.
  let index ← getIndexForNewBuilder state
  let b : Builder :=
    { pubkey, version, executionAddress, balance := amount,
      depositEpoch := computeEpochAtSlot slot, withdrawableEpoch := Const.farFutureEpoch }
  setOrAppendState builders index b
/-- `apply_deposit_for_builder` (retained as a helper; the spec inlines it into
`onboard_builders_from_pending_deposits`): top up an existing builder, or add a new one
with a valid proof-of-possession, stamped `PAYLOAD_BUILDER_VERSION`. -/
forkdef applyDepositForBuilder (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei)
    (sig : BLSSignature) (slot : Slot) : StateTransition Unit := do
  let state ← get
  match state.builders.findIdx? (·.pubkey == pubkey) with
  | some builderIndex =>
      -- `BuilderIndex(builder_pubkeys.index(pubkey))`: the read is in range, because
      -- `findIdx?` returned the position. The cast is omitted and cannot raise: the builder
      -- list is a `ProgressiveList`, and a Lean array holds fewer than `2^61` entries.
      -- `builder.balance += amount`: the checked `Gwei` add, bound here; the store
      -- writes the value the add returned.
      let newBalance ← state.builders[builderIndex]!.balance + amount
      modifyState fun state =>
        sszModify state builders[builderIndex]! as b => { b with balance := newBalance }
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
  let validatorPubkeys := state.validators.map (·.pubkey)
  let mut kept : Array PendingDeposit := #[]

  for d in state.pendingDeposits do
    let state ← get
    let builderPubkeys := state.builders.map (·.pubkey)
    let keep :=
      validatorPubkeys.contains d.pubkey ||
      (!builderPubkeys.contains d.pubkey &&
        (!isBuilderWithdrawalCredential d.withdrawalCredentials || isPendingValidator kept d.pubkey))
    if keep then
      kept := kept.push d
    else
      applyDepositForBuilder d.pubkey d.withdrawalCredentials d.amount d.signature d.slot

  -- `pendingDeposits` is a progressive list at the pin: the kept deposits go back
  -- whole, with no `PENDING_DEPOSITS_LIMIT` cap and no `.listFull` raise.
  let keptList : ProgressiveList PendingDeposit := ⟨kept⟩
  modifyState fun state => { state with pendingDeposits := keptList }

/-- `initialize_ptc_window(state)` (`gloas/fork.md:37-56`): the cached PTC window that seeds
a Gloas state at the fork. The first `SLOTS_PER_EPOCH` entries (the previous epoch, which has
no Gloas PTC) hold zeroed committees; the next `1 + MIN_SEED_LOOKAHEAD` epochs hold
`compute_ptc` for each slot. The window is `(2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH`
long (`MIN_SEED_LOOKAHEAD` is `1`), the `ptc_window` field's declared length.

`upgrade_to_gloas` computes it over the Gloas post-state, with Gloas's own `compute_ptc`.
The registry, balances, and RANDAO mixes the committee reads carry over unchanged from the
Fulu pre-state. Each entry is an `Except` carrying its own faults. The spec's per-entry
`current_epoch + e` (`e` below `1 + MIN_SEED_LOOKAHEAD`) is the checked `Epoch` add, bound
before the entry's `compute_ptc` read. It raises the `.arithmetic` fault past `UINT64_MAX`,
where the pinned `eth-ssz-specs` raises `SSZValueError`, a `ValueError`. The checked
`start_slot + index` binds next, and `compute_ptc` itself rejects a slot with no committee
members.
`completeUpgradeToGloas` maps the entries in index order, so the first rejecting slot
surfaces, matching the spec's list comprehension. -/
forkdef initializePtcWindow (state : State) :
    Vector (Except StateTransitionError (Vector ValidatorIndex Const.ptcSize))
      ((Const.minSeedLookahead.toPlainNat + 2) * Const.slotsPerEpoch) :=
  let currentEpoch := currentEpochOf state
  let emptyCommittee : Vector ValidatorIndex Const.ptcSize := Vector.replicate Const.ptcSize 0
  Vector.ofFn fun i : Fin ((Const.minSeedLookahead.toPlainNat + 2) * Const.slotsPerEpoch) =>
    if i.val < Const.slotsPerEpoch then pure emptyCommittee
    else do
      let j := i.val - Const.slotsPerEpoch
      -- `epoch = current_epoch + e`: the checked `Epoch` add over the plain loop
      -- offset (`e` is `0` or `1`), bound before the entry's `compute_ptc` read
      -- (`SPEC_ARITHMETIC.md` §4.3).
      let epoch ← currentEpoch + (j / Const.slotsPerEpoch)
      let startSlot ← computeStartSlotAtEpoch epoch
      -- `start_slot + index` is the pyspec's checked `Slot` add of a plain `int`,
      -- bound per entry.
      let slot ← startSlot + (j % Const.slotsPerEpoch)
      computePtc state slot

/-- The state-side close of `upgrade_to_gloas` (`gloas/fork.md:227-230`): fill the post-state's
`ptc_window` with `initialize_ptc_window(post)`, then onboard the builders from the pending
deposits. `upgradeToGloas` (`Gloas/Upgrade.lean`) builds the post-state's fields from the Fulu
pre-state; these two steps read and write the Gloas state, so they run on it, in the spec's
order. -/
forkdef completeUpgradeToGloas : StateTransition Unit := do
  let window ← liftErr ((initializePtcWindow (← get)).mapM id)
  modifyState fun state => { state with ptcWindow := window }
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

/-- `process_builder_deposit_request` (EIP-8282): ignore a deposit whose
withdrawal-credential prefix is not the builder prefix. A new pubkey with a valid
proof-of-possession is onboarded at `PAYLOAD_BUILDER_VERSION`. An existing builder
is topped up; if it has exited and its balance is already zero, its withdrawable
epoch is pushed back out before the balance increases. -/
forkdef processBuilderDepositRequest (request : BuilderDepositRequest) : StateTransition Unit := do
  if !isBuilderWithdrawalCredential request.withdrawalCredentials then return
  let state ← get
  match state.builders.findIdx? (·.pubkey == request.pubkey) with
  | none =>
    if isValidBuilderDepositSignature request then
      addBuilderToRegistry request.pubkey Const.payloadBuilderVersion
        (addressOfCred request.withdrawalCredentials) request.amount state.slot
  | some idx =>
    -- `builder_index = BuilderIndex(builder_pubkeys.index(request.pubkey))`: the checked
    -- cast, then the `state.builders[builder_index]` read.
    let builderIndex ← CLUint64.ofNat? idx
    let b ← sszGetIdx state.builders builderIndex
    let epoch := currentEpochOf state
    -- "If exited and swept, reset the withdrawable epoch": the reset sum is the checked
    -- `Epoch` add, formed only in the reset branch and bound there (`SPEC_ARITHMETIC.md`
    -- §4.3); the `balance +=` after it is the checked `Gwei` add, in Python's order.
    let withdrawable ← if b.withdrawableEpoch != Const.farFutureEpoch && b.balance == 0 then
      epoch + Const.minBuilderWithdrawabilityDelay
    else pure b.withdrawableEpoch
    let newBalance ← b.balance + request.amount
    -- `toPlainNat`: the raising read above proved `builderIndex` in range for this list.
    modifyState fun state =>
      sszModify state builders[builderIndex.toPlainNat]! as b =>
        { b with balance := newBalance, withdrawableEpoch := withdrawable }

/-- `process_builder_exit_request` (EIP-8282): an EL-triggered builder exit. A no-op
unless the pubkey names an active builder whose registered execution address matches the
request's `source_address` and that has no pending balance to withdraw; otherwise it
initiates the builder's exit. -/
forkdef processBuilderExitRequest (request : BuilderExitRequest) : StateTransition Unit := do
  let state ← get
  match state.builders.findIdx? (·.pubkey == request.pubkey) with
  | none => pure ()
  | some idx =>
    -- `builder_index = BuilderIndex(builder_pubkeys.index(request.pubkey))`: the checked
    -- cast, then the `state.builders[builder_index]` read (`gloas/minimal.py:8266-8267`).
    let builderIndex ← CLUint64.ofNat? idx
    let builder ← sszGetIdx state.builders builderIndex
    -- Python's gate ladder returns early before the pending balance computes
    -- (`gloas/mainnet.py:8277-8281`), so the checked fold binds only in the
    -- branch that reaches it.
    if !(← liftErr (isActiveBuilder state builderIndex)) then pure ()
    else if builder.executionAddress != request.sourceAddress then pure ()
    else
      let pending ← getPendingBalanceToWithdrawForBuilder state builderIndex
      if pending == 0 then initiateBuilderExit builderIndex else pure ()

/-! ## Attestation (payload-aware) + payload-timeliness committee (EIP-7732) -/

/-- `is_attestation_same_slot`: the attestation votes for the block proposed at its
own slot (head matches this slot's block root but differs from the previous slot's).
The `slot == 0` guard avoids the `slot - 1` underflow, the pyspec's checked subtraction,
so the previous slot binds in the branch Python forms it. -/
forkdef isAttestationSameSlot (state : State) (data : AttestationData) : StateTransition Bool := do
  if data.slot == 0 then pure true
  else
    let blockroot := data.beaconBlockRoot
    let slotRoot ← getBlockRootAtSlot state data.slot
    let prevSlot ← data.slot - 1
    let prevRoot ← getBlockRootAtSlot state prevSlot
    pure (blockroot == slotRoot && blockroot != prevRoot)

/-- `get_attestation_participation_flag_indices` (Gloas, EIP-7732,
`gloas/beacon-chain.md:1339-1386`): adds the payload-matching constraint to `is_matching_head`.
A same-slot attestation must have `data.index == 0` (a second reject, surfaced as `none`);
otherwise `payload_matches` compares `data.index` to the `execution_payload_availability`
bit at `parent_slot`. `none` also covers the `assert is_matching_source` reject (as in Fulu).

v1.7.0-beta.4 adds the `parent_slot` parameter, the slot of the parent of the block being
processed, and reads the payload bit there rather than at `data.slot`. The timely head flag
needs both the minimum inclusion delay and a head root that matches the block root at the
attestation slot, so only an attestation to the parent block can earn it, and the parent's
payload availability is recorded at `parent_slot` even when `data.slot` is a skipped slot.

The pinned body (`gloas/minimal.py:5123-5142`) performs every read before
`assert is_matching_source`: the target root, the same-slot check with its
`assert data.index == 0`, the payload bit, and the head root. Near the maximum slot the
target-root read raises the uncaught range fault (`slot + SLOTS_PER_HISTORICAL_ROOT`
overflows). So the source check comes last, and a mismatched source cannot turn that fault
into the caught assert (`SPEC_ARITHMETIC.md` §1). -/
forkdef getAttestationParticipationFlagIndices (state : State) (data : AttestationData)
    (inclusionDelay : Slot) (parentSlot : Slot) : StateTransition (Option (Array CLUint64)) := do
  let justified := if data.target.epoch == currentEpochOf state then state.currentJustifiedCheckpoint
                   else state.previousJustifiedCheckpoint
  let isMatchingSource := data.source.epoch == justified.epoch && data.source.root == justified.root

  let targetRoot ← getBlockRoot state data.target.epoch
  let isMatchingTarget := data.target.root == targetRoot
  let sameSlot ← isAttestationSameSlot state data
  if sameSlot && data.index != 0 then return none
  -- The payload-availability bit sits at `parent_slot % SLOTS_PER_HISTORICAL_ROOT`: the
  -- checked slot reduces by the proved-total divisor view and narrows to the structural
  -- bit index (`SPEC_ARITHMETIC.md` §4.2, §4.5).
  let payloadMatches : Bool :=
    if sameSlot then true
    else
      let bit := bitGet state.executionPayloadAvailability
        (parentSlot % Const.slotsPerHistoricalRootDiv).toPlainNat
      -- `Uint64(data.index) == Uint64(payload_index)`: the bit casts to `0` or `1`.
      data.index == (if bit then (1 : CommitteeIndex) else 0)
  let headRoot ← getBlockRootAtSlot state data.slot
  let isMatchingHead := isMatchingTarget && data.beaconBlockRoot == headRoot && payloadMatches
  if !isMatchingSource then return none

  -- The returned list holds the pinned checked constants (`TIMELY_*_FLAG_INDEX` =
  -- `Uint64(0..2)`); its only consumer is the value-equality `in` test of
  -- `process_attestation`, a total comparison.
  let mut flags : Array CLUint64 := #[]
  -- The comparisons never raise in Python. `integer_squareroot(SLOTS_PER_EPOCH)` is the
  -- total checked-kind root, so both bounds meet the delay in the checked kind.
  if inclusionDelay ≤ Const.slotsPerEpochC.integerSquareroot then flags := flags.push Const.timelySourceFlagIndex
  if isMatchingTarget then flags := flags.push Const.timelyTargetFlagIndex
  if isMatchingHead && inclusionDelay == Const.minAttestationInclusionDelay then flags := flags.push Const.timelyHeadFlagIndex
  return some flags

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
  -- `data.slot + MIN_ATTESTATION_INCLUSION_DELAY`: `data.slot` is wire-controlled, so the
  -- checked `Slot` add can raise at the maximum, the state-transition twin of
  -- `on_attestation`'s. pyspec's checked `uint64` add raises `SSZValueError`, a `ValueError`
  -- that `expect_assertion_error` does not catch, so the `.arithmetic` reject classifies as
  -- `uncaughtFault`. The add binds after the two epoch asserts above, in Python's evaluation
  -- order, and before the inclusion-slot assert.
  let inclusionSlot ← data.slot + Const.minAttestationInclusionDelay
  assert (inclusionSlot ≤ state.slot)
  assert (data.index < 2)

  -- Every committee index is valid and non-empty; the bitfield covers them all.
  let (ok, offset) ← liftErr (verifyCommitteeCoverage state data att)
  assert ok
  assert (att.aggregationBits.size == offset)

  -- Resolve the participation flags, then validate the aggregate signature. The
  -- inclusion delay is the pyspec's checked `state.slot - data.slot`, bound at the
  -- argument position Python evaluates it.
  let inclusionDelay ← state.slot - data.slot
  let flagIndices ← match ← getAttestationParticipationFlagIndices state data inclusionDelay parentSlot with
    | some f => pure f
    | none   => throw (StateTransitionError.assert "attestation participation flags")
  let indexedAttestation : IndexedAttestation :=
    { attestingIndices := ⟨(← liftErr (getAttestingIndices state att)).qsort (· < ·)⟩,
      data := att.data, signature := att.signature }
  assert (isValidIndexedAttestation state indexedAttestation)

  -- Apply participation flags and accumulate the builder-payment weight.
  let currentTarget := data.target.epoch == currentEpochOf state
  -- Python calls `is_attestation_same_slot` inside the per-validator `and`, so it can run
  -- zero or many times. This bind runs it once. The move cannot add a fault:
  -- `get_attestation_participation_flag_indices` above already ran the same call on the same
  -- `state` and `data`, and the flag writes leave `slot` and `block_roots` unchanged.
  let sameSlot ← isAttestationSameSlot state data
  let paymentIdx := builderPaymentIndex data.slot currentTarget
  let payment0 := vget state.builderPendingPayments paymentIdx
  let mut stateAcc := state
  -- `proposer_reward_numerator = 0` starts plain; the first
  -- `get_base_reward(state, index) * weight` makes it a `Gwei`, and each `+=` after
  -- that is the checked `Gwei` add (`SPEC_ARITHMETIC.md` §3.2, the `sum` row).
  let mut proposerNum : Gwei := 0
  let mut weight := payment0.weight
  for vi in (← liftErr (getAttestingIndices state att)) do
    -- `vi` is a data-derived attesting-validator index; read the participation flag
    -- through `sszGetIdx` so an out-of-range index rejects with `outOfBounds` rather
    -- than masking as a default flag (the matching `[i]!` writes are then in range).
    -- [New in Gloas:EIP7732] the flags this validator held before this attestation:
    -- `epoch_participation[index] == 0b0000_0000`, a total value comparison.
    let flags0 ← if currentTarget then sszGetIdx stateAcc.currentEpochParticipation vi
                 else sszGetIdx stateAcc.previousEpochParticipation vi
    -- `toPlainNat`: the raising read above proved `vi` in range for this list.
    let i := vi.toPlainNat
    let hadNoParticipation := flags0 == 0
    let mut willSet := false
    for flagIndex in [0:3] do
      -- `flag_index in participation_flag_indices and not has_flag(...)` (`gloas/minimal.py`,
      -- `process_attestation`): the `and` short-circuits, so the flag read forms only for a
      -- flag the attestation earns. The `in` compares a plain enumerate index against the
      -- checked constants by value, a total comparison, so the membership reads the
      -- elements' plain values.
      if !flagIndices.any (·.toPlainNat == flagIndex) then continue
      let flag ← if currentTarget then sszGetIdx stateAcc.currentEpochParticipation vi
                 else sszGetIdx stateAcc.previousEpochParticipation vi
      -- `not has_flag(...)`: the mask `ParticipationFlags(2**flag_index)` raises past
      -- flag index 7, so the test binds (`SPEC_ARITHMETIC.md` §5.1).
      if !(← CLUint8.hasFlag flag flagIndex) then
        -- `add_flag`'s mask raises past flag index 7; the write stores the bound value,
        -- as Python assigns the `add_flag(...)` result.
        let flag' ← CLUint8.addFlag flag flagIndex
        stateAcc := if currentTarget then
                   { stateAcc with currentEpochParticipation := stateAcc.currentEpochParticipation.set! i flag' }
                 else
                   { stateAcc with previousEpochParticipation := stateAcc.previousEpochParticipation.set! i flag' }
        let base ← liftErr (getBaseReward state vi)
        let weighted ← base * Const.participationFlagWeights[flagIndex]!
        proposerNum := ← proposerNum + weighted
        willSet := true
    if willSet && hadNoParticipation && sameSlot && payment0.withdrawal.amount > 0 then
      let attester ← sszGetIdx state.validators vi
      weight := ← weight + attester.effectiveBalance

  -- Reward the proposer, then write back the (possibly weight-updated) payment, which the
  -- spec does unconditionally and in this order. The denominator
  -- `(WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR // PROPOSER_WEIGHT`
  -- is checked arithmetic at the pin (every operand a `Uint64` constant), so the chain
  -- binds; the shipped values cannot leave range, and the mixed `Gwei / CLUint64`
  -- division carries the checked raise.
  let proposerDenom ← (Const.weightDenominator - Const.proposerWeight) * Const.weightDenominator / Const.proposerWeight
  let proposerReward ← proposerNum / proposerDenom
  stateAcc ← increaseBalance stateAcc (getBeaconProposerIndex stateAcc) proposerReward
  stateAcc := { stateAcc with builderPendingPayments := stateAcc.builderPendingPayments.set! paymentIdx { payment0 with weight := weight } }
  set stateAcc
where
  /-- Walk the committee bits: each referenced committee index is in range and
  attested by at least one bit, and the running `offset` totals their sizes (the
  aggregation bitfield must match it exactly). Returns `(valid?, totalSize)`.
  Python's per-index `assert` (`gloas/minimal.py:2614-2623`) aborts at the first
  failure, so the walk stops there and no later `get_beacon_committee` fault can
  preempt the assertion (`SPEC_ARITHMETIC.md` §1, the failure point). The range assert
  forms `get_committee_count_per_slot` per index, as the pinned loop does. The attester
  set reads `attestation.aggregation_bits[committee_offset + index]` for every member
  before its assert, and a read past the bit list's end raises `IndexError`, so each
  read goes through `getAt`. -/
  verifyCommitteeCoverage (state : State) (data : AttestationData) (att : Attestation) :
      Except StateTransitionError (Bool × Nat) := do
    let committeeIndices ← getCommitteeIndices att.committeeBits
    committeeIndices.foldlM
      (fun (acc : Bool × Nat) ci => do
        let (okAcc, off) := acc
        if !okAcc then pure acc
        else
        let count ← getCommitteeCountPerSlot state data.target.epoch
        -- `committee_index < get_committee_count_per_slot(...)`: two `Uint64` values, a
        -- comparison, which never raises.
        if ci ≥ count then pure (false, off)
        else do
          let committee ← getBeaconCommittee state data.slot ci
          let attesters ← (List.range committee.size).foldlM
            (fun (a : Nat) i => do
              let bit ← liftErr (getAt att.aggregationBits (off + i))
              pure (if bit then a + 1 else a)) 0
          pure (attesters > 0, off + committee.size))
      (true, 0)

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
the else branch's `epoch - state_epoch` is at most `MIN_SEED_LOOKAHEAD`, so the scaled offset
is at most `MIN_SEED_LOOKAHEAD + 1` epochs, and the read lands inside the
`(MIN_SEED_LOOKAHEAD + 2) * SLOTS_PER_EPOCH` window by construction. That is why the total `vget` is sound once the asserts are in place, and why the
spec's own `IndexError` on this subscript is unreachable rather than unmodeled. Throwing, so
`get_indexed_payload_attestation` and the fork-choice handler bind it. -/
forkdef getPtc (state : State) (slot : Slot) :
    StateTransition (Vector ValidatorIndex Const.ptcSize) := do
  let epoch := computeEpochAtSlot slot
  assert (epoch ≥ Const.gloasForkEpoch)
  let stateEpoch := currentEpochOf state
  if epoch < stateEpoch then
    -- `epoch + 1 == state_epoch`: the checked `Epoch` add, bound before its assert
    -- (`SPEC_ARITHMETIC.md` §4.3).
    let nextEpoch ← epoch + 1
    assert (nextEpoch == stateEpoch)
    -- The window index `slot % SLOTS_PER_EPOCH` passes the checked slot's word to the
    -- proved-total `vmodGet` route, whose bound is the mod itself (§4.5). The window
    -- length is the preset product, so the call passes the `d ≤ n` bound: `1 ≤
    -- MIN_SEED_LOOKAHEAD + 2`.
    pure (vmodGet state.ptcWindow slot.val Const.slotsPerEpoch
      (hle := Nat.le_mul_of_pos_left Const.slotsPerEpoch
        (Nat.succ_pos (Const.minSeedLookahead.toPlainNat + 1))))
  else
    -- `epoch <= state_epoch + MIN_SEED_LOOKAHEAD`: the checked `Epoch` add.
    let lookaheadBound ← stateEpoch + Const.minSeedLookahead
    assert (epoch ≤ lookaheadBound)
    -- `Uint64(epoch - state_epoch + 1) * SLOTS_PER_EPOCH + slot % SLOTS_PER_EPOCH`: each
    -- step binds. The `Uint64(...)` cast strips the epoch unit, so the product keeps the
    -- `Slot` unit and the index sum is the checked `Slot` add (§3.4). The `slot %
    -- SLOTS_PER_EPOCH` remainder takes the proved-total divisor view (§4.2).
    let diff ← epoch - stateEpoch
    let offset ← diff + 1
    let scaled ← offset * Const.slotsPerEpochC
    let slotIdx := slot % Const.slotsPerEpochDiv
    let idx ← scaled + slotIdx
    pure (vget state.ptcWindow idx.toPlainNat)

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
(the PTC can repeat a validator), in range, with a valid `DOMAIN_PTC_ATTESTER`
aggregate signature over the `PayloadAttestationData`. -/
forkdef isValidIndexedPayloadAttestation (state : State) (a : IndexedPayloadAttestation) : Bool :=
  let idx := a.attestingIndices.toArray
  let nonStrictSorted := (Array.range (idx.size - 1)).all (fun i => idx[i]?.getD default ≤ idx[i+1]?.getD default)
  if idx.size == 0 || !nonStrictSorted then false
  else
    let validators := state.validators
    -- The pyspec's pubkey read `state.validators[i]` raises `IndexError` past the registry.
    -- The range test returns `false` there, and the caller's `assert` raises the assert
    -- class; the runner catches both. The reads after the test are in range by it
    -- (`SPEC_ARITHMETIC.md` §6, a test before the operation). The characterization
    -- theorem reads this form directly.
    if !idx.all (·.toPlainNat < validators.size) then false
    else
      let pubkeys := idx.map (fun i => (validators[i.toPlainNat]!).pubkey)
      blsFastAggregateVerify pubkeys
        (computeSigningRoot a.data (getDomain state Const.domainPtcAttester (computeEpochAtSlot a.data.slot)))
        a.signature

/-- `process_payload_attestation` (NEW, EIP-7732): the attestation is for the parent
block and the previous slot, with a valid indexed signature. Pure validation, no
state change on success. -/
forkdef processPayloadAttestation (pa : PayloadAttestation) : StateTransition Unit := do
  let state ← get
  let data := pa.data
  assert (data.beaconBlockRoot == state.latestBlockHeader.parentRoot)
  -- pyspec's `data.slot + 1` is a checked `uint64` add, bound here before its assert. At
  -- `data.slot = UINT64_MAX` it raises the `.arithmetic` range fault, as Python raises
  -- `SSZValueError`, a `ValueError` that `expect_assertion_error` does not catch, so the
  -- reject classifies as `uncaughtFault`.
  let attestedSlot ← data.slot + 1
  assert (attestedSlot == state.slot)
  -- The bind stays after the slot assert: that assert is what bounds `get_ptc`'s index, and the
  -- spec's order is `beacon_block_root`, then `data.slot + 1 == state.slot`, then the indexed
  -- signature check.
  let indexed ← getIndexedPayloadAttestation state pa
  assert (isValidIndexedPayloadAttestation state indexed)

/-! ## Execution payload bid + parent-payload application (EIP-7732) -/

/-- `convert_builder_index_to_validator_index` (`gloas/minimal.py:7728-7729`): set the
`BUILDER_INDEX_FLAG` bit, `ValidatorIndex(builder_index | BUILDER_INDEX_FLAG)`. The `|` of two
checked values is the total same-width route (`SPEC_ARITHMETIC.md` §5.1), and the
`ValidatorIndex(...)` cast of that in-range value is the same value. -/
forkdef convertBuilderIndexToValidatorIndex (builderIndex : BuilderIndex) : ValidatorIndex :=
  builderIndex ||| Const.builderIndexFlag

/-- `can_builder_cover_bid` (`gloas/mainnet.py:7767-7775`): the builder's balance,
after reserving `MIN_DEPOSIT_AMOUNT` plus its already-pending withdrawals, covers
the bid value. `state.builders[builder_index]` is a bare list index, so an
out-of-range index raises `IndexError` through `getAt`. The pending sum, the reserve
add, and the cover subtraction are the checked `Gwei` chain, each bound where the
pyspec forms it. -/
forkdef canBuilderCoverBid (state : State) (builderIndex : BuilderIndex) (bidAmount : Gwei) :
    Except StateTransitionError Bool := do
  let builder ← liftErr (getAt state.builders builderIndex)
  let builderBalance := builder.balance
  let pending ← getPendingBalanceToWithdrawForBuilder state builderIndex
  let minBalance ← Const.minDepositAmountG + pending
  if builderBalance < minBalance then pure false
  else
    let cover ← builderBalance - minBalance
    pure (cover ≥ bidAmount)

/-- `verify_execution_payload_bid_signature` (`gloas/minimal.py:8126-8133`): the bid is
signed by the builder's key under `DOMAIN_BEACON_BUILDER` at the current epoch.
`state.builders[signed_bid.message.builder_index]` is a bare list index, so an out-of-range
index raises `IndexError` through `getAt`. -/
forkdef verifyExecutionPayloadBidSignature (state : State) (signedBid : SignedExecutionPayloadBid) :
    Except StateTransitionError Bool := do
  let builder ← liftErr (getAt state.builders signedBid.message.builderIndex)
  pure (blsVerifySigned builder.pubkey signedBid.message
    (getDomain state Const.domainBeaconBuilder (currentEpochOf state)) signedBid.signature)

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
      let validatorIndex := state.latestBlockHeader.proposerIndex
      let v ← sszGetIdx state.validators validatorIndex
      pure v.pubkey
    else do
      let b ← sszGetIdx state.builders builderIndex
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
  let payment := vget state.builderPendingPayments paymentIndex

  if payment.withdrawal.amount > 0 then
    appendState builderPendingWithdrawals payment.withdrawal

  let empty : BuilderPendingPayment := default
  modifyState fun state =>
    { state with builderPendingPayments := state.builderPendingPayments.set! paymentIndex empty }

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
    -- Each gate reads `state.builders[builder_index]`, a bare list index that raises
    -- `IndexError` out of range; the first read, inside `is_active_builder`, raises first.
    assert (← liftErr (isActiveBuilder state builderIndex))
    let builder ← sszGetIdx state.builders builderIndex
    assert (builder.version == Const.payloadBuilderVersion)
    assert (← liftErr (canBuilderCoverBid state builderIndex amount))
    assert (← liftErr (verifyExecutionPayloadBidSignature state signedBid))

  -- The plain `len(...)` against the plain blob limit: a comparison, which never raises.
  assert (len bid.blobKzgCommitments ≤ (getBlobParameters (currentEpochOf state)).maxBlobsPerBlock)
  assert (bid.slot == state.slot)
  assert (state.slot > Const.genesisSlot)
  assert (bid.parentBlockHash == state.latestBlockHash)
  -- [New at v1.7.0-beta.4] the bid's block hash must differ from its parent's.
  assert (bid.blockHash != bid.parentBlockHash)
  -- `get_block_root_at_slot(state, state.slot - 1)`: the checked subtraction binds at the
  -- argument position Python evaluates it.
  let prevSlot ← state.slot - 1
  let parentBlockRoot ← getBlockRootAtSlot state prevSlot
  assert (bid.parentBlockRoot == parentBlockRoot)
  let randaoMix ← getRandaoMix (currentEpochOf state)
  assert (bid.prevRandao == randaoMix)

  if amount > 0 then
    let pending : BuilderPendingPayment :=
      { weight := 0,
        withdrawal := { feeRecipient := bid.feeRecipient, amount := amount, builderIndex := builderIndex },
        proposerIndex := getBeaconProposerIndex state }
    modifyState fun state =>
      { state with builderPendingPayments := state.builderPendingPayments.set! (builderPaymentIndex bid.slot true) pending }

  modifyState fun state => { state with latestExecutionPayloadBid := bid }

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
  let parentBid := state.latestExecutionPayloadBid
  let parentSlot := state.latestBlockHeader.slot
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

  -- The availability bit sits at `parent_slot % SLOTS_PER_HISTORICAL_ROOT`: the checked
  -- slot reduces by the proved-total divisor view and narrows to the structural bit index
  -- (`SPEC_ARITHMETIC.md` §4.2, §4.5).
  modifyState fun state => { state with executionPayloadAvailability :=
    (bitSet state.executionPayloadAvailability
      (parentSlot % Const.slotsPerHistoricalRootDiv).toPlainNat true) }
  modifyState fun state => { state with latestBlockHash := parentBid.blockHash }

/-- `process_parent_execution_payload` (NEW, EIP-7732): if the bid's parent hash does
not match the cached bid, the parent was empty (no requests expected); otherwise the
parent was full, so verify the requests commitment and apply them. -/
forkdef processParentExecutionPayload (block : BeaconBlock) : StateTransition Unit := do
  let state ← get
  let bid := block.body.signedExecutionPayloadBid.message
  let parentBid := state.latestExecutionPayloadBid
  let requests := block.body.parentExecutionRequests
  if bid.parentBlockHash != parentBid.blockHash then
    assert (htr requests == htr (default : ExecutionRequests))
  else
    assert (htr requests == parentBid.executionRequestsRoot)
    applyParentExecutionPayload requests

end

end EthCLSpecs.Gloas
