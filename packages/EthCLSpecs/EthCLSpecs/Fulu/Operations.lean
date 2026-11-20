import EthCLSpecs.Fulu.Deposits
import EthCLSpecs.Fulu.Blocks

/-!
# `EthCLSpecs.Fulu.Operations`: `process_operations` and the per-operation steps

The block-operation pipeline: proposer / attester slashings, attestations (with
participation-flag accounting and the proposer reward), deposits, voluntary exits,
BLS-to-execution changes, and the Electra execution requests (deposit / withdrawal
/ consolidation). Signature checks go through the `[CryptoBackend]` seam; the
deposit Merkle branch is checked against `eth1_data.deposit_root`.

Each `assert` is an expected rejection: an invalid vector hits one and the harness
classifies it as a faithful reject. Input-controlled indices are bounds-guarded
(`assert idx < size`) so an out-of-range read rejects the way the pyspec's
`IndexError` does, never panicking.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-! ## Attestation validity predicates -/

/-- A strictly-increasing index array (so the indices are sorted and unique). -/
forkdef strictlySorted (a : Array ValidatorIndex) : Bool := Id.run do
  let mut ok := true
  for i in [0:a.size] do
    if i + 1 < a.size && !(a[i]! < a[i+1]!) then ok := false
  return ok

/-- `is_slashable_attestation_data`: a double vote (same target epoch, different
data) or a surround vote. -/
forkdef isSlashableAttestationData (d1 d2 : AttestationData) : Bool :=
  (htr d1 != htr d2 && d1.target.epoch == d2.target.epoch) ||
  (d1.source.epoch < d2.source.epoch && d2.target.epoch < d1.target.epoch)

/-- `is_valid_indexed_attestation`: non-empty, sorted-unique indices in range, and a
valid aggregate signature (through the `[CryptoBackend]` seam). The pyspec's pubkey read
`state.validators[i]` raises `IndexError` for an index past the registry. This body is a
pure `Bool`, so it returns `false` there, and the caller's `assert` raises the assert class.
The runner catches both classes, so the vector outcome agrees. The pubkey reads go through
`getAt`, so the range test is the size-aware index interface's own. -/
forkdef isValidIndexedAttestation (state : State) (a : IndexedAttestation) : Bool :=
  let validators := sszGet state validators
  let idx := a.attestingIndices.toArray
  if idx.size == 0 || !strictlySorted idx then false
  else match idx.mapM (fun i => getAt validators i) with
    | .error _ => false
    | .ok attesters =>
      blsFastAggregateVerify (attesters.map (·.pubkey))
        (computeSigningRoot a.data (getDomain state Const.domainBeaconAttester a.data.target.epoch))
        a.signature

/-! ## Slashings -/

/-- `process_proposer_slashing`. -/
forkdef processProposerSlashing (ps : ProposerSlashing) : StateTransition Unit := do
  let state ← get
  let h1 := ps.signedHeader1.message
  let h2 := ps.signedHeader2.message

  assert (h1.slot == h2.slot)
  assert (h1.proposerIndex == h2.proposerIndex)
  assert (htr h1 != htr h2)

  -- `proposer = state.validators[header_1.proposer_index]` (`fulu/minimal.py:2008`): a
  -- raising list read, so an out-of-range proposer rejects with `IndexError`'s class.
  let proposer ← sszGetIdx (sszGet state validators) h1.proposerIndex
  assert (isSlashableValidator proposer (currentEpochOf state))
  assert (blsVerifySigned proposer.pubkey h1
    (getDomain state Const.domainBeaconProposer (computeEpochAtSlot h1.slot)) ps.signedHeader1.signature)
  assert (blsVerifySigned proposer.pubkey h2
    (getDomain state Const.domainBeaconProposer (computeEpochAtSlot h2.slot)) ps.signedHeader2.signature)

  slashValidator h1.proposerIndex

/-- `process_attester_slashing`. -/
forkdef processAttesterSlashing (asl : AttesterSlashing) : StateTransition Unit := do
  let state ← get
  assert (isSlashableAttestationData asl.attestation1.data asl.attestation2.data)
  assert (isValidIndexedAttestation state asl.attestation1)
  assert (isValidIndexedAttestation state asl.attestation2)

  let set2 := asl.attestation2.attestingIndices.toArray
  let indices := (arrayInter asl.attestation1.attestingIndices.toArray set2).qsort (· < ·)

  let mut slashedAny := false
  for idx in indices do
    let state ← get
    -- `state.validators[index]`: a raising list read.
    let validator ← sszGetIdx (sszGet state validators) idx
    if isSlashableValidator validator (currentEpochOf state) then
      slashValidator idx
      slashedAny := true
  assert slashedAny

/-! ## Attestations -/

/-- `get_attestation_participation_flag_indices`. Returns `none` for the
`is_matching_source` assertion (a valid attestation always matches source), so the
caller rejects; `some flags` otherwise. `inclusionDelay` is the pyspec's
`state.slot - data.slot` checked difference, a `Slot`; the comparisons never raise in
Python. `integer_squareroot(SLOTS_PER_EPOCH)` is the total checked-kind root
(`CLUint64.integerSquareroot`), so both bounds meet the delay in the checked kind.
The returned list holds the pinned checked constants (`TIMELY_*_FLAG_INDEX` =
`Uint64(0..2)`, `fulu/minimal.py:138-140`); its only consumer is the value-equality
`in` test of `process_attestation`, a total comparison.

The pinned body (`fulu/minimal.py:4414-4423`) reads the target root and the head root
before `assert is_matching_source`. Both reads can raise the uncaught range fault: near the
maximum slot, `get_block_root_at_slot`'s `slot + SLOTS_PER_HISTORICAL_ROOT` overflows. So
the reads bind first and the source check comes last, and a mismatched source cannot turn
that fault into the caught assert (`SPEC_ARITHMETIC.md` §1). -/
forkdef getAttestationParticipationFlagIndices (state : State) (data : AttestationData)
    (inclusionDelay : Slot) : StateTransition (Option (Array CLUint64)) := do
  let justified := if data.target.epoch == currentEpochOf state then sszGet state currentJustifiedCheckpoint
                   else sszGet state previousJustifiedCheckpoint
  let isMatchingSource := data.source.epoch == justified.epoch && data.source.root == justified.root
  let targetRoot ← getBlockRoot state data.target.epoch
  let isMatchingTarget := data.target.root == targetRoot
  let headRoot ← getBlockRootAtSlot state data.slot
  let isMatchingHead := isMatchingTarget && data.beaconBlockRoot == headRoot
  if !isMatchingSource then return none

  let mut flags : Array CLUint64 := #[]
  if inclusionDelay ≤ Const.slotsPerEpochC.integerSquareroot then flags := flags.push Const.timelySourceFlagIndex
  if isMatchingTarget then flags := flags.push Const.timelyTargetFlagIndex
  if isMatchingHead && inclusionDelay == Const.minAttestationInclusionDelay then flags := flags.push Const.timelyHeadFlagIndex
  return some flags

/-- `get_attesting_indices`: the validators flagged across the slot's committees. Returns
`Except StateTransitionError` on both faults it can hit (`SPEC_ARITHMETIC.md` §4.6: a
mixed fallible helper uses the common typed error channel): the block-supplied
`aggregation_bits` is read at a committee offset it does not bound, so an over-length read
rejects `IndexError`-shaped rather than masking to `false`, and each `getBeaconCommittee`
carries the seed walk's checked `Epoch` chain. The `committee[i]` read stays total, `i` is
bounded by the committee it just built. -/
forkdef getAttestingIndices (state : State) (att : Attestation) :
    Except StateTransitionError (Array ValidatorIndex) := do
  let mut out : Array ValidatorIndex := #[]
  let mut offset := 0
  for ci in ← getCommitteeIndices att.committeeBits do
    let committee ← getBeaconCommittee state att.data.slot ci
    for i in [0:committee.size] do
      if (← bitlistGetIdx att.aggregationBits (offset + i)) then out := out.push committee[i]!
    offset := offset + committee.size
  return out

/-- `process_attestation`. -/
forkdef processAttestation (att : Attestation) : StateTransition Unit := do
  let state ← get
  let data := att.data

  -- Reject on shape: target epoch, slot timing, and the committee index bound.
  assert (data.target.epoch == previousEpochOf state || data.target.epoch == currentEpochOf state)
  assert (data.target.epoch == computeEpochAtSlot data.slot)
  -- `data.slot` is wire-controlled and `MIN_ATTESTATION_INCLUSION_DELAY` is 1, so the checked
  -- add raises past the maximum where a bare `+` would wrap `0xFFFF…FFFF + 1` to `0` and
  -- `0 ≤ state.slot` would bypass the guard for every state: a false ACCEPT, the
  -- state-transition twin of `on_attestation`'s. pyspec's checked `uint64` add raises
  -- `ValueError`, which `process_attestation` does not catch, so the driver scores it
  -- `uncaughtFault`. Sequenced after the two epoch asserts above, matching Python's order.
  let inclusionSlot ← data.slot + Const.minAttestationInclusionDelay
  assert (inclusionSlot ≤ sszGet state slot)
  assert (data.index == 0)

  -- Every committee index is valid and contributes at least one attester; the
  -- aggregation bitfield length matches the total committee size.
  let (ok, offset) ← liftErr (verifyCommitteeCoverage state data)
  assert ok
  assert (att.aggregationBits.size == offset)

  -- Resolve the participation flags, then validate the aggregate signature. The
  -- inclusion delay is the pyspec's checked `state.slot - data.slot`, bound at the
  -- argument position Python evaluates it.
  let inclusionDelay ← (sszGet state slot) - data.slot
  let flagIndices ← match ← getAttestationParticipationFlagIndices state data inclusionDelay with
    | some f => pure f
    | none   => throw (StateTransitionError.assert "is_matching_source")
  let indexedAttestation : IndexedAttestation :=
    { attestingIndices := ← sszOfArrayM "attestingIndices"
        ((← liftErr (getAttestingIndices state att)).qsort (· < ·)),
      data := att.data, signature := att.signature }
  assert (isValidIndexedAttestation state indexedAttestation)

  -- Apply participation flags and accumulate the proposer-reward numerator.
  let currentTarget := data.target.epoch == currentEpochOf state
  let mut stateAcc := state
  -- `proposer_reward_numerator = 0` starts plain; the first
  -- `get_base_reward(state, index) * weight` makes it a `Gwei`, and each `+=` after
  -- that is the checked `Gwei` add (`SPEC_ARITHMETIC.md` §3.2, the `sum` row).
  let mut proposerNum : Gwei := 0
  for vi in ← liftErr (getAttestingIndices state att) do
    for flagIndex in [0:3] do
      -- `flag_index in participation_flag_indices and not has_flag(epoch_participation[index],
      -- flag_index)` (`fulu/minimal.py:2081-2084`): the `and` short-circuits, so the flag read
      -- forms only for a flag the attestation earns. The `in` compares a plain enumerate
      -- index against the checked constants by value — a total comparison (`BaseUint.__eq__`
      -- admits a bare integer) — so the membership reads the elements' plain values.
      -- `vi` is a data-derived attesting-validator index; the read goes through
      -- `sszGetIdx` so an out-of-range index rejects with `outOfBounds` rather than
      -- masking as a default flag.
      if !flagIndices.any (·.toPlainNat == flagIndex) then continue
      let flag ← if currentTarget then sszGetIdx (sszGet stateAcc currentEpochParticipation) vi
                 else sszGetIdx (sszGet stateAcc previousEpochParticipation) vi
      -- `not has_flag(...)`: the mask `ParticipationFlags(2**flag_index)` raises past
      -- flag index 7, so the test binds (`SPEC_ARITHMETIC.md` §5.1).
      if !(← CLUint8.hasFlag flag flagIndex) then
        -- `toPlainNat`: the raising read above proved `vi` in range for this list.
        let i := vi.toPlainNat
        -- `add_flag`'s mask raises past flag index 7; the write stores the bound value,
        -- as Python assigns the `add_flag(...)` result.
        let flag' ← CLUint8.addFlag flag flagIndex
        stateAcc := if currentTarget then
                   sszUpdate stateAcc with currentEpochParticipation[i]! := flag'
                 else
                   sszUpdate stateAcc with previousEpochParticipation[i]! := flag'
        let base ← liftErr (getBaseReward state vi)
        let weighted ← base * Const.participationFlagWeights[flagIndex]!
        proposerNum := ← proposerNum + weighted

  -- Pay the proposer the accumulated weight. The denominator
  -- `(WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR // PROPOSER_WEIGHT`
  -- is checked arithmetic at the pin (every operand a `Uint64` constant), so the chain
  -- binds; the shipped values cannot leave range, and the mixed `Gwei / CLUint64`
  -- division carries the checked raise.
  let proposerDenom ← (Const.weightDenominator - Const.proposerWeight) * Const.weightDenominator / Const.proposerWeight
  let proposerReward ← proposerNum / proposerDenom
  stateAcc ← increaseBalance stateAcc (getBeaconProposerIndex stateAcc) proposerReward
  set stateAcc
where
  /-- Fold over the attestation's committee indices: each must be below `count` and
  contribute at least one attester. Returns `(allValid, totalCommitteeSize)`.

  The pinned loop (`fulu/minimal.py:2051-2060`) checks each index in this order: the
  range assert, then `get_beacon_committee`, then the attester assert. A failed assert
  aborts the loop. So the fold stops at the first failed check, and no later
  `get_beacon_committee` fault can preempt the caught assert (`SPEC_ARITHMETIC.md` §1,
  the failure point). The range assert forms `get_committee_count_per_slot` per index, as
  the pinned loop does, so its active-set casts run only when an index exists. The
  attester set reads `attestation.aggregation_bits[committee_offset + index]` for every
  member before its assert, and a read past the bit list's end raises `IndexError`, so
  each read goes through `getAt`. -/
  verifyCommitteeCoverage (state : State) (data : AttestationData) :
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

/-! ## Deposits -/

/-- `apply_deposit`: a new pubkey is added only with a valid proof-of-possession;
either way (existing, or freshly added) the amount is queued as a pending deposit. -/
forkdef applyDeposit (pubkey : BLSPubkey) (wc : Bytes32) (amount : Gwei) (sig : BLSSignature) :
    StateTransition Unit := do
  let state ← get
  let pendingDeposit : PendingDeposit :=
    { pubkey, withdrawalCredentials := wc, amount, signature := sig, slot := Const.genesisSlot }
  if (sszGet state validators).any (·.pubkey == pubkey) then
    appendState pendingDeposits pendingDeposit
  else if isValidDepositSignature pubkey wc amount sig then
    addValidatorToRegistry pubkey wc 0
    appendState pendingDeposits pendingDeposit

/-- `process_deposit`: verify the Merkle branch into `eth1_data.deposit_root`,
advance `eth1_deposit_index`, then apply. -/
forkdef processDeposit (d : Deposit) : StateTransition Unit := do
  let state ← get
  assert (isValidMerkleBranch (htr d.data) d.proof.toArray (Const.depositContractTreeDepth + 1)
    (sszGet state eth1DepositIndex).toNat (sszGet state eth1Data).depositRoot)

  modifyState fun state => sszUpdate state with eth1DepositIndex := (sszGet state eth1DepositIndex) + 1
  applyDeposit d.data.pubkey d.data.withdrawalCredentials d.data.amount d.data.signature

/-! ## Voluntary exits -/

/-- `process_voluntary_exit`. -/
forkdef processVoluntaryExit (sve : SignedVoluntaryExit) : StateTransition Unit := do
  let state ← get
  let ve := sve.message
  -- `validator = state.validators[voluntary_exit.validator_index]` (`fulu/minimal.py:2134`):
  -- a raising list read, so an out-of-range index rejects with `IndexError`'s class.
  let validator ← sszGetIdx (sszGet state validators) ve.validatorIndex

  assert (isActiveValidator validator (currentEpochOf state))
  assert (hasNotInitiatedExit validator)
  assert (currentEpochOf state ≥ ve.epoch)
  -- `passed_shard_committee_period`'s checked sum binds before its assert.
  assert (← passedShardCommitteePeriod validator (currentEpochOf state))
  let pending ← getPendingBalanceToWithdraw state ve.validatorIndex
  assert (pending == 0)

  let domain := computeDomain Const.domainVoluntaryExit Const.capellaForkVersion (sszGet state genesisValidatorsRoot)
  assert (blsVerifySigned validator.pubkey ve domain sve.signature)

  initiateValidatorExit ve.validatorIndex

/-! ## BLS-to-execution changes -/

/-- `process_bls_to_execution_change`. -/
forkdef processBlsToExecutionChange (sbc : SignedBLSToExecutionChange) : StateTransition Unit := do
  let state ← get
  let ac := sbc.message
  -- `assert address_change.validator_index < len(state.validators)`: the checked index
  -- against the plain length, a comparison that never raises. `int(x)` carries the index
  -- into the plain kind, where it meets `len`. The read after it is then in range.
  assert (ac.validatorIndex.toCLInt < len (sszGet state validators))
  let validator ← sszGetIdx (sszGet state validators) ac.validatorIndex

  assert (credPrefix validator.withdrawalCredentials == Const.blsWithdrawalPrefix)
  let h := sha ac.fromBlsPubkey
  assert ((List.range 31).all (fun k => vget validator.withdrawalCredentials (k + 1) == h.get! (k + 1)))
  let domain := computeDomain Const.domainBlsToExecutionChange Const.genesisForkVersion (sszGet state genesisValidatorsRoot)
  assert (blsVerifySigned ac.fromBlsPubkey ac domain sbc.signature)

  let newWc : Bytes32 := Vector.ofFn (fun i : Fin 32 =>
    if i.val == 0 then Const.eth1AddressWithdrawalPrefix
    else if i.val < 12 then 0
    else vget ac.toExecutionAddress (i.val - 12))
  modifyState fun state => modValidator state ac.validatorIndex (fun validator => { validator with withdrawalCredentials := newWc })

/-! ## Execution requests (Electra) -/

/-- `process_deposit_request` (Fulu, `fulu/beacon-chain.md`, "Modified
`process_deposit_request`"): queue the request as a pending deposit at the current slot.
Fulu removes the former deposit mechanism (consensus-specs #4704, in the text since
alpha.12), so the Electra write of `deposit_requests_start_index` on the first request is gone.
Gloas and Heze inherit this version. -/
forkdef processDepositRequest (dr : DepositRequest) : StateTransition Unit := do
  let state ← get
  appendState pendingDeposits
    { pubkey := dr.pubkey, withdrawalCredentials := dr.withdrawalCredentials, amount := dr.amount,
      signature := dr.signature, slot := sszGet state slot }

/-- `process_withdrawal_request` (EIP-7002 / EIP-7251): a full exit, or a partial
withdrawal for a compounding validator with excess balance. -/
forkdef processWithdrawalRequest (wr : WithdrawalRequest) : StateTransition Unit := do
  let state ← get
  let isFullExit := wr.amount == Const.fullExitRequestAmount
  -- Gate: the partial-withdrawal queue has room (full exits bypass the queue cap).
  if (sszGet state pendingPartialWithdrawals).size == Const.pendingPartialWithdrawalsLimit && !isFullExit then
    pure ()
  else
    match validatorIndexByPubkey? state wr.validatorPubkey with
    | none => pure ()
    | some idxN =>
      -- `index = ValidatorIndex(validator_pubkeys.index(request_pubkey))`: the checked cast.
      let index ← CLUint64.ofNat? idxN
      let validator ← sszGetIdx (sszGet state validators) index
      let correctCred := hasExecutionWithdrawalCredential validator
      let correctSource := vecSliceEq validator.withdrawalCredentials 12 wr.sourceAddress 0 20
      -- Validity ladder: execution credential + matching source, active, not exiting,
      -- past the shard-committee period.
      if !(correctCred && correctSource) then pure ()
      else if !isActiveValidator validator (currentEpochOf state) then pure ()
      else if !hasNotInitiatedExit validator then pure ()
      else if !(← passedShardCommitteePeriod validator (currentEpochOf state)) then pure ()
      else
        -- `pending_balance_to_withdraw` is the checked `Gwei` sum, formed on both
        -- paths, so it binds before the full-exit branch reads it.
        let pending ← getPendingBalanceToWithdraw state index
        if isFullExit then
          if pending == 0 then initiateValidatorExit index else pure ()
        else
          -- `index` is in range for `validators` (it came from `findIdx?` there); reading
          -- the parallel `balances` at it goes through `sszGetIdx`, so a broken
          -- validators/balances length parity rejects with `outOfBounds` rather than
          -- silently reading a default balance.
          let balance ← sszGetIdx (sszGet state balances) index
          let sufficientEff := validator.effectiveBalance ≥ Const.minActivationBalance
          let excessThreshold ← Const.minActivationBalance + pending
          let excess := balance > excessThreshold
          if hasCompoundingWithdrawalCredential validator && sufficientEff && excess then
            -- `min(balances[index] - MIN_ACTIVATION_BALANCE - pending, amount)`: each
            -- subtraction is a checked `Gwei` step, bound in order.
            let excessBalance ← balance - Const.minActivationBalance
            let toWithdrawCand ← excessBalance - pending
            let toWithdraw := min toWithdrawCand wr.amount
            let exitEpoch ← computeExitEpochAndUpdateChurn toWithdraw
            -- `withdrawable_epoch = exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY`,
            -- the checked `Epoch` add the partial-withdrawal store records.
            let we ← exitEpoch + Const.minValidatorWithdrawabilityDelay
            appendState pendingPartialWithdrawals
              { validatorIndex := index, amount := toWithdraw, withdrawableEpoch := we }
          else pure ()

/-- `is_valid_switch_to_compounding_request`. -/
forkdef isValidSwitchToCompoundingRequest (state : State) (req : ConsolidationRequest) : Bool :=
  if req.sourcePubkey != req.targetPubkey then false
  else match validatorIndexByPubkey? state req.sourcePubkey with
    | none => false
    | some si =>
      let validator := sszGet state validators[si]!
      if !(vecSliceEq validator.withdrawalCredentials 12 req.sourceAddress 0 20) then false
      else if !hasEth1WithdrawalCredential validator then false
      else if !isActiveValidator validator (currentEpochOf state) then false
      else if !hasNotInitiatedExit validator then false
      else true

/-- `process_consolidation_request` (EIP-7251). -/
forkdef processConsolidationRequest (req : ConsolidationRequest) : StateTransition Unit := do
  let state ← get
  -- A switch-to-compounding request is handled separately from a consolidation.
  if isValidSwitchToCompoundingRequest state req then
    match validatorIndexByPubkey? state req.sourcePubkey with
    | some si =>
      -- `source_index = ValidatorIndex(validator_pubkeys.index(…))`: the checked cast.
      let sourceIndex ← CLUint64.ofNat? si
      switchToCompoundingValidator sourceIndex
    | none    => pure ()
  -- Request-level gates: distinct source/target, queue room, churn capacity.
  else if req.sourcePubkey == req.targetPubkey then pure ()
  else if (sszGet state pendingConsolidations).size == Const.pendingConsolidationsLimit then pure ()
  else if (← liftErr (getConsolidationChurnLimit state)) ≤ Const.minActivationBalance then pure ()
  else
    match validatorIndexByPubkey? state req.sourcePubkey, validatorIndexByPubkey? state req.targetPubkey with
    | some srcN, some tgtN =>
      -- The two checked `ValidatorIndex(…)` casts, then the two registry reads, in the
      -- pyspec's order (`fulu/minimal.py:6392-6395`).
      let sourceIndex ← CLUint64.ofNat? srcN
      let targetIndex ← CLUint64.ofNat? tgtN
      let src ← sszGetIdx (sszGet state validators) sourceIndex
      let tgt ← sszGetIdx (sszGet state validators) targetIndex
      let correctCred := hasExecutionWithdrawalCredential src
      let correctSource := vecSliceEq src.withdrawalCredentials 12 req.sourceAddress 0 20
      -- Validity ladder: source execution credential + matching source, target
      -- compounding, both active, neither exiting, source past the shard-committee
      -- period with no pending withdrawal.
      if !(correctCred && correctSource) then pure ()
      else if !hasCompoundingWithdrawalCredential tgt then pure ()
      else if !isActiveValidator src (currentEpochOf state) then pure ()
      else if !isActiveValidator tgt (currentEpochOf state) then pure ()
      else if !hasNotInitiatedExit src then pure ()
      else if !hasNotInitiatedExit tgt then pure ()
      else if !(← passedShardCommitteePeriod src (currentEpochOf state)) then pure ()
      else if (← getPendingBalanceToWithdraw state sourceIndex) > 0 then pure ()
      else
        let exitEpoch ← computeConsolidationEpochAndUpdateChurn src.effectiveBalance
        -- `withdrawable_epoch = exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY`, the
        -- checked `Epoch` add, bound before the store that records both fields.
        let we ← exitEpoch + Const.minValidatorWithdrawabilityDelay
        modifyState fun state => modValidator state sourceIndex fun validator =>
          { validator with exitEpoch := exitEpoch, withdrawableEpoch := we }
        appendState pendingConsolidations { sourceIndex := sourceIndex, targetIndex := targetIndex }
    | _, _ => pure ()

/-! ## process_operations -/

/-- `process_operations` (Fulu, `fulu/beacon-chain.md`, "Modified `process_operations`"): no
in-block deposits (`assert len(body.deposits) == 0`), then each operation list in order, then
the Electra execution requests. Fulu removes the former deposit mechanism (consensus-specs
#4704, in the text since alpha.12): Electra's deposit-count gate and the `process_deposit`
loop are gone. -/
forkdef processOperations (body : BeaconBlockBody) : StateTransition Unit := do
  assert (body.deposits.size == 0)

  for op in body.proposerSlashings do processProposerSlashing op
  for op in body.attesterSlashings do processAttesterSlashing op
  for op in body.attestations do processAttestation op
  for op in body.voluntaryExits do processVoluntaryExit op
  for op in body.blsToExecutionChanges do processBlsToExecutionChange op
  for op in body.executionRequests.deposits do processDepositRequest op
  for op in body.executionRequests.withdrawals do processWithdrawalRequest op
  for op in body.executionRequests.consolidations do processConsolidationRequest op

end

end EthCLSpecs.Fulu
