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
def strictlySorted (a : Array ValidatorIndex) : Bool := Id.run do
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
valid aggregate signature (through the `[CryptoBackend]` seam). A pure `Bool`, so an
index past the registry returns `false` (the pyspec's `IndexError` reject outcome)
rather than panicking. -/
forkdef isValidIndexedAttestation (state : State) (a : IndexedAttestation) : Bool :=
  let validators := sszGet state validators
  let idx := a.attestingIndices.toArray
  if idx.size == 0 || !strictlySorted idx then false
  else if !idx.all (·.toNat < validators.size) then false
  else
    let pubkeys := idx.map (fun i => (validators[i.toNat]!).pubkey)
    blsFastAggregateVerify pubkeys
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

  let hb ← assertH (h1.proposerIndex.toNat < (sszGet state validators).size)
  let proposer := (sszGet state validators)[h1.proposerIndex.toNat]'hb.down
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
    if idx.toNat < (sszGet state validators).size
        && isSlashableValidator (sszGet state validators[idx.toNat]!) (currentEpochOf state) then
      slashValidator idx
      slashedAny := true
  assert slashedAny

/-! ## Attestations -/

/-- `get_attestation_participation_flag_indices`. Returns `none` for the
`is_matching_source` assertion (a valid attestation always matches source), so the
caller rejects; `some flags` otherwise. -/
forkdef getAttestationParticipationFlagIndices (state : State) (data : AttestationData)
    (inclusionDelay : UInt64) : Option (Array Nat) := Id.run do
  let justified := if data.target.epoch == currentEpochOf state then sszGet state currentJustifiedCheckpoint
                   else sszGet state previousJustifiedCheckpoint
  let isMatchingSource := data.source.epoch == justified.epoch && data.source.root == justified.root
  if !isMatchingSource then return none
  let isMatchingTarget := data.target.root == getBlockRoot state data.target.epoch
  let isMatchingHead := isMatchingTarget && data.beaconBlockRoot == getBlockRootAtSlot state data.slot

  let mut flags : Array Nat := #[]
  if inclusionDelay ≤ UInt64.ofNat (isqrt Const.slotsPerEpoch) then flags := flags.push Const.timelySourceFlagIndex
  if isMatchingTarget then flags := flags.push Const.timelyTargetFlagIndex
  if isMatchingHead && inclusionDelay == Const.minAttestationInclusionDelay then flags := flags.push Const.timelyHeadFlagIndex
  return some flags

/-- `get_attesting_indices`: the validators flagged across the slot's committees. Returns
`Except IndexError` because the block-supplied `aggregation_bits` is read at a committee
offset it does not bound; an over-length read rejects rather than masking to `false`. The
`committee[i]` read stays total, `i` is bounded by the committee it just built. -/
forkdef getAttestingIndices (state : State) (att : Attestation) : Except IndexError (Array ValidatorIndex) := do
  let mut out : Array ValidatorIndex := #[]
  let mut offset := 0
  for ci in getCommitteeIndices att.committeeBits do
    let committee := getBeaconCommittee state att.data.slot ci
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
  assert (data.slot + Const.minAttestationInclusionDelay ≤ sszGet state slot)
  assert (data.index == 0)

  -- Every committee index is valid and contributes at least one attester; the
  -- aggregation bitfield length matches the total committee size.
  let count := getCommitteeCountPerSlot state data.target.epoch
  let (ok, offset) := verifyCommitteeCoverage state data count
  assert ok
  assert (att.aggregationBits.size == offset)

  -- Resolve the participation flags, then validate the aggregate signature.
  let flagIndices ← match getAttestationParticipationFlagIndices state data ((sszGet state slot) - data.slot) with
    | some f => pure f
    | none   => throw (StateTransitionError.assert "is_matching_source")
  let indexedAttestation : IndexedAttestation :=
    { attestingIndices := sszOfArray ((← liftErr (getAttestingIndices state att)).qsort (· < ·)),
      data := att.data, signature := att.signature }
  assert (isValidIndexedAttestation state indexedAttestation)

  -- Apply participation flags and accumulate the proposer-reward numerator.
  let currentTarget := data.target.epoch == currentEpochOf state
  let mut stateAcc := state
  let mut proposerNum := 0
  for vi in (← liftErr (getAttestingIndices state att)) do
    let i := vi.toNat
    for flagIndex in [0:3] do
      -- `i` is a data-derived attesting-validator index; read the participation flag
      -- through `sszGetIdx` so an out-of-range index rejects with `outOfBounds` rather
      -- than masking as a default flag. The matching `[i]!` write below is then a
      -- provably-in-range write (the read at `i` just succeeded).
      let flag ← if currentTarget then sszGetIdx (sszGet stateAcc currentEpochParticipation) i
                 else sszGetIdx (sszGet stateAcc previousEpochParticipation) i
      if flagIndices.contains flagIndex && !hasFlag flag flagIndex then
        stateAcc := if currentTarget then
                   sszUpdate stateAcc with currentEpochParticipation[i]! := addFlag flag flagIndex
                 else
                   sszUpdate stateAcc with previousEpochParticipation[i]! := addFlag flag flagIndex
        proposerNum := proposerNum + (← liftErr (getBaseReward state vi)) * Const.participationFlagWeights[flagIndex]!

  -- Pay the proposer the accumulated weight.
  let proposerDenom := (Const.weightDenominator - Const.proposerWeight) * Const.weightDenominator / Const.proposerWeight
  stateAcc := increaseBalance stateAcc (getBeaconProposerIndex stateAcc) (UInt64.ofNat (proposerNum / proposerDenom))
  set stateAcc
where
  /-- Fold over the attestation's committee indices: each must be below `count` and
  contribute at least one attester. Returns `(allValid, totalCommitteeSize)`. -/
  verifyCommitteeCoverage (state : State) (data : AttestationData) (count : Nat) : Bool × Nat :=
    (getCommitteeIndices att.committeeBits).foldl
      (fun (acc : Bool × Nat) ci => Id.run do
        let (okAcc, off) := acc
        if (UInt64.ofNat ci).toNat ≥ count then return (false, off)
        let committee := getBeaconCommittee state data.slot ci
        let attesters := (List.range committee.size).foldl
          (fun a i => if att.aggregationBits[off + i]! then a + 1 else a) 0
        return (okAcc && attesters > 0, off + committee.size))
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
  let hb ← assertH (ve.validatorIndex.toNat < (sszGet state validators).size)
  let validator := (sszGet state validators)[ve.validatorIndex.toNat]'hb.down

  assert (isActiveValidator validator (currentEpochOf state))
  assert (hasNotInitiatedExit validator)
  assert (currentEpochOf state ≥ ve.epoch)
  assert (passedShardCommitteePeriod validator (currentEpochOf state))
  assert (getPendingBalanceToWithdraw state ve.validatorIndex == 0)

  let domain := computeDomain Const.domainVoluntaryExit Const.capellaForkVersion (sszGet state genesisValidatorsRoot)
  assert (blsVerifySigned validator.pubkey ve domain sve.signature)

  initiateValidatorExit ve.validatorIndex

/-! ## BLS-to-execution changes -/

/-- `process_bls_to_execution_change`. -/
forkdef processBlsToExecutionChange (sbc : SignedBLSToExecutionChange) : StateTransition Unit := do
  let state ← get
  let ac := sbc.message
  let hb ← assertH (ac.validatorIndex.toNat < (sszGet state validators).size)
  let validator := (sszGet state validators)[ac.validatorIndex.toNat]'hb.down

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

/-- `process_deposit_request`. -/
forkdef processDepositRequest (dr : DepositRequest) : StateTransition Unit := do
  modifyState fun state =>
    if (sszGet state depositRequestsStartIndex) == Const.unsetDepositRequestsStartIndex then
      sszUpdate state with depositRequestsStartIndex := dr.index
    else state
  modifyState fun state => sszAppend state pendingDeposits
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
      let index := UInt64.ofNat idxN
      let validator := sszGet state validators[idxN]!
      let correctCred := hasExecutionWithdrawalCredential validator
      let correctSource := vecSliceEq validator.withdrawalCredentials 12 wr.sourceAddress 0 20
      -- Validity ladder: execution credential + matching source, active, not exiting,
      -- past the shard-committee period.
      if !(correctCred && correctSource) then pure ()
      else if !isActiveValidator validator (currentEpochOf state) then pure ()
      else if !hasNotInitiatedExit validator then pure ()
      else if !passedShardCommitteePeriod validator (currentEpochOf state) then pure ()
      else
        let pending := getPendingBalanceToWithdraw state index
        if isFullExit then
          if pending == 0 then initiateValidatorExit index else pure ()
        else
          -- `idxN` is in range for `validators` (it came from `findIdx?` there); reading
          -- the parallel `balances` at it goes through `sszGetIdx`, so a broken
          -- validators/balances length parity rejects with `outOfBounds` rather than
          -- silently reading a default balance.
          let balance ← sszGetIdx (sszGet state balances) idxN
          let sufficientEff := validator.effectiveBalance ≥ Const.minActivationBalance
          let excess := balance > Const.minActivationBalance + pending
          if hasCompoundingWithdrawalCredential validator && sufficientEff && excess then
            let toWithdraw := umin (balance - Const.minActivationBalance - pending) wr.amount
            let exitEpoch ← computeExitEpochAndUpdateChurn toWithdraw
            let we := exitEpoch + Const.minValidatorWithdrawabilityDelay
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
    | some si => switchToCompoundingValidator (UInt64.ofNat si)
    | none    => pure ()
  -- Request-level gates: distinct source/target, queue room, churn capacity.
  else if req.sourcePubkey == req.targetPubkey then pure ()
  else if (sszGet state pendingConsolidations).size == Const.pendingConsolidationsLimit then pure ()
  else if getConsolidationChurnLimit state ≤ Const.minActivationBalance then pure ()
  else
    let validators := (sszGet state validators).toArray
    match validatorIndexByPubkey? state req.sourcePubkey, validatorIndexByPubkey? state req.targetPubkey with
    | some srcN, some tgtN =>
      let src := validators[srcN]?.getD default
      let tgt := validators[tgtN]?.getD default
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
      else if !passedShardCommitteePeriod src (currentEpochOf state) then pure ()
      else if getPendingBalanceToWithdraw state (UInt64.ofNat srcN) > 0 then pure ()
      else
        let exitEpoch ← computeConsolidationEpochAndUpdateChurn src.effectiveBalance
        modifyState fun state => modValidator state (UInt64.ofNat srcN) fun validator =>
          { validator with exitEpoch := exitEpoch, withdrawableEpoch := exitEpoch + Const.minValidatorWithdrawabilityDelay }
        appendState pendingConsolidations { sourceIndex := UInt64.ofNat srcN, targetIndex := UInt64.ofNat tgtN }
    | _, _ => pure ()

/-! ## process_operations -/

/-- `process_operations`: the deposit-count gate, then each operation list in
order, then the Electra execution requests. -/
forkdef processOperations (body : BeaconBlockBody) : StateTransition Unit := do
  let state ← get
  let limit := umin (sszGet state eth1Data).depositCount (sszGet state depositRequestsStartIndex)
  if (sszGet state eth1DepositIndex) < limit then
    assert (UInt64.ofNat body.deposits.size == umin (UInt64.ofNat Const.maxDeposits) (limit - (sszGet state eth1DepositIndex)))
  else
    assert (body.deposits.size == 0)

  for op in body.proposerSlashings do processProposerSlashing op
  for op in body.attesterSlashings do processAttesterSlashing op
  for op in body.attestations do processAttestation op
  for op in body.deposits do processDeposit op
  for op in body.voluntaryExits do processVoluntaryExit op
  for op in body.blsToExecutionChanges do processBlsToExecutionChange op
  for op in body.executionRequests.deposits do processDepositRequest op
  for op in body.executionRequests.withdrawals do processWithdrawalRequest op
  for op in body.executionRequests.consolidations do processConsolidationRequest op

end

end EthCLSpecs.Fulu
