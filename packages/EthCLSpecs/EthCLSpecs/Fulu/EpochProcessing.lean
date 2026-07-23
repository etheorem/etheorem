import EthCLSpecs.Fulu.Deposits

/-!
# `EthCLSpecs.Fulu.EpochProcessing`: epoch-transition substeps (load order row 31)

The `process_epoch` substeps. This slice ports the period-reset substeps, the
smallest, dependency-light members of the set (`process_slashings_reset`,
`process_randao_mixes_reset`, `process_eth1_data_reset`,
`process_participation_flag_updates`); they read only the time / RANDAO helpers
and rewrite one state field. The heavier substeps (justification/finalization,
rewards/penalties, registry updates, slashings, pending deposits/consolidations,
effective balances, sync-committee updates, proposer lookahead) and the
`processEpoch` composition follow.

Each is a `forkdef StateTransition Unit`, driven in isolation by the
`epoch_processing/<handler>` vector format.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section
-- `processRegistryUpdates` exits validators (churn) using `[Config]` churn constants;
-- `processSyncCommitteeUpdates` aggregates pubkeys through `[CryptoBackend]`. Both
-- seams come from `state_section` and attach only to the substeps that use them.

/-! ## Justification & finalization -/

/-- The justification-bits + checkpoint update, given the three target balances. -/
forkdef weighJustificationAndFinalization (totalActive prevTarget currTarget : Gwei) :
    StateTransition Unit := do
  let state ← get
  let prevEpoch := previousEpochOf state
  let currEpoch := currentEpochOf state
  let justifyPrev := prevTarget.toNat * 3 ≥ totalActive.toNat * 2
  let justifyCurr := currTarget.toNat * 3 ≥ totalActive.toNat * 2
  -- `get_block_root` is read ONLY inside its justify branch in the spec (lazy); read
  -- each only when its branch fires, so the recency assert fires exactly where the
  -- spec's read does. An unconditional read would assert on an epoch-boundary pull-up
  -- state whose justify condition is false, a slot the spec never reads there.
  let prevRoot ← if justifyPrev then getBlockRoot state prevEpoch else pure default
  let currRoot ← if justifyCurr then getBlockRoot state currEpoch else pure default
  modifyState fun state => Id.run do
    let oldPrev := sszGet state previousJustifiedCheckpoint
    let oldCurr := sszGet state currentJustifiedCheckpoint
    let mut state := state

    -- Shift the bit window, then justify the previous and current epochs that reached
    -- a two-thirds target supermajority.
    state := sszUpdate state with
      previousJustifiedCheckpoint := oldCurr,
      justificationBits := { data := (sszGet state justificationBits).data <<< 1 }
    if justifyPrev then
      state := sszUpdate state with
        currentJustifiedCheckpoint := { epoch := prevEpoch, root := prevRoot },
        justificationBits := bitSet (sszGet state justificationBits) 1 true
    if justifyCurr then
      state := sszUpdate state with
        currentJustifiedCheckpoint := { epoch := currEpoch, root := currRoot },
        justificationBits := bitSet (sszGet state justificationBits) 0 true

    -- Finalize on the four supermajority-link bit patterns.
    let bits := sszGet state justificationBits
    if bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && oldPrev.epoch + 3 == currEpoch then
      state := sszUpdate state with finalizedCheckpoint := oldPrev
    if bitGet bits 1 && bitGet bits 2 && oldPrev.epoch + 2 == currEpoch then
      state := sszUpdate state with finalizedCheckpoint := oldPrev
    if bitGet bits 0 && bitGet bits 1 && bitGet bits 2 && oldCurr.epoch + 2 == currEpoch then
      state := sszUpdate state with finalizedCheckpoint := oldCurr
    if bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == currEpoch then
      state := sszUpdate state with finalizedCheckpoint := oldCurr
    return state

/-- `process_justification_and_finalization`. -/
forkdef processJustificationAndFinalization : StateTransition Unit := do
  let state ← get
  if currentEpochOf state ≤ Const.genesisEpoch + 1 then pure ()
  else
    let prevIdx := getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state)
    let currIdx := getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (currentEpochOf state)
    weighJustificationAndFinalization (getTotalActiveBalance state)
      (getTotalBalance state prevIdx) (getTotalBalance state currIdx)

/-! ## Inactivity -/

/-- `process_inactivity_updates`. -/
forkdef processInactivityUpdates : StateTransition Unit := do
  let state ← get
  if currentEpochOf state == Const.genesisEpoch then pure ()
  else
    let matchingTarget := getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state)
    let leak := isInInactivityLeak state
    let eligible := getEligibleValidatorIndices state

    modifyState fun state => Id.run do
      let mut state := state
      for vi in eligible do
        let i := vi.toNat
        state := sszModify state inactivityScores[i]! as cur =>
          let cur := if matchingTarget.contains vi then cur - umin 1 cur else cur + Const.inactivityScoreBias
          if !leak then cur - umin Const.inactivityScoreRecoveryRate cur else cur
      return state

/-! ## Rewards & penalties -/

/-- `get_flag_index_deltas` for one flag: `(rewards, penalties)` per validator. Returns
`Except IndexError` because `getBaseReward` does; a bad validator index rejects rather than
masking. -/
forkdef getFlagIndexDeltas (state : State) (flagIndex : Nat) : Except IndexError (Array Gwei × Array Gwei) := do
  let n := (sszGet state validators).size
  let mut rewards := Array.replicate n (0 : Gwei)
  let mut penalties := Array.replicate n (0 : Gwei)

  let prevEpoch := previousEpochOf state
  let unslashed := getUnslashedParticipatingIndices state flagIndex prevEpoch
  let weight := Const.participationFlagWeights[flagIndex]!
  let unslashedIncrements := (getTotalBalance state unslashed).toNat / Const.effectiveBalanceIncrement
  let activeIncrements := (getTotalActiveBalance state).toNat / Const.effectiveBalanceIncrement
  let leak := isInInactivityLeak state

  for vi in getEligibleValidatorIndices state do
    let i := vi.toNat
    let baseReward ← getBaseReward state vi
    if unslashed.contains vi then
      if !leak then
        rewards := rewards.set! i (UInt64.ofNat (baseReward * weight * unslashedIncrements / (activeIncrements * Const.weightDenominator)))
    else if flagIndex != Const.timelyHeadFlagIndex then
      penalties := penalties.set! i (UInt64.ofNat (baseReward * weight / Const.weightDenominator))
  return (rewards, penalties)

/-- `get_inactivity_penalty_deltas`: penalties only. -/
forkdef getInactivityPenaltyDeltas (state : State) : Array Gwei := Id.run do
  let validators := sszGet state validators
  let iscores := sszGet state inactivityScores
  let mut penalties := Array.replicate validators.size (0 : Gwei)
  let matchingTarget := getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state)

  for vi in getEligibleValidatorIndices state do
    let i := vi.toNat
    if !matchingTarget.contains vi then
      let num := (validators[i]!).effectiveBalance.toNat * (iscores[i]!).toNat
      let denom := Const.inactivityScoreBias.toNat * Const.inactivityPenaltyQuotientBellatrix
      penalties := penalties.set! i (UInt64.ofNat (num / denom))
  return penalties

/-- Apply per-validator `(rewards, penalties)` to balances. -/
forkdef applyDeltas (rewards penalties : Array Gwei) (state : State) : State := Id.run do
  let mut state := state
  for i in [0 : (sszGet state validators).size] do
    state := increaseBalance state (UInt64.ofNat i) (rewards[i]!)
    state := decreaseBalance state (UInt64.ofNat i) (penalties[i]!)
  return state

/-- `process_rewards_and_penalties`. -/
forkdef processRewardsAndPenalties : StateTransition Unit := do
  let state ← get
  if currentEpochOf state == Const.genesisEpoch then pure ()
  else
    let flagDeltas ← liftErr ((List.range 3).mapM (fun f => getFlagIndexDeltas state f))
    let inactPenalties := getInactivityPenaltyDeltas state
    let zeros := Array.replicate (sszGet state validators).size (0 : Gwei)

    for (rewards, penalties) in flagDeltas do
      modifyState (applyDeltas rewards penalties)
    modifyState (applyDeltas zeros inactPenalties)

/-! ## Registry updates -/

/-- `process_registry_updates` (Electra: activation-eligibility, ejections, and
churn-unlimited activations in one pass). -/
forkdef processRegistryUpdates : StateTransition Unit := do
  let currentEpoch := currentEpochOf (← get)
  let activationEpoch := computeActivationExitEpoch currentEpoch
  let n := (sszGet (← get) validators).size

  for idx in [0 : n] do
    let state ← get
    let validator := sszGet state validators[idx]!
    if isEligibleForActivationQueue validator then
      modifyState fun state => modValidator state (UInt64.ofNat idx) fun validator => { validator with activationEligibilityEpoch := currentEpoch + 1 }
    if isActiveValidator validator currentEpoch && validator.effectiveBalance ≤ Const.ejectionBalanceG then
      initiateValidatorExit (UInt64.ofNat idx)
    if isEligibleForActivation state validator then
      modifyState fun state => modValidator state (UInt64.ofNat idx) fun validator => { validator with activationEpoch := activationEpoch }

/-! ## Slashings (epoch penalty) -/

/-- `process_slashings`. -/
forkdef processSlashings : StateTransition Unit := do
  let state ← get
  let epoch := currentEpochOf state
  let totalBalance := getTotalActiveBalance state
  let sumSlashings := (sszGet state slashings).toArray.foldl (· + ·) (0 : Gwei)
  let adjusted := umin (sumSlashings * UInt64.ofNat Const.proportionalSlashingMultiplierBellatrix) totalBalance
  let increment := Const.effectiveBalanceIncrementG
  let penaltyPerIncrement := adjusted / (totalBalance / increment)

  modifyState fun state => Id.run do
    let mut state := state
    for i in [0 : (sszGet state validators).size] do
      let validator := sszGet state validators[i]!
      if validator.slashed && epoch + (UInt64.ofNat Const.epochsPerSlashingsVector / 2) == validator.withdrawableEpoch then
        state := decreaseBalance state (UInt64.ofNat i) (penaltyPerIncrement * (validator.effectiveBalance / increment))
    return state

/-! ## Pending deposits (Electra deposit queue) -/

/-- The running state of the pending-deposit scan, and its result. `ndi` is the spec's
`next_deposit_index`: both the queue cursor and the count of dequeued deposits, since
every step advances it or stops, so the two never diverge. `churnReached` is set only
when the per-epoch churn limit halts the scan. -/
forkstruct DepositScan where
  ndi          : Nat := 0
  processed    : Gwei := 0
  postpone     : Array PendingDeposit := #[]
  churnReached : Bool := false

/-- The deposit-queue scan, tail-recursive on `fuel = #deposits`. A deposit for a
withdrawn validator applies without consuming churn; one for an exiting validator is
postponed; otherwise it applies while it fits the per-epoch churn, and the scan stops
(setting `churnReached`) once it does not. The eth1-bridge / not-finalized /
per-epoch-limit stops leave `churnReached` false. -/
forkdef ppdLoop (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei) (nextEpoch : Epoch) :
    StateTransition DepositScan :=
  -- Fuel is `deposits.size + 1`: the `ndi ≥ deposits.size` guard returns `.done` one step
  -- before exhaustion, so `fuelLoop`'s `exhausted` value is unreachable.
  fuelLoop (deposits.size + 1) ({} : DepositScan) ({} : DepositScan) fun s => do
    if s.ndi ≥ deposits.size then return .done s
    let state ← get
    let deposit := deposits[s.ndi]!

    -- Stop the scan early: the eth1-bridge deposits are not yet applied, the deposit is
    -- not finalized, or this epoch's deposit cap is reached.
    if deposit.slot > Const.genesisSlot
        && (sszGet state eth1DepositIndex) < (sszGet state depositRequestsStartIndex) then return .done s
    if deposit.slot > finalizedSlot then return .done s
    if s.ndi ≥ Const.maxPendingDepositsPerEpoch then return .done s

    -- Advance past this deposit, carrying the running churn and postpone list forward.
    let advance (processed : Gwei) (postpone : Array PendingDeposit) : Step DepositScan DepositScan :=
      .next { s with ndi := s.ndi + 1, processed, postpone }

    -- Read the deposit's validator once, if its pubkey is known, and derive the two flags
    -- the spec branches on. An unknown pubkey leaves both false, so it falls through to the
    -- churn check.
    let (isWithdrawn, isExited) := match validatorIndexByPubkey? state deposit.pubkey with
      | some vi =>
        let v := sszGet state validators[vi]!
        (decide (v.withdrawableEpoch < nextEpoch), decide (v.exitEpoch < Const.farFutureEpoch))
      | none => (false, false)

    if isWithdrawn then applyPendingDeposit deposit; return advance s.processed s.postpone
    else if isExited then return advance s.processed (s.postpone.push deposit)
    else if s.processed + deposit.amount > avail then return .done { s with churnReached := true }
    else applyPendingDeposit deposit; return advance (s.processed + deposit.amount) s.postpone

/-- `process_pending_deposits`. Churn is accumulated into `deposit_balance_to_consume`
only when the churn limit was actually hit; every other stop resets it to zero. -/
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + 1
  let avail := (sszGet state depositBalanceToConsume) + getActivationExitChurnLimit state
  let finalizedSlot := computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch
  let deposits := (sszGet state pendingDeposits).toArray
  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch

  modifyState fun state => sszUpdate state with
    pendingDeposits := sszOfArray (deposits.extract scan.ndi deposits.size ++ scan.postpone),
    depositBalanceToConsume := if scan.churnReached then avail - scan.processed else 0

/-! ## Pending consolidations -/

/-- The consolidation-queue scan. Returns the next-pending index, tail-recursive on
`fuel = #consolidations`. A slashed source is skipped; an unwithdrawable source
stops the scan; otherwise the source's effective balance moves to the target. -/
forkdef pcLoop (cons : Array PendingConsolidation) (nextEpoch : Epoch) : StateTransition Nat :=
  -- Threaded accumulator is the next-pending index `npc`; `fuelLoop` owns the counter. Fuel is
  -- `cons.size + 1` (the `fuelIterate` `length + 1` idiom): the `npc ≥ cons.size` guard fires as
  -- a `.done` one step before exhaustion, so the `exhausted` value is unreachable. A slashed
  -- source `.next`s; an unwithdrawable source `.done`s; a moved balance `.next`s.
  fuelLoop (cons.size + 1) (0 : Nat) (cons.size) fun npc => do
    if npc ≥ cons.size then return .done npc
    else
      let state ← get
      let pc := cons[npc]!
      -- `pc.sourceIndex` is a data-derived validator index from the queued
      -- consolidation; the source validator and balance reads go through `sszGetIdx`,
      -- so an out-of-range source rejects with `outOfBounds` instead of masking.
      let src ← sszGetIdx (sszGet state validators) pc.sourceIndex.toNat
      if src.slashed then return .next (npc + 1)
      else if src.withdrawableEpoch > nextEpoch then return .done npc
      else
        let srcBal ← sszGetIdx (sszGet state balances) pc.sourceIndex.toNat
        let amt := umin srcBal src.effectiveBalance
        modifyState fun state => increaseBalance (decreaseBalance state pc.sourceIndex amt) pc.targetIndex amt
        return .next (npc + 1)

/-- `process_pending_consolidations`. -/
forkdef processPendingConsolidations : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + 1
  let pending := sszGet state pendingConsolidations
  let cons := pending.toArray
  let npc ← pcLoop cons nextEpoch

  modifyState fun state =>
    sszUpdate state with pendingConsolidations := sszDrop pending npc

/-! ## Effective-balance updates -/

/-- `process_effective_balance_updates` (the hysteresis rule). -/
forkdef processEffectiveBalanceUpdates : StateTransition Unit :=
  modifyState fun state => Id.run do
    let mut state := state
    let hysteresisIncrement := Const.effectiveBalanceIncrementG / UInt64.ofNat Const.hysteresisQuotient
    let downward := hysteresisIncrement * UInt64.ofNat Const.hysteresisDownwardMultiplier
    let upward := hysteresisIncrement * UInt64.ofNat Const.hysteresisUpwardMultiplier

    for i in [0 : (sszGet state validators).size] do
      let validator := sszGet state validators[i]!
      let balance := sszGet state balances[i]!
      if balance + downward < validator.effectiveBalance || validator.effectiveBalance + upward < balance then
        let newEff := umin (balance - balance % Const.effectiveBalanceIncrementG) (getMaxEffectiveBalance validator)
        state := modValidator state (UInt64.ofNat i) (fun validator => { validator with effectiveBalance := newEff })
    return state

/-- `process_slashings_reset`: zero the next epoch's slashings slot. The index is in
range by construction (`nextEpoch % EPOCHS_PER_SLASHINGS_VECTOR`), so the infallible
`[idx]!` element write is total (fits the `modifyState` context, no reject path). -/
forkdef processSlashingsReset : StateTransition Unit := do
  let nextEpoch := (← getCurrentEpoch) + 1
  let idx := umodIdx nextEpoch Const.epochsPerSlashingsVector
  modifyState fun state =>
    sszUpdate state with slashings[idx]! := (0 : Gwei)

/-- `process_randao_mixes_reset`: carry the current epoch's RANDAO mix into the
next epoch's slot. -/
forkdef processRandaoMixesReset : StateTransition Unit := do
  let currentEpoch ← getCurrentEpoch
  let mix ← getRandaoMix currentEpoch
  let idx := umodIdx (currentEpoch + 1) Const.epochsPerHistoricalVector
  modifyState fun state =>
    sszUpdate state with randaoMixes[idx]! := mix

/-- `process_eth1_data_reset`: clear the eth1 vote tally at the end of a voting
period. -/
forkdef processEth1DataReset : StateTransition Unit := do
  let nextEpoch := (← getCurrentEpoch) + 1
  if nextEpoch % UInt64.ofNat Const.epochsPerEth1VotingPeriod == 0 then
    modifyState fun state =>
      sszUpdate state with eth1DataVotes := sszOfArray #[]

/-- `process_historical_summaries_update`: at the end of a historical-root period,
append a summary of the block-roots and state-roots vectors. -/
forkdef processHistoricalSummariesUpdate : StateTransition Unit := do
  let nextEpoch := (← getCurrentEpoch) + 1
  let period := UInt64.ofNat (Const.slotsPerHistoricalRoot / Const.slotsPerEpoch)
  if nextEpoch % period == 0 then
    let state ← get
    let summary : HistoricalSummary :=
      { blockSummaryRoot := htr (sszGet state blockRoots),
        stateSummaryRoot := htr (sszGet state stateRoots) }
    appendState historicalSummaries summary

/-- `process_participation_flag_updates`: rotate current participation into
previous and reset current to all-zero flags, one per validator. -/
forkdef processParticipationFlagUpdates : StateTransition Unit := do
  let state ← get
  let current := sszGet state currentEpochParticipation
  let count := (sszGet state validators).size
  modifyState fun state =>
    sszUpdate state with
      previousEpochParticipation := current,
      currentEpochParticipation  := sszOfArray (Array.replicate count (0 : ParticipationFlags))

/-! ## Sync-committee rotation & proposer lookahead (shuffle-dependent) -/

/-- `process_sync_committee_updates`: at a sync-committee-period boundary, rotate
`next` into `current` and select a fresh `next` (balance-weighted, with the real
BLS aggregate pubkey). -/
forkdef processSyncCommitteeUpdates : StateTransition Unit := do
  let state ← get
  if (currentEpochOf state + 1) % UInt64.ofNat Const.epochsPerSyncCommitteePeriod == 0 then
    let nsc := getNextSyncCommittee state
    set (sszUpdate state with
      currentSyncCommittee := sszGet state nextSyncCommittee,
      nextSyncCommittee := nsc)

/-- `process_proposer_lookahead` (Fulu, EIP-7917): shift out the first epoch's
proposers and append the freshly-computed proposers for
`current_epoch + MIN_SEED_LOOKAHEAD + 1`. -/
forkdef processProposerLookahead : StateTransition Unit := do
  let state ← get
  let newProposers := getBeaconProposerIndices state (currentEpochOf state + Const.minSeedLookahead + 1)
  let old := sszGet state proposerLookahead
  set (sszUpdate state with proposerLookahead :=
    Vector.ofFn (fun i : Fin (2 * Const.slotsPerEpoch) =>
      if i.val < Const.slotsPerEpoch then vget old (i.val + Const.slotsPerEpoch)
      else newProposers[i.val - Const.slotsPerEpoch]!))

end

end EthCLSpecs.Fulu
