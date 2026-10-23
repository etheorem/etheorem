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

/-- The justification-bits + checkpoint update, given the three target balances.

The pyspec's comparisons multiply `Gwei` values, so `target * 3` and `total * 2` are checked
`uint64` products, and each raises `ValueError` past `2 ^ 64`. The body forms them through
`checkedMul` (`.arithmetic`), in the pyspec's order: the previous-epoch pair, its root read,
then the current-epoch pair and its root read. Each finalization rule tests its bits first,
and Python's `and` forms the epoch sum only when they all hold. That sum is a checked
`uint64` add, so the body forms it through `checkedAdd` after the bit test. -/
forkdef weighJustificationAndFinalization (totalActive prevTarget currTarget : Gwei) :
    StateTransition Unit := do
  let state ← get
  let prevEpoch := previousEpochOf state
  let currEpoch := currentEpochOf state
  let oldPrev := sszGet state previousJustifiedCheckpoint
  let oldCurr := sszGet state currentJustifiedCheckpoint

  -- Justify the previous epoch. `get_block_root` is read ONLY inside its justify branch in
  -- the spec (lazy), so the recency assert fires exactly where the spec's read does. An
  -- unconditional read would assert on an epoch-boundary pull-up state whose justify
  -- condition is false, a slot the spec never reads there.
  let prevWeight ← checkedMul prevTarget 3
    "weigh_justification_and_finalization: previous_epoch_target_balance * 3"
  let prevQuorum ← checkedMul totalActive 2
    "weigh_justification_and_finalization: total_active_balance * 2"
  let justifyPrev := prevWeight ≥ prevQuorum
  let prevRoot ← if justifyPrev then getBlockRoot state prevEpoch else pure default

  -- Justify the current epoch, the same way.
  let currWeight ← checkedMul currTarget 3
    "weigh_justification_and_finalization: current_epoch_target_balance * 3"
  let currQuorum ← checkedMul totalActive 2
    "weigh_justification_and_finalization: total_active_balance * 2"
  let justifyCurr := currWeight ≥ currQuorum
  let currRoot ← if justifyCurr then getBlockRoot state currEpoch else pure default

  -- The bit window after the shift and the two justifications.
  let shifted : Bitvector Const.justificationBitsLength :={ data := (sszGet state justificationBits).data <<< 1 }
  let afterPrev := if justifyPrev then bitSet shifted 1 true else shifted
  let bits := if justifyCurr then bitSet afterPrev 0 true else afterPrev

  -- The four finalization rules. Each forms its epoch sum only after its bit test passes.
  let linkEpoch (bitsHold : Bool) (source : Epoch) (k : UInt64) (descr : String) :
      StateTransition Bool :=
    if bitsHold then do pure ((← checkedAdd source k descr) == currEpoch) else pure false
  let rule1 ← linkEpoch (bitGet bits 1 && bitGet bits 2 && bitGet bits 3) oldPrev.epoch 3
    "weigh_justification_and_finalization: old_previous_justified_checkpoint.epoch + 3"
  let rule2 ← linkEpoch (bitGet bits 1 && bitGet bits 2) oldPrev.epoch 2
    "weigh_justification_and_finalization: old_previous_justified_checkpoint.epoch + 2"
  let rule3 ← linkEpoch (bitGet bits 0 && bitGet bits 1 && bitGet bits 2) oldCurr.epoch 2
    "weigh_justification_and_finalization: old_current_justified_checkpoint.epoch + 2"
  let rule4 ← linkEpoch (bitGet bits 0 && bitGet bits 1) oldCurr.epoch 1
    "weigh_justification_and_finalization: old_current_justified_checkpoint.epoch + 1"

  modifyState fun state => Id.run do
    let mut state := state
    -- Shift the window, then justify the epochs that reached a two-thirds supermajority.
    state := sszUpdate state with previousJustifiedCheckpoint := oldCurr, justificationBits := bits
    if justifyPrev then
      state := sszUpdate state with currentJustifiedCheckpoint := { epoch := prevEpoch, root := prevRoot }
    if justifyCurr then
      state := sszUpdate state with currentJustifiedCheckpoint := { epoch := currEpoch, root := currRoot }
    -- Finalize. A later rule overwrites an earlier one, as the pyspec's `if` chain does.
    if rule1 then state := sszUpdate state with finalizedCheckpoint := oldPrev
    if rule2 then state := sszUpdate state with finalizedCheckpoint := oldPrev
    if rule3 then state := sszUpdate state with finalizedCheckpoint := oldCurr
    if rule4 then state := sszUpdate state with finalizedCheckpoint := oldCurr
    return state

/-- `process_justification_and_finalization`. The five reads run in the pyspec's order: the
two participant sets, the active total, then the two target totals. -/
forkdef processJustificationAndFinalization : StateTransition Unit := do
  let state ← get
  if currentEpochOf state ≤ Const.genesisEpoch + 1 then pure ()
  else
    let prevIdx ← liftErr (getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state))
    let currIdx ← liftErr (getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (currentEpochOf state))
    let totalActive ← liftErr (getTotalActiveBalance state)
    let prevTarget ← liftErr (getTotalBalance state prevIdx)
    let currTarget ← liftErr (getTotalBalance state currIdx)
    weighJustificationAndFinalization totalActive prevTarget currTarget

/-! ## Inactivity -/

/-- `process_inactivity_updates`.

The pyspec calls `get_unslashed_participating_indices` and `is_in_inactivity_leak` inside the
loop, once per eligible validator, so neither runs when no validator is eligible. Neither reads
`inactivity_scores`, so each has the same value at every step, and the body computes each one
once. For each validator the pyspec order is: the participant set, the score read and update,
then the leak test. So the participant set comes before the loop, guarded by a nonempty
eligible list, and the leak test comes after the first score update.

The score read raises `IndexError` on a list shorter than the registry, and the body reads
through `sszGetIdx` (`.outOfBounds`). `+= INACTIVITY_SCORE_BIAS` is a checked `uint64` add
(`.arithmetic`). The two subtractions take at most the score, so they cannot underflow. -/
forkdef processInactivityUpdates : StateTransition Unit := do
  let state ← get
  if currentEpochOf state == Const.genesisEpoch then pure ()
  else
    let eligible := getEligibleValidatorIndices state
    if eligible.isEmpty then pure ()
    else
      let matchingTarget ← liftErr
        (getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state))
      for vi in eligible do
        let state ← get
        let i := vi.toNat
        let cur ← sszGetIdx (sszGet state inactivityScores) i
        let cur ← (if matchingTarget.contains vi then pure (cur - umin 1 cur)
          else checkedAdd cur Const.inactivityScoreBias
            "process_inactivity_updates: inactivity_scores[index] + INACTIVITY_SCORE_BIAS")
        let leak ← liftErr (isInInactivityLeak state)
        let cur := if !leak then cur - umin Const.inactivityScoreRecoveryRate cur else cur
        set (sszUpdate state with inactivityScores[i]! := cur)

/-! ## Rewards & penalties -/

/-- `get_flag_index_deltas` for one flag: `(rewards, penalties)` per validator.

The reads run in the pyspec's order: the participant set, the participant total, the active
total, then the per-validator base reward. The pyspec tests the leak only for a participant,
inside the loop. The reward numerator `base_reward * weight * increments` multiplies `Gwei`
values left to right, so each product is a checked `uint64`. The body forms both through
`checkedMul` (`.arithmetic`), and the penalty's `base_reward * weight` the same way. The
divisor `active_increments * WEIGHT_DENOMINATOR` comes after the numerator, and it is a
checked product too. It overflows when `EFFECTIVE_BALANCE_INCREMENT` is small enough that
`active_increments` reaches `2 ^ 58`. -/
forkdef getFlagIndexDeltas (state : State) (flagIndex : Nat) :
    Except StateTransitionError (Array Gwei × Array Gwei) := do
  let n := (sszGet state validators).size
  let mut rewards := Array.replicate n (0 : Gwei)
  let mut penalties := Array.replicate n (0 : Gwei)

  let prevEpoch := previousEpochOf state
  let unslashed ← getUnslashedParticipatingIndices state flagIndex prevEpoch
  let weight : UInt64 := UInt64.ofNat Const.participationFlagWeights[flagIndex]!
  let unslashedIncrements := (← getTotalBalance state unslashed) / Const.effectiveBalanceIncrementG
  let activeIncrements := (← getTotalActiveBalance state) / Const.effectiveBalanceIncrementG

  for vi in getEligibleValidatorIndices state do
    let i := vi.toNat
    let baseReward := UInt64.ofNat (← getBaseReward state vi)
    if unslashed.contains vi then
      if !(← isInInactivityLeak state) then
        let weighted ← checkedMul baseReward weight
          "get_flag_index_deltas: base_reward * weight"
        let numerator ← checkedMul weighted unslashedIncrements
          "get_flag_index_deltas: base_reward * weight * unslashed_participating_increments"
        let denominator ← checkedMul activeIncrements (UInt64.ofNat Const.weightDenominator)
          "get_flag_index_deltas: active_increments * WEIGHT_DENOMINATOR"
        rewards := rewards.set! i (numerator / denominator)
    else if flagIndex != Const.timelyHeadFlagIndex then
      let weighted ← checkedMul baseReward weight
        "get_flag_index_deltas: base_reward * weight"
      penalties := penalties.set! i (weighted / UInt64.ofNat Const.weightDenominator)
  return (rewards, penalties)

/-- `get_inactivity_penalty_deltas`: penalties only. The score read raises `IndexError` on a
list shorter than the registry, and the body reads through `sszGetIdx` (`.outOfBounds`). The
numerator `effective_balance * inactivity_score` is a checked `uint64` product
(`.arithmetic`). The eligible indices come from `validators`, so that read stays in range.
The denominator `INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX` is a checked
product as well. pyspec forms it inside the loop, after the numerator, so it raises only
when a non-participating validator is eligible, and the body keeps that place. -/
forkdef getInactivityPenaltyDeltas (state : State) : Except StateTransitionError (Array Gwei) := do
  let validators := sszGet state validators
  let iscores := sszGet state inactivityScores
  let mut penalties := Array.replicate validators.size (0 : Gwei)
  let matchingTarget ← getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state)

  for vi in getEligibleValidatorIndices state do
    let i := vi.toNat
    if !matchingTarget.contains vi then
      let score ← sszGetIdx iscores i
      let num ← checkedMul (validators[i]!).effectiveBalance score
        "get_inactivity_penalty_deltas: effective_balance * inactivity_scores[index]"
      let denom ← checkedMul Const.inactivityScoreBias
        (UInt64.ofNat Const.inactivityPenaltyQuotientBellatrix)
        "get_inactivity_penalty_deltas: INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX"
      penalties := penalties.set! i (num / denom)
  return penalties

/-- Apply per-validator `(rewards, penalties)` to balances. `increaseBalance` rejects on a
`uint64` overflow, so the fold runs in `StateTransition`. -/
forkdef applyDeltas (rewards penalties : Array Gwei) (state : State) :
    StateTransition State := do
  let mut state := state
  for i in [0 : (sszGet state validators).size] do
    state ← increaseBalance state (UInt64.ofNat i) (rewards[i]!)
    state ← decreaseBalance state (UInt64.ofNat i) (penalties[i]!)
  return state

/-- `process_rewards_and_penalties`. -/
forkdef processRewardsAndPenalties : StateTransition Unit := do
  let state ← get
  if currentEpochOf state == Const.genesisEpoch then pure ()
  else
    let flagDeltas ← liftErr ((List.range 3).mapM (fun f => getFlagIndexDeltas state f))
    let inactPenalties ← liftErr (getInactivityPenaltyDeltas state)
    let zeros := Array.replicate (sszGet state validators).size (0 : Gwei)

    for (rewards, penalties) in flagDeltas do
      set (← applyDeltas rewards penalties (← get))
    set (← applyDeltas zeros inactPenalties (← get))

/-! ## Registry updates -/

/-- `process_registry_updates` (Electra: activation-eligibility, ejections, and
churn-unlimited activations in one pass). The three cases are the pyspec's
`if / elif / elif`, so a validator takes at most one of them per epoch. -/
forkdef processRegistryUpdates : StateTransition Unit := do
  let currentEpoch := currentEpochOf (← get)
  let activationEpoch ← liftErr (computeActivationExitEpoch currentEpoch)
  let n := (sszGet (← get) validators).size

  for idx in [0 : n] do
    let state ← get
    let validator := sszGet state validators[idx]!
    if isEligibleForActivationQueue validator then
      modifyState fun state => modValidator state (UInt64.ofNat idx) fun validator => { validator with activationEligibilityEpoch := currentEpoch + 1 }
    else if isActiveValidator validator currentEpoch && validator.effectiveBalance ≤ Const.ejectionBalanceG then
      initiateValidatorExit (UInt64.ofNat idx)
    else if isEligibleForActivation state validator then
      modifyState fun state => modValidator state (UInt64.ofNat idx) fun validator => { validator with activationEpoch := activationEpoch }

/-! ## Slashings (epoch penalty) -/

/-- `process_slashings`. The pyspec's `sum(state.slashings)` adds `Gwei` values, the
multiplier product is a `Gwei` product, and so is the per-validator penalty. Each is a checked
`uint64` op that raises `ValueError` past `2 ^ 64`, and the body forms each through
`checkedAdd` or `checkedMul` (`.arithmetic`). The epoch sum `epoch + EPOCHS_PER_SLASHINGS_VECTOR
// 2` runs only for a slashed validator (Python's `and`), and it is checked the same way. -/
forkdef processSlashings : StateTransition Unit := do
  let state ← get
  let epoch := currentEpochOf state
  let totalBalance ← liftErr (getTotalActiveBalance state)
  let sumSlashings ← (sszGet state slashings).toArray.foldlM (init := (0 : Gwei)) fun acc s =>
    checkedAdd acc s "process_slashings: sum(state.slashings)"
  let scaled ← checkedMul sumSlashings (UInt64.ofNat Const.proportionalSlashingMultiplierBellatrix)
    "process_slashings: sum(state.slashings) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX"
  let adjusted := umin scaled totalBalance
  let increment := Const.effectiveBalanceIncrementG
  let penaltyPerIncrement := adjusted / (totalBalance / increment)

  let mut state := state
  for i in [0 : (sszGet state validators).size] do
    let validator := sszGet state validators[i]!
    if validator.slashed then
      let target ← checkedAdd epoch (UInt64.ofNat Const.epochsPerSlashingsVector / 2)
        "process_slashings: epoch + EPOCHS_PER_SLASHINGS_VECTOR // 2"
      if target == validator.withdrawableEpoch then
        let penalty ← checkedMul penaltyPerIncrement (validator.effectiveBalance / increment)
          "process_slashings: penalty_per_effective_balance_increment * effective_balance_increments"
        state ← decreaseBalance state (UInt64.ofNat i) penalty
  set state

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
(setting `churnReached`) once it does not. The not-finalized and per-epoch-limit stops
leave `churnReached` false. Fulu removes the Electra stop at an eth1-bridge deposit
(`fulu/beacon-chain.md`, modified `process_pending_deposits`). -/
forkdef ppdLoop (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei) (nextEpoch : Epoch) :
    StateTransition DepositScan :=
  -- Fuel rather than a measure (§7.2): the scan stops on a data-dependent guard (churn
  -- exhausted, a not-yet-finalized slot, the per-epoch cap), not on a quantity that
  -- decreases every step, so the terminating invariant is not available at definition time.
  -- Fuel is `deposits.size + 1`: the `ndi ≥ deposits.size` guard returns `.done` one step
  -- before exhaustion, so `fuelLoop`'s `exhausted` value is unreachable.
  fuelLoop (deposits.size + 1) ({} : DepositScan) ({} : DepositScan) fun s => do
    if s.ndi ≥ deposits.size then return .done s
    let state ← get
    let deposit := deposits[s.ndi]!

    -- Stop the scan early: the deposit is not finalized, or this epoch's deposit cap is
    -- reached.
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
    else
      -- `processed_amount + deposit.amount` adds `Gwei` values, a checked `uint64` add.
      let total ← checkedAdd s.processed deposit.amount
        "process_pending_deposits: processed_amount + deposit.amount"
      if total > avail then return .done { s with churnReached := true }
      else applyPendingDeposit deposit; return advance total s.postpone

/-- `process_pending_deposits`. Churn is accumulated into `deposit_balance_to_consume`
only when the churn limit was actually hit; every other stop resets it to zero.
`deposit_balance_to_consume + churn` is a checked `uint64` add (`.arithmetic`). The final
`available - processed` cannot underflow, since the scan adds a deposit only while the sum
stays at most `available`. -/
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + 1
  let churn ← liftErr (getActivationExitChurnLimit state)
  let avail ← checkedAdd (sszGet state depositBalanceToConsume) churn
    "process_pending_deposits: deposit_balance_to_consume + get_activation_exit_churn_limit"
  let finalizedSlot ← liftErr (computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch)
  let deposits := (sszGet state pendingDeposits).toArray

  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch
  let remaining : SSZList PendingDeposit Const.pendingDepositsLimit ←
    sszOfArrayM "pendingDeposits" (deposits.extract scan.ndi deposits.size ++ scan.postpone)
  modifyState fun state => sszUpdate state with
    pendingDeposits := remaining,
    depositBalanceToConsume := if scan.churnReached then avail - scan.processed else 0

/-! ## Pending consolidations -/

/-- The consolidation-queue scan. Returns the next-pending index, tail-recursive on
`fuel = #consolidations`. A slashed source is skipped; an unwithdrawable source
stops the scan; otherwise the source's effective balance moves to the target. -/
forkdef pcLoop (cons : Array PendingConsolidation) (nextEpoch : Epoch) : StateTransition Nat :=
  -- Threaded accumulator is the next-pending index `npc`; `fuelLoop` owns the counter. Fuel
  -- rather than a measure (§7.2): an unwithdrawable source stops the scan early, so `npc` is
  -- the only quantity that moves and the stop is data-dependent, not structural. Fuel is
  -- `cons.size + 1`: the `npc ≥ cons.size` guard fires as
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
        let state ← decreaseBalance state pc.sourceIndex amt
        set (← increaseBalance state pc.targetIndex amt)
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

/-- `process_effective_balance_updates` (the hysteresis rule).

The pyspec reads `state.balances[index]` for each validator, and that read raises
`IndexError` on a list shorter than the registry. The body reads through `sszGetIdx`
(`.outOfBounds`). Both threshold sums are checked `uint64` adds that raise `ValueError` past
`2 ^ 64`. Python's `or` forms the second sum only when the first test fails, and the body
keeps that order. -/
forkdef processEffectiveBalanceUpdates : StateTransition Unit := do
  let hysteresisIncrement := Const.effectiveBalanceIncrementG / UInt64.ofNat Const.hysteresisQuotient
  let downward := hysteresisIncrement * UInt64.ofNat Const.hysteresisDownwardMultiplier
  let upward := hysteresisIncrement * UInt64.ofNat Const.hysteresisUpwardMultiplier
  let n := (sszGet (← get) validators).size

  for i in [0 : n] do
    let state ← get
    let validator := sszGet state validators[i]!
    let balance ← sszGetIdx (sszGet state balances) i
    let lower ← checkedAdd balance downward
      "process_effective_balance_updates: balance + DOWNWARD_THRESHOLD"
    let update ← if lower < validator.effectiveBalance then pure true
      else do
        let upper ← checkedAdd validator.effectiveBalance upward
          "process_effective_balance_updates: effective_balance + UPWARD_THRESHOLD"
        pure (decide (upper < balance))
    if update then
      let newEff := umin (balance - balance % Const.effectiveBalanceIncrementG) (getMaxEffectiveBalance validator)
      set (modValidator state (UInt64.ofNat i) (fun validator => { validator with effectiveBalance := newEff }))

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
  let zeros : SSZList ParticipationFlags Const.validatorRegistryLimit ←
    sszOfArrayM "currentEpochParticipation" (Array.replicate count (0 : ParticipationFlags))
  modifyState fun state =>
    sszUpdate state with
      previousEpochParticipation := current,
      currentEpochParticipation  := zeros

/-! ## Sync-committee rotation & proposer lookahead (shuffle-dependent) -/

/-- `process_sync_committee_updates`: at a sync-committee-period boundary, rotate
`next` into `current` and select a fresh `next` (balance-weighted, with the real
BLS aggregate pubkey).

The body writes twice. The pyspec assigns `current_sync_committee` before the call that can
fault (`altair/beacon-chain.md:779-784`). So when the selection faults, the state keeps the
rotated `current`, in the pyspec and here. The selection reads only the validators and the
randao mixes, and the first write does not change them. -/
forkdef processSyncCommitteeUpdates : StateTransition Unit := do
  let state ← get
  if (currentEpochOf state + 1) % UInt64.ofNat Const.epochsPerSyncCommitteePeriod == 0 then
    set (sszUpdate state with currentSyncCommittee := sszGet state nextSyncCommittee)
    let rotated ← get
    let nsc ← liftErr (getNextSyncCommittee rotated)
    modifyState fun state => sszUpdate state with nextSyncCommittee := nsc

/-- `process_proposer_lookahead` (Fulu, EIP-7917): shift out the first epoch's
proposers and append the freshly-computed proposers for
`current_epoch + MIN_SEED_LOOKAHEAD + 1`. -/
forkdef processProposerLookahead : StateTransition Unit := do
  let state ← get
  let old := sszGet state proposerLookahead
  -- Two writes: pyspec assigns the shifted slice before the call that can fault.
  set (sszUpdate state with proposerLookahead :=
    Vector.ofFn (fun i : Fin (2 * Const.slotsPerEpoch) =>
      if i.val < Const.slotsPerEpoch then vget old (i.val + Const.slotsPerEpoch)
      else vget old i.val))
  let shifted ← get
  let newProposers ←
    getBeaconProposerIndices shifted (currentEpochOf shifted + Const.minSeedLookahead + 1)
  modifyState fun state =>
    sszUpdate state with proposerLookahead :=
      Vector.ofFn (fun i : Fin (2 * Const.slotsPerEpoch) =>
        if i.val < Const.slotsPerEpoch then vget (sszGet state proposerLookahead) i.val
        else newProposers[i.val - Const.slotsPerEpoch]!)

end

end EthCLSpecs.Fulu
