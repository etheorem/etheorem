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
The two-thirds tests are the pyspec's `get_total_balance(state, indices) * 3 >=
total_active_balance * 2` pairs: checked `Gwei` products, each bound where the
pyspec forms it (left operand first, then the active balance's). A `Nat`
narrowing would hide the product's own range raise near `2^64`
(`SPEC_ARITHMETIC.md` §6). -/
forkdef weighJustificationAndFinalization (totalActive prevTarget currTarget : Gwei) :
    StateTransition Unit := do
  let state ← get
  let prevEpoch := previousEpochOf state
  let currEpoch := currentEpochOf state
  -- Evaluation order is Python's: each target's product forms in its own `if`
  -- condition, the root read only in the branch, so the current-epoch product
  -- forms after the previous branch's root read. A `Nat` narrowing would hide
  -- the product's own range raise near `2^64` (`SPEC_ARITHMETIC.md` §6).
  let prevScaled ← prevTarget * 3
  let activeScaled ← totalActive * 2
  let justifyPrev := prevScaled ≥ activeScaled
  let prevRoot ← if justifyPrev then getBlockRoot state prevEpoch else pure default
  let currScaled ← currTarget * 3
  let justifyCurr := currScaled ≥ activeScaled
  let currRoot ← if justifyCurr then getBlockRoot state currEpoch else pure default
  -- The checkpoints the finalization tests read are the ones the shift-and-justify write
  -- started from, so they are captured before it lands.
  let oldPrev := sszGet state previousJustifiedCheckpoint
  let oldCurr := sszGet state currentJustifiedCheckpoint

  -- Shift the bit window, then justify the previous and current epochs that reached
  -- a two-thirds target supermajority.
  modifyState fun state => Id.run do
    let mut state := state
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
    return state

  -- Finalize on the four supermajority-link bit patterns. Python tests them in order
  -- against the updated bits, forming each `old.epoch + k` only once its bit conjuncts
  -- pass, so every sum binds inside its own branch (`SPEC_ARITHMETIC.md` §4.3), and a
  -- later match overwrites an earlier one.
  let bits := sszGet (← get) justificationBits
  let fin3 ← if bitGet bits 1 && bitGet bits 2 && bitGet bits 3 then
    (do let sum ← oldPrev.epoch + 3; pure (sum == currEpoch))
  else pure false
  let fin2 ← if bitGet bits 1 && bitGet bits 2 then
    (do let sum ← oldPrev.epoch + 2; pure (sum == currEpoch))
  else pure false
  let fin3c ← if bitGet bits 0 && bitGet bits 1 && bitGet bits 2 then
    (do let sum ← oldCurr.epoch + 2; pure (sum == currEpoch))
  else pure false
  let fin2c ← if bitGet bits 0 && bitGet bits 1 then
    (do let sum ← oldCurr.epoch + 1; pure (sum == currEpoch))
  else pure false
  let mut finalized : Option Checkpoint := none
  if fin3 then finalized := some oldPrev
  if fin2 then finalized := some oldPrev
  if fin3c then finalized := some oldCurr
  if fin2c then finalized := some oldCurr
  if let some cp := finalized then
    modifyState fun state => sszUpdate state with finalizedCheckpoint := cp

/-- `process_justification_and_finalization`. -/
forkdef processJustificationAndFinalization : StateTransition Unit := do
  let state ← get
  -- `get_current_epoch(state) <= GENESIS_EPOCH + 1`: the sum is the checked `Epoch` add.
  let genesisPlusOne ← Const.genesisEpoch + 1
  if currentEpochOf state ≤ genesisPlusOne then pure ()
  else
    -- `fulu/minimal.py:1724-1734`: both index sets, then the three totals, in this order;
    -- each can raise `IndexError` on a registry read.
    let prevIdx ← liftErr (getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state))
    let currIdx ← liftErr (getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (currentEpochOf state))
    let totalActive ← liftErr (getTotalActiveBalance state)
    let prevTotal ← liftErr (getTotalBalance state prevIdx)
    let currTotal ← liftErr (getTotalBalance state currIdx)
    weighJustificationAndFinalization totalActive prevTotal currTotal

/-! ## Inactivity -/

/-- `process_inactivity_updates` (`fulu/mainnet.py:4537-4554`): a timely-target voter's score
drops by one, any other eligible validator's rises by `INACTIVITY_SCORE_BIAS`, and outside a
leak every score drops by `INACTIVITY_SCORE_RECOVERY_RATE`. Both drops are the spec's
`saturating_sub`, floored at zero. The leak check sits inside the loop, after the score
update, at its pinned position: `is_in_inactivity_leak` reads `finalized_checkpoint.epoch`
against `previous_epoch`, so binding it before the loop would raise the delay's checked
subtraction on states the loop never inspects (an empty eligible set succeeds in Python).

The pyspec forms `get_unslashed_participating_indices` inside the loop, once per eligible
index, after the eligible set. The loop never writes a field that set reads, so every
evaluation returns the same set or raises the same fault; the body forms it on the first
iteration and reuses it. An empty eligible set therefore never reads the participation
list, as in Python. `state.inactivity_scores[index]` is a raising list read. -/
forkdef processInactivityUpdates : StateTransition Unit := do
  let state ← get
  if currentEpochOf state == Const.genesisEpoch then pure ()
  else
    let eligible ← getEligibleValidatorIndices state

    let mut state := state
    let mut matchingTarget : Option (Array ValidatorIndex) := none
    for vi in eligible do
      let matching ← match matchingTarget with
        | some m => pure m
        | none => liftErr (getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex
            (previousEpochOf state))
      matchingTarget := some matching
      -- The score is a checked `Gwei`: `saturating_sub` floors at zero (the
      -- spec's own guard), and `+= INACTIVITY_SCORE_BIAS` is the checked add,
      -- bound in the branch that forms it; the write is the plain store of the
      -- value the monadic block computed.
      let cur ← sszGetIdx (sszGet state inactivityScores) vi
      let cur ← if matching.contains vi then pure (cur.saturatingSub 1)
                else cur + Const.inactivityScoreBias
      -- `is_in_inactivity_leak` runs here, after the score update, per validator.
      let leak ← isInInactivityLeak state
      let cur := if !leak then cur.saturatingSub Const.inactivityScoreRecoveryRate else cur
      -- `toPlainNat`: the raising read above proved `vi` in range for this list.
      state := sszModify state inactivityScores[vi.toPlainNat]! as _old => cur
    set state

/-! ## Rewards & penalties -/

/-- `get_flag_index_deltas` for one flag: `(rewards, penalties)` per validator
(`fulu/mainnet.py:4445-4471`). Returns `Except StateTransitionError` because
`getBaseReward` does; a bad validator index rejects rather than masking. The
increments, the reward numerator, the divisor, and each `+=` are the checked
`Gwei` chain, bound where the pyspec assigns it (`SPEC_ARITHMETIC.md` §4.3's
worked example). The leak check sits in the unslashed-participating branch, after
`getBaseReward`, at its pinned position: an eligible set that never enters that
branch never calls `is_in_inactivity_leak`, so its fault cannot fire where Python
succeeds. -/
forkdef getFlagIndexDeltas (state : State) (flagIndex : Nat) :
    Except StateTransitionError (Array Gwei × Array Gwei) := do
  let n := (sszGet state validators).size
  let mut rewards := Array.replicate n (0 : Gwei)
  let mut penalties := Array.replicate n (0 : Gwei)

  let prevEpoch := previousEpochOf state
  let unslashed ← getUnslashedParticipatingIndices state flagIndex prevEpoch
  let weight := Const.participationFlagWeights[flagIndex]!
  let unslashedBalance ← getTotalBalance state unslashed
  let unslashedIncrements ← unslashedBalance / Const.effectiveBalanceIncrementG
  let activeBalance ← getTotalActiveBalance state
  let activeIncrements ← activeBalance / Const.effectiveBalanceIncrementG

  for vi in ← getEligibleValidatorIndices state do
    let baseReward ← getBaseReward state vi
    if unslashed.contains vi then
      -- `is_in_inactivity_leak` runs here, after `get_base_reward`, and only for
      -- an unslashed participating validator.
      let leak ← isInInactivityLeak state
      if !leak then
        let rewardNumerator ← baseReward * weight * unslashedIncrements
        -- `rewards[index] += …` reads the element before it forms the right side.
        let previousReward ← liftErr (getAt rewards vi)
        let rewardDelta ← rewardNumerator / (activeIncrements * Const.weightDenominator)
        let updatedReward ← previousReward + rewardDelta
        rewards ← liftErr (setAt rewards vi updatedReward)
    else if flagIndex != Const.timelyHeadFlagIndex then
      let previousPenalty ← liftErr (getAt penalties vi)
      let penaltyDelta ← baseReward * weight / Const.weightDenominator
      let updatedPenalty ← previousPenalty + penaltyDelta
      penalties ← liftErr (setAt penalties vi updatedPenalty)
  return (rewards, penalties)

/-- `get_inactivity_penalty_deltas` (`fulu/mainnet.py:1815-1832`): penalties only.
The numerator is the checked `effective_balance * inactivity_scores[index]`
product, the divisor the checked product
`INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX`, and the `+=` the
checked `Gwei` add. The two reads `state.validators[index]` and
`state.inactivity_scores[index]` raise `IndexError` past the end, so they go through
`getAt` in the pyspec's order. -/
forkdef getInactivityPenaltyDeltas (state : State) : Except StateTransitionError (Array Gwei) := do
  let validators := sszGet state validators
  let iscores := sszGet state inactivityScores
  let mut penalties := Array.replicate validators.size (0 : Gwei)
  let matchingTarget ← getUnslashedParticipatingIndices state Const.timelyTargetFlagIndex (previousEpochOf state)

  for vi in ← getEligibleValidatorIndices state do
    if !matchingTarget.contains vi then
      let validator ← liftErr (getAt validators vi)
      let score ← liftErr (getAt iscores vi)
      let num ← validator.effectiveBalance * score
      -- `INACTIVITY_SCORE_BIAS` is a checked config value at the pin, so the
      -- divisor is the checked product, with no `Nat` intermediate over a checked
      -- operand (`SPEC_ARITHMETIC.md` §6). The product binds each time Python forms
      -- it, inside the loop, so an overflow raises only once a penalty is due.
      let denom ← Const.inactivityScoreBias * Const.inactivityPenaltyQuotientBellatrix
      -- `penalties[index] += …` reads the element before it forms the right side.
      let previousPenalty ← liftErr (getAt penalties vi)
      let delta ← num / denom
      let updated ← previousPenalty + delta
      penalties ← liftErr (setAt penalties vi updated)
  return penalties

/-- Apply per-validator `(rewards, penalties)` to balances. `increaseBalance` rejects on a
`uint64` overflow, so the fold runs in `StateTransition`. Each call casts the position with
the pyspec's checked `ValidatorIndex(index)` (`fulu/minimal.py:1840-1841`). The delta arrays
have the registry's length, so their reads are structural. -/
forkdef applyDeltas (rewards penalties : Array Gwei) (state : State) :
    StateTransition State := do
  let mut state := state
  for i in [0 : (sszGet state validators).size] do
    let vi ← CLUint64.ofNat? i
    state ← increaseBalance state vi (rewards[i]!)
    let vi ← CLUint64.ofNat? i
    state ← decreaseBalance state vi (penalties[i]!)
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
churn-unlimited activations in one pass). -/
forkdef processRegistryUpdates : StateTransition Unit := do
  let currentEpoch := currentEpochOf (← get)
  let activationEpoch ← computeActivationExitEpoch currentEpoch
  let n := (sszGet (← get) validators).size

  -- `validator.activation_eligibility_epoch = current_epoch + 1`: the checked `Epoch` add,
  -- bound once where Python computes it (inside the loop body, per validator).
  let nextEligibility ← currentEpoch + 1
  for idx in [0 : n] do
    let state ← get
    let validator := sszGet state validators[idx]!
    -- The two field writes go through the enumerated position, as the pyspec writes
    -- through the `validator` object; only the exit call casts `ValidatorIndex(index)`.
    if isEligibleForActivationQueue validator then
      modifyState fun state => sszModify state validators[idx]! := fun validator =>
        { validator with activationEligibilityEpoch := nextEligibility }
    if isActiveValidator validator currentEpoch && validator.effectiveBalance ≤ Const.ejectionBalanceG then
      let vi ← CLUint64.ofNat? idx
      initiateValidatorExit vi
    if isEligibleForActivation state validator then
      modifyState fun state => sszModify state validators[idx]! := fun validator =>
        { validator with activationEpoch := activationEpoch }

/-! ## Slashings (epoch penalty) -/

/-- `process_slashings` (`fulu/mainnet.py:1871-1895`). The `sum(state.slashings)`
accumulator and the multiplier product are the checked `Gwei` chain; the
increment division divides first, the guard the spec writes out
(`SPEC_ARITHMETIC.md` §3.5). Each intermediate binds where the pyspec forms it. -/
forkdef processSlashings : StateTransition Unit := do
  let state ← get
  let epoch := currentEpochOf state
  let totalBalance ← liftErr (getTotalActiveBalance state)
  let sumSlashings ← (sszGet state slashings).toArray.foldlM (fun acc x => acc + x) (0 : Gwei)
  let scaled ← sumSlashings * Const.proportionalSlashingMultiplierBellatrix
  let adjusted := min scaled totalBalance
  let increment := Const.effectiveBalanceIncrementG
  let penaltyPerIncrement ← adjusted / (totalBalance / increment)

  -- `epoch + EPOCHS_PER_SLASHINGS_VECTOR // 2`: the divisor is the checked constant, so the
  -- half-ring sum is the checked `Epoch` chain, bound before the loop Python computes it in.
  let halfRing ← Const.epochsPerSlashingsVectorC / 2
  let withdrawableBound ← epoch + halfRing
  let mut state := state
  for i in [0 : (sszGet state validators).size] do
    let validator := sszGet state validators[i]!
    if validator.slashed && withdrawableBound == validator.withdrawableEpoch then
      let increments ← validator.effectiveBalance / increment
      let penalty ← penaltyPerIncrement * increments
      -- `decrease_balance(state, ValidatorIndex(index), penalty)`: the checked cast.
      let vi ← CLUint64.ofNat? i
      state ← decreaseBalance state vi penalty
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
(setting `churnReached`) once it does not. The not-finalized / per-epoch-limit stops leave
`churnReached` false.

Fulu's `process_pending_deposits` (`fulu/beacon-chain.md`, "Modified
`process_pending_deposits`") drops Electra's eth1-bridge stop, because Fulu removes the former
deposit mechanism (consensus-specs #4704, in the text since alpha.12). F1
signature repair (inventory §2.5): `finalizedSlot` is the spec's
`compute_start_slot_at_epoch(...)` value, a `Slot`; it keeps the raw `Slot` type
until Stage 5. -/
forkdef ppdLoop (deposits : Array PendingDeposit) (finalizedSlot : Slot) (avail : Gwei)
    (nextEpoch : Epoch) :
    StateTransition DepositScan :=
  -- Fuel rather than a measure (§7.2): the scan stops on a data-dependent guard (churn
  -- exhausted, a not-yet-finalized slot), not on a quantity that
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
      -- `is_churn_limit_reached = processed_amount + deposit.amount >
      -- available_for_processing`: the sum is the checked `Gwei` add, bound inside
      -- the branch that forms it.
      let running ← s.processed + deposit.amount
      if running > avail then return .done { s with churnReached := true }
      else
        applyPendingDeposit deposit
        return advance running s.postpone

/-- `process_pending_deposits`. Churn is accumulated into `deposit_balance_to_consume`
only when the churn limit was actually hit; every other stop resets it to zero. -/
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + 1
  -- `available_for_processing = deposit_balance_to_consume +
  -- get_activation_exit_churn_limit(state)`: the checked `Gwei` add, bound here.
  let churn ← liftErr (getActivationExitChurnLimit state)
  let avail ← (sszGet state depositBalanceToConsume) + churn
  let finalizedSlot ← computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch
  let deposits := (sszGet state pendingDeposits).toArray

  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch
  let remaining : SSZList PendingDeposit Const.pendingDepositsLimit ←
    sszOfArrayM "pendingDeposits" (deposits.extract scan.ndi deposits.size ++ scan.postpone)
  -- `available_for_processing - processed_amount` forms only in the churn-hit
  -- branch (the reset arm stores `Gwei(0)`), so the bind sits in its branch.
  let remainingChurn ← if scan.churnReached then avail - scan.processed else pure (0 : Gwei)
  modifyState fun state => sszUpdate state with
    pendingDeposits := remaining,
    depositBalanceToConsume := if scan.churnReached then remainingChurn else 0

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
      let src ← sszGetIdx (sszGet state validators) pc.sourceIndex
      if src.slashed then return .next (npc + 1)
      else if src.withdrawableEpoch > nextEpoch then return .done npc
      else
        let srcBal ← sszGetIdx (sszGet state balances) pc.sourceIndex
        -- `source_effective_balance = min(balances[source_index],
        -- source_validator.effective_balance)`: `min` picks an operand, total.
        let amt := min srcBal src.effectiveBalance
        let state ← decreaseBalance state pc.sourceIndex amt
        set (← increaseBalance state pc.targetIndex amt)
        return .next (npc + 1)

/-- `process_pending_consolidations`. -/
forkdef processPendingConsolidations : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + 1
  let pending := sszGet state pendingConsolidations
  let cons := pending.toArray
  let npc ← pcLoop cons nextEpoch

  modifyState fun state =>
    sszUpdate state with pendingConsolidations := sszDrop pending npc

/-! ## Effective-balance updates -/

/-- `process_effective_balance_updates` (`fulu/mainnet.py:1901-1926`), the
hysteresis rule. The thresholds are the checked `Gwei` chain
`EFFECTIVE_BALANCE_INCREMENT // HYSTERESIS_QUOTIENT` and its multiplier
products, and each comparison operand binds where the pyspec forms it; the
Python `or` short-circuits, so the upward add forms only when the downward
comparison is false. The reset is the checked round-and-cap pair. -/
forkdef processEffectiveBalanceUpdates : StateTransition Unit := do
  let mut state ← get

  for i in [0 : (sszGet state validators).size] do
    -- `balance = state.balances[index]` comes first (`fulu/minimal.py:1896`), a raising
    -- list read: a `balances` list shorter than the registry raises `IndexError` here.
    let validator := sszGet state validators[i]!
    let balance ← sszGetIdx (sszGet state balances) i
    -- Python assigns the three thresholds inside the loop
    -- (`fulu/mainnet.py:1903-1907`), so they form only for a validator that
    -- exists; a degenerate configuration raises there, not before the loop.
    let hysteresisIncrement ← Const.effectiveBalanceIncrementG / Const.hysteresisQuotient
    let downward ← hysteresisIncrement * Const.hysteresisDownwardMultiplier
    let upward ← hysteresisIncrement * Const.hysteresisUpwardMultiplier
    let downwardHit ← balance + downward
    let hit ← if downwardHit < validator.effectiveBalance then pure true
              else do
                let upwardHit ← validator.effectiveBalance + upward
                pure (upwardHit < balance)
    if hit then
      let rounded ← balance % Const.effectiveBalanceIncrementG
      let excess ← balance - rounded
      let newEff := min excess (getMaxEffectiveBalance validator)
      -- The pyspec writes through the enumerated `validator` object, with no cast.
      state := sszModify state validators[i]! := fun validator =>
        { validator with effectiveBalance := newEff }
  set state

/-- `process_slashings_reset`: zero the next epoch's slashings slot. The index is in
range by construction (`nextEpoch % EPOCHS_PER_SLASHINGS_VECTOR`), so the infallible
`[idx]!` element write is total (fits the `modifyState` context, no reject path). -/
forkdef processSlashingsReset : StateTransition Unit := do
  let nextEpoch ← (← getCurrentEpoch) + 1
  -- `nextEpoch % EPOCHS_PER_SLASHINGS_VECTOR` is the checked modulo; its in-range
  -- remainder is the write index (§4.5: the projection the mod bound permits).
  let idx ← nextEpoch % Const.epochsPerSlashingsVectorC
  modifyState fun state =>
    sszUpdate state with slashings[idx.toPlainNat]! := (0 : Gwei)

/-- `process_randao_mixes_reset`: carry the current epoch's RANDAO mix into the
next epoch's slot. -/
forkdef processRandaoMixesReset : StateTransition Unit := do
  let currentEpoch ← getCurrentEpoch
  let mix ← getRandaoMix currentEpoch
  let nextEpoch ← currentEpoch + 1
  let idx ← nextEpoch % Const.epochsPerHistoricalVectorC
  modifyState fun state =>
    sszUpdate state with randaoMixes[idx.toPlainNat]! := mix

/-- `process_eth1_data_reset`: clear the eth1 vote tally at the end of a voting
period. -/
forkdef processEth1DataReset : StateTransition Unit := do
  let nextEpoch ← (← getCurrentEpoch) + 1
  let period ← nextEpoch % Const.epochsPerEth1VotingPeriodC
  if period == (0 : Epoch) then
    modifyState fun state =>
      sszUpdate state with eth1DataVotes := sszOfArray #[] (by simp)

/-- `process_historical_summaries_update`: at the end of a historical-root period,
append a summary of the block-roots and state-roots vectors. -/
forkdef processHistoricalSummariesUpdate : StateTransition Unit := do
  let nextEpoch ← (← getCurrentEpoch) + 1
  -- `SLOTS_PER_HISTORICAL_ROOT // SLOTS_PER_EPOCH` stays the structural `Nat` quotient of
  -- the two slot-side constants; the mixed modulo keeps the checked raise (§4.2).
  let period ← (nextEpoch % (Const.slotsPerHistoricalRoot / Const.slotsPerEpoch) : Checked _)
  if period == (0 : Epoch) then
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
BLS aggregate pubkey). -/
forkdef processSyncCommitteeUpdates : StateTransition Unit := do
  let state ← get
  let nextEpoch ← currentEpochOf state + 1
  let period ← nextEpoch % Const.epochsPerSyncCommitteePeriodC
  if period == (0 : Epoch) then
    let nsc ← liftErr (getNextSyncCommittee state)
    set (sszUpdate state with
      currentSyncCommittee := sszGet state nextSyncCommittee,
      nextSyncCommittee := nsc)

/-- `process_proposer_lookahead` (Fulu, EIP-7917): shift out the first epoch's
proposers and append the freshly-computed proposers for
`current_epoch + MIN_SEED_LOOKAHEAD + 1`. -/
forkdef processProposerLookahead : StateTransition Unit := do
  let state ← get
  -- `get_current_epoch(state) + MIN_SEED_LOOKAHEAD + 1`: the checked `Epoch` chain, bound
  -- before the proposer walk it feeds.
  let lookaheadEpoch ← currentEpochOf state + Const.minSeedLookahead + 1
  let newProposers ←
    liftErr (getBeaconProposerIndices state lookaheadEpoch)
  let old := sszGet state proposerLookahead
  set (sszUpdate state with proposerLookahead :=
    Vector.ofFn (fun i : Fin (2 * Const.slotsPerEpoch) =>
      if i.val < Const.slotsPerEpoch then vget old (i.val + Const.slotsPerEpoch)
      else newProposers[i.val - Const.slotsPerEpoch]!))

end

end EthCLSpecs.Fulu
