import EthCLSpecs.Proofs.Gloas.ConfigValid
import EthCLSpecs.Proofs.Gloas.StateInvariants
import EthCLSpecs.Gloas.Transition
import EthCLLib.Proofs.IndicesWhere

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSafe`: the states on which `process_epoch` cannot fail

The Gloas counterpart of `Proofs/Fulu/EpochSafe.lean`. Gloas's registry lists and queues are
progressive lists, with no cap, so no append can fail; `registryRoom` bounds the registry by
`2^64` instead, which keeps every registry index a `uint64`. Gloas adds two error sites the
liveness fields cover: the proposer lookahead samples only unslashed validators
(`liveUnslashed`), and the payload-timeliness committee window needs at least `SLOTS_PER_EPOCH`
validators active at `E + MIN_SEED_LOOKAHEAD + 1` (`liveCount`), so that every slot's beacon
committees are nonempty. `ptcRoom` keeps that epoch's slots below `2^64`.

`EpochSafe b n v` collects the facts about a Fulu `BeaconState` under which `processEpoch` runs
to `.ok`, and which the post-state satisfies again (`Proofs/Gloas/EpochSuccess.lean`). Each fact
rules out one error site the epoch can reach:

* `registrySizes`: the balance, inactivity and participation lists have the registry's length,
  so a balance read at a validator index and the five registry appends never fail.
* `consolidationIdx`, `consolidationCount`, `effCap`: a queued consolidation names validators in
  the registry, and moves at most `MAX_EFFECTIVE_BALANCE_ELECTRA` into its target.
* `depositCap`: a pending deposit adds at most `b.deposit` to a balance.
* `slotRoom`: the block-root reads of justification add `SLOTS_PER_HISTORICAL_ROOT` to an epoch
  start without a `uint64` overflow, and the activation epoch `E + 1 + MAX_SEED_LOOKAHEAD` does
  not wrap.
* `registryRoom`: the registry, with every validator the deposit queue can create, indexes
  below `2^64`.
* `exitRoom`: an ejection's `exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` does not
  overflow.
* `historyRoom`: the historical-summaries list has room for an append.
* `balanceRoom`: no balance overflows when rewards, deposits and consolidations add to it.
* `live`: some validator is active at `E + 1` and at `E + MIN_SEED_LOOKAHEAD + 1`, the epochs the
  sync committee and the proposer lookahead sample.

Two failure modes need premises outside the state. `RewardsWithin R v` bounds each flag reward
by `R`: the reward formula divides by the current active balance, and no structural fact bounds
the previous epoch's participating balance against it. `ZeroChunksOften`
(`EthCLLib/Proofs/ZeroChunks.lean`) is the hash premise for balance-weighted selection.

## The budget

Three quantities grow with every call, even at a fixed slot: the historical summaries (one
append per period), the earliest exit epoch (one step per ejection), and the balances (rewards,
deposits and consolidations). No bound on them is closed under `processEpoch`. `n` counts the
calls the headroom still covers, and a call spends one unit: `EpochSafe b (n + 1) v` gives
`EpochSafe b n w`. `EpochBudget` fixes the per-call caps that size one unit.

## Not necessary for reachability

`registrySizes`, `consolidationIdx` and `effCap` hold on every reachable state. The rest do not:
the budgets run out, a deposit request may carry any amount, and every validator may exit.
`EpochSafe` is a sufficient condition for one more epoch, not a consequence of reachability.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Gloas

/-- The per-call caps one unit of the budget covers. -/
structure EpochBudget where
  /-- The cap on one validator's reward for one participation flag. -/
  reward : Nat
  /-- The cap on one pending deposit's amount. -/
  deposit : Nat
  /-- The cap on the pending-consolidation queue's length. -/
  consolidations : Nat

/-- How much one call can add to one balance: three flag rewards, the deposits one call applies,
and one consolidation per queued entry, each moving at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
def EpochBudget.growth [Preset] (b : EpochBudget) : Nat :=
  3 * b.reward + Const.maxPendingDepositsPerEpoch * b.deposit +
    b.consolidations * Const.maxEffectiveBalanceElectra

/-- The smallest per-epoch exit churn the config allows: `get_activation_exit_churn_limit` is the
smaller of `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` and the balance churn, and the balance
churn is at least `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA` rounded down to an increment. -/
def exitChurnFloor [Preset] [Config] : Nat :=
  min Const.maxPerEpochActivationExitChurnLimit.toNat
    (Const.minPerEpochChurnLimitElectra.toNat -
      Const.minPerEpochChurnLimitElectra.toNat % Const.effectiveBalanceIncrement)

/-- How far one ejection can move the earliest exit epoch: an ejected validator's effective
balance is at most `EJECTION_BALANCE`, and the churn spends at least `exitChurnFloor` per epoch. -/
def ejectionStep [Preset] [Config] : Nat :=
  (Const.ejectionBalanceG.toNat - 1) / exitChurnFloor + 1

/-- The epoch the next exit can land on, at the earliest: `compute_exit_epoch_and_update_churn`
starts from the larger of `earliest_exit_epoch` and `E + 1 + MAX_SEED_LOOKAHEAD`. -/
def exitStart [Preset] (v : BeaconState) : Nat :=
  max v.earliestExitEpoch.toNat ((computeEpochAtSlot v.slot).toNat + 1 + Const.maxSeedLookahead.toNat)

/-- The registry plus the validators the deposit queue can still create. A call never grows it:
an applied deposit leaves the queue and adds at most one validator. -/
def registryPotential [Preset] (v : BeaconState) : Nat :=
  v.validators.val.size + v.pendingDeposits.val.size

/-- Some validator is active at `e`. -/
def Live [Preset] (v : BeaconState) (e : Epoch) : Prop :=
  ∃ i, ∃ h : i < v.validators.val.size, isActiveValidator v.validators.val[i] e = true

/-- Some unslashed validator is active at `e`: the Gloas proposer lookahead samples only those. -/
def LiveUnslashed [Preset] (v : BeaconState) (e : Epoch) : Prop :=
  ∃ i, ∃ h : i < v.validators.val.size,
    isActiveValidator v.validators.val[i] e = true ∧ v.validators.val[i].slashed = false

/-- At least `k` validators are active at `e`, counted as `get_active_validator_indices` does. -/
def LiveCount [Preset] (v : BeaconState) (e : Epoch) (k : Nat) : Prop :=
  k ≤ (EthCLLib.Spec.indicesWhere v.validators.val (fun x _ => isActiveValidator x e)).size

/-- A live epoch gives the samplers a nonempty candidate list. -/
theorem Live.activeIndices_pos [Preset] [HasherTag] {v : BeaconState} {e : Epoch} (h : Live v e) :
    0 < (getActiveValidatorIndices (pureState v) e).size := by
  unfold getActiveValidatorIndices
  apply EthCLLib.Proofs.indicesWhere_size_pos
  obtain ⟨i, hi, ha⟩ := h
  refine ⟨i, hi, ?_⟩
  simp only [EthCLLib.Proofs.pureState_eq_uncached, EthCLLib.Proofs.box_view_uncached,
    EthCLLib.Proofs.uncachedSSZ_ofValue_view]
  rw [getElem!_pos _ i hi]
  exact ha

/-- A live unslashed validator gives the Gloas proposer lookahead a nonempty candidate list. -/
theorem LiveUnslashed.proposers_pos [Preset] [HasherTag] {v : BeaconState} {e : Epoch}
    (h : LiveUnslashed v e) (hV : v.validators.val.size < 2 ^ 64) :
    0 < ((getActiveValidatorIndices (pureState v) e).filter
      (fun vi => !((pureState v).view.validators[vi.toNat]!).slashed)).size := by
  obtain ⟨i, hi, ha, hsl⟩ := h
  have hsize : UInt64.size = 2 ^ 64 := rfl
  have hi' : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by omega)
  have hget : (pureState v).view.validators[i]! = v.validators.val[i] := by
    show v.validators[i]! = _
    rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.ProgressiveList Validator) i => i < xs.size)
      (h := hi)]
    rfl
  have hmem : UInt64.ofNat i ∈ getActiveValidatorIndices (pureState v) e := by
    unfold getActiveValidatorIndices
    refine EthCLLib.Proofs.mem_indicesWhere_of (xs := (pureState v).view.validators.toArray) hi ?_
    show isActiveValidator ((pureState v).view.validators.toArray[i]!) e = true
    rw [getElem!_pos _ i hi]
    exact ha
  refine Array.size_pos_of_mem (Array.mem_filter.mpr ⟨hmem, ?_⟩)
  rw [hi', hget, hsl]
  rfl

/-- The reward `get_flag_index_deltas` pays validator `vi` for flag `f` outside an inactivity
leak: `base_reward * weight * unslashed_participating_increments // (active_increments *
WEIGHT_DENOMINATOR)`, read off the state as the spec does (`Gloas/EpochProcessing.lean:132`). In a
leak the spec pays nothing, so this bounds the reward either way. -/
def flagReward [Preset] [HasherTag] (v : BeaconState) (f : Nat) (vi : ValidatorIndex) : Nat :=
  (v.validators.val[vi.toNat]!).effectiveBalance.toNat / Const.effectiveBalanceIncrement *
      getBaseRewardPerIncrement (pureState v) *
    Const.participationFlagWeights[f]! *
    ((getTotalBalance (pureState v) (getUnslashedParticipatingIndices (pureState v) f
      (previousEpochOf (pureState v)))).toNat / Const.effectiveBalanceIncrement) /
    ((getTotalActiveBalance (pureState v)).toNat / Const.effectiveBalanceIncrement *
      Const.weightDenominator)

/-- The fields the reward formula reads. -/
def rewardInputs [Preset] (v : BeaconState) :
    Slot × SizzLean.Repr.ProgressiveList Validator ×
      SizzLean.Repr.ProgressiveList ParticipationFlags ×
      SizzLean.Repr.ProgressiveList ParticipationFlags :=
  (v.slot, v.validators, v.previousEpochParticipation, v.currentEpochParticipation)

/-- The reward formula reads only `rewardInputs`. -/
theorem flagReward_congr [Preset] [HasherTag] {v w : BeaconState} (h : rewardInputs w = rewardInputs v)
    (f : Nat) (vi : ValidatorIndex) : flagReward w f vi = flagReward v f vi := by
  simp only [rewardInputs, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [flagReward, getBaseRewardPerIncrement, getTotalActiveBalance, getTotalBalance,
    getActiveValidatorIndices, getUnslashedParticipatingIndices, previousEpochOf, currentEpochOf,
    EthCLLib.Proofs.pureState_eq_uncached, EthCLLib.Proofs.box_view_uncached,
    EthCLLib.Proofs.uncachedSSZ_ofValue_view, h1, h2, h3, h4]
  rfl

/-- Every flag reward of every validator is at most `R`. A premise of each call, because the
reward formula divides by the current active balance, which the state does not bound below. -/
def RewardsWithin [Preset] [HasherTag] (R : Nat) (v : BeaconState) : Prop :=
  ∀ f < 3, ∀ i < v.validators.val.size, flagReward v f (UInt64.ofNat i) ≤ R

/-- The reward bound carries across a step that keeps `rewardInputs`. -/
theorem RewardsWithin.congr [Preset] [HasherTag] {R : Nat} {v w : BeaconState} (hv : RewardsWithin R v)
    (h : rewardInputs w = rewardInputs v) : RewardsWithin R w := by
  intro f hf i hi
  rw [flagReward_congr h]
  have hval : w.validators = v.validators := by
    simp only [rewardInputs, Prod.mk.injEq] at h; exact h.2.1
  exact hv f hf i (by rw [← hval]; exact hi)

/-- The states from which `processEpoch` succeeds `n + 1` more times, given the per-call premises.
The module docstring names the error site each field rules out. -/
structure EpochSafe [Preset] [Config] (b : EpochBudget) (n : Nat) (v : BeaconState) : Prop where
  registrySizes : RegistrySizes v
  consolidationIdx : ∀ pc ∈ v.pendingConsolidations.val,
    pc.sourceIndex.toNat < v.validators.val.size ∧ pc.targetIndex.toNat < v.validators.val.size
  consolidationCount : v.pendingConsolidations.val.size ≤ b.consolidations
  effCap : ∀ x ∈ v.validators.val, x.effectiveBalance.toNat ≤ Const.maxEffectiveBalanceElectra
  depositCap : ∀ d ∈ v.pendingDeposits.val, d.amount.toNat ≤ b.deposit
  slotRoom : v.slot.toNat + Const.slotsPerHistoricalRoot < 2 ^ 64 ∧
    (computeEpochAtSlot v.slot).toNat + 1 + Const.maxSeedLookahead.toNat < 2 ^ 64
  registryRoom : registryPotential v + Const.maxPendingDepositsPerEpoch < 2 ^ 64
  ptcRoom : ((computeEpochAtSlot v.slot).toNat + Const.minSeedLookahead.toNat + 2) *
    Const.slotsPerEpoch ≤ 2 ^ 64
  exitRoom : exitStart v + (n + 1) * (ejectionStep * registryPotential v) +
    Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64
  historyRoom : v.historicalSummaries.val.size + n + 1 ≤ Const.historicalRootsLimit
  balanceRoom : (n + 1) * b.growth < 2 ^ 64 ∧
    ∀ x ∈ v.balances.val, x.toNat + (n + 1) * b.growth < 2 ^ 64
  live : Live v (computeEpochAtSlot v.slot + 1) ∧
    Live v (computeEpochAtSlot v.slot + Const.minSeedLookahead + 1)
  liveUnslashed : LiveUnslashed v (computeEpochAtSlot v.slot + Const.minSeedLookahead + 1)
  liveCount : LiveCount v (computeEpochAtSlot v.slot + Const.minSeedLookahead + 1) Const.slotsPerEpoch

end EthCLSpecs.Proofs.Gloas
