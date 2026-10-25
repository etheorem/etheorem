import EthCLSpecs.Proofs.Heze.KeepsUncached.Block

/-!
# `EthCLSpecs.Proofs.Heze.KeepsUncached.Withdrawals`: the withdrawal sweep keeps the uncached box

`processWithdrawals` is the third substep of `processBlock`. It computes the expected
withdrawals with four readers, applies them with `applyWithdrawals`, and then writes six
bookkeeping fields. This file proves `KeepsUncached` for each of these functions.

The four readers and `balanceAfterWithdrawals` only read the state, through loops,
checked reads and checked arithmetic. `applyWithdrawals` threads a local state through a
loop over the withdrawals. Each step writes a builder balance or returns a new local
state through `decreaseBalance`. The loop invariant says that the local state is pure
(`IsPure`), as in `processSyncAggregate`. All the lemmas are supporting facts, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze (Preset Config ValidatorIndex BeaconState Withdrawal WithdrawalIndex
  balanceAfterWithdrawals getBuilderWithdrawals getPendingPartialWithdrawals
  getBuildersSweepWithdrawals getValidatorsSweepWithdrawals getExpectedWithdrawals
  applyWithdrawals processWithdrawals)
open EthCLLib.Proofs (pureState KeepsUncached keepsUncached_bind keepsUncached_liftErr
  keepsUncached_get keepsUncached_ite keepsUncached_pure keepsUncached_modify
  keepsUncached_foldlM_list keepsUncachedFrom_get_bind keepsUncachedFrom_set
  keepsUncachedFrom_forIn_array_bind_P IsPure returnsPureVia_bind_returns
  returnsPureVia_bind_keeps returnsPureVia_pure step_of_returnsPureVia)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `balanceAfterWithdrawals` keeps the flavour: a checked sum over the withdrawals, one
checked read of the balance, and one checked difference. The sum is an `Array.foldlM`,
which runs as the `List.foldlM` of its `toList`. -/
theorem keepsUncached_balanceAfterWithdrawals (state : BeaconState) (vi : ValidatorIndex)
    (ws : Array Withdrawal) :
    KeepsUncached (balanceAfterWithdrawals (StateTransition := HezeRun) (pureState state)
      vi ws) := by
  unfold balanceAfterWithdrawals
  refine keepsUncached_bind ?_ (fun _ => ?_)
  · rw [← Array.foldlM_toList]
    exact keepsUncached_foldlM_list _ (fun _ _ => by keeps_uncached) _ _
  · keeps_uncached

/-- `getBuilderWithdrawals` keeps the flavour: a read, then a loop over the builder
queue that builds the withdrawal list and writes nothing. -/
theorem keepsUncached_getBuilderWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) :
    KeepsUncached (getBuilderWithdrawals (StateTransition := HezeRun) withdrawalIndex prior) := by
  unfold getBuilderWithdrawals
  keeps_uncached

/-- `getPendingPartialWithdrawals` keeps the flavour: a read, then a loop over the
pending partial queue with a checked validator read and `balanceAfterWithdrawals`. -/
theorem keepsUncached_getPendingPartialWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) :
    KeepsUncached (getPendingPartialWithdrawals (StateTransition := HezeRun) withdrawalIndex
      prior) := by
  unfold getPendingPartialWithdrawals
  keeps_uncached_using [keepsUncached_balanceAfterWithdrawals _ _ _]

/-- `getBuildersSweepWithdrawals` keeps the flavour: a read, then a range loop over the
builders with a checked builder read. -/
theorem keepsUncached_getBuildersSweepWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) :
    KeepsUncached (getBuildersSweepWithdrawals (StateTransition := HezeRun) withdrawalIndex
      prior) := by
  unfold getBuildersSweepWithdrawals
  keeps_uncached

/-- `getValidatorsSweepWithdrawals` keeps the flavour: a read, then a range loop over
the validators with a checked validator read and `balanceAfterWithdrawals`. -/
theorem keepsUncached_getValidatorsSweepWithdrawals (withdrawalIndex : WithdrawalIndex)
    (prior : Array Withdrawal) :
    KeepsUncached (getValidatorsSweepWithdrawals (StateTransition := HezeRun) withdrawalIndex
      prior) := by
  unfold getValidatorsSweepWithdrawals
  keeps_uncached_using [keepsUncached_balanceAfterWithdrawals _ _ _]

/-- `getExpectedWithdrawals` keeps the flavour: a read of the first index, then the four
readers in order, and a pure return. -/
theorem keepsUncached_getExpectedWithdrawals :
    KeepsUncached (getExpectedWithdrawals (StateTransition := HezeRun)) := by
  unfold getExpectedWithdrawals
  keeps_uncached_using [keepsUncached_getBuilderWithdrawals _ _,
    keepsUncached_getPendingPartialWithdrawals _ _, keepsUncached_getBuildersSweepWithdrawals _ _,
    keepsUncached_getValidatorsSweepWithdrawals _ _]

/-- `applyWithdrawals` keeps the flavour. It reads the state into a local state, runs a
loop over the withdrawals, and writes the local state back with `set`. A builder step
reads the builder through a checked read and writes its balance. A validator step
returns the new local state through `decreaseBalance`. Both steps keep the local state
pure, which is the loop invariant. -/
theorem keepsUncached_applyWithdrawals (withdrawals : Array Withdrawal) :
    KeepsUncached (applyWithdrawals (StateTransition := HezeRun) withdrawals) := by
  intro preState
  unfold applyWithdrawals
  apply keepsUncachedFrom_get_bind
  intro state
  refine keepsUncachedFrom_forIn_array_bind_P _ _ IsPure ?body ?tail _ _ ⟨state, rfl⟩
  · intro wd b
    rintro v r s ⟨w, rfl⟩ hrun
    revert v r s hrun
    -- The `refine` unifies the action of `step_of_returnsPureVia` with the body that the
    -- goal names.
    refine step_of_returnsPureVia ?_
    dsimp only
    split
    · exact returnsPureVia_bind_keeps (keepsUncached_liftErr _)
        (fun _ => returnsPureVia_pure _ ⟨_, rfl⟩)
    · exact returnsPureVia_bind_returns (returnsUncached_decreaseBalance _ _ _)
        (fun w₁ => returnsPureVia_pure _ ⟨w₁, rfl⟩)
  · intro b w' hb
    obtain ⟨w, rfl⟩ := hb
    exact keepsUncachedFrom_set w' w

/-- `processWithdrawals` keeps the flavour. It returns at once when the parent block
carried no payload. Otherwise it runs `getExpectedWithdrawals` and `applyWithdrawals`,
builds the expected list through `sszOfArrayM`, and writes the six bookkeeping fields.
Two of those writers branch on the registry size, and `is_pure` closes them. -/
theorem keepsUncached_processWithdrawals :
    KeepsUncached (processWithdrawals (StateTransition := HezeRun)) := by
  unfold processWithdrawals
  refine keepsUncached_bind keepsUncached_get (fun state => ?_)
  refine keepsUncached_ite (fun _ => keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_pure _) (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_getExpectedWithdrawals (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_applyWithdrawals _) (fun _ => ?_)
  -- The bookkeeping writes after the first `if` elaborate to a join point
  -- `have __do_jp := fun _ => …` that both branches call. `extract_lets` names it, so the
  -- fact about it is proved once. The first binding it names is the `Bool`
  -- `sweptFullPayload`, which the cursor writer reads.
  extract_lets sweptFull jp
  have hjp : ∀ y, KeepsUncached (jp y) := fun _ => by keeps_uncached
  -- The next withdrawal index is a checked `+ 1`, then its write.
  exact keepsUncached_ite
    (fun _ => keepsUncached_bind (keepsUncached_checkedAdd _ _ _)
      (fun _ => keepsUncached_bind (keepsUncached_modify _ (fun _ => ⟨_, rfl⟩)) hjp))
    (fun _ => keepsUncached_bind (keepsUncached_pure _) hjp)

end

end EthCLSpecs.Proofs.Heze
