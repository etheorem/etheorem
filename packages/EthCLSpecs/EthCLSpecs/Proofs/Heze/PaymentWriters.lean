import EthCLSpecs.Proofs.Heze.PaymentFrame
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.KeepsUncached.Slots

/-!
# `EthCLSpecs.Proofs.Heze.PaymentWriters`: the five writers of the payment window

`builderPendingPayments` holds `2 * SLOTS_PER_EPOCH` entries. The lower half holds the
previous epoch. The upper half holds the current epoch. `builderPaymentIndex slot current`
picks the entry of a slot. Five spec functions write the window:

| Writer | Index | Effect on the withdrawal |
| --- | --- | --- |
| `processExecutionPayloadBid` | the bid's slot, upper half | writes it when the value is `> 0` |
| `processAttestation` | the attested slot | keeps it, changes the weight |
| `slashValidator` | every index that records the slashed validator | clears it |
| `settleBuilderPayment` | its argument | clears it |
| `processBuilderPendingPayments` | every index | shifts the window down |

Both slashing handlers reach the window through `slashValidator`. The settlement of
`applyParentExecutionPayload` is at the slot of the latest header.

The index facts say when two slots share an index. In one half, two slots of one epoch
share an index only when they are equal (`builderPaymentIndex_inj`). The two halves never
share one. `vget_payments_write` states the window after a write at one index.

Each writer lemma states a successful run of one writer from the uncached box of a plain
value to the uncached box of another. It gives the withdrawal (`withdrawalAt`) and the
recorded proposer (`proposerAt`) at every index, and the spine (`spineView`). The lemmas
invert the run one action at a time. Every action keeps the uncached box
(`KeepsUncached.lean`), so each state on the way is `pureState` of a value
(`run_bind_eq_ok_pure`). A read or an assert keeps the state, and `frame_invert` proves it
(`run_bind_eq_ok_keep`). The epoch substep has its lemmas in `BuilderPendingPayments.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState run_bind_eq_ok run_bind_eq_ok_pure run_get_bind_eq_ok
  run_assert_bind_eq_ok run_pure_state_eq run_pure_eq_ok_state run_ite_eq_ok run_modifyThe_eq_ok
  keepsUncached_bind keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset State BeaconState Slot BuilderPendingPayment builderPaymentIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt)

/-- `v[i]!` on a vector reads the entry that `vget` reads. -/
theorem vector_getElem!_eq_vget {α : Type} [Inhabited α] {n : Nat} (v : Vector α n)
    (i : Nat) : v[i]! = vget v i := by
  unfold vget
  by_cases hi : i < n
  · simp [hi]
  · simp [hi]

section
variable [Preset]

/-- The index as a `Nat`: the offset of the half plus the slot modulo `SLOTS_PER_EPOCH`. -/
theorem builderPaymentIndex_eq (s : Slot) (c : Bool) :
    builderPaymentIndex s c = (if c then slotsPerEpoch else 0) + s.toNat % slotsPerEpoch := by
  have h : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt slotsPerEpochLt
  simp [builderPaymentIndex, umodIdx, UInt64.toNat_mod, h]

/-- Every index is inside the window. -/
theorem builderPaymentIndex_lt (s : Slot) (c : Bool) :
    builderPaymentIndex s c < 2 * slotsPerEpoch := by
  rw [builderPaymentIndex_eq]
  have := Nat.mod_lt s.toNat slotsPerEpochPos
  cases c <;> simp <;> omega

/-- In one half, two slots of one epoch with one index are equal. -/
theorem builderPaymentIndex_inj {s t : Slot} {c : Bool}
    (hidx : builderPaymentIndex s c = builderPaymentIndex t c)
    (hep : s.toNat / slotsPerEpoch = t.toNat / slotsPerEpoch) : s = t := by
  rw [builderPaymentIndex_eq, builderPaymentIndex_eq] at hidx
  have hmod : s.toNat % slotsPerEpoch = t.toNat % slotsPerEpoch := by omega
  apply UInt64.toNat_inj.mp
  rw [← Nat.div_add_mod s.toNat slotsPerEpoch, ← Nat.div_add_mod t.toNat slotsPerEpoch,
    hep, hmod]

/-- The upper and lower halves share no index. -/
theorem builderPaymentIndex_true_ne_false (s t : Slot) :
    builderPaymentIndex s true ≠ builderPaymentIndex t false := by
  rw [builderPaymentIndex_eq, builderPaymentIndex_eq]
  have := Nat.mod_lt s.toNat slotsPerEpochPos
  have := Nat.mod_lt t.toNat slotsPerEpochPos
  simp
  omega

/-- `computeEpochAtSlot` as a `Nat` division. -/
theorem computeEpochAtSlot_toNat (s : Slot) :
    (EthCLSpecs.Heze.computeEpochAtSlot s).toNat = s.toNat / slotsPerEpoch := by
  have h : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt slotsPerEpochLt
  simp [EthCLSpecs.Heze.computeEpochAtSlot, UInt64.toNat_div, h]

end

section
variable [Preset] [HasherTag]

/-- After a write of `x` at index `j` of the window, the entry at `j` is `x`. Every other
entry keeps its old value. -/
theorem vget_payments_write (st : BeaconState) (j : Nat) (hj : j < 2 * slotsPerEpoch)
    (x : BuilderPendingPayment) (i : Nat) :
    vget (sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
        builderPendingPayments) i
      = if i = j then x else vget (sszGet (pureState st) builderPendingPayments) i := by
  have hview : sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
      builderPendingPayments = (sszGet (pureState st) builderPendingPayments).set! j x := rfl
  rw [hview]
  unfold vget
  by_cases hij : i = j
  · subst hij
    simp [Vector.toArray_set!, hj]
  · simp [Vector.toArray_set!, hij, getElem!_def,
      Array.getElem?_setIfInBounds_ne (Ne.symm hij)]

/-- An indexed write of the window keeps the entry at every other index. The proofs below
close goals with this lemma by `exact`, so the goal can hold the write in an unfolded
form. -/
theorem vget_payments_write_ne (st : BeaconState) (j : Nat) (hj : j < 2 * slotsPerEpoch)
    (x : BuilderPendingPayment) {i : Nat} (hij : i ≠ j) :
    vget (sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
        builderPendingPayments) i
      = vget (sszGet (pureState st) builderPendingPayments) i := by
  rw [vget_payments_write st j hj x i, ite_eq_right hij]

/-- An indexed write of the window sets the entry at its index. -/
theorem vget_payments_write_eq (st : BeaconState) (j : Nat) (hj : j < 2 * slotsPerEpoch)
    (x : BuilderPendingPayment) :
    vget (sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
        builderPendingPayments) j = x := by
  rw [vget_payments_write st j hj x j, ite_eq_left rfl]

/-- The withdrawal of the window entry at `i`. -/
def withdrawalAt (st : State) (i : Nat) : EthCLSpecs.Heze.BuilderPendingWithdrawal :=
  (vget (sszGet st builderPendingPayments) i).withdrawal

/-- The recorded proposer of the window entry at `i`. -/
def proposerAt (st : State) (i : Nat) : EthCLSpecs.Heze.ValidatorIndex :=
  (vget (sszGet st builderPendingPayments) i).proposerIndex

/-- The entry that `processExecutionPayloadBid` writes for `bid`, with proposer `p`. -/
def pendingOf (bid : EthCLSpecs.Heze.ExecutionPayloadBid) (p : EthCLSpecs.Heze.ValidatorIndex) :
    BuilderPendingPayment :=
  { weight := 0, withdrawal := bidWithdrawal bid, proposerIndex := p }

/-- A successful `modifyState g` from the uncached box of `s` ends in `g` of that box. -/
theorem modifyState_run_eq {g : State → State} {s s' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.modifyState g : HezeRun PUnit).run (pureState s)
      = .ok (a, pureState s')) : pureState s' = g (pureState s) :=
  run_modifyThe_eq_ok h

/-- Two states with one `windowView` have one window. -/
theorem payments_of_frame {s s' : BeaconState}
    (h : windowView (pureState s') = windowView (pureState s)) :
    sszGet (pureState s') builderPendingPayments = sszGet (pureState s) builderPendingPayments :=
  congrArg Prod.snd h

/-- A successful settlement keeps the spine, and the entry at every index but `j`. -/
theorem settleBuilderPayment_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend] (j : Nat)
    (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) j).run (pureState st)
      = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧ ∀ i, i ≠ j →
      withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i := by
  refine ⟨settleBuilderPayment_frame_spine h, fun i hij => ?_⟩
  unfold EthCLSpecs.Heze.settleBuilderPayment at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨hj, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The `if` without `else` calls a join point `jp` in both branches.
  extract_lets _ jp at h
  split at h
  · -- The append to the withdrawal queue keeps the window.
    obtain ⟨_, s1, h1, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
    have hp1 := payments_of_frame (by frame_invert h1)
    have h := modifyState_run_eq h
    have hw : vget (sszGet (pureState st') builderPendingPayments) i
        = vget (sszGet (pureState s1) builderPendingPayments) i := by
      rw [h]
      exact vget_payments_write_ne s1 j hj default hij
    simp only [withdrawalAt, proposerAt, hw, hp1, and_self]
  · have h := modifyState_run_eq h
    have hw : vget (sszGet (pureState st') builderPendingPayments) i
        = vget (sszGet (pureState st) builderPendingPayments) i := by
      rw [h]
      exact vget_payments_write_ne st j hj default hij
    simp only [withdrawalAt, proposerAt, hw, and_self]

/-- A write of the cached bid sets the cached bid and keeps the slot, the header, and the
window. -/
theorem cacheWrite_reads (t : BeaconState) (b : EthCLSpecs.Heze.ExecutionPayloadBid) :
    spineView (sszUpdate (pureState t) with latestExecutionPayloadBid := b)
        = (sszGet (pureState t) slot, (sszGet (pureState t) latestBlockHeader).slot, b) ∧
      sszGet (sszUpdate (pureState t) with latestExecutionPayloadBid := b)
          builderPendingPayments
        = sszGet (pureState t) builderPendingPayments :=
  ⟨rfl, rfl⟩

/-- A successful bid run. The bid is for the state slot. The run keeps the slot and the
header, and caches the bid. The window changes only at the index of the bid's slot in the
upper half. There, a bid with value `> 0` writes its withdrawal and the proposer of the
state. -/
theorem processExecutionPayloadBid_run_payment [EthCLSpecs.Heze.Config] [CryptoBackend]
    (sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState st) = .ok ((), pureState st')) :
    sbid.message.slot = sszGet (pureState st) slot ∧
    spineView (pureState st') = (sszGet (pureState st) slot,
      (sszGet (pureState st) latestBlockHeader).slot, sbid.message) ∧
    (∀ i, i ≠ builderPaymentIndex sbid.message.slot true →
      withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∧
    (0 < sbid.message.value →
      withdrawalAt (pureState st') (builderPaymentIndex sbid.message.slot true)
        = bidWithdrawal sbid.message ∧
      proposerAt (pureState st') (builderPaymentIndex sbid.message.slot true)
        = EthCLSpecs.Heze.getBeaconProposerIndex (pureState st)) := by
  unfold EthCLSpecs.Heze.processExecutionPayloadBid at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- Both branches of the self-build test end in a join point, the body after the builder
  -- checks. `dsimp only` inlines it, so the two goals below run the same steps.
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  -- The self-build branch: two asserts. Then the builder branch: the `Except` read of the
  -- active test and its assert, the version assert, the `Except` coverage test and its
  -- assert, and the signature assert.
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  rotate_left
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  all_goals
    -- The blob cap, the slot, the genesis slot, the parent hash, and the new block-hash
    -- assert of v1.7.0-beta.4.
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    obtain ⟨hslot, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    -- The two reads keep the state.
    obtain ⟨_, -, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    obtain ⟨_, -, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    have hslot : sbid.message.slot = sszGet (pureState st) slot := beq_iff_eq.mp hslot
    refine ⟨hslot, ?_⟩
    -- Both branches of the value test end in the write of the cached bid.
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hv, h⟩
    · obtain ⟨_, s4, h4, h⟩ :=
        run_bind_eq_ok_pure (EthCLLib.Proofs.keepsUncached_modify _ (fun _ => ⟨_, rfl⟩)) h
      have hs4 : pureState s4 = sszUpdate (pureState st) with builderPendingPayments[
          builderPaymentIndex sbid.message.slot true]! :=
          pendingOf sbid.message (EthCLSpecs.Heze.getBeaconProposerIndex (pureState st)) :=
        modifyState_run_eq h4
      have hst' : pureState st' = sszUpdate (pureState s4) with
          latestExecutionPayloadBid := sbid.message :=
        modifyState_run_eq h
      obtain ⟨hspine, hpay⟩ := cacheWrite_reads s4 sbid.message
      have hj := builderPaymentIndex_lt sbid.message.slot true
      refine ⟨?_, fun i hi => ?_, fun _ => ?_⟩
      · rw [hst', hspine, hs4]
        rfl
      · unfold withdrawalAt proposerAt
        rw [hst', hpay, hs4, vget_payments_write_ne st _ hj _ hi]
        exact ⟨rfl, rfl⟩
      · unfold withdrawalAt proposerAt
        rw [hst', hpay, hs4, vget_payments_write_eq st _ hj]
        exact ⟨rfl, rfl⟩
    · have hst' : pureState st' = sszUpdate (pureState st) with
          latestExecutionPayloadBid := sbid.message :=
        modifyState_run_eq h
      obtain ⟨hspine, hpay⟩ := cacheWrite_reads st sbid.message
      refine ⟨hst' ▸ hspine, fun i _ => ?_, fun hv' => absurd hv' hv⟩
      unfold withdrawalAt proposerAt
      rw [hst', hpay]
      exact ⟨rfl, rfl⟩

/-- A successful header run. The block is for the state slot, after the old header, and
by the proposer of the state. The new header has the block's slot. The slot, the cached
bid, and the window stay. -/
theorem processBlockHeader_run_spine [EthCLSpecs.Heze.Config] [CryptoBackend]
    (b : EthCLSpecs.Heze.BeaconBlock) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState st)
      = .ok ((), pureState st')) :
    b.slot = sszGet (pureState st) slot ∧ (sszGet (pureState st) latestBlockHeader).slot < b.slot ∧
    b.proposerIndex = EthCLSpecs.Heze.getBeaconProposerIndex (pureState st) ∧
    spineView (pureState st') = (sszGet (pureState st) slot, b.slot,
      sszGet (pureState st) latestExecutionPayloadBid) ∧
    sszGet (pureState st') builderPendingPayments
      = sszGet (pureState st) builderPendingPayments := by
  unfold EthCLSpecs.Heze.processBlockHeader at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨hslot, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hgt, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hprop, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The proposer read through `sszGetIdx` keeps the state.
  simp only [EthCLLib.Spec.sszGetIdx] at h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  refine ⟨beq_iff_eq.mp hslot, hgt, beq_iff_eq.mp hprop, ?_⟩
  have h := modifyState_run_eq h
  rw [h]
  exact ⟨rfl, rfl⟩

/-- The steps of `slashValidator` before its payment loop: the exit, the slashing, the
penalty, and the rewards. The text is the spec body, so `slashValidator_eq` holds by
`rfl`. -/
def slashValidatorPrefix [EthCLSpecs.Heze.Config] (i : EthCLSpecs.Heze.ValidatorIndex) :
    HezeRun Unit := do
  let epoch := EthCLSpecs.Heze.computeEpochAtSlot (sszGet (← get) slot)
  EthCLSpecs.Heze.initiateValidatorExit i
  let state ← get
  let validator ← sszGetIdx (sszGet state validators) i.toNat
  let slashIdx := umodIdx epoch EthCLSpecs.Heze.Const.epochsPerSlashingsVector
  let slashedEpoch ← checkedAdd epoch
    (UInt64.ofNat EthCLSpecs.Heze.Const.epochsPerSlashingsVector)
    "slash_validator: epoch + EPOCHS_PER_SLASHINGS_VECTOR"
  let state := EthCLSpecs.Heze.modValidator state i fun validator =>
    { validator with
        slashed := true,
        withdrawableEpoch := umax validator.withdrawableEpoch slashedEpoch }
  let slashed ← checkedAdd (vget (sszGet state slashings) slashIdx) validator.effectiveBalance
    "slash_validator: state.slashings[epoch % EPOCHS_PER_SLASHINGS_VECTOR] + effective_balance"
  let state := sszUpdate state with slashings[slashIdx]! := slashed
  let state ← EthCLSpecs.Heze.decreaseBalance state i (validator.effectiveBalance /
    UInt64.ofNat EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra)
  set state
  let proposerIdx := EthCLSpecs.Heze.getBeaconProposerIndex (← get)
  let whistleblowerReward := validator.effectiveBalance /
    UInt64.ofNat EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra
  let weighted ← checkedMul whistleblowerReward (UInt64.ofNat EthCLSpecs.Heze.Const.proposerWeight)
    "slash_validator: whistleblower_reward * PROPOSER_WEIGHT"
  let proposerReward := weighted / UInt64.ofNat EthCLSpecs.Heze.Const.weightDenominator
  let state ← EthCLSpecs.Heze.increaseBalance state proposerIdx proposerReward
  set (← EthCLSpecs.Heze.increaseBalance state proposerIdx (whistleblowerReward - proposerReward))

/-- The payment loop of `slashValidator`: void each entry whose recorded proposer is `i`. -/
def voidPayments (i : EthCLSpecs.Heze.ValidatorIndex) (state : State) : State := Id.run do
  let mut state := state
  for paymentIndex in [0:2 * slotsPerEpoch] do
    if (vget (sszGet state builderPendingPayments) paymentIndex).proposerIndex == i then
      state := sszUpdate state with builderPendingPayments[paymentIndex]! :=
        (default : BuilderPendingPayment)
  return state

/-- `slashValidator` is its prefix, then the payment loop. -/
theorem slashValidator_eq [EthCLSpecs.Heze.Config] (i : EthCLSpecs.Heze.ValidatorIndex) :
    EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i
      = (slashValidatorPrefix i >>= fun _ => EthCLSpecs.Heze.modifyState (voidPayments i)) := by
  unfold EthCLSpecs.Heze.slashValidator slashValidatorPrefix voidPayments
  simp only [bind_assoc]
  rfl

/-- Two states with one window have one entry at every index. -/
theorem entry_of_payments {a b : BeaconState}
    (hp : sszGet (pureState a) builderPendingPayments
      = sszGet (pureState b) builderPendingPayments) (i : Nat) :
    withdrawalAt (pureState a) i = withdrawalAt (pureState b) i ∧
      proposerAt (pureState a) i = proposerAt (pureState b) i := by
  unfold withdrawalAt proposerAt
  rw [hp]
  exact ⟨rfl, rfl⟩

omit [Preset] [HasherTag] in
/-- An indexed write of a vector keeps the entry at every other index, in range or not. -/
theorem vget_set!_ne {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (j : Nat) (x : α)
    {i : Nat} (hij : i ≠ j) : vget (v.set! j x) i = vget v i := by
  unfold vget
  simp [Vector.toArray_set!, getElem!_def, Array.getElem?_setIfInBounds_ne (Ne.symm hij)]

/-- The payment loop keeps the spine. Each entry keeps its withdrawal and its recorded
proposer, or the start state records `i` there. The invariant needs no index: the loop
writes at `d` only after it reads `i` as the recorded proposer at `d`. -/
theorem voidPayments_entry (i : EthCLSpecs.Heze.ValidatorIndex) (u : BeaconState) :
    ∃ w, voidPayments i (pureState u) = pureState w ∧
      spineView (pureState w) = spineView (pureState u) ∧
      ∀ k, (withdrawalAt (pureState w) k = withdrawalAt (pureState u) k ∧
          proposerAt (pureState w) k = proposerAt (pureState u) k) ∨
        proposerAt (pureState u) k = i := by
  let P : State → Prop := fun s => ∃ w, s = pureState w ∧
    spineView (pureState w) = spineView (pureState u) ∧
    ∀ k, (withdrawalAt (pureState w) k = withdrawalAt (pureState u) k ∧
        proposerAt (pureState w) k = proposerAt (pureState u) k) ∨
      proposerAt (pureState u) k = i
  show P (voidPayments i (pureState u))
  unfold voidPayments
  simp only [bind_pure]
  refine EthCLLib.Proofs.id_forIn_range_inv P _ ?_ _ _ ⟨u, rfl, rfl, fun k => .inl ⟨rfl, rfl⟩⟩
  rintro d s ⟨w, rfl, hsp, hk⟩
  try dsimp only
  split
  · rename_i hc
    refine ⟨{ w with builderPendingPayments := w.builderPendingPayments.set! d default }, rfl,
      hsp, fun k => ?_⟩
    by_cases hkd : k = d
    · -- The loop read `i` at `d`, so the start state records `i` there.
      subst hkd
      have hc' : proposerAt (pureState w) k = i := beq_iff_eq.mp hc
      rcases hk k with ⟨-, hpr⟩ | hu
      · exact .inr (hpr ▸ hc')
      · exact .inr hu
    · have hv : vget (w.builderPendingPayments.set! d default) k
          = vget w.builderPendingPayments k := vget_set!_ne _ _ _ hkd
      rcases hk k with ⟨hw', hp'⟩ | hu
      · refine .inl ⟨?_, ?_⟩
        · exact (congrArg BuilderPendingPayment.withdrawal hv).trans hw'
        · exact (congrArg BuilderPendingPayment.proposerIndex hv).trans hp'
      · exact .inr hu
  · exact ⟨w, rfl, hsp, hk⟩

open EthCLLib.Proofs (keepsUncachedFrom_bind keepsUncachedFrom_get keepsUncachedFrom_get_bind
  keepsUncachedFrom_liftErr keepsUncachedFrom_ite keepsUncachedFrom_throw keepsUncachedFrom_pure
  keepsUncachedFrom_set returnsUncachedFrom_bind keepsUncached_iff_forall_from) in
/-- `slashValidatorPrefix` keeps the uncached box. The steps are those of
`keepsUncached_slashValidator` before its payment loop. -/
theorem keepsUncached_slashValidatorPrefix [EthCLSpecs.Heze.Config] [CryptoBackend]
    (i : EthCLSpecs.Heze.ValidatorIndex) :
    EthCLLib.Proofs.KeepsUncached (slashValidatorPrefix i) := by
  intro preState
  unfold slashValidatorPrefix
  refine keepsUncachedFrom_bind (keepsUncachedFrom_get preState) (fun _ midState₁ => ?_)
  refine keepsUncachedFrom_bind
    ((keepsUncached_iff_forall_from.mp (keepsUncached_initiateValidatorExit i)) midState₁)
    (fun _ midState₂ => ?_)
  refine keepsUncachedFrom_get_bind (fun state => ?_)
  refine keepsUncachedFrom_bind
    (keepsUncachedFrom_liftErr (T := BeaconState) (ε := EthCLLib.Spec.StateTransitionError)
      (ε' := EthCLLib.Spec.IndexError) (α := EthCLSpecs.Heze.Validator) state _)
    (fun validator midState₃ => ?_)
  refine keepsUncachedFrom_bind ?ce (fun _ midState₃a => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
      (fun _ => keepsUncachedFrom_pure _ _)
  refine keepsUncachedFrom_bind ?cs (fun _ midState₃b => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
      (fun _ => keepsUncachedFrom_pure _ _)
  refine returnsUncachedFrom_bind (returnsUncached_decreaseBalance _ i _)
    (fun afterDecrease midState₄ => ?_)
  refine keepsUncachedFrom_bind (v := midState₄) (keepsUncachedFrom_set midState₄ afterDecrease)
    (fun _ midState₅ => ?_)
  refine keepsUncachedFrom_get_bind (fun state' => ?_)
  refine keepsUncachedFrom_bind ?cm (fun _ midState₅a => ?_)
  · exact keepsUncachedFrom_ite (fun _ => keepsUncachedFrom_throw _ _)
      (fun _ => keepsUncachedFrom_pure _ _)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterProposerReward midState₆ => ?_)
  refine returnsUncachedFrom_bind (returnsUncached_increaseBalance _ _ _)
    (fun afterWhistleblowerReward midState₇ => ?_)
  exact keepsUncachedFrom_set midState₇ afterWhistleblowerReward

/-- `slashValidatorPrefix` keeps the tracked fields. -/
theorem slashValidatorPrefix_frame [EthCLSpecs.Heze.Config] [CryptoBackend] {t t' : BeaconState}
    {a : PUnit} {i : EthCLSpecs.Heze.ValidatorIndex}
    (h : (slashValidatorPrefix i).run (pureState t) = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  unfold slashValidatorPrefix at h
  frame_invert h

/-- A successful `slashValidator i` keeps the spine. Each entry keeps its withdrawal and
its recorded proposer, or the start state records `i` there. At v1.7.0-beta.4 the function
voids every payment that `i` proposed. -/
theorem slashValidator_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend]
    (i : EthCLSpecs.Heze.ValidatorIndex) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState st)
      = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
    ∀ k, (withdrawalAt (pureState st') k = withdrawalAt (pureState st) k ∧
        proposerAt (pureState st') k = proposerAt (pureState st) k) ∨
      proposerAt (pureState st) k = i := by
  rw [slashValidator_eq] at h
  obtain ⟨_, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_slashValidatorPrefix i) h
  have hw1 := slashValidatorPrefix_frame h1
  have hs := modifyState_run_eq h
  obtain ⟨w, hw, hsp, hk⟩ := voidPayments_entry i s1
  rw [hw] at hs
  obtain rfl := EthCLLib.Proofs.pureState_inj hs
  refine ⟨hsp.trans (congrArg Prod.fst hw1), fun k => ?_⟩
  obtain ⟨hwk, hpk⟩ := entry_of_payments (payments_of_frame hw1) k
  rcases hk k with ⟨ha, hb⟩ | hu
  · exact .inl ⟨ha.trans hwk, hb.trans hpk⟩
  · exact .inr (hpk ▸ hu)

/-- A successful proposer slashing keeps the spine. Each entry keeps its withdrawal and its
recorded proposer, or the start state records the slashed proposer there. -/
theorem processProposerSlashing_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend]
    (ps : EthCLSpecs.Heze.ProposerSlashing) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
    ∀ k, (withdrawalAt (pureState st') k = withdrawalAt (pureState st) k ∧
        proposerAt (pureState st') k = proposerAt (pureState st) k) ∨
      proposerAt (pureState st) k = ps.signedHeader1.message.proposerIndex := by
  unfold EthCLSpecs.Heze.processProposerSlashing at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The proposer read through `sszGetIdx` keeps the state.
  simp only [EthCLLib.Spec.sszGetIdx] at h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact slashValidator_run_withdrawal _ st st' h

/-- The validators that an attester slashing tries to slash: the sorted intersection of the
attesting indices of its two attestations, as `processAttesterSlashing` computes it. -/
def attesterSlashingIndices (asl : EthCLSpecs.Heze.AttesterSlashing) :
    Array EthCLSpecs.Heze.ValidatorIndex :=
  (arrayInter asl.attestation1.attestingIndices.toArray
    asl.attestation2.attestingIndices.toArray).qsort (· < ·)

/-- A successful attester slashing keeps the spine. Each entry keeps its withdrawal and its
recorded proposer, or the start state records one of the indices that the slashing tries
to slash. Each slashing in the loop is a `slashValidator` run. -/
theorem processAttesterSlashing_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend]
    (asl : EthCLSpecs.Heze.AttesterSlashing) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
    ∀ k, (withdrawalAt (pureState st') k = withdrawalAt (pureState st) k ∧
        proposerAt (pureState st') k = proposerAt (pureState st) k) ∨
      ∃ v ∈ attesterSlashingIndices asl, proposerAt (pureState st) k = v := by
  -- The invariant of the loop: an uncached box with the spine of `st`, whose entries keep
  -- their values or record a slashed index.
  let P : Bool → State → Prop := fun _ s => ∃ w, s = pureState w ∧
    spineView (pureState w) = spineView (pureState st) ∧
    ∀ k, (withdrawalAt (pureState w) k = withdrawalAt (pureState st) k ∧
        proposerAt (pureState w) k = proposerAt (pureState st) k) ∨
      ∃ v ∈ attesterSlashingIndices asl, proposerAt (pureState st) k = v
  unfold EthCLSpecs.Heze.processAttesterSlashing at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨r, s1, hloop, hrest⟩ := run_bind_eq_ok _ _ _ _ h
  have hP := EthCLLib.Proofs.forIn_array_run_inv_state P (fun idx hidx r s st1 s' hs hbody => by
    obtain ⟨w, rfl, hsp, hk⟩ := hs
    have hbody := run_get_bind_eq_ok _ _ _ hbody
    dsimp only at hbody
    split at hbody
    · obtain ⟨_, w2, h2, h3⟩ := run_bind_eq_ok_pure (keepsUncached_slashValidator idx) hbody
      obtain ⟨hst, rfl⟩ := run_pure_eq_ok_state h3
      obtain ⟨hsp2, hk2⟩ := slashValidator_run_withdrawal idx w w2 h2
      refine ⟨w2, rfl, hsp2.trans hsp, fun k => ?_⟩
      rcases hk2 k with ⟨ha, hb⟩ | hu
      · rcases hk k with ⟨ha', hb'⟩ | hv
        · exact .inl ⟨ha.trans ha', hb.trans hb'⟩
        · exact .inr hv
      · rcases hk k with ⟨-, hb'⟩ | hv
        · exact .inr ⟨idx, Array.mem_toList_iff.mp hidx, hb'.symm.trans hu⟩
        · exact .inr hv
    · obtain ⟨hst, rfl⟩ := run_pure_eq_ok_state hbody
      exact ⟨w, rfl, hsp, hk⟩) ⟨st, rfl, rfl, fun k => .inl ⟨rfl, rfl⟩⟩ hloop
  obtain ⟨w, rfl, hsp, hk⟩ := hP
  -- The final assert keeps the state.
  have hw : pureState st' = pureState w := by
    rcases run_ite_eq_ok hrest with ⟨-, hp⟩ | ⟨-, hp⟩
    · exact (run_pure_eq_ok_state hp).2
    · cases hp
  obtain rfl := EthCLLib.Proofs.pureState_inj hw
  exact ⟨hsp, hk⟩

/-- A successful `applyParentExecutionPayload` keeps the entry at every index but one. It
settles the index of the latest header's slot in the half that its epoch picks. At
v1.7.0-beta.4 the parent slot is the slot of the latest header, and the settlement comes
before the request loops. -/
theorem applyParentExecutionPayload_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend]
    (requests : EthCLSpecs.Heze.ExecutionRequests) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState st) = .ok ((), pureState st')) (i : Nat) :
    (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestBlockHeader).slot true ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestBlockHeader).slot
          = EthCLSpecs.Heze.currentEpochOf (pureState st)) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestBlockHeader).slot false ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestBlockHeader).slot
          = EthCLSpecs.Heze.previousEpochOf (pureState st)) := by
  unfold EthCLSpecs.Heze.applyParentExecutionPayload at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The `if`s of the settlement end in a join point. `dsimp only` inlines it.
  dsimp only at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- One settlement at index `j`. The request loops and the two writes after it keep the
  -- window.
  have settle : ∀ j (k : PUnit → HezeRun Unit),
      (∀ s : BeaconState, (k ()).run (pureState s) = .ok ((), pureState st') →
        windowView (pureState st') = windowView (pureState s)) →
      (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) j >>= k).run
          (pureState st) = .ok ((), pureState st') →
      (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨ i = j := by
    intro j k hk hrun
    obtain ⟨_, s6, h6, h7⟩ := run_bind_eq_ok_pure (keepsUncached_settleBuilderPayment _) hrun
    have hp7 := payments_of_frame (hk s6 h7)
    by_cases hij : i = j
    · exact .inr hij
    · obtain ⟨-, hset⟩ := settleBuilderPayment_run_withdrawal _ _ _ h6
      obtain ⟨hw, hpr⟩ := hset i hij
      obtain ⟨hw7, hpr7⟩ := entry_of_payments hp7 i
      exact .inl ⟨hw7.trans hw, hpr7.trans hpr⟩
  rcases run_ite_eq_ok h with ⟨he, h⟩ | ⟨-, h⟩
  · rcases settle _ _ (fun _ h7 => by frame_invert h7) h with hl | hi
    · exact .inl hl
    · exact .inr (.inl ⟨hi, beq_iff_eq.mp he⟩)
  · rcases run_ite_eq_ok h with ⟨he, h⟩ | ⟨-, h⟩
    · rcases settle _ _ (fun _ h7 => by frame_invert h7) h with hl | hi
      · exact .inl hl
      · exact .inr (.inr ⟨hi, beq_iff_eq.mp he⟩)
    · -- Outside the window: an append to the withdrawal queue, the loops, and the writes.
      exact .inl (entry_of_payments (payments_of_frame (by frame_invert h)) i)

/-- A successful parent-payload run keeps the spine. On the EMPTY edge, it keeps the
state. On the FULL edge, it keeps the entry at every index but one, the index of the
latest header's slot in the half that its epoch picks. -/
theorem processParentExecutionPayload_run_withdrawal [EthCLSpecs.Heze.Config]
    [CryptoBackend] (b : EthCLSpecs.Heze.BeaconBlock) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun) b).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
    (b.body.signedExecutionPayloadBid.message.parentBlockHash
        ≠ (sszGet (pureState st) latestExecutionPayloadBid).blockHash → st' = st) ∧
    ∀ i, (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestBlockHeader).slot true ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestBlockHeader).slot
          = EthCLSpecs.Heze.currentEpochOf (pureState st)) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestBlockHeader).slot false ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestBlockHeader).slot
          = EthCLSpecs.Heze.previousEpochOf (pureState st)) := by
  refine ⟨processParentExecutionPayload_frame_spine h, ?_⟩
  unfold EthCLSpecs.Heze.processParentExecutionPayload at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨heq, h⟩
  · -- The EMPTY edge: one assert.
    have e : (pureState st').view = (pureState st).view := by frame_invert h
    change st' = st at e
    subst e
    exact ⟨fun _ => rfl, fun _ => .inl ⟨rfl, rfl⟩⟩
  · refine ⟨fun hne => absurd (bne_iff_ne.mpr hne) heq, fun i => ?_⟩
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    exact applyParentExecutionPayload_run_withdrawal _ _ _ h i

end

/-! ## The attestation

`processAttestation` writes the entry at the attested slot back with a new weight. The
withdrawal and the recorded proposer of that entry come from the state it read, so they do
not change. The walk of `PaymentFrame.lean` proves this with the view `entryView`, which
drops the weight. One rule closes the side goal of the write back
(`entryView_weightWrite`). -/

/-- A write at `j` of a value with the image of the old entry keeps the image of the
vector. -/
theorem vector_map_set!_same {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) (j : Nat)
    (x : α) (hx : ∀ hj : j < n, f x = f v[j]) : (v.set! j x).map f = v.map f := by
  ext i hi
  simp only [Vector.getElem_map]
  by_cases hij : j = i
  · subst hij
    simp [Vector.set!, hx hi]
  · simp only [Vector.set!, Vector.getElem_mk, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds_ne (xs := v.toArray) (by simpa using hi) hij]
    rfl

section
variable [Preset] [HasherTag]

/-- The withdrawal and the recorded proposer of an entry. -/
def entryProj (p : BuilderPendingPayment) :
    EthCLSpecs.Heze.BuilderPendingWithdrawal × EthCLSpecs.Heze.ValidatorIndex :=
  (p.withdrawal, p.proposerIndex)

/-- The spine and the withdrawal and recorded proposer of every entry. -/
def entryView (st : State) :
    (Slot × Slot × EthCLSpecs.Heze.ExecutionPayloadBid) ×
      Vector (EthCLSpecs.Heze.BuilderPendingWithdrawal × EthCLSpecs.Heze.ValidatorIndex)
        (2 * slotsPerEpoch) :=
  (spineView st, (sszGet st builderPendingPayments).map entryProj)

/-- Two states with one `entryView` have one withdrawal and one recorded proposer at every
index. -/
theorem entry_of_entryView {a b : BeaconState}
    (h : entryView (pureState a) = entryView (pureState b)) (i : Nat) :
    withdrawalAt (pureState a) i = withdrawalAt (pureState b) i ∧
      proposerAt (pureState a) i = proposerAt (pureState b) i := by
  have hm := congrArg Prod.snd h
  simp only [entryView] at hm
  unfold withdrawalAt proposerAt vget
  by_cases hi : i < 2 * slotsPerEpoch
  · have := congrArg (·[i]'hi) hm
    simp only [Vector.getElem_map, entryProj, Prod.mk.injEq] at this
    simpa [hi] using this
  · simp [hi]

/-- A run that keeps `windowView` keeps `entryView`, a function of it. -/
@[frame_proj] theorem entry_of_window {a b : BeaconState}
    (h : windowView (pureState a) = windowView (pureState b)) :
    entryView (pureState a) = entryView (pureState b) := by
  simp only [windowView] at h
  simp only [entryView, (Prod.mk.injEq _ _ _ _).mp h]

/-- The write back of `processAttestation`: the entry at `j` of the state `st` that the
attestation read, with a new weight, written into the accumulator `acc`. Both states have
the `entryView` `v`, so the write keeps it. -/
@[frame_close] theorem entryView_weightWrite {acc st : BeaconState} {j : Nat}
    {w : EthCLSpecs.Heze.Gwei} {v : _}
    (hacc : entryView (pureState acc) = v) (hst : entryView (pureState st) = v) :
    entryView (sszUpdate (pureState acc) with builderPendingPayments[j]! :=
      { vget (sszGet (pureState st) builderPendingPayments) j with weight := w }) = v := by
  rw [← hacc]
  have hm : (sszGet (pureState acc) builderPendingPayments).map entryProj
      = (sszGet (pureState st) builderPendingPayments).map entryProj :=
    congrArg Prod.snd (hacc.trans hst.symm)
  have hview : sszGet (sszUpdate (pureState acc) with builderPendingPayments[j]! :=
      { vget (sszGet (pureState st) builderPendingPayments) j with weight := w })
        builderPendingPayments
      = (sszGet (pureState acc) builderPendingPayments).set! j
          { vget (sszGet (pureState st) builderPendingPayments) j with weight := w } := rfl
  have hspine : spineView (sszUpdate (pureState acc) with builderPendingPayments[j]! :=
      { vget (sszGet (pureState st) builderPendingPayments) j with weight := w })
      = spineView (pureState acc) := rfl
  simp only [entryView, hspine, hview]
  congr 1
  refine vector_map_set!_same _ _ _ _ fun hj => ?_
  have := congrArg (·[j]'hj) hm
  simp only [Vector.getElem_map] at this
  rw [this]
  simp [entryProj, vget, hj]

end

section
variable [Preset] [HasherTag] [EthCLSpecs.Heze.Config] [CryptoBackend]

set_option maxHeartbeats 1000000 in
/-- A successful attestation run keeps the spine, and the withdrawal and the recorded
proposer at every index. It changes only weights in the window.

The body threads the state through two nested loops, next to counters. The inversion
names the state part of each accumulator as `pureState` of a value. The write back of the
weight closes by `entryView_weightWrite`. -/
@[frame] theorem processAttestation_frame_entry {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation} {parentSlot : Slot}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att parentSlot).run
      (pureState t) = .ok (a, pureState t')) :
    entryView (pureState t') = entryView (pureState t) := by
  frame_invert h

/-- A successful attestation run keeps the spine, and the withdrawal and the recorded
proposer at every index. -/
theorem processAttestation_run_withdrawal (att : EthCLSpecs.Heze.Attestation)
    (parentSlot : Slot) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att parentSlot).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
      ∀ i, withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i := by
  have he := processAttestation_frame_entry h
  exact ⟨congrArg Prod.fst he, entry_of_entryView he⟩

end

end EthCLSpecs.Proofs.Heze
