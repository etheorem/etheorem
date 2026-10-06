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
| `processProposerSlashing` | the first header's slot | clears it when the proposer matches |
| `settleBuilderPayment` | its argument | clears it |
| `processBuilderPendingPayments` | every index | shifts the window down |

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
  run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok run_modifyThe_eq_ok keepsUncached_bind
  keepsUncached_pure keepsUncached_forIn_sszList)
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
  rw [vget_payments_write st j hj x i, if_neg hij]

/-- An indexed write of the window sets the entry at its index. -/
theorem vget_payments_write_eq (st : BeaconState) (j : Nat) (hj : j < 2 * slotsPerEpoch)
    (x : BuilderPendingPayment) :
    vget (sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := x)
        builderPendingPayments) j = x := by
  rw [vget_payments_write st j hj x j, if_pos rfl]

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
  -- active test and four asserts.
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  rotate_left
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The checked pending balance of `canBuilderCoverBid` keeps the state, then its assert.
  obtain ⟨_, -, h⟩ := run_bind_eq_ok_keep (by frame_keeps) (fun _ _ h => by frame_invert h) h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  all_goals
    obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
    obtain ⟨hslot, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
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

/-- A successful proposer slashing keeps the spine. It keeps the entry at every index but
one, the index of the first header's slot in the half that its epoch picks. It clears that
entry only when the recorded proposer is the slashed proposer. -/
theorem processProposerSlashing_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend]
    (ps : EthCLSpecs.Heze.ProposerSlashing) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
    ∀ i, (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨
      (proposerAt (pureState st) i = ps.signedHeader1.message.proposerIndex ∧
        ((i = builderPaymentIndex ps.signedHeader1.message.slot true ∧
          EthCLSpecs.Heze.computeEpochAtSlot ps.signedHeader1.message.slot
            = EthCLSpecs.Heze.currentEpochOf (pureState st)) ∨
        (i = builderPaymentIndex ps.signedHeader1.message.slot false ∧
          EthCLSpecs.Heze.computeEpochAtSlot ps.signedHeader1.message.slot
            = EthCLSpecs.Heze.previousEpochOf (pureState st)))) := by
  refine ⟨processProposerSlashing_frame_spine h, fun i => ?_⟩
  unfold EthCLSpecs.Heze.processProposerSlashing at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The `if`s before `slashValidator` end in a join point. `dsimp only` inlines it.
  dsimp only at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The proposer read through `sszGetIdx` keeps the state.
  simp only [EthCLLib.Spec.sszGetIdx] at h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- `slashValidator` keeps the window, so only the clear of one entry changes it.
  have kept : ∀ t : BeaconState, sszGet (pureState t) builderPendingPayments
        = sszGet (pureState st) builderPendingPayments →
      (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun)
        ps.signedHeader1.message.proposerIndex).run (pureState t) = .ok ((), pureState st') →
      sszGet (pureState st') builderPendingPayments
        = sszGet (pureState st) builderPendingPayments :=
    fun t ht hrun => (congrArg Prod.snd (slashValidator_frame hrun)).trans ht
  have keep_left : sszGet (pureState st') builderPendingPayments
        = sszGet (pureState st) builderPendingPayments →
      (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) := by
    intro hp
    unfold withdrawalAt proposerAt
    rw [hp]
    exact ⟨rfl, rfl⟩
  -- One clear at index `j`, in the half `c`, after the epoch test `he` and the proposer
  -- test `hm`.
  have clear : ∀ (c : Bool), let j := builderPaymentIndex ps.signedHeader1.message.slot c
      (((sszGet (pureState st) builderPendingPayments)[j]!).proposerIndex
        == ps.signedHeader1.message.proposerIndex) = true →
      (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun)
        ps.signedHeader1.message.proposerIndex).run
          (sszUpdate (pureState st) with builderPendingPayments[j]! := default)
        = .ok ((), pureState st') →
      (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
          proposerAt (pureState st') i = proposerAt (pureState st) i) ∨
        (proposerAt (pureState st) i = ps.signedHeader1.message.proposerIndex ∧ i = j) := by
    intro c j hm hrun
    have hj := builderPaymentIndex_lt ps.signedHeader1.message.slot c
    -- The clear writes the uncached box of a value. Name it.
    have hp : sszGet (pureState st') builderPendingPayments
        = sszGet (sszUpdate (pureState st) with builderPendingPayments[j]! := default)
          builderPendingPayments := by
      obtain ⟨u, hu⟩ : EthCLLib.Proofs.IsPure
          (sszUpdate (pureState st) with builderPendingPayments[j]! := default) := ⟨_, rfl⟩
      rw [hu] at hrun ⊢
      exact congrArg Prod.snd (slashValidator_frame hrun)
    by_cases hij : i = j
    · subst hij
      refine .inr ⟨?_, rfl⟩
      rw [vector_getElem!_eq_vget] at hm
      exact beq_iff_eq.mp hm
    · refine .inl ?_
      unfold withdrawalAt proposerAt
      rw [hp]
      exact ⟨congrArg _ (vget_payments_write_ne st _ hj _ hij),
        congrArg _ (vget_payments_write_ne st _ hj _ hij)⟩
  rcases run_ite_eq_ok h with ⟨he, h⟩ | ⟨-, h⟩
  · rcases run_ite_eq_ok h with ⟨hm, h⟩ | ⟨-, h⟩
    · obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
      have hs2 : s2 = sszUpdate (pureState st) with builderPendingPayments[builderPaymentIndex
          ps.signedHeader1.message.slot true]! := default := run_modifyThe_eq_ok h2
      subst hs2
      rcases clear true hm h with hl | ⟨hp, hi⟩
      · exact .inl hl
      · exact .inr ⟨hp, .inl ⟨hi, beq_iff_eq.mp he⟩⟩
    · exact .inl (keep_left (kept _ rfl h))
  · rcases run_ite_eq_ok h with ⟨he, h⟩ | ⟨-, h⟩
    · rcases run_ite_eq_ok h with ⟨hm, h⟩ | ⟨-, h⟩
      · obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
        have hs2 : s2 = sszUpdate (pureState st) with builderPendingPayments[builderPaymentIndex
            ps.signedHeader1.message.slot false]! := default := run_modifyThe_eq_ok h2
        subst hs2
        rcases clear false hm h with hl | ⟨hp, hi⟩
        · exact .inl hl
        · exact .inr ⟨hp, .inr ⟨hi, beq_iff_eq.mp he⟩⟩
      · exact .inl (keep_left (kept _ rfl h))
    · exact .inl (keep_left (kept _ rfl h))

/-- Two states with one window have one entry at every index. -/
theorem entry_of_payments {a b : BeaconState}
    (hp : sszGet (pureState a) builderPendingPayments
      = sszGet (pureState b) builderPendingPayments) (i : Nat) :
    withdrawalAt (pureState a) i = withdrawalAt (pureState b) i ∧
      proposerAt (pureState a) i = proposerAt (pureState b) i := by
  unfold withdrawalAt proposerAt
  rw [hp]
  exact ⟨rfl, rfl⟩

/-- A successful `applyParentExecutionPayload` keeps the entry at every index but one. It
settles the index of the cached bid's slot in the half that its epoch picks. -/
theorem applyParentExecutionPayload_run_withdrawal [EthCLSpecs.Heze.Config] [CryptoBackend]
    (requests : EthCLSpecs.Heze.ExecutionRequests) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState st) = .ok ((), pureState st')) (i : Nat) :
    (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestExecutionPayloadBid).slot true ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestExecutionPayloadBid).slot
          = EthCLSpecs.Heze.currentEpochOf (pureState st)) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestExecutionPayloadBid).slot false ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestExecutionPayloadBid).slot
          = EthCLSpecs.Heze.previousEpochOf (pureState st)) := by
  unfold EthCLSpecs.Heze.applyParentExecutionPayload at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The `if`s of the settlement end in a join point. `dsimp only` inlines it.
  dsimp only at h
  -- The five request loops keep the uncached box and the window.
  obtain ⟨_, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun d _ =>
    keepsUncached_bind (keepsUncached_processDepositRequest d)
      (fun _ => keepsUncached_pure _)) _ _) h
  have hp1 := payments_of_frame (by frame_invert h1)
  obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun w _ =>
    keepsUncached_bind (keepsUncached_processWithdrawalRequest w)
      (fun _ => keepsUncached_pure _)) _ _) h
  have hp2 := payments_of_frame (by frame_invert h2)
  obtain ⟨_, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun c _ =>
    keepsUncached_bind (keepsUncached_processConsolidationRequest c)
      (fun _ => keepsUncached_pure _)) _ _) h
  have hp3 := payments_of_frame (by frame_invert h3)
  obtain ⟨_, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun bd _ =>
    keepsUncached_bind (keepsUncached_processBuilderDepositRequest bd)
      (fun _ => keepsUncached_pure _)) _ _) h
  have hp4 := payments_of_frame (by frame_invert h4)
  obtain ⟨_, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun be _ =>
    keepsUncached_bind (keepsUncached_processBuilderExitRequest be)
      (fun _ => keepsUncached_pure _)) _ _) h
  have hp5 := payments_of_frame (by frame_invert h5)
  have hp15 := hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1)))
  -- One settlement at index `j`, then the two writes at the end, which keep the window.
  have settle : ∀ j, (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) j
        >>= fun _ =>
          (EthCLSpecs.Heze.modifyState fun state => sszUpdate state with
            executionPayloadAvailability := bitSet (sszGet state executionPayloadAvailability)
              (umodIdx (sszGet (pureState st) latestExecutionPayloadBid).slot
                EthCLSpecs.Heze.Const.slotsPerHistoricalRoot) true) >>= fun _ =>
          EthCLSpecs.Heze.modifyState fun state => sszUpdate state with
            latestBlockHash := (sszGet (pureState st) latestExecutionPayloadBid).blockHash).run
          (pureState s5)
        = .ok ((), pureState st') →
      (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨ i = j := by
    intro j hrun
    obtain ⟨_, s6, h6, h7⟩ := run_bind_eq_ok_pure (keepsUncached_settleBuilderPayment _) hrun
    have hp7 := payments_of_frame (by frame_invert h7)
    by_cases hij : i = j
    · exact .inr hij
    · obtain ⟨-, hset⟩ := settleBuilderPayment_run_withdrawal _ _ _ h6
      obtain ⟨hw, hpr⟩ := hset i hij
      obtain ⟨hw7, hpr7⟩ := entry_of_payments hp7 i
      obtain ⟨hw5, hpr5⟩ := entry_of_payments hp15 i
      exact .inl ⟨hw7.trans (hw.trans hw5), hpr7.trans (hpr.trans hpr5)⟩
  rcases run_ite_eq_ok h with ⟨he, h⟩ | ⟨-, h⟩
  · rcases settle _ h with hl | hi
    · exact .inl hl
    · exact .inr (.inl ⟨hi, beq_iff_eq.mp he⟩)
  · rcases run_ite_eq_ok h with ⟨he, h⟩ | ⟨-, h⟩
    · rcases settle _ h with hl | hi
      · exact .inl hl
      · exact .inr (.inr ⟨hi, beq_iff_eq.mp he⟩)
    · -- Outside the window: an append to the withdrawal queue and the two writes.
      exact .inl (entry_of_payments
        ((payments_of_frame (by frame_invert h)).trans hp15) i)

/-- A successful parent-payload run keeps the spine. On the EMPTY edge, it keeps the
state. On the FULL edge, it keeps the entry at every index but one, the index of the
cached bid's slot in the half that its epoch picks. -/
theorem processParentExecutionPayload_run_withdrawal [EthCLSpecs.Heze.Config]
    [CryptoBackend] (b : EthCLSpecs.Heze.BeaconBlock) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun) b).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
    (b.body.signedExecutionPayloadBid.message.parentBlockHash
        ≠ (sszGet (pureState st) latestExecutionPayloadBid).blockHash → st' = st) ∧
    ∀ i, (withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestExecutionPayloadBid).slot true ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestExecutionPayloadBid).slot
          = EthCLSpecs.Heze.currentEpochOf (pureState st)) ∨
      (i = builderPaymentIndex (sszGet (pureState st) latestExecutionPayloadBid).slot false ∧
        EthCLSpecs.Heze.computeEpochAtSlot (sszGet (pureState st) latestExecutionPayloadBid).slot
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
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    entryView (pureState t') = entryView (pureState t) := by
  frame_invert h

/-- A successful attestation run keeps the spine, and the withdrawal and the recorded
proposer at every index. -/
theorem processAttestation_run_withdrawal (att : EthCLSpecs.Heze.Attestation)
    (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState st) = .ok ((), pureState st')) :
    spineView (pureState st') = spineView (pureState st) ∧
      ∀ i, withdrawalAt (pureState st') i = withdrawalAt (pureState st) i ∧
        proposerAt (pureState st') i = proposerAt (pureState st) i := by
  have he := processAttestation_frame_entry h
  exact ⟨congrArg Prod.fst he, entry_of_entryView he⟩

end

end EthCLSpecs.Proofs.Heze
