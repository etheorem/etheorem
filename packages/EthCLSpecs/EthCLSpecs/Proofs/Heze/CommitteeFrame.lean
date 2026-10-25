import EthCLSpecs.Proofs.Heze.ParticipationRotate
import EthCLSpecs.Proofs.Heze.DriftChurn

/-!
# `EthCLSpecs.Proofs.Heze.CommitteeFrame`: a block keeps the committees of its epochs

`get_attesting_indices` reads a state through `get_beacon_committee` only. A committee of
epoch `e` reads two things: the activity of each validator at `e` (its activation epoch and its
exit epoch), and the RANDAO mix that seeds the shuffle of `e`. `comView e` holds these two and
the flag `CommitteeWindow`. The window says that `e` is the current or the previous epoch, and
that the epoch arithmetic has room below `2 ^ 64`. Two states with one `comView e` have one
committee for each slot of `e` (`getBeaconCommittee_eq_of_comView`). So they have one set of
attesting indices for each attestation of `e` (`getAttestingIndices_eq_of_comView`).

A block keeps `comView e` up to and inside the attestation loop:

- An exit sets the exit epoch of a validator that had none. The exit epoch is at least
  `compute_activation_exit_epoch` of the current epoch (`computeExitEpochAndUpdateChurn_ge`).
  That epoch is after `e`. The checked activation epoch and the checked churn reservation make
  this hold on every successful run. So the validator stays active at `e`
  (`initiateValidatorExit_frame_com`). A
  consolidation sets the exit epoch of its source in the same way.
- `processRandao` writes the mix of the current epoch. The seed of `e` reads the mix of
  `e - MIN_SEED_LOOKAHEAD - 1`. That is another entry when `MIN_SEED_LOOKAHEAD + 2` is below
  `EPOCHS_PER_HISTORICAL_VECTOR` (`processRandao_frame_com`). `CommitteeWindow` holds this
  bound.
- The other writes keep the activation and exit epochs and the mixes.

So a block sets the target flag of each attesting index of its attestations at the start state
of the block (`processBlock_sets_flag`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure runPure_of_run_ok run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_pure_eq_ok run_ite_eq_ok run_assert_bind_eq_ok keepsUncached_bind
  keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot BeaconState BeaconBlock Epoch Gwei ValidatorIndex
  Validator currentEpochOf previousEpochOf isActiveValidator)
open EthCLSpecs.Heze.Const (slotsPerEpoch epochsPerHistoricalVector minSeedLookahead
  maxSeedLookahead)

section
variable [Preset] [HasherTag]

/-! ## The view -/

/-- The epoch `e` is the current or the previous epoch of `st`, and the epoch arithmetic of
the exits and of the seed has room below `2 ^ 64`. The seed entry of `e` differs from the
entries that the current and the next epoch write when `MIN_SEED_LOOKAHEAD + 2` is below the
length of the mix vector. The registry indices fit a `uint64`. -/
def CommitteeWindow (e : Epoch) (st : State) : Prop :=
  e.toNat ≤ (currentEpochOf st).toNat ∧ (currentEpochOf st).toNat ≤ e.toNat + 1 ∧
    (currentEpochOf st).toNat + 1 + maxSeedLookahead.toNat < 2 ^ 64 ∧
    minSeedLookahead.toNat + 2 < epochsPerHistoricalVector ∧
    e.toNat + epochsPerHistoricalVector < 2 ^ 64 ∧ (sszGet st validators).val.size < 2 ^ 64

instance (e : Epoch) (st : State) : Decidable (CommitteeWindow e st) := by
  unfold CommitteeWindow
  infer_instance

/-- The RANDAO mix that seeds the shuffle of epoch `e`, as `get_seed` reads it. -/
def seedMix (e : Epoch) (st : State) : EthCLSpecs.Heze.Bytes32 :=
  vmodGet (sszGet st randaoMixes)
    (e + UInt64.ofNat epochsPerHistoricalVector - minSeedLookahead - 1) epochsPerHistoricalVector

/-- The committees of epoch `e`: the window flag, the activity of each validator at `e`, and
the seed mix of `e`. -/
def comView (e : Epoch) (st : State) : Bool × Array Bool × EthCLSpecs.Heze.Bytes32 :=
  (decide (CommitteeWindow e st), (sszGet st validators).val.map (isActiveValidator · e),
    seedMix e st)

/-! ## One view, one committee -/

/-- Two registries with one activity at `e` have one active set at `e`. -/
theorem getActiveValidatorIndices_eq_of_map {s u : BeaconState} {e : Epoch}
    (h : s.validators.val.map (isActiveValidator · e) =
      u.validators.val.map (isActiveValidator · e)) :
    EthCLSpecs.Heze.getActiveValidatorIndices (pureState s) e =
      EthCLSpecs.Heze.getActiveValidatorIndices (pureState u) e := by
  have hsz : s.validators.val.size = u.validators.val.size := by
    simpa using congrArg Array.size h
  apply Array.toList_inj.mp
  rw [getActiveValidatorIndices_toList, getActiveValidatorIndices_toList, hsz]
  congr 1
  refine List.filter_congr fun i hi => ?_
  have hi' : i < u.validators.val.size := List.mem_range.mp hi
  have hs' : i < s.validators.val.size := by omega
  have e1 := congrArg (fun a : Array Bool => a[i]!) h
  simp only at e1
  rw [getElem!_pos (s.validators.val.map _) i (by simpa using hs'),
    getElem!_pos (u.validators.val.map _) i (by simpa using hi')] at e1
  simp only [Array.getElem_map] at e1
  rw [getElem!_pos s.validators.val i hs', getElem!_pos u.validators.val i hi']
  exact e1

/-- Two states with one `comView e` have one committee for each slot of `e`. -/
theorem getBeaconCommittee_eq_of_comView {s u : BeaconState} {e : Epoch}
    (h : comView e (pureState s) = comView e (pureState u)) (slot : Slot)
    (he : EthCLSpecs.Heze.computeEpochAtSlot slot = e) (ci : Nat) :
    EthCLSpecs.Heze.getBeaconCommittee (pureState s) slot ci =
      EthCLSpecs.Heze.getBeaconCommittee (pureState u) slot ci := by
  simp only [comView, Prod.mk.injEq] at h
  obtain ⟨-, hv, hm⟩ := h
  have ha := getActiveValidatorIndices_eq_of_map (s := s) (u := u) (e := e) hv
  unfold EthCLSpecs.Heze.getBeaconCommittee EthCLSpecs.Heze.getCommitteeCountPerSlot
    EthCLSpecs.Heze.getSeed
  rw [he]
  unfold seedMix at hm
  dsimp only
  rw [ha, hm]

variable [Config] [CryptoBackend]

/-- Two states with one `comView e` have one set of attesting indices for each attestation of
a slot of `e`. -/
theorem getAttestingIndices_eq_of_comView {s u : BeaconState} {e : Epoch}
    (h : comView e (pureState s) = comView e (pureState u))
    (att : EthCLSpecs.Heze.Attestation)
    (he : EthCLSpecs.Heze.computeEpochAtSlot att.data.slot = e) :
    EthCLSpecs.Heze.getAttestingIndices (pureState s) att =
      EthCLSpecs.Heze.getAttestingIndices (pureState u) att := by
  unfold EthCLSpecs.Heze.getAttestingIndices
  simp only [getBeaconCommittee_eq_of_comView h att.data.slot he]

end

/-! ## The target root across states with one slot and one ring of block roots -/

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The block-root read of a state depends on its slot and its ring of block roots only. It
reads no state of the monad, so a successful run on one state succeeds on every state with
the same slot and block roots, with the same root. -/
theorem getBlockRoot_run_transfer {u s : BeaconState} {ep : Epoch} {r : EthCLSpecs.Heze.Root}
    (hsl : s.slot = u.slot) (hbr : s.blockRoots = u.blockRoots)
    (h : runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState u) ep) u
      = .ok (r, u)) :
    runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState s) ep) s
      = .ok (r, s) := by
  unfold EthCLSpecs.Heze.getBlockRoot at h ⊢
  -- The checked start slot reads no state, so both runs compute the same slot `x`.
  rw [EthCLLib.Proofs.runPure_eq, EthCLLib.Proofs.run_bind] at h ⊢
  cases hx : (EthCLSpecs.Heze.computeStartSlotAtEpoch ep : Except StateTransitionError Slot) with
  | error err =>
    rw [hx, EthCLLib.Proofs.run_liftErr_of_error _ _ rfl] at h
    cases h
  | ok x =>
  rw [hx, EthCLLib.Proofs.run_liftErr_of_ok _ _ rfl, EthCLLib.Proofs.except_bind_ok] at h
  rw [EthCLLib.Proofs.run_liftErr_of_ok _ _ rfl, EthCLLib.Proofs.except_bind_ok]
  rw [← EthCLLib.Proofs.runPure_eq] at h ⊢
  have e : EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun) (pureState s) x =
      EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun) (pureState u) x := by
    unfold EthCLSpecs.Heze.getBlockRootAtSlot
    have h1 : sszGet (pureState s) slot = sszGet (pureState u) slot := hsl
    have h2 : sszGet (pureState s) blockRoots = sszGet (pureState u) blockRoots := hbr
    rw [h1, h2]
  rw [e]
  have hk := keepsUncached_getBlockRootAtSlot u x
  rw [EthCLLib.Proofs.runPure_iff_run_of_keepsUncached hk] at h ⊢
  unfold EthCLSpecs.Heze.getBlockRootAtSlot at h ⊢
  -- The three checks on `u`. They read the slot only, and `s` has the slot of `u`.
  obtain ⟨c1, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨bound, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  unfold checkedAdd at h2
  split at h2
  · cases h2
  rename_i c2
  have eb := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h2
  have es := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h2
  subst eb es
  obtain ⟨c3, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  have er := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h
  subst er
  simp only [EthCLLib.Proofs.run_bind, checkedAdd, if_pos c1, if_neg c2, if_pos c3,
    EthCLLib.Proofs.run_pure, EthCLLib.Proofs.except_bind_ok]

end

/-! ## Exits land after the window -/

section
variable [Preset] [HasherTag]

omit [Preset] [HasherTag] in
/-- The epoch of a successful churn reservation is at least its `earliest` epoch. Each case is
one of the results of `Churn.lean`: the balance fits, the limit is zero, every sum stays below
`2 ^ 64`, or one reaches it. Only the first and the third succeed. -/
theorem reserveChurn_fst_ge {bal consume per earliest x c : Gwei}
    (hr : (EthCLSpecs.Heze.reserveChurn bal consume per earliest : Except StateTransitionError _)
      = .ok (x, c)) :
    earliest.toNat ≤ x.toNat := by
  by_cases hfit : bal ≤ consume
  · rw [reserveChurn_fits _ _ _ _ hfit] at hr
    injection hr with hr
    injection hr with h1 _
    subst h1
    exact Nat.le_refl _
  have hlt : consume < bal := UInt64.lt_iff_toNat_lt.mpr
    (Nat.lt_of_not_le fun h' => hfit (UInt64.le_iff_toNat_le.mpr h'))
  by_cases hp : per = 0
  · subst hp
    rw [reserveChurn_zero _ _ _ hlt] at hr
    cases hr
  have hp' : 0 < per.toNat := Nat.pos_of_ne_zero fun hz => hp (UInt64.toNat_inj.mp hz)
  -- The overflow case: some checked result reaches `2 ^ 64`, and the reservation rejects.
  have hover : (2 ^ 64 ≤ earliest.toNat +
        EthCLSpecs.Proofs.Fulu.churnEpochs bal consume per ∨
      2 ^ 64 ≤ EthCLSpecs.Proofs.Fulu.churnEpochs bal consume per * per.toNat ∨
      2 ^ 64 ≤ consume.toNat +
        EthCLSpecs.Proofs.Fulu.churnEpochs bal consume per * per.toNat) → False := fun hb => by
    obtain ⟨_, he⟩ := reserveChurn_overflow _ _ _ earliest hlt hp' hb
    rw [he] at hr
    cases hr
  by_cases h1 : earliest.toNat + EthCLSpecs.Proofs.Fulu.churnEpochs bal consume per < 2 ^ 64
  · by_cases h2 : EthCLSpecs.Proofs.Fulu.churnEpochs bal consume per * per.toNat < 2 ^ 64
    · by_cases h3 : consume.toNat +
          EthCLSpecs.Proofs.Fulu.churnEpochs bal consume per * per.toNat < 2 ^ 64
      · obtain ⟨_, _, hok, he1, -⟩ := reserveChurn_ok _ _ _ _ hlt hp' h1 h2 h3
        rw [hok] at hr
        injection hr with hr
        injection hr with h1' _
        subst h1'
        rw [he1]
        exact Nat.le_add_right _ _
      · exact (hover (.inr (.inr (Nat.le_of_not_lt h3)))).elim
    · exact (hover (.inr (.inl (Nat.le_of_not_lt h2)))).elim
  · exact (hover (.inl (Nat.le_of_not_lt h1))).elim

omit [HasherTag] in
/-- A successful `compute_activation_exit_epoch` of the current epoch is after the epochs of
the window. It does not wrap, since a sum at `2 ^ 64` rejects
(`computeActivationExitEpoch_overflow`), and below it the result is the exact sum
(`computeActivationExitEpoch_no_wrap`). -/
theorem activationExit_toNat {cur act : Epoch}
    (hact : (EthCLSpecs.Heze.computeActivationExitEpoch cur : Except StateTransitionError UInt64)
      = .ok act) :
    act.toNat = cur.toNat + 1 + maxSeedLookahead.toNat := by
  by_cases hb : cur.toNat + 1 + maxSeedLookahead.toNat < 2 ^ 64
  · obtain ⟨r, hr, hrN⟩ := computeActivationExitEpoch_no_wrap cur hb
    rw [hr] at hact
    injection hact with hact
    subst hact
    exact hrN
  · obtain ⟨_, he⟩ := computeActivationExitEpoch_overflow cur (Nat.le_of_not_lt hb)
    rw [he] at hact
    cases hact

variable [Config]

/-- The exit epoch that `computeExitEpochAndUpdateChurn` returns is at least
`compute_activation_exit_epoch` of the current epoch. A successful run computed that epoch and
reserved the churn without a fault (`computeExitEpochAndUpdateChurn_run`). -/
theorem computeExitEpochAndUpdateChurn_ge {bal : Gwei} {a b : BeaconState} {x : Epoch}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) bal).run
      (pureState a) = .ok (x, pureState b)) :
    (EthCLSpecs.Heze.computeEpochAtSlot a.slot).toNat + 1 + maxSeedLookahead.toNat ≤ x.toNat := by
  obtain ⟨act, c, hact, -, hres, -⟩ := computeExitEpochAndUpdateChurn_run _ _ h
  refine Nat.le_trans ?_ (reserveChurn_fst_ge hres)
  rw [umax_toNat, activationExit_toNat hact]
  exact Nat.le_max_right _ _

/-- The exit epoch that `computeConsolidationEpochAndUpdateChurn` returns is at least
`compute_activation_exit_epoch` of the current epoch. -/
theorem computeConsolidationEpochAndUpdateChurn_ge {bal : Gwei} {a b : BeaconState} {x : Epoch}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      bal).run (pureState a) = .ok (x, pureState b)) :
    (currentEpochOf (pureState a)).toNat + 1 + maxSeedLookahead.toNat ≤ x.toNat := by
  obtain ⟨act, c, hact, -, hres, -⟩ := computeConsolidationEpochAndUpdateChurn_run _ _ h
  refine Nat.le_trans ?_ (reserveChurn_fst_ge hres)
  rw [umax_toNat, activationExit_toNat hact]
  exact Nat.le_max_right _ _

end

/-! ## Validator writes -/

section
variable [Preset] [HasherTag]

/-- A write at index `j` keeps `comView e` when the new validator has the activity at `e` of
the old validator at `j`. -/
theorem comView_setValidator {e : Epoch} (a : BeaconState) (j : Nat) (v' : Validator)
    (hv : isActiveValidator v' e = isActiveValidator a.validators[j]! e) :
    comView e (pureState { a with validators := a.validators.set! j v' }) =
      comView e (pureState a) := by
  simp only [comView, Prod.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · -- The write keeps the length of the registry.
    have hsz : (a.validators.set! j v').val.size = a.validators.val.size := by
      show (a.validators.val.setIfInBounds j v').size = _
      exact Array.size_setIfInBounds
    exact decide_eq_decide.mpr (by
      unfold CommitteeWindow
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (a.validators.set! j v').val.size < 2 ^ 64 ↔
        _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ a.validators.val.size < 2 ^ 64
      rw [hsz]
      exact Iff.rfl)
  show (a.validators.val.setIfInBounds j v').map (isActiveValidator · e) =
    a.validators.val.map (isActiveValidator · e)
  rw [Array.map_setIfInBounds]
  apply Array.ext_getElem?
  intro k
  rw [Array.getElem?_setIfInBounds]
  split
  · rename_i hk
    subst hk
    split
    · rename_i hb
      rw [Array.size_map] at hb
      rw [hv, getElem!_pos a.validators j hb, Array.getElem?_map, Array.getElem?_eq_getElem hb]
      rfl
    · rename_i hb
      exact (Array.getElem?_eq_none (Nat.le_of_not_lt hb)).symm
  · rfl

/-- A write that keeps the activation epoch and the exit epoch keeps `comView e`. -/
@[frame_close] theorem comView_modValidator {e : Epoch} {acc : BeaconState} {i : ValidatorIndex}
    {pk : Validator → EthCLSpecs.Heze.BLSPubkey} {wc : Validator → EthCLSpecs.Heze.Bytes32}
    {eb : Validator → Gwei} {sl : Validator → Bool} {aee we : Validator → Epoch} {v : _}
    (hacc : comView e (pureState acc) = v) :
    comView e (EthCLSpecs.Heze.modValidator (pureState acc) i fun w =>
      { pubkey := pk w, withdrawalCredentials := wc w, effectiveBalance := eb w,
        slashed := sl w, activationEligibilityEpoch := aee w, activationEpoch := w.activationEpoch,
        exitEpoch := w.exitEpoch, withdrawableEpoch := we w }) = v := by
  rw [← hacc, modValidator_pureState]
  exact comView_setValidator acc _ _ rfl

/-- A window flag of `true` in a `comView` value gives the window. -/
theorem window_of_comView {e : Epoch} {t : BeaconState} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (hs : comView e (pureState t) = (true, c)) : CommitteeWindow e (pureState t) := by
  have := congrArg Prod.fst hs
  simpa [comView] using this

omit [HasherTag] in
/-- A validator without an exit that gets an exit epoch after `e` keeps its activity at `e`. -/
theorem isActive_of_later_exit (w : Validator) (x y e : Epoch)
    (hfar : w.exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch) (hex : e.toNat < x.toNat)
    (hef : e.toNat < EthCLSpecs.Heze.Const.farFutureEpoch.toNat) :
    isActiveValidator { w with exitEpoch := x, withdrawableEpoch := y } e =
      isActiveValidator w e := by
  unfold isActiveValidator
  rw [hfar]
  simp [UInt64.lt_iff_toNat_lt, hex, hef]

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `increaseBalance` returns a state value with the `comView` of its argument. -/
@[frame] theorem increaseBalance_ret_com {e : Epoch} {u t t' b : BeaconState}
    {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.increaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    comView e (pureState b) = comView e (pureState u) := by
  frame_invert h

/-- `decreaseBalance` returns a state value with the `comView` of its argument. -/
@[frame] theorem decreaseBalance_ret_com {e : Epoch} {u t t' b : BeaconState}
    {i : ValidatorIndex} {d : Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    comView e (pureState b) = comView e (pureState u) := by
  frame_invert h

/-- **An exit keeps the committees of the window.** `initiateValidatorExit` sets the exit
epoch of a validator without one. The new exit epoch is at least
`compute_activation_exit_epoch` of the current epoch (`computeExitEpochAndUpdateChurn_ge`), so
it is after `e`, and the validator stays active at `e`. -/
@[frame] theorem initiateValidatorExit_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  have hw := window_of_comView hs
  unfold EthCLSpecs.Heze.initiateValidatorExit at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v, s1, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hv', rfl⟩ := sszGetIdx_run_ok hv
  simp only [SizzLean.Proofs.view_uncachedBox] at hv'
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, h⟩
  · rw [pureState_inj (EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h)]
    exact hs
  · have hfar : v.exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch := by
      unfold EthCLSpecs.Heze.hasNotInitiatedExit at hc
      simpa using hc
    obtain ⟨x, s2, hx, h⟩ :=
      run_bind_eq_ok_pure (keepsUncached_computeExitEpochAndUpdateChurn _) h
    have hxb := computeExitEpochAndUpdateChurn_ge hx
    obtain ⟨_act, _c, _, _, _, hs2⟩ := computeExitEpochAndUpdateChurn_run _ _ hx
    subst hs2
    obtain ⟨we, s3, hwe, h⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨rfl, -, -⟩ := checkedAdd_run_ok hwe
    have e1 := EthCLLib.Proofs.run_modifyThe_eq_ok h
    rw [modValidator_pureState] at e1
    rw [e1, ← hs]
    have hget : t.validators[i.toNat]! = v := by
      rw [sszList_getElem!_eq]
      have hlt := (Array.getElem?_eq_some_iff.mp hv').1
      rw [getElem!_pos t.validators.val i.toNat hlt]
      exact (Array.getElem?_eq_some_iff.mp hv').2
    refine (comView_setValidator _ _ _ ?_).trans rfl
    show isActiveValidator { t.validators[i.toNat]! with exitEpoch := x, withdrawableEpoch := _ } e =
      isActiveValidator t.validators[i.toNat]! e
    rw [hget]
    have hfar64 : EthCLSpecs.Heze.Const.farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
    have hcur := hw.1
    have hroom := hw.2.2.1
    refine isActive_of_later_exit v x _ e hfar ?_ ?_
    · change e.toNat ≤ (EthCLSpecs.Heze.computeEpochAtSlot t.slot).toNat at hcur
      change (EthCLSpecs.Heze.computeEpochAtSlot t.slot).toNat + 1 + maxSeedLookahead.toNat
        < 2 ^ 64 at hroom
      omega
    · rw [hfar64]
      change (currentEpochOf (pureState t)).toNat + 1 + maxSeedLookahead.toNat < 2 ^ 64 at hroom
      omega

/-- **A slashing keeps the committees of the window.** `slashValidator` runs the exit, then
writes the slashed flag and the withdrawable epoch, the slashings vector, and three balances. -/
@[frame] theorem slashValidator_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.slashValidator (StateTransition := HezeRun) i).run (pureState t)
      = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  unfold EthCLSpecs.Heze.slashValidator at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨⟨⟩, a1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_initiateValidatorExit i) h
  have k1 := initiateValidatorExit_frame_com h1 hs
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨v1, s, hv, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hv
  simp only [modValidator_pureState] at h
  simp only [pureState_eq_ofValue, uncached_ofValue_view] at h
  simp only [box_view_uncached, uncached_ofValue_view, uncached_mk_eq] at h
  simp only [← pureState_eq_ofValue] at h
  -- The two checked sums keep the state.
  obtain ⟨se, s0, hse, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok hse
  obtain ⟨sl, s0', hsl, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedAdd_run_ok hsl
  obtain ⟨x1, s1, h2, h⟩ := run_bind_eq_ok_ret (returnsUncached_decreaseBalance _ _ _) h
  obtain ⟨u1, s2, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h3
  subst e3
  have h := run_get_bind_eq_ok _ _ _ h
  -- The checked product `whistleblower_reward * PROPOSER_WEIGHT` keeps the state.
  obtain ⟨_, s2', hs2', h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, rfl, -⟩ := checkedMul_run_ok hs2'
  obtain ⟨x2, s3, h4, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  obtain ⟨x3, s4, h5, h⟩ := run_bind_eq_ok_ret (returnsUncached_increaseBalance _ _ _) h
  have e6 := EthCLLib.Proofs.run_set_state_eq _ _ _ _ h
  rw [e6, increaseBalance_ret_com h5, increaseBalance_ret_com h4, decreaseBalance_ret_com h2,
    ← k1]
  exact comView_setValidator a1 _ _ rfl

/-! ## The functions that write neither the activity nor the mixes -/

/-- `computeExitEpochAndUpdateChurn` keeps `comView`. -/
@[frame] theorem computeExitEpochAndUpdateChurn_frame_com {e : Epoch} {t t' : BeaconState}
    {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `computeConsolidationEpochAndUpdateChurn` keeps `comView`. -/
@[frame] theorem computeConsolidationEpochAndUpdateChurn_frame_com {e : Epoch}
    {t t' : BeaconState} {a : _} {b : Gwei}
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
      b).run (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `queueExcessActiveBalance` keeps `comView`. -/
@[frame] theorem queueExcessActiveBalance_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.queueExcessActiveBalance (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `switchToCompoundingValidator` keeps `comView`. Its write keeps the activation and exit
epochs. -/
@[frame] theorem switchToCompoundingValidator_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {i : ValidatorIndex}
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `initiateBuilderExit` keeps `comView`. -/
@[frame] theorem initiateBuilderExit_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {i : EthCLSpecs.Heze.BuilderIndex}
    (h : (EthCLSpecs.Heze.initiateBuilderExit (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `addBuilderToRegistry` keeps `comView`. -/
@[frame] theorem addBuilderToRegistry_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {pk : EthCLSpecs.Heze.BLSPubkey} {ver : UInt8} {addr : EthCLSpecs.Heze.ExecutionAddress}
    {amount : Gwei} {slot : Slot}
    (h : (EthCLSpecs.Heze.addBuilderToRegistry (StateTransition := HezeRun)
      pk ver addr amount slot).run (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processDepositRequest` keeps `comView`. It appends to the deposit queue. -/
@[frame] theorem processDepositRequest_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {dr : EthCLSpecs.Heze.DepositRequest}
    (h : (EthCLSpecs.Heze.processDepositRequest (StateTransition := HezeRun) dr).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processBuilderDepositRequest` keeps `comView`. -/
@[frame] theorem processBuilderDepositRequest_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {req : EthCLSpecs.Heze.BuilderDepositRequest}
    (h : (EthCLSpecs.Heze.processBuilderDepositRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processBuilderExitRequest` keeps `comView`. -/
@[frame] theorem processBuilderExitRequest_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {req : EthCLSpecs.Heze.BuilderExitRequest}
    (h : (EthCLSpecs.Heze.processBuilderExitRequest (StateTransition := HezeRun) req).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `settleBuilderPayment` keeps `comView`. -/
@[frame] theorem settleBuilderPayment_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {i : Nat}
    (h : (EthCLSpecs.Heze.settleBuilderPayment (StateTransition := HezeRun) i).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `applyWithdrawals` keeps `comView`. -/
@[frame] theorem applyWithdrawals_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps `comView`. -/
@[frame] theorem processWithdrawals_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps `comView`. -/
@[frame] theorem processEth1Data_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-- `processBlockHeader` keeps `comView`. -/
@[frame] theorem processBlockHeader_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {b : EthCLSpecs.Heze.BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processExecutionPayloadBid` keeps `comView`. Its builder checks need more than the
default heartbeat limit. -/
@[frame] theorem processExecutionPayloadBid_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {sbid : EthCLSpecs.Heze.SignedExecutionPayloadBid}
    (h : (EthCLSpecs.Heze.processExecutionPayloadBid (StateTransition := HezeRun) sbid).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

set_option maxHeartbeats 1000000 in
/-- `processAttestation` keeps `comView`. Its two nested loops need more than the default
heartbeat limit. -/
@[frame] theorem processAttestation_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {att : EthCLSpecs.Heze.Attestation}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState t) = .ok (a, pureState t')) :
    comView e (pureState t') = comView e (pureState t) := by
  frame_invert h

/-! ## The RANDAO write -/

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- Two numbers in one class modulo `n` differ by a multiple of `n`. A gap strictly between
zero and `n` is no multiple. -/
theorem mod_ne_of_gap {a b n : Nat} (hlt : b < a) (hgap : a - b < n)
    (h : a % n = b % n) : False := by
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq h
  have hd := Nat.dvd_of_mod_eq_zero h0
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- The entry that `processRandao` writes is not the seed entry of an epoch of the window. -/
theorem randaoIdx_ne {e cur : Epoch} (hcur : e.toNat ≤ cur.toNat ∧ cur.toNat ≤ e.toNat + 1)
    (hla : minSeedLookahead.toNat + 2 < epochsPerHistoricalVector)
    (hroom : e.toNat + epochsPerHistoricalVector < 2 ^ 64) :
    (cur % UInt64.ofNat epochsPerHistoricalVector).toNat ≠
      ((e + UInt64.ofNat epochsPerHistoricalVector - minSeedLookahead - 1) %
        UInt64.ofNat epochsPerHistoricalVector).toNat := by
  have hN := EthCLSpecs.Heze.Const.epochsPerHistoricalVectorLt
  have hN0 := EthCLSpecs.Heze.Const.epochsPerHistoricalVectorPos
  have hNn : (UInt64.ofNat epochsPerHistoricalVector).toNat = epochsPerHistoricalVector :=
    EthCLLib.Proofs.toNat_ofNat_lt64 hN
  have hsum : (e + UInt64.ofNat epochsPerHistoricalVector).toNat =
      e.toNat + epochsPerHistoricalVector := by
    rw [UInt64.toNat_add, hNn, Nat.mod_eq_of_lt hroom]
  have hs1 : (e + UInt64.ofNat epochsPerHistoricalVector - minSeedLookahead).toNat =
      e.toNat + epochsPerHistoricalVector - minSeedLookahead.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hsum]; omega), hsum]
  have hs2 : (e + UInt64.ofNat epochsPerHistoricalVector - minSeedLookahead - 1).toNat =
      e.toNat + epochsPerHistoricalVector - minSeedLookahead.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hs1]; simp; omega), hs1]
    simp
  rw [UInt64.toNat_mod, UInt64.toNat_mod, hNn, hs2]
  intro h
  rcases Nat.lt_or_ge cur.toNat (e.toNat + epochsPerHistoricalVector - minSeedLookahead.toNat - 1)
    with hl | hl
  · exact mod_ne_of_gap hl (by omega) h.symm
  · exact mod_ne_of_gap (b := e.toNat + epochsPerHistoricalVector - minSeedLookahead.toNat - 1)
      (a := cur.toNat + epochsPerHistoricalVector) (by omega) (by omega)
      (by rw [Nat.add_mod_right]; exact h)

/-- **`processRandao` keeps the committees of the window.** It writes the mix of the current
epoch, and the seed of `e` reads another entry (`randaoIdx_ne`). -/
@[frame] theorem processRandao_frame_com {e : Epoch} {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody} {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processRandao (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  have hw := window_of_comView hs
  unfold EthCLSpecs.Heze.processRandao at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨p, s1, hp, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hp
  obtain ⟨-, h⟩ := EthCLLib.Proofs.run_assert_bind_eq_ok _ _ _ _ h
  have e1 := EthCLLib.Proofs.run_modifyThe_eq_ok h
  -- The write changes one entry of the mix vector, at the index of the current epoch.
  have hrm := congrArg (fun s : State => s.view.randaoMixes) e1
  change t'.randaoMixes = t.randaoMixes.set!
    (umodIdx (currentEpochOf (pureState t)) epochsPerHistoricalVector) _ at hrm
  have hsl : t'.slot = t.slot := congrArg (fun s : State => s.view.slot) e1
  have hvs : t'.validators = t.validators := congrArg (fun s : State => s.view.validators) e1
  rw [← hs]
  simp only [comView, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · have hce : currentEpochOf (pureState t') = currentEpochOf (pureState t) := by
      show EthCLSpecs.Heze.computeEpochAtSlot t'.slot = EthCLSpecs.Heze.computeEpochAtSlot t.slot
      rw [hsl]
    exact decide_eq_decide.mpr (by
      unfold CommitteeWindow
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ t'.validators.val.size < 2 ^ 64 ↔ _
      rw [hce, hvs]
      try exact Iff.rfl)
  · show t'.validators.val.map _ = t.validators.val.map _
    rw [hvs]
  · show vmodGet t'.randaoMixes _ _ _ = vmodGet t.randaoMixes _ _ _
    unfold vmodGet
    simp only [hrm, Vector.set!]
    exact Vector.getElem_setIfInBounds_ne _
      (randaoIdx_ne ⟨hw.1, hw.2.1⟩ hw.2.2.2.1 hw.2.2.2.2.1)

/-! ## The functions that run an exit -/

open EthCLSpecs.Heze (modifyState) in
/-- An append to the consolidation queue keeps `comView`. -/
theorem appendConsolidation_frame_com {e : Epoch} {r t' : BeaconState}
    {q : EthCLSpecs.Heze.PendingConsolidation}
    (h : (appendState pendingConsolidations q : HezeRun Unit).run (pureState r)
      = .ok ((), pureState t')) :
    comView e (pureState t') = comView e (pureState r) := by
  frame_invert h

/-- **A consolidation request keeps the committees of the window.** A switch to compounding
writes credentials only. A consolidation sets the exit epoch of a source without one. The new
exit epoch is at least `compute_activation_exit_epoch` of the current epoch
(`computeConsolidationEpochAndUpdateChurn_ge`), so the source stays active at `e`. -/
@[frame] theorem processConsolidationRequest_frame_com {e : Epoch} {s t' : BeaconState}
    {a : PUnit} {req : EthCLSpecs.Heze.ConsolidationRequest}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState s) = .ok (a, pureState t'))
    (hs : comView e (pureState s) = (true, c)) : comView e (pureState t') = (true, c) := by
  have hw := window_of_comView hs
  -- A branch that returns `pure ()` keeps the state.
  have keep : ∀ {x : HezeRun PUnit}, x = pure PUnit.unit →
      x.run (pureState s) = .ok (a, pureState t') → comView e (pureState t') = (true, c) := by
    intro x hx hr
    subst hx
    rw [pureState_inj (EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hr)]
    exact hs
  unfold EthCLSpecs.Heze.processConsolidationRequest at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · -- A switch to compounding.
    split at h
    · exact (switchToCompoundingValidator_frame_com h).trans hs
    · exact keep rfl h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact keep rfl h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact keep rfl h
  -- The churn read keeps the state, and a low churn returns.
  obtain ⟨cl, s0, hcl, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := liftErr_run_ok_spec hcl
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact keep rfl h
  obtain ⟨⟨⟩, s0, h0, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h0
  subst e0
  split at h
  · rename_i srcN tgtN hsrc htgt
    have hsN := validatorIndexByPubkey?_lt hsrc
    have hv : s.validators.val[srcN]? = some (s.validators.val[srcN]'hsN) :=
      getElem?_pos s.validators.val srcN hsN
    simp only [SizzLean.Proofs.view_uncachedBox, SizzLean.Repr.SSZList.toArray, hv,
      Option.getD_some] at h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hne, h⟩
    · exact keep rfl h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    -- The pending-withdrawal read keeps the state, and a pending balance returns.
    obtain ⟨pb, s1, hpb, h⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨-, rfl⟩ := liftErr_run_ok_spec hpb
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact keep rfl h
    obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e1 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h1
    subst e1
    have hfar : (s.validators.val[srcN]'hsN).exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch := by
      unfold EthCLSpecs.Heze.hasNotInitiatedExit at hne
      simpa using hne
    have h64 : s.validators.val.size < 2 ^ 64 := hw.2.2.2.2.2
    obtain ⟨x, s2, hx, h⟩ :=
      run_bind_eq_ok_pure (keepsUncached_computeConsolidationEpochAndUpdateChurn _) h
    have hxb := computeConsolidationEpochAndUpdateChurn_ge hx
    obtain ⟨_act, c, _, _, _, hs2⟩ := computeConsolidationEpochAndUpdateChurn_run _ _ hx
    subst hs2
    obtain ⟨we, s3, hwe, h⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨rfl, -, -⟩ := checkedAdd_run_ok hwe
    obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e4 := EthCLLib.Proofs.run_modifyThe_eq_ok h4
    rw [modValidator_pureState] at e4
    subst e4
    rw [appendConsolidation_frame_com h, ← hs]
    have hj64 : (UInt64.ofNat srcN).toNat = srcN := EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)
    have hget : (afterConsChurn s (s.validators.val[srcN]'hsN).effectiveBalance x c).validators[
        (UInt64.ofNat srcN).toNat]! = s.validators.val[srcN]'hsN := by
      show s.validators[(UInt64.ofNat srcN).toNat]! = _
      rw [hj64, sszList_getElem!_eq, getElem!_pos s.validators.val srcN hsN]
    refine (comView_setValidator _ _ _ ?_).trans rfl
    rw [hget]
    have hfar64 : EthCLSpecs.Heze.Const.farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
    have hcur := hw.1
    have hroom := hw.2.2.1
    refine isActive_of_later_exit _ x _ e hfar ?_ ?_
    · omega
    · rw [hfar64]
      omega
  · exact keep rfl h

/-- `processWithdrawalRequest` keeps the committees of the window. A full exit runs
`initiateValidatorExit`, and a partial withdrawal writes the withdrawal queue. -/
@[frame] theorem processWithdrawalRequest_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {wr : EthCLSpecs.Heze.WithdrawalRequest}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-- `processProposerSlashing` keeps the committees of the window. -/
@[frame] theorem processProposerSlashing_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {ps : EthCLSpecs.Heze.ProposerSlashing}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-- `processAttesterSlashing` keeps the committees of the window. -/
@[frame] theorem processAttesterSlashing_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {asl : EthCLSpecs.Heze.AttesterSlashing}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processAttesterSlashing (StateTransition := HezeRun) asl).run
      (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-- `applyParentExecutionPayload` keeps the committees of the window. -/
@[frame] theorem applyParentExecutionPayload_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {requests : EthCLSpecs.Heze.ExecutionRequests}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.applyParentExecutionPayload (StateTransition := HezeRun)
      requests).run (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-- `processParentExecutionPayload` keeps the committees of the window. -/
@[frame] theorem processParentExecutionPayload_frame_com {e : Epoch} {t t' : BeaconState}
    {a : PUnit} {block : EthCLSpecs.Heze.BeaconBlock}
    {c : Array Bool × EthCLSpecs.Heze.Bytes32}
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun)
      block).run (pureState t) = .ok (a, pureState t'))
    (hs : comView e (pureState t) = (true, c)) : comView e (pureState t') = (true, c) := by
  frame_invert h

/-! ## A block sets the flag of each attesting index -/

/-- The loop invariant of a block before and inside the attestation loop: the committees of
`e` and the `locView` of the start state `u`. -/
def BlockInv (e : Epoch) (c : Array Bool × EthCLSpecs.Heze.Bytes32) (u s : BeaconState) : Prop :=
  comView e (pureState s) = (true, c) ∧ locView (pureState s) = locView (pureState u)

/-- A target flag stays set across a step that keeps the bits and the slot. -/
theorem flag_step {s s' : BeaconState} {j : Nat} {ep : Epoch} (hf : TargetFlagSet s j ep)
    (hk : BitsKept s s') (hsl : s'.slot = s.slot) : TargetFlagSet s' j ep :=
  hf.of_bitsKept hk hsl

/-- **A block sets the target flag of each attesting index of its attestations.** The
attestation `att` of the body has `i` as an attesting index at the start state `u`, and its
target root is the block root of its target epoch there. The block keeps the committees of the
epoch of `att` (`comView`) and the slot and the block roots (`locView`) up to the loop state of
`att`. So `processAttestation` sees the same attesting indices and the same target root, and it
sets the flag. The later functions of the block keep it. -/
theorem processBlock_sets_flag (b : BeaconBlock) {u u' : BeaconState}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState u)
      = .ok ((), pureState u'))
    {att : EthCLSpecs.Heze.Attestation} (ha : att ∈ b.body.attestations.toArray)
    {i : ValidatorIndex} {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getAttestingIndices (pureState u) att = .ok idx) (hi : i ∈ idx)
    (htgt : runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState u)
      att.data.target.epoch) u = .ok (att.data.target.root, u))
    (hwin : CommitteeWindow (EthCLSpecs.Heze.computeEpochAtSlot att.data.slot) (pureState u)) :
    TargetFlagSet u' i.toNat att.data.target.epoch := by
  let e := EthCLSpecs.Heze.computeEpochAtSlot att.data.slot
  let c := (comView e (pureState u)).2
  have hs0 : comView e (pureState u) = (true, c) := by
    show ((comView e (pureState u)).1, (comView e (pureState u)).2) = (true, c)
    have : (comView e (pureState u)).1 = true := by simpa [comView] using hwin
    rw [this]
  have I0 : BlockInv e c u u := ⟨hs0, rfl⟩
  -- A step with the two frames keeps the invariant.
  have step : ∀ {s s' : BeaconState}, BlockInv e c u s →
      (comView e (pureState s) = (true, c) → comView e (pureState s') = (true, c)) →
      locView (pureState s') = locView (pureState s) → BlockInv e c u s' :=
    fun hI hc hl => ⟨hc hI.1, hl.trans hI.2⟩
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  obtain ⟨⟨⟩, s7, h7, h8⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  have I1 := step I0 (processParentExecutionPayload_frame_com h1)
    (locView_of_frames (processParentExecutionPayload_frame_ord h1)
      (processParentExecutionPayload_frame_hdr h1))
  have I2 : BlockInv e c u s2 := by
    refine step I1 (fun hc => (processBlockHeader_frame_com h2).trans hc) ?_
    have e1 := processBlockHeader_frame_ord h2
    obtain ⟨-, -, -, e2, -⟩ := processBlockHeader_run_hdr _ _ _ h2
    simp only [locView, Prod.mk.injEq]
    exact ⟨e1, e2⟩
  have I3 := step I2 (fun hc => (processWithdrawals_frame_com h3).trans hc)
    (locView_of_frames (processWithdrawals_frame_ord h3) (processWithdrawals_frame_hdr h3))
  have I4 := step I3 (fun hc => (processExecutionPayloadBid_frame_com h4).trans hc)
    (locView_of_frames (processExecutionPayloadBid_frame_ord h4)
      (processExecutionPayloadBid_frame_hdr h4))
  have I5 := step I4 (processRandao_frame_com h5)
    (locView_of_frames (processRandao_frame_ord h5) (processRandao_frame_hdr h5))
  have I6 := step I5 (fun hc => (processEth1Data_frame_com h6).trans hc)
    (locView_of_frames (processEth1Data_frame_ord h6) (processEth1Data_frame_hdr h6))
  -- The sync aggregate keeps the bits and the slot.
  have f8 : ∀ {j : Nat} {ep : Epoch}, TargetFlagSet s7 j ep → TargetFlagSet u' j ep :=
    fun hf => flag_step hf
      (BitsKept.of_partView fun w j => processSyncAggregate_frame_part (cur := w) (i := j) h8)
      (congrArg Prod.snd (processSyncAggregate_frame_part (cur := true) (i := 0) h8))
  refine f8 ?_
  -- The operations.
  unfold EthCLSpecs.Heze.processOperations at h7
  obtain ⟨-, h7⟩ := run_assert_bind_eq_ok _ _ _ _ h7
  obtain ⟨⟨⟩, o1, k1, h7⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun ps _ =>
    keepsUncached_bind (keepsUncached_processProposerSlashing ps)
      (fun _ => keepsUncached_pure _)) _ _) h7
  have J1 : BlockInv e c u o1 := forIn_array_ops_inv (BlockInv e c u) _
    keepsUncached_processProposerSlashing b.body.proposerSlashings.val
    (fun _ _ s s' hs hr => step hs (processProposerSlashing_frame_com hr)
      (locView_of_frames (processProposerSlashing_frame_ord hr)
        (processProposerSlashing_frame_hdr hr)))
    s6 o1 I6 k1
  obtain ⟨⟨⟩, o2, k2, h7⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttesterSlashing a)
      (fun _ => keepsUncached_pure _)) _ _) h7
  have J2 : BlockInv e c u o2 := forIn_array_ops_inv (BlockInv e c u) _
    keepsUncached_processAttesterSlashing b.body.attesterSlashings.val
    (fun _ _ s s' hs hr => step hs (processAttesterSlashing_frame_com hr)
      (locView_of_frames (processAttesterSlashing_frame_ord hr)
        (processAttesterSlashing_frame_hdr hr)))
    o1 o2 J1 k2
  obtain ⟨⟨⟩, o3, k3, h7⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h7
  -- The attestation loop: `att` sets the flag, and the other attestations keep it.
  have J3 : TargetFlagSet o3 i.toNat att.data.target.epoch :=
    forIn_array_ops_at (BlockInv e c u) (fun s => TargetFlagSet s i.toNat att.data.target.epoch)
      _ keepsUncached_processAttestation b.body.attestations.val att ha
      (fun d _ s s' hs hr => ⟨step hs (fun hc => (processAttestation_frame_com hr).trans hc)
          (locView_of_frames (processAttestation_frame_ord hr) (processAttestation_frame_hdr hr)),
        fun hf => flag_step hf (processAttestation_keeps d hr)
          (congrArg Prod.snd (processAttestation_frame_ord hr))⟩)
      (fun s s' hs hr => by
        have hc : comView e (pureState s) = comView e (pureState u) := hs.1.trans hs0.symm
        have hidx' := (getAttestingIndices_eq_of_comView hc att rfl).trans hidx
        have hl := hs.2
        simp only [locView, ordView, Prod.mk.injEq] at hl
        obtain ⟨⟨-, hsl⟩, hbr⟩ := hl
        have htgt' := getBlockRoot_run_transfer hsl hbr htgt
        exact processAttestation_sets_target att s s' idx (runPure_of_run_ok hr) hidx' htgt' i hi)
      o2 o3 J2 k3
  -- The rest of the operations keep the bits and the slot.
  obtain ⟨⟨⟩, o4, k4, h7⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processVoluntaryExit a)
      (fun _ => keepsUncached_pure _)) _ _) h7
  obtain ⟨⟨⟩, o5, k5, h7⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processBlsToExecutionChange a)
      (fun _ => keepsUncached_pure _)) _ _) h7
  obtain ⟨⟨⟩, o6, k6, hp⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processPayloadAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h7
  rw [pureState_inj (EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hp)]
  let Q : BeaconState → Prop := fun s => TargetFlagSet s i.toNat att.data.target.epoch
  have keepQ : ∀ s s' : BeaconState, Q s →
      (∀ w j, partView w j (pureState s') = partView w j (pureState s)) → Q s' :=
    fun s s' hs hb => flag_step hs (BitsKept.of_partView hb) (congrArg Prod.snd (hb true 0))
  have J4 : Q o4 := forIn_array_ops_inv Q _ keepsUncached_processVoluntaryExit
    b.body.voluntaryExits.val
    (fun _ _ s s' hs hr => keepQ s s' hs fun w j =>
      processVoluntaryExit_frame_part (cur := w) (i := j) hr) o3 o4 J3 k4
  have J5 : Q o5 := forIn_array_ops_inv Q _ keepsUncached_processBlsToExecutionChange
    b.body.blsToExecutionChanges.val
    (fun _ _ s s' hs hr => keepQ s s' hs fun w j =>
      processBlsToExecutionChange_frame_part (cur := w) (i := j) hr) o4 o5 J4 k5
  exact forIn_array_ops_inv Q _ keepsUncached_processPayloadAttestation
    b.body.payloadAttestations.val
    (fun _ _ s s' hs hr => keepQ s s' hs fun _ _ =>
      frame_of_reads (processPayloadAttestation_frame hr)) o5 o6 J5 k6

end

end EthCLSpecs.Proofs.Heze
