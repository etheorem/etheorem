import EthCLSpecs.Proofs.Heze.StoreFinality
import EthCLSpecs.Proofs.Heze.StoreClock

/-!
# `EthCLSpecs.Proofs.Heze.FinLag`: the finalized epoch lags the clock by two epochs

`finalized_epoch_le` bounds the finalized epoch of a store by the previous epoch of its clock.
The spec keeps it lower: the finalized epoch of an honest store is at most the current epoch
less two, or the anchor's.

## States

`process_justification_and_finalization` writes a finalized checkpoint at most the old current
justified one (`processJustificationAndFinalization_run_fin_le_cj`), and that is at most the
previous epoch (`StateCkptOrd`). It runs at the end of an epoch, and the slot increment then
starts the next epoch. So a chain state has a finalized epoch at most its epoch less two, or the
anchor's (`StateLag`, `ChainRun.stateLag`). A pull-up runs the same step without the increment,
so its finalized epoch is at most the state's epoch less one (`pullup_fin_le`).

## Stores

`on_tick_per_slot` realizes the unrealized checkpoints only at the first slot of a new epoch
(`onTickPerSlot_run_fin`). A tick that moves the clock forward does that at a later epoch of the
clock, or keeps the finalized checkpoint (`onTick_run_fin`). `compute_pulled_up_tip` writes the
pulled-up finalized checkpoint onto the realized one only for a block before the clock's epoch
(`computePulledUpTip_run_fin`). So a store keeps `StoreLag`: its finalized epoch is at most the
anchor's or the clock's epoch less two, and its unrealized one at most the anchor's or the
clock's epoch less one (`NodeTrace.storeLag`).

## Clocked traces

A tick that moves the clock back keeps the unrealized finalized checkpoint and copies it at most
into the finalized one. Each event of a clocked trace runs at its wall time, and the wall times
do not decrease. So a tick moves the clock forward, or the store before it has both finalized
epochs at most the anchor epoch (`NodeTrace.clockLast`, `ClockedTrace.tickLag`). The anchor
store starts there, so every store of a clocked trace meets `StoreLag` (`ClockedTrace.storeLag`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt LawfulFcMap pureState runPure runPure_of_run_ok
  run_bind_eq_ok run_bind_eq_ok_pure run_get_bind_eq_ok run_ite_eq_ok run_pure_eq_ok
  run_pure_state_eq run_set_state_eq)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Checkpoint BeaconBlock
  SignedBeaconBlock SignedInclusionList previousEpochOf currentEpochOf
  processJustificationAndFinalization updateCheckpoints computePulledUpTip onTick onTickPerSlot
  onBlock getCurrentSlot getCurrentStoreEpoch)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

/-! ## States -/

section States
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `processJustificationAndFinalization` on an ordered state writes a finalized epoch at most
the old current justified epoch. The finalized checkpoint it writes is one of the two old
justified ones or the old finalized one (`finalizeRules`), and the order puts all three at or
below the old current justified one. -/
theorem processJustificationAndFinalization_run_fin_le_cj (v w : BeaconState)
    (hv : StateCkptOrd v)
    (h : runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v
      = .ok ((), w)) :
    w.finalizedCheckpoint.epoch.toNat ≤ v.currentJustifiedCheckpoint.epoch.toNat := by
  obtain ⟨h1, h2, -⟩ := hv
  rw [UInt64.le_iff_toNat_le] at h1 h2
  by_cases hg : currentEpochOf (pureState v) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1
  · rw [processJustificationAndFinalization_run_eq, ite_eq_left hg] at h
    cases h
    omega
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, h⟩ := processJustificationAndFinalization_run_ok h hg
    obtain ⟨pr, cr, hw⟩ := weighJustificationAndFinalization_run_ok v w _ _ _ h
    dsimp only at hw
    obtain ⟨-, -, -, hf, -, -⟩ := hw
    rw [hf]
    exact finalizeRules_epoch_le _ _ _ _ _ _ h2 (Nat.le_refl _) (Nat.le_trans h1 h2)

/-- The finalized epoch of a state is at most `e₀`, or at most its epoch less two. -/
def StateLag (e₀ : Nat) (v : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch.toNat ≤ e₀ ∨
    v.finalizedCheckpoint.epoch.toNat + 2 ≤ v.slot.toNat / slotsPerEpoch

/-- A pull-up of an ordered state writes a finalized epoch at most the state's epoch less one,
or zero. -/
theorem pullup_fin_le (v w : BeaconState) (hv : StateCkptOrd v)
    (h : runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v
      = .ok ((), w)) :
    w.finalizedCheckpoint.epoch.toNat = 0 ∨
      w.finalizedCheckpoint.epoch.toNat + 1 ≤ v.slot.toNat / slotsPerEpoch := by
  have h1 := processJustificationAndFinalization_run_fin_le_cj v w hv h
  have h3 := hv.2.2
  rw [UInt64.le_iff_toNat_le, previousEpochOf_toNat_sub] at h3
  omega

/-- A slot step keeps `StateLag`. At the end of an epoch, the finalized epoch it writes is at
most the old current justified epoch, at most the old epoch less one, and the increment starts
the next epoch. Otherwise the finalized checkpoint stays and the epoch does not go down. -/
theorem SlotStep.stateLag {e₀ : Nat} {st st' : BeaconState} (h : SlotStep st st')
    (hlt : st.slot.toNat + 1 < 2 ^ 64) (hv : StateCkptOrd st) (hl : StateLag e₀ st) :
    StateLag e₀ st' := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 : ordView (pureState st1) = ordView (pureState st) := processSlot_frame_ord h1
  simp only [ordView, Prod.mk.injEq] at e1
  obtain ⟨ck1, sl1⟩ := e1
  change st1.slot = st.slot at sl1
  have hck' : ckView (pureState st') = ckView (pureState st2) := by
    rw [hst']
    rfl
  have hsl' : st'.slot = st2.slot + 1 := by
    change sszGet (pureState st') slot = _
    rw [hst']
    rfl
  have hv1 : StateCkptOrd st1 := hv.of_ckView ck1 (Nat.le_of_eq (by
    rw [previousEpochOf_toNat_sub, previousEpochOf_toNat_sub, sl1]))
  simp only [ckView, Prod.mk.injEq] at ck1 hck'
  obtain ⟨-, hc1, hf1, -⟩ := ck1
  change st1.currentJustifiedCheckpoint = st.currentJustifiedCheckpoint at hc1
  change st1.finalizedCheckpoint = st.finalizedCheckpoint at hf1
  obtain ⟨-, -, hf', -⟩ := hck'
  change st'.finalizedCheckpoint = st2.finalizedCheckpoint at hf'
  split at h2
  · rename_i htest
    have hb := (epochTest_iff st1.slot (by rw [sl1]; exact hlt)).mp htest
    rw [sl1] at hb
    rw [processEpoch_eq_jf] at h2
    obtain ⟨⟨⟩, mid, hjf, hrest⟩ :=
      run_bind_eq_ok_pure keepsUncached_processJustificationAndFinalization h2
    have er : ordView (pureState st2) = ordView (pureState mid) :=
      processEpochAfterJF_frame_ord hrest
    simp only [ordView, Prod.mk.injEq] at er
    obtain ⟨ck2, sl2⟩ := er
    change st2.slot = mid.slot at sl2
    simp only [ckView, Prod.mk.injEq] at ck2
    obtain ⟨-, -, hf2, -⟩ := ck2
    change st2.finalizedCheckpoint = mid.finalizedCheckpoint at hf2
    have o4 := (processJustificationAndFinalization_run_ord st1 mid hv1
      (runPure_of_run_ok hjf)).2.2.2
    have hfin := processJustificationAndFinalization_run_fin_le_cj st1 mid hv1
      (runPure_of_run_ok hjf)
    have hsln : st'.slot.toNat = st.slot.toNat + 1 := by
      rw [hsl', sl2, o4, sl1, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    have hcj := hv.2.2
    rw [UInt64.le_iff_toNat_le, previousEpochOf_toNat_sub] at hcj
    rw [hc1] at hfin
    have hdiv : st'.slot.toNat / slotsPerEpoch = st.slot.toNat / slotsPerEpoch + 1 := by
      rw [hsln]
      exact succ_div_of_mod_eq hb
    unfold StateLag
    rw [hf', hf2, hdiv]
    omega
  · subst h2
    have hsln : st'.slot.toNat = st.slot.toNat + 1 := by
      rw [hsl', sl1, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    have hdiv : st.slot.toNat / slotsPerEpoch ≤ st'.slot.toNat / slotsPerEpoch := by
      rw [hsln]
      exact Nat.div_le_div_right (Nat.le_succ _)
    unfold StateLag at hl ⊢
    rw [hf', hf1]
    omega

/-- A block step keeps `StateLag`: `processBlock` keeps the finalized checkpoint and the slot. -/
theorem BlockStep.stateLag {e₀ : Nat} {sb : SignedBeaconBlock} {vr : Bool}
    {st st' : BeaconState} (h : BlockStep sb vr st st') (hl : StateLag e₀ st) :
    StateLag e₀ st' := by
  have e := processBlock_frame_ord h.2.1
  simp only [ordView, Prod.mk.injEq] at e
  obtain ⟨ck, sl⟩ := e
  change st'.slot = st.slot at sl
  simp only [ckView, Prod.mk.injEq] at ck
  obtain ⟨-, -, hf, -⟩ := ck
  change st'.finalizedCheckpoint = st.finalizedCheckpoint at hf
  unfold StateLag at hl ⊢
  rw [hf, sl]
  exact hl

/-- A chain run keeps `StateLag`, with the state order along it. -/
theorem ChainRun.stateLag {e₀ hi : Nat} {steps : List ChainStep} {v w : BeaconState}
    (h : ChainRun hi steps v w) (hhi : hi ≤ 2 ^ 64 - 1) (hv : StateCkptOrd v)
    (hl : StateLag e₀ v) : StateLag e₀ w := by
  induction h with
  | nil => exact hl
  | @slot _ st _ _ hlt hstep _ ih =>
    have hlt' : st.slot.toNat + 1 < 2 ^ 64 := by change st.slot.toNat < hi at hlt; omega
    exact ih (hstep.stateCkptOrd hlt' hv) (hstep.stateLag hlt' hv hl)
  | block sb vr hstep _ ih => exact ih (hstep.stateCkptOrd hv) (hstep.stateLag hl)

end States

/-! ## The tick -/

section Tick
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

omit [HasherTag] [Config] in
/-- Zero slots since the epoch start, as `on_tick_per_slot` computes them, put `x` at the first
slot of an epoch. The converse of `slotsSinceEpochStart_zero`. -/
theorem slotsSinceEpochStart_zero_mod {x r : UInt64}
    (hr : (EthCLSpecs.Heze.computeStartSlotAtEpoch (EthCLSpecs.Heze.computeEpochAtSlot x)
      : Except StateTransitionError UInt64) = .ok r) (h0 : x - r = 0) :
    x.toNat % slotsPerEpoch = 0 := by
  have hp := slotsPerEpochPos
  have hlt := EthCLSpecs.Heze.Const.slotsPerEpochLt
  have hk : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    EthCLLib.Proofs.toNat_ofNat_lt64 hlt
  have hm : r.toNat = x.toNat / slotsPerEpoch * slotsPerEpoch := by
    rw [computeStartSlotAtEpoch_ok_eq hr]
    unfold EthCLSpecs.Heze.computeEpochAtSlot
    rw [UInt64.toNat_mul, UInt64.toNat_div, hk]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.toNat_lt
  have hle : r.toNat ≤ x.toNat := by rw [hm]; exact Nat.div_mul_le_self _ _
  have hs := congrArg UInt64.toNat h0
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hle)] at hs
  have hx : x.toNat = x.toNat / slotsPerEpoch * slotsPerEpoch := by
    change x.toNat - r.toNat = 0 at hs
    omega
  rw [hx, Nat.mul_mod_left]

/-- **A per-slot tick and the finalized checkpoint.** The tick keeps the unrealized finalized
checkpoint and sets the clock. It keeps the finalized checkpoint, or it takes the unrealized one
by `ckptPick`, and then the new clock reads the first slot of an epoch, above the old slot. -/
theorem onTickPerSlot_run_fin (store post st st' : Store map) (time : UInt64)
    (h : (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store time).run st
      = .ok (post, st')) :
    post.unrealizedFinalizedCheckpoint = store.unrealizedFinalizedCheckpoint ∧
    (post.finalizedCheckpoint = store.finalizedCheckpoint ∨
      (post.finalizedCheckpoint =
          ckptPick store.finalizedCheckpoint store.unrealizedFinalizedCheckpoint ∧
        storeSlot store < storeSlot { store with timeMs := time } ∧
        storeSlot { store with timeMs := time } % slotsPerEpoch = 0)) := by
  simp only [onTickPerSlot, EthCLLib.Proofs.run_bind] at h
  cases h1 : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run st
    with
  | error e => rw [h1] at h; exact nomatch h
  | ok p =>
    rw [h1, EthCLLib.Proofs.except_bind_ok] at h
    cases h2 : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
        { store with timeMs := time }).run p.2 with
    | error e => rw [h2] at h; exact nomatch h
    | ok q =>
      rw [h2, EthCLLib.Proofs.except_bind_ok] at h
      cases h3 : (onTickPerSlot.computeSlotsSinceEpochStart
          (StoreTransition := ForkChoiceStoreRun (Store map)) q.1).run q.2 with
      | error e => rw [h3] at h; exact nomatch h
      | ok k =>
      rw [h3, EthCLLib.Proofs.except_bind_ok, EthCLLib.Proofs.run_pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e1 := getCurrentSlot_storeSlot h1
      have e2 := getCurrentSlot_storeSlot h2
      -- The slots since the epoch start: zero puts the new slot at an epoch start.
      have hk0 : k.1 = 0 → storeSlot { store with timeMs := time } % slotsPerEpoch = 0 := by
        intro hk
        unfold onTickPerSlot.computeSlotsSinceEpochStart at h3
        rw [EthCLLib.Proofs.run_bind] at h3
        cases hr : (EthCLSpecs.Heze.computeStartSlotAtEpoch
            (EthCLSpecs.Heze.computeEpochAtSlot q.1) : Except StateTransitionError UInt64) with
        | error err =>
          rw [hr, EthCLLib.Proofs.run_liftErr_of_error _ _ rfl] at h3
          cases h3
        | ok r =>
          rw [hr, EthCLLib.Proofs.run_liftErr_of_ok _ _ rfl, EthCLLib.Proofs.except_bind_ok,
            EthCLLib.Proofs.run_pure] at h3
          injection h3 with h3
          have hq : q.1 - r = 0 := by
            have h3' := congrArg Prod.fst h3
            simp only at h3'
            rw [h3']
            exact hk
          rw [← e2]
          exact slotsSinceEpochStart_zero_mod hr hq
      split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨hgt, hk⟩ := hc
        rw [updateCheckpoints_eq]
        refine ⟨by split <;> rfl, .inr ⟨by split <;> rfl, ?_, hk0 hk⟩⟩
        have := UInt64.lt_iff_toNat_lt.mp hgt
        omega
      · exact ⟨by split <;> rfl, .inl (by split <;> rfl)⟩

omit [HasherTag] [Config] [FcMap map] in
/-- A second `ckptPick` with the same candidate changes nothing. -/
theorem ckptPick_idem (a b : Checkpoint) : ckptPick (ckptPick a b) b = ckptPick a b := by
  unfold ckptPick
  split
  · simp [UInt64.lt_irrefl]
  · simp

/-- The state of the tick loop toward the tick slot `T`, from the store `p`: the genesis time
and the unrealized finalized checkpoint of `p`, a slot from the slot of `p` to `T`, and the
finalized checkpoint of `p`, or the pick of `p`'s unrealized one at a later epoch. -/
def TickLag (p : Store map) (T : Nat) (s : Store map) : Prop :=
  s.genesisTimeMs = p.genesisTimeMs ∧
  s.unrealizedFinalizedCheckpoint = p.unrealizedFinalizedCheckpoint ∧
  storeSlot p ≤ storeSlot s ∧ storeSlot s ≤ T ∧
  (s.finalizedCheckpoint = p.finalizedCheckpoint ∨
    (s.finalizedCheckpoint = ckptPick p.finalizedCheckpoint p.unrealizedFinalizedCheckpoint ∧
      storeSlot p / slotsPerEpoch < storeSlot s / slotsPerEpoch))

/-- **A tick forward and the finalized checkpoint.** A tick to a time no earlier than the clock
keeps the unrealized finalized checkpoint and does not move the slot back. It keeps the
finalized checkpoint, or it takes the unrealized one by `ckptPick` at a later epoch of the
clock. Each step of the loop moves to the next slot up to the tick slot, and a step that
realizes lands on the first slot of an epoch above the old slot (`onTickPerSlot_run_fin`). -/
theorem onTick_run_fin (hD0 : 0 < EthCLSpecs.Heze.Const.slotDurationMs.toNat) (time : UInt64)
    {pre post : Store map}
    (hmono : storeSlot pre ≤
      (time.toNat - pre.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat)
    (h : (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time).run pre
      = .ok ((), post)) :
    post.unrealizedFinalizedCheckpoint = pre.unrealizedFinalizedCheckpoint ∧
    storeSlot pre ≤ storeSlot post ∧
    storeSlot post ≤
      (time.toNat - pre.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat ∧
    (post.finalizedCheckpoint = pre.finalizedCheckpoint ∨
      (post.finalizedCheckpoint =
          ckptPick pre.finalizedCheckpoint pre.unrealizedFinalizedCheckpoint ∧
        storeSlot pre / slotsPerEpoch < storeSlot post / slotsPerEpoch)) := by
  have hp := slotsPerEpochPos
  unfold onTick at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨tickSlot, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨htk, e1⟩ := EthCLLib.Proofs.run_liftErr_eq_ok _ _ _ _ h1
  rw [e1] at h
  obtain ⟨-, htkv⟩ := computeSlotAtTimeMs_ok htk
  obtain ⟨cur, s3, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 : s3 = pre := getCurrentSlot_keeps pre pre pre cur s3 rfl h3
  rw [e3] at h
  have hsame : ∀ a b : Store map, a.timeMs = b.timeMs → a.genesisTimeMs = b.genesisTimeMs →
      storeSlot a = storeSlot b := by
    intro a b ht hg
    unfold storeSlot
    rw [ht, hg]
  -- The tick slot bounds the slot of `pre`: the clock moves forward.
  have hpT : storeSlot pre ≤ tickSlot.toNat := by
    rw [htkv]
    exact hmono
  have hfin := GrowsAt.fuelIterateM!
    (R := fun s s' => TickLag pre tickSlot.toNat s → TickLag pre tickSlot.toNat s')
    (fun _ hs => hs) (fun _ _ _ hab hbc hs => hbc (hab hs)) _ _ ?_ _ _ pre () post h
    ⟨rfl, rfl, Nat.le_refl _, hpT, .inl rfl⟩
  · obtain ⟨-, huf, hlo, hhi, hf⟩ := hfin
    exact ⟨huf, hlo, by rw [← htkv]; exact hhi, hf⟩
  intro b s a s' hr hQs
  obtain ⟨hgs, hufs, hlos, hhis, hfs⟩ := hQs
  have hr := run_get_bind_eq_ok _ _ _ hr
  obtain ⟨cs, t1, hc, hr⟩ := run_bind_eq_ok _ _ _ _ hr
  have et1 : t1 = s := getCurrentSlot_keeps s s s cs t1 rfl hc
  rw [et1] at hr
  have hcs := getCurrentSlot_storeSlot hc
  -- The finalized checkpoint after a per-slot step from `s` to a clock of slot `n`.
  have hstep : ∀ (nt : UInt64) (p' : Store map) (t5 : Store map),
      (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) s nt).run s
        = .ok (p', t5) →
      storeSlot s ≤ storeSlot { s with timeMs := nt } →
      storeSlot { s with timeMs := nt } ≤ tickSlot.toNat →
      TickLag pre tickSlot.toNat p' := by
    intro nt p' t5 hpst hle hle'
    obtain ⟨hpt, hpg⟩ := onTickPerSlot_run_clock _ _ _ _ _ hpst
    obtain ⟨huf', hf'⟩ := onTickPerSlot_run_fin _ _ _ _ _ hpst
    have hps : storeSlot p' = storeSlot { s with timeMs := nt } := hsame _ _ hpt hpg
    refine ⟨hpg.trans hgs, huf'.trans hufs, by omega, by omega, ?_⟩
    rcases hf' with e | ⟨e, hlt, hz⟩
    · rw [e]
      rcases hfs with e' | ⟨e', hlt'⟩
      · exact .inl e'
      · exact .inr ⟨e', Nat.lt_of_lt_of_le hlt' (Nat.div_le_div_right (by omega))⟩
    · refine .inr ⟨?_, ?_⟩
      · rw [e, hufs]
        rcases hfs with e' | ⟨e', -⟩
        · rw [e']
        · rw [e', ckptPick_idem]
      · rw [hps]
        have hk := Nat.div_add_mod (storeSlot { s with timeMs := nt }) slotsPerEpoch
        rw [hz, Nat.add_zero] at hk
        have hlt2 : storeSlot pre < storeSlot { s with timeMs := nt } := by omega
        have : storeSlot pre / slotsPerEpoch < storeSlot { s with timeMs := nt } / slotsPerEpoch := by
          apply (Nat.div_lt_iff_lt_mul hp).mpr
          rw [Nat.mul_comm] at hk
          omega
        exact this
  rcases run_ite_eq_ok hr with ⟨hlt, hr⟩ | ⟨hnl, hr⟩
  · -- A step to the start of the next slot.
    obtain ⟨bumped, t2, hb, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨eb, hbv, hbfit⟩ := store_checkedAdd_ok hb
    rw [eb] at hr
    have hr := run_get_bind_eq_ok _ _ _ hr
    obtain ⟨nt, t4, hnt, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨hntv, ent⟩ := EthCLLib.Proofs.run_liftErr_eq_ok _ _ _ _ hnt
    rw [ent] at hr
    have hr := run_get_bind_eq_ok _ _ _ hr
    obtain ⟨p, t5, hpst, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨u, t6, hu, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    have e6 := run_set_state_eq _ _ _ _ hu
    rw [e6] at hr
    have e7 := run_pure_state_eq _ _ _ _ hr
    subst e7
    have hbfit' : cs.toNat + 1 < 2 ^ 64 := by simpa using hbfit
    have hb1 : bumped.toNat = cs.toNat + 1 := by
      rw [hbv, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hbfit']
    have hcs1 : storeSlot { s with timeMs := nt } = cs.toNat + 1 := by
      unfold storeSlot
      show (nt.toNat - s.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat = _
      rw [computeTimeAtSlotMs_ok hntv, hb1, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hD0]
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    exact hstep nt _ t5 hpst (by omega) (by omega)
  · -- The last step: the clock is `time`, whose slot is the tick slot.
    have hr := run_get_bind_eq_ok _ _ _ hr
    obtain ⟨p, t5, hpst, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨u, t6, hu, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    have e6 := run_set_state_eq _ _ _ _ hu
    rw [e6] at hr
    have e7 := run_pure_state_eq _ _ _ _ hr
    subst e7
    have htick : storeSlot { s with timeMs := time } = tickSlot.toNat := by
      unfold storeSlot
      show (time.toNat - s.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat = _
      rw [hgs, htkv]
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hnl)
    exact hstep time _ t5 hpst (by omega) (by omega)

end Tick

/-! ## The block -/

section Block
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]

omit [Config] [CryptoBackend] [FcMap map] in
/-- `update_unrealized_checkpoints` keeps the clock and the genesis time. -/
theorem updateUnrealizedCheckpoints_clock (s : Store map) (j f : Checkpoint) :
    (EthCLSpecs.Heze.updateUnrealizedCheckpoints s j f).timeMs = s.timeMs ∧
    (EthCLSpecs.Heze.updateUnrealizedCheckpoints s j f).genesisTimeMs = s.genesisTimeMs := by
  simp only [EthCLSpecs.Heze.updateUnrealizedCheckpoints]
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

omit [CryptoBackend] in
/-- `update_checkpoints` keeps the clock and the genesis time. -/
theorem updateCheckpoints_clock (s : Store map) (j f : Checkpoint) :
    (updateCheckpoints s j f).timeMs = s.timeMs ∧
    (updateCheckpoints s j f).genesisTimeMs = s.genesisTimeMs := by
  rw [updateCheckpoints_eq]
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- **The pull-up and the finalized checkpoint.** `computePulledUpTip` at a root whose stored
state is `w` writes the pull-up's finalized checkpoint onto the unrealized one by `ckptPick`. It
keeps the finalized checkpoint, or it writes the pull-up's onto it, and then the block at the
root is from an epoch before the clock's. It keeps the clock and the genesis time. -/
theorem computePulledUpTip_run_fin (root : Root) (w : BeaconState) (u post : Store map)
    (hl : FcMap.lookup u.blockStates root = some (pureState w))
    (h : (computePulledUpTip (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      root).run u = .ok ((), post)) :
    ∃ pulled : BeaconState,
      runPure (processJustificationAndFinalization (StateTransition := HezeRun)) w
        = .ok ((), pulled) ∧
      post.timeMs = u.timeMs ∧ post.genesisTimeMs = u.genesisTimeMs ∧
      post.unrealizedFinalizedCheckpoint =
        ckptPick u.unrealizedFinalizedCheckpoint pulled.finalizedCheckpoint ∧
      (post.finalizedCheckpoint = u.finalizedCheckpoint ∨
        (post.finalizedCheckpoint = ckptPick u.finalizedCheckpoint pulled.finalizedCheckpoint ∧
          ∃ b : BeaconBlock, FcMap.lookup u.blocks root = some b ∧
            b.slot.toNat / slotsPerEpoch < storeSlot u / slotsPerEpoch)) := by
  unfold computePulledUpTip at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨st, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hl', e0⟩ := getOrThrow_run_eq_ok _ _ _ _ _ hread
  rw [e0] at h
  rw [hl] at hl'
  injection hl' with hl'
  subst hl'
  obtain ⟨pulled, hjf, h⟩ := runNestedStateTransition_bind_eq_ok w _
    keepsUncached_processJustificationAndFinalization _ _ _ h
  refine ⟨pulled, runPure_of_run_ok hjf, ?_⟩
  obtain ⟨⟨⟩, t1, hs1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e1 := run_set_state_eq _ _ _ _ hs1
  subst e1
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨⟨⟩, t2, hs2, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2 := run_set_state_eq _ _ _ _ hs2
  subst e2
  -- The block read and the store epoch.
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨blk, t3, hb, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlb, rfl⟩ := getOrThrow_run_eq_ok _ _ _ _ _ hb
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨ce, t4, he, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e4 := getCurrentStoreEpoch_keeps _ _ _ _ _ rfl he
  subst e4
  let u1 : Store map := { u with unrealizedJustifications :=
    (FcMap.insert u.unrealizedJustifications root pulled.currentJustifiedCheckpoint) }
  obtain ⟨uj, uf, ujs, ufs, ub, ubs⟩ := updateUnrealizedCheckpoints_ckpt u1
    pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
  have htime := updateUnrealizedCheckpoints_clock u1 pulled.currentJustifiedCheckpoint
    pulled.finalizedCheckpoint
  -- The store epoch is the epoch of the clock of `u`.
  have hce : ce.toNat = storeSlot u / slotsPerEpoch := by
    unfold getCurrentStoreEpoch at he
    obtain ⟨cs, t5, hcs, he⟩ := run_bind_eq_ok _ _ _ _ he
    have hcv := run_pure_eq_ok _ _ _ _ he
    rw [hcv, computeEpochAtSlot_toNat, getCurrentSlot_storeSlot hcs]
    simp only [storeSlot, updateUnrealizedCheckpoints_clock]
  have hlb' : FcMap.lookup u.blocks root = some blk := by
    rw [show u.blocks = (EthCLSpecs.Heze.updateUnrealizedCheckpoints u1
      pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint).blocks from ub.symm]
    exact hlb
  rcases run_ite_eq_ok h with ⟨hcond, h⟩ | ⟨-, h⟩
  · -- A block from an earlier epoch: the realized pair takes the pair of `pulled` too.
    have h := run_get_bind_eq_ok _ _ _ h
    have e := run_set_state_eq _ _ _ _ h
    subst e
    obtain ⟨j', f', uj', uf', b', bs'⟩ := updateCheckpoints_ckpt
      (EthCLSpecs.Heze.updateUnrealizedCheckpoints u1 pulled.currentJustifiedCheckpoint
        pulled.finalizedCheckpoint)
      pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
    have ht' := updateCheckpoints_clock (EthCLSpecs.Heze.updateUnrealizedCheckpoints u1
      pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint)
      pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
    refine ⟨ht'.1.trans htime.1, ht'.2.trans htime.2, uf'.trans ufs,
      .inr ⟨f'.trans (by rw [uf]), blk, hlb', ?_⟩⟩
    have := UInt64.lt_iff_toNat_lt.mp hcond
    rw [computeEpochAtSlot_toNat, hce] at this
    exact this
  · have e := run_pure_state_eq _ _ _ _ h
    subst e
    exact ⟨htime.1, htime.2, ufs, .inl uf⟩

end Block

/-! ## The store -/

section StoreLag
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- **The lag of a store.** Its finalized epoch is at most `e₀` or at most the epoch of its clock
less two. Its unrealized finalized epoch is at most `e₀` or at most that epoch less one. -/
def StoreLag (e₀ : Nat) (s : Store map) : Prop :=
  (s.finalizedCheckpoint.epoch.toNat ≤ e₀ ∨
    s.finalizedCheckpoint.epoch.toNat + 2 ≤ storeSlot s / slotsPerEpoch) ∧
  (s.unrealizedFinalizedCheckpoint.epoch.toNat ≤ e₀ ∨
    s.unrealizedFinalizedCheckpoint.epoch.toNat + 1 ≤ storeSlot s / slotsPerEpoch)

end StoreLag

section Trace
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]
  [LawfulFcMap map Root]
  [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
    EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]

/-- **The lag along a trace.** A traced store meets `StoreLag` for the anchor epoch, when the
seed does, the store before each event meets `CkptInv`, and each tick moves the clock forward or
starts from checkpoints at or below the anchor epoch.

- A tick keeps the unrealized finalized checkpoint and the slot order. A realized one takes the
  unrealized checkpoint at a later epoch of the clock (`onTick_run_fin`).
- A new block writes the finalized checkpoint of its state, at most its epoch less two or the
  anchor's (`ChainRun.stateLag`), and its epoch is at most the clock's. Its pull-up writes a
  finalized epoch at most the block epoch less one (`pullup_fin_le`) onto the unrealized
  checkpoint, and onto the finalized one only for a block before the clock's epoch
  (`computePulledUpTip_run_fin`).
- The other events keep the checkpoints and the clock. -/
theorem NodeTrace.storeLag (hD0 : 0 < EthCLSpecs.Heze.Const.slotDurationMs.toNat)
    {A : BeaconState} {a : BeaconBlock} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × Bool)}
    (h : NodeTrace s0 events arrivals s) (hord : StateCkptOrd A)
    (hinv : ∀ es1 es2 arr1 mid, events = es1 ++ es2 → NodeTrace s0 es1 arr1 mid →
      CkptInv A a mid)
    (h0 : StoreLag (epochOf A) s0)
    (htick : ∀ es1 es2 arr1 mid time, events = es1 ++ .handler (.tick time) :: es2 →
      NodeTrace s0 es1 arr1 mid →
      storeSlot mid ≤
          (time.toNat - mid.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat ∨
        (mid.finalizedCheckpoint.epoch.toNat ≤ epochOf A ∧
          mid.unrealizedFinalizedCheckpoint.epoch.toNat ≤ epochOf A)) :
    StoreLag (epochOf A) s := by
  have hp := slotsPerEpochPos
  induction h with
  | nil => exact h0
  | @handler events arrs pre post e htrace hrun ih =>
    have ih := ih (fun es1 es2 arr1 mid hes h1 => hinv es1 (es2 ++ [.handler e]) arr1 mid
      (by rw [hes]; simp) h1)
      (fun es1 es2 arr1 mid time hes h1 => htick es1 (es2 ++ [.handler e]) arr1 mid time
        (by rw [hes]; simp) h1)
    obtain ⟨lf, luf⟩ := ih
    have hgen : post.genesisTimeMs = pre.genesisTimeMs :=
      HandlerEvent.run_keeps_genesisTime e _ _ hrun
    -- An event that keeps the checkpoints and the clock keeps the lag.
    have hkeep : storeCkpts post = storeCkpts pre → post.timeMs = pre.timeMs →
        StoreLag (epochOf A) post := fun hck ht => by
      simp only [storeCkpts, Prod.mk.injEq] at hck
      obtain ⟨-, c2, -, c4⟩ := hck
      have hs : storeSlot post = storeSlot pre := by unfold storeSlot; rw [ht, hgen]
      unfold StoreLag
      rw [c2, c4, hs]
      exact ⟨lf, luf⟩
    cases e with
    | tick time =>
      rcases htick events [] arrs pre time (by simp) htrace with hmono | ⟨hf0, huf0⟩
      · obtain ⟨huf, hsl, -, hf⟩ := onTick_run_fin hD0 time hmono hrun
        have hdiv : storeSlot pre / slotsPerEpoch ≤ storeSlot post / slotsPerEpoch :=
          Nat.div_le_div_right hsl
        refine ⟨?_, by rw [huf]; omega⟩
        rcases hf with e | ⟨e, hlt⟩
        · rw [e]; omega
        · rw [e]
          rcases ckptPick_cases pre.finalizedCheckpoint pre.unrealizedFinalizedCheckpoint
            with e' | e' <;> rw [e'] <;> omega
      · obtain ⟨-, -, uf, -, f, -⟩ := onTick_growsAt time pre () post hrun
        refine ⟨?_, .inl (by rw [uf]; exact huf0)⟩
        rcases f with e | e <;> rw [e]
        · exact .inl hf0
        · exact .inl huf0
    | attestation att isFromBlock =>
      exact hkeep (onAttestation_keeps_ckpts _ att isFromBlock pre () post rfl hrun)
        (onAttestation_keeps_time _ att isFromBlock pre () post rfl hrun)
    | attesterSlashing asl =>
      exact hkeep (onAttesterSlashing_keeps_ckpts _ asl pre () post rfl hrun)
        (onAttesterSlashing_keeps_time _ asl pre () post rfl hrun)
    | payloadAttestation msg isFromBlock =>
      exact hkeep (onPayloadAttestationMessage_keeps_ckpts _ msg isFromBlock pre () post rfl hrun)
        (onPayloadAttestationMessage_keeps_time _ msg isFromBlock pre () post rfl hrun)
    | envelope signedEnv =>
      exact hkeep (onExecutionPayloadEnvelope_keeps_ckpts _ signedEnv pre () post rfl hrun)
        (onExecutionPayloadEnvelope_keeps_time _ signedEnv pre () post rfl hrun)
    | block sb =>
      cases hknown : FcMap.contains pre.blocks (htr sb.message)
      case true =>
        rw [onBlock_run_of_known sb pre post hknown hrun]
        exact ⟨lf, luf⟩
      have hpre := hinv events [.handler (.block sb)] arrs pre rfl htrace
      have htime : post.timeMs = pre.timeMs := onBlock_keeps_time _ sb pre () post rfl hrun
      have hS : storeSlot post = storeSlot pre := by unfold storeSlot; rw [htime, hgen]
      obtain ⟨cs, sc, sc', hcs, hle⟩ := onBlock_run_ok_currentSlot sb pre post hknown hrun
      have hbS : sb.message.slot.toNat ≤ storeSlot pre := by
        rw [← getCurrentSlot_storeSlot hcs]
        exact UInt64.le_iff_toNat_le.mp hle
      obtain ⟨pv, w, u, hps, htrans, hbu, hbsu, hck, hpull, -⟩ :=
        onBlock_run_ckpt sb pre post hpre.slot.statesPure hknown hrun
      obtain ⟨-, f1, -, uf1, b1, bs1⟩ :=
        updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, LawfulFcMap.lookup_insert_self]
      obtain ⟨pulled, hjf, ptime, pgen, puf, hf⟩ :=
        computePulledUpTip_run_fin _ w _ post hl hpull
      -- The state after the block is on a run from `A`, at the block slot.
      obtain ⟨steps0, hrun0, -, -⟩ := hpre.chains _ pv hps
      obtain ⟨nk, hrunT⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1)
        (by have := sb.message.slot.toNat_lt; omega) pv w htrans
      have hrunW := hrun0.append hrunT
      obtain ⟨m, -, hm2⟩ := hrunT.split
      have hwslot : w.slot.toNat = sb.message.slot.toNat := by
        cases hm2 with
        | block _ _ hstep hrest =>
          cases hrest
          obtain ⟨h1, h2⟩ := hstep.slot
          omega
      have hordW := hrunW.stateCkptOrd (Nat.le_refl _) hord
      have hlagA : StateLag (epochOf A) A := by
        left
        obtain ⟨h1, h2, h3⟩ := hord
        rw [UInt64.le_iff_toNat_le] at h1 h2 h3
        rw [previousEpochOf_toNat_sub] at h3
        unfold epochOf
        exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_trans h3 (Nat.sub_le _ _))
      have hlagW := hrunW.stateLag (Nat.le_refl _) hord hlagA
      have hpf := pullup_fin_le w pulled hordW hjf
      simp only [storeCkpts, Prod.mk.injEq] at hck
      obtain ⟨-, cf, -, cuf⟩ := hck
      unfold StateLag at hlagW
      rw [hwslot] at hlagW hpf
      have hbc : sb.message.slot.toNat / slotsPerEpoch ≤ storeSlot pre / slotsPerEpoch :=
        Nat.div_le_div_right hbS
      -- The finalized checkpoint between the two writes.
      have mf : (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).finalizedCheckpoint.epoch.toNat ≤ epochOf A ∨
          (updateCheckpoints u w.currentJustifiedCheckpoint
            w.finalizedCheckpoint).finalizedCheckpoint.epoch.toNat + 2 ≤
            storeSlot pre / slotsPerEpoch := by
        rw [f1, cf]
        rcases ckptPick_cases pre.finalizedCheckpoint w.finalizedCheckpoint with e | e <;>
          rw [e] <;> omega
      unfold StoreLag
      rw [hS]
      refine ⟨?_, ?_⟩
      · rcases hf with e | ⟨e, b, hb, hlt⟩
        · rw [e]; exact mf
        · -- The pull-up reached the realized pair: the block is before the clock's epoch.
          have hb' : b = sb.message := by
            rw [b1, hbu, LawfulFcMap.lookup_insert_self] at hb
            exact (Option.some.inj hb).symm
          subst hb'
          have hst : storeSlot (updateCheckpoints u w.currentJustifiedCheckpoint
              w.finalizedCheckpoint) = storeSlot pre := by
            rw [← hS]
            unfold storeSlot
            rw [ptime, pgen]
          rw [hst] at hlt
          rw [e]
          rcases ckptPick_cases (updateCheckpoints u w.currentJustifiedCheckpoint
              w.finalizedCheckpoint).finalizedCheckpoint pulled.finalizedCheckpoint
            with e' | e' <;> rw [e']
          · exact mf
          · omega
      · rw [puf, uf1, cuf]
        rcases ckptPick_cases pre.unrealizedFinalizedCheckpoint pulled.finalizedCheckpoint
          with e | e <;> rw [e] <;> omega
  | @inclusionList events arrs pre post signed _ htrace hrun _ ih =>
    have ih := ih (fun es1 es2 arr1 mid hes h1 => hinv es1 (es2 ++ [.inclusionList signed]) arr1
      mid (by rw [hes]; simp) h1)
      (fun es1 es2 arr1 mid time hes h1 => htick es1 (es2 ++ [.inclusionList signed]) arr1 mid
        time (by rw [hes]; simp) h1)
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs']
    exact ih

/-- **The clock after a prefix of a clocked trace.** The slot of the store is at most the slot of
the wall time of an event of the prefix, or its two finalized epochs are at most `e₀`.

- An event other than a tick runs on a store whose clock is its wall time, and keeps the clock.
- A tick after a store of an earlier slot moves the clock to its own wall time at most
  (`onTick_run_fin`).
- Any other tick keeps the unrealized finalized checkpoint and writes the old finalized one or
  the unrealized one (`onTick_growsAt`). So both stay at most `e₀`. -/
theorem NodeTrace.clockLast (hD0 : 0 < EthCLSpecs.Heze.Const.slotDurationMs.toNat) {e₀ : Nat}
    {s0 s sT : Store map} {tevs : List (TraceEvent × Nat)}
    {arrT : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrT sT)
    (h0 : s0.finalizedCheckpoint.epoch.toNat ≤ e₀ ∧
      s0.unrealizedFinalizedCheckpoint.epoch.toNat ≤ e₀)
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × Bool)}
    (h : NodeTrace s0 events arrivals s) :
    ∀ (P rest : List (TraceEvent × Nat)), tevs = P ++ rest → P.map Prod.fst = events →
      (∃ z ∈ P, storeSlot s ≤
        (z.2 - s.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat) ∨
      (s.finalizedCheckpoint.epoch.toNat ≤ e₀ ∧
        s.unrealizedFinalizedCheckpoint.epoch.toNat ≤ e₀) := by
  -- Split `P` at its last event `y`, the event of the last step of the trace.
  have hlast : ∀ (P : List (TraceEvent × Nat)) (events : List TraceEvent) (ev : TraceEvent),
      P.map Prod.fst = events ++ [ev] →
      ∃ P' y, P = P' ++ [y] ∧ P'.map Prod.fst = events ∧ y.1 = ev := by
    intro P events ev hP
    obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.mp hP
    obtain ⟨y, l3, rfl, hy, h3⟩ := List.map_eq_cons_iff.mp h2
    rw [List.map_eq_nil_iff] at h3
    subst h3
    exact ⟨l1, y, rfl, h1, hy⟩
  induction h with
  | nil => exact fun _ _ _ _ => .inr h0
  | @handler events arrs pre post e htrace hrun ih =>
    intro P rest htev hP
    obtain ⟨P', y, rfl, hP', hy⟩ := hlast P events (.handler e) hP
    have htev' : tevs = P' ++ y :: rest := by rw [htev]; simp
    have ih := ih P' (y :: rest) htev' hP'
    have hc := hct.clock P' y rest htev' arrs pre (hP' ▸ htrace)
    rw [hy] at hc
    have hmem : y ∈ P' ++ [y] := List.mem_append_right _ List.mem_cons_self
    have hgen : post.genesisTimeMs = pre.genesisTimeMs :=
      HandlerEvent.run_keeps_genesisTime e _ _ hrun
    -- An event that keeps the clock leaves the store at the slot of its wall time.
    have hkeep : post.timeMs = pre.timeMs → pre.timeMs.toNat = y.2 →
        (∃ z ∈ P' ++ [y], storeSlot post ≤
          (z.2 - post.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat) ∨
        (post.finalizedCheckpoint.epoch.toNat ≤ e₀ ∧
          post.unrealizedFinalizedCheckpoint.epoch.toNat ≤ e₀) := fun ht hw =>
      .inl ⟨y, hmem, Nat.le_of_eq (by unfold storeSlot; rw [ht, hw])⟩
    cases e with
    | tick time =>
      have hc : time.toNat = y.2 := hc
      rcases ih with ⟨z, hz, hle⟩ | ⟨hf0, huf0⟩
      · have hmono := hct.mono
        rw [htev', List.pairwise_append] at hmono
        have hzy : z.2 ≤ y.2 := hmono.2.2 z hz y List.mem_cons_self
        have hpre : storeSlot pre ≤
            (time.toNat - pre.genesisTimeMs.toNat) /
              EthCLSpecs.Heze.Const.slotDurationMs.toNat := by
          rw [hc]
          exact Nat.le_trans hle (Nat.div_le_div_right (Nat.sub_le_sub_right hzy _))
        obtain ⟨-, -, hhi, -⟩ := onTick_run_fin hD0 time hpre hrun
        refine .inl ⟨y, hmem, ?_⟩
        rw [hgen, ← hc]
        exact hhi
      · obtain ⟨-, -, uf, -, f, -⟩ := onTick_growsAt time pre () post hrun
        refine .inr ⟨?_, by rw [uf]; exact huf0⟩
        rcases f with e | e <;> rw [e]
        · exact hf0
        · exact huf0
    | attestation att isFromBlock =>
      exact hkeep (onAttestation_keeps_time _ att isFromBlock pre () post rfl hrun) hc
    | attesterSlashing asl =>
      exact hkeep (onAttesterSlashing_keeps_time _ asl pre () post rfl hrun) hc
    | payloadAttestation msg isFromBlock =>
      exact hkeep (onPayloadAttestationMessage_keeps_time _ msg isFromBlock pre () post rfl hrun) hc
    | envelope signedEnv =>
      exact hkeep (onExecutionPayloadEnvelope_keeps_time _ signedEnv pre () post rfl hrun) hc
    | block sb =>
      exact hkeep (onBlock_keeps_time _ sb pre () post rfl hrun) hc
  | @inclusionList events arrs pre post signed _ htrace hrun _ ih =>
    intro P rest htev hP
    obtain ⟨P', y, rfl, hP', hy⟩ := hlast P events (.inclusionList signed) hP
    have htev' : tevs = P' ++ y :: rest := by rw [htev]; simp
    have hc := hct.clock P' y rest htev' arrs pre (hP' ▸ htrace)
    rw [hy] at hc
    have hc : pre.timeMs.toNat = y.2 := hc
    -- `onInclusionList` writes only the IL store.
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs']
    exact .inl ⟨y, List.mem_append_right _ List.mem_cons_self,
      Nat.le_of_eq (by unfold storeSlot; rw [hc])⟩

/-- **A tick of a clocked trace moves the clock forward, or starts low.** The store before a tick
is at the slot of an earlier wall time at most, and the wall times do not decrease. Before the
first event, the seed's two finalized epochs are at most `e₀`. -/
theorem ClockedTrace.tickLag (hD0 : 0 < EthCLSpecs.Heze.Const.slotDurationMs.toNat) {e₀ : Nat}
    {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrivals s)
    (h0 : s0.finalizedCheckpoint.epoch.toNat ≤ e₀ ∧
      s0.unrealizedFinalizedCheckpoint.epoch.toNat ≤ e₀) :
    ∀ es1 es2 arr1 (mid : Store map) (time : UInt64),
      tevs.map Prod.fst = es1 ++ .handler (.tick time) :: es2 →
      NodeTrace s0 es1 arr1 mid →
      storeSlot mid ≤
          (time.toNat - mid.genesisTimeMs.toNat) / EthCLSpecs.Heze.Const.slotDurationMs.toNat ∨
        (mid.finalizedCheckpoint.epoch.toNat ≤ e₀ ∧
          mid.unrealizedFinalizedCheckpoint.epoch.toNat ≤ e₀) := by
  intro es1 es2 arr1 mid time hes h1
  obtain ⟨P, L, htev, hP, hL⟩ := List.map_eq_append_iff.mp hes
  obtain ⟨x, rest, rfl, hx, -⟩ := List.map_eq_cons_iff.mp hL
  have hc := hct.clock P x rest htev arr1 mid (hP ▸ h1)
  rw [hx] at hc
  have hc : time.toNat = x.2 := hc
  rcases h1.clockLast hD0 hct h0 P (x :: rest) htev hP with ⟨z, hz, hle⟩ | hlow
  · have hmono := hct.mono
    rw [htev, List.pairwise_append] at hmono
    have hzx : z.2 ≤ x.2 := hmono.2.2 z hz x List.mem_cons_self
    refine .inl ?_
    rw [hc]
    exact Nat.le_trans hle (Nat.div_le_div_right (Nat.sub_le_sub_right hzx _))
  · exact .inr hlow

/-- **The lag along a clocked trace.** The store meets `StoreLag` for the anchor epoch, when the
seed's two finalized epochs are at most the anchor epoch and the store before each event meets
`CkptInv`. -/
theorem ClockedTrace.storeLag (hD0 : 0 < EthCLSpecs.Heze.Const.slotDurationMs.toNat)
    {A : BeaconState} {a : BeaconBlock} {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrivals s)
    (hord : StateCkptOrd A)
    (hinv : ∀ es1 es2 arr1 mid, tevs.map Prod.fst = es1 ++ es2 → NodeTrace s0 es1 arr1 mid →
      CkptInv A a mid)
    (h0 : s0.finalizedCheckpoint.epoch.toNat ≤ epochOf A ∧
      s0.unrealizedFinalizedCheckpoint.epoch.toNat ≤ epochOf A) :
    StoreLag (epochOf A) s :=
  hct.trace.storeLag hD0 hord hinv ⟨.inl h0.1, .inl h0.2⟩ (hct.tickLag hD0 h0)

end Trace

end EthCLSpecs.Proofs.Heze
