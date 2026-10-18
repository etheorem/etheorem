import EthCLSpecs.Proofs.Heze.CheckpointFrame
import EthCLSpecs.Proofs.Heze.StorePure

/-!
# `EthCLSpecs.Proofs.Heze.CheckpointInvariants`: the checkpoint order and the store growth

## The state order

A beacon state holds three checkpoints: the finalized one, the previous justified one, and
the current justified one. Between two chain steps their epochs are in order, and the
current justified epoch is at most the previous epoch of the state (`StateCkptOrd`).
`ChainRun.stateCkptOrd` proves that a chain run keeps the order.

Only `process_justification_and_finalization` writes the checkpoints
(`CheckpointFrame.lean`). It runs at the end of an epoch, before the slot increment. The old
current justified checkpoint becomes the previous one. A new current justified checkpoint
has the current or the previous epoch. A new finalized checkpoint is one of the two old
justified checkpoints. So the order holds after the increment, when the current epoch
becomes the previous epoch. The run bound `hi` must be below `2 ^ 64`: at the last slot,
the increment wraps to slot zero and the order fails.

## The store growth

The fork-choice store holds four checkpoints: the justified, the finalized, and the two
unrealized ones. `CkptGrows pre post` states that no epoch of the four goes down.
`HandlerEvent.run_ckptGrows` proves it for one handler event, and `NodeTrace.ckptGrows` for
a trace. Two handlers write the checkpoints. Each write calls `update_checkpoints` or
`update_unrealized_checkpoints`, and these write a candidate only when its epoch is greater
(`ckptPick`).

- `onTick` copies the unrealized pair into the realized pair at the start of an epoch
  (`onTickPerSlot_run_ckpt`). The loop of `onTick` keeps the relation `TickRel` by the
  rules of `GrowsAt`.
- `onBlock` writes the checkpoints of the post-state, then `computePulledUpTip` writes the
  checkpoints of `process_justification_and_finalization` on that state
  (`onBlock_run_ckpt`, `computePulledUpTip_run_ok`).

The other handlers keep the four checkpoints.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt KeepsUncached LawfulFcMap pureState runPure
  runPure_of_run_ok run_bind_eq_ok run_bind_eq_ok_pure run_get_bind_eq_ok run_ite_eq_ok
  run_pure_eq_ok run_pure_state_eq run_set_state_eq)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Checkpoint BeaconBlock
  SignedBeaconBlock SignedInclusionList previousEpochOf currentEpochOf
  processJustificationAndFinalization updateCheckpoints updateUnrealizedCheckpoints
  computePulledUpTip onTick onTickPerSlot onBlock getCurrentSlot getCurrentStoreEpoch
  recordBlockTimeliness updateProposerBoostRoot notifyPtcMessages)
open EthCLSpecs.Heze.Const (slotsPerEpoch justificationBitsLength)

/-! ## The state order -/

section
variable [Preset] [HasherTag]

/-- The order of the checkpoints of a state between two chain steps. The finalized epoch is
at most the previous justified epoch. That is at most the current justified epoch, and that
is at most the previous epoch. -/
def StateCkptOrd (v : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
  v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
  v.currentJustifiedCheckpoint.epoch ≤ previousEpochOf (pureState v)

/-- The previous epoch as a `Nat`: the current epoch less one, and zero in the first epoch. -/
theorem previousEpochOf_toNat_sub (v : BeaconState) :
    (previousEpochOf (pureState v)).toNat = v.slot.toNat / slotsPerEpoch - 1 := by
  by_cases h : 0 < v.slot.toNat / slotsPerEpoch
  · exact previousEpochOf_toNat v h
  · have hc : (currentEpochOf (pureState v)).toNat = 0 := by
      rw [currentEpochOf_toNat]
      exact Nat.eq_zero_of_not_pos h
    have he : currentEpochOf (pureState v) = EthCLSpecs.Heze.Const.genesisEpoch :=
      UInt64.toNat_inj.mp hc
    unfold previousEpochOf
    simp only [he, beq_self_eq_true, ↓reduceIte]
    simp [EthCLSpecs.Heze.Const.genesisEpoch]
    omega

omit [HasherTag] in
/-- A bound on all three input checkpoints bounds the checkpoint that `finalizeRules`
returns. -/
theorem finalizeRules_epoch_le (bits : Bitvector justificationBitsLength)
    (op oc of : Checkpoint) (ce : UInt64) (n : Nat) (hp : op.epoch.toNat ≤ n)
    (hc : oc.epoch.toNat ≤ n) (hf : of.epoch.toNat ≤ n) :
    (finalizeRules bits op oc of ce).epoch.toNat ≤ n := by
  rcases finalizeRules_cases bits op oc of ce with e | ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;>
    assumption

/-- A state with the four fields of `ckView` of `v`, and a previous epoch no less than that
of `v`, keeps the state order of `v`. -/
theorem StateCkptOrd.of_ckView {v w : BeaconState} (hv : StateCkptOrd v)
    (hck : ckView (pureState w) = ckView (pureState v))
    (hprev : (previousEpochOf (pureState v)).toNat ≤ (previousEpochOf (pureState w)).toNat) :
    StateCkptOrd w := by
  simp only [ckView, Prod.mk.injEq] at hck
  obtain ⟨hp, hc, hf, -⟩ := hck
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · change w.finalizedCheckpoint.epoch ≤ w.previousJustifiedCheckpoint.epoch
    change w.previousJustifiedCheckpoint = v.previousJustifiedCheckpoint at hp
    change w.finalizedCheckpoint = v.finalizedCheckpoint at hf
    rw [hp, hf]
    exact h1
  · change w.previousJustifiedCheckpoint = v.previousJustifiedCheckpoint at hp
    change w.currentJustifiedCheckpoint = v.currentJustifiedCheckpoint at hc
    rw [hp, hc]
    exact h2
  · change w.currentJustifiedCheckpoint = v.currentJustifiedCheckpoint at hc
    rw [hc]
    rw [UInt64.le_iff_toNat_le] at h3 ⊢
    omega

variable [Config] [CryptoBackend]

/-- `processJustificationAndFinalization` on an ordered state. The finalized epoch is at most
the previous justified epoch, which is at most the current justified epoch. The current
justified epoch is at most the current epoch. The step keeps the slot.

The new previous justified checkpoint is the old current one. The new current one has the
current epoch or the previous epoch, or it stays. The new finalized one is one of the two
old justified ones, or it stays. -/
theorem processJustificationAndFinalization_run_ord (v w : BeaconState) (hv : StateCkptOrd v)
    (h : runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v
      = .ok ((), w)) :
    w.finalizedCheckpoint.epoch ≤ w.previousJustifiedCheckpoint.epoch ∧
    w.previousJustifiedCheckpoint.epoch ≤ w.currentJustifiedCheckpoint.epoch ∧
    w.currentJustifiedCheckpoint.epoch.toNat ≤ v.slot.toNat / slotsPerEpoch ∧
    w.slot = v.slot := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hP := previousEpochOf_toNat_sub v
  have hE := currentEpochOf_toNat v
  change (currentEpochOf (pureState v)).toNat = v.slot.toNat / slotsPerEpoch at hE
  rw [UInt64.le_iff_toNat_le] at h1 h2 h3
  by_cases hg : currentEpochOf (pureState v) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1
  · -- The first two epochs: the step keeps the state.
    rw [processJustificationAndFinalization_run_eq, if_pos hg] at h
    cases h
    refine ⟨UInt64.le_iff_toNat_le.mpr h1, UInt64.le_iff_toNat_le.mpr h2, by omega, rfl⟩
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, h⟩ := processJustificationAndFinalization_run_ok h hg
    have hk := congrArg (·.slot) (weighJustificationAndFinalization_run_keeps v w _ _ _ h)
    obtain ⟨pr, cr, hw⟩ := weighJustificationAndFinalization_run_ok v w _ _ _ h
    dsimp only at hw hk
    obtain ⟨hp, hc, -, hf, -, -⟩ := hw
    -- The new current justified epoch: the current epoch, the previous epoch, or the old one.
    have hcj : v.currentJustifiedCheckpoint.epoch.toNat ≤
          w.currentJustifiedCheckpoint.epoch.toNat ∧
        w.currentJustifiedCheckpoint.epoch.toNat ≤ v.slot.toNat / slotsPerEpoch := by
      rw [hc]
      split
      · dsimp only
        exact ⟨by omega, by omega⟩
      · split
        · dsimp only
          exact ⟨by omega, by omega⟩
        · exact ⟨Nat.le_refl _, by omega⟩
    refine ⟨?_, ?_, hcj.2, hk⟩ <;> rw [UInt64.le_iff_toNat_le, hp]
    · rw [hf]
      exact finalizeRules_epoch_le _ _ _ _ _ _ h2 (Nat.le_refl _) (Nat.le_trans h1 h2)
    · exact hcj.1

/-- `processJustificationAndFinalization` on an ordered state writes a finalized epoch at
most its current justified epoch. -/
theorem processJustificationAndFinalization_run_fin_le (v w : BeaconState)
    (hv : StateCkptOrd v)
    (h : runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v
      = .ok ((), w)) :
    w.finalizedCheckpoint.epoch ≤ w.currentJustifiedCheckpoint.epoch := by
  obtain ⟨h1, h2, -, -⟩ := processJustificationAndFinalization_run_ord v w hv h
  exact UInt64.le_trans h1 h2

/-- A slot step keeps the state order, when the slot increment does not wrap. At the end of
an epoch, `processJustificationAndFinalization` writes a current justified epoch at most the
current epoch. The increment makes that epoch the previous epoch. -/
theorem SlotStep.stateCkptOrd {st st' : BeaconState} (h : SlotStep st st')
    (hlt : st.slot.toNat + 1 < 2 ^ 64) (hv : StateCkptOrd st) : StateCkptOrd st' := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 : ordView (pureState st1) = ordView (pureState st) := processSlot_frame_ord h1
  simp only [ordView, Prod.mk.injEq] at e1
  obtain ⟨ck1, sl1⟩ := e1
  change st1.slot = st.slot at sl1
  -- The step ends with the increment: the four fields of `st2` and the slot plus one.
  have hck' : ckView (pureState st') = ckView (pureState st2) := by
    rw [hst']
    rfl
  have hsl' : st'.slot = st2.slot + 1 := by
    change sszGet (pureState st') slot = _
    rw [hst']
    rfl
  have hv1 : StateCkptOrd st1 := hv.of_ckView ck1 (Nat.le_of_eq (by
    rw [previousEpochOf_toNat_sub, previousEpochOf_toNat_sub, sl1]))
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
    obtain ⟨o1, o2, o3, o4⟩ :=
      processJustificationAndFinalization_run_ord st1 mid hv1 (runPure_of_run_ok hjf)
    have hsln : st'.slot.toNat = st.slot.toNat + 1 := by
      rw [hsl', sl2, o4, sl1, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    rw [sl1] at o3
    simp only [ckView, Prod.mk.injEq] at hck' ck2
    obtain ⟨hp', hc', hf', -⟩ := hck'
    obtain ⟨hp2, hc2, hf2, -⟩ := ck2
    change st'.previousJustifiedCheckpoint = st2.previousJustifiedCheckpoint at hp'
    change st'.currentJustifiedCheckpoint = st2.currentJustifiedCheckpoint at hc'
    change st'.finalizedCheckpoint = st2.finalizedCheckpoint at hf'
    change st2.previousJustifiedCheckpoint = mid.previousJustifiedCheckpoint at hp2
    change st2.currentJustifiedCheckpoint = mid.currentJustifiedCheckpoint at hc2
    change st2.finalizedCheckpoint = mid.finalizedCheckpoint at hf2
    refine ⟨?_, ?_, ?_⟩
    · rw [hf', hp', hf2, hp2]; exact o1
    · rw [hp', hc', hp2, hc2]; exact o2
    · rw [UInt64.le_iff_toNat_le, previousEpochOf_toNat_sub, hsln, succ_div_of_mod_eq hb,
        hc', hc2]
      omega
  · subst h2
    refine hv1.of_ckView hck' ?_
    rw [previousEpochOf_toNat_sub, previousEpochOf_toNat_sub, hsl', sl1, UInt64.toNat_add,
      UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.le_succ _)) 1

/-- A block step keeps the state order: `processBlock` keeps the four fields and the slot. -/
theorem BlockStep.stateCkptOrd {sb : SignedBeaconBlock} {vr : Bool} {st st' : BeaconState}
    (h : BlockStep sb vr st st') (hv : StateCkptOrd st) : StateCkptOrd st' := by
  have e := processBlock_frame_ord h.2.1
  simp only [ordView, Prod.mk.injEq] at e
  obtain ⟨ck, sl⟩ := e
  change st'.slot = st.slot at sl
  exact hv.of_ckView ck
    (Nat.le_of_eq (by rw [previousEpochOf_toNat_sub, previousEpochOf_toNat_sub, sl]))

/-- A chain run keeps the state order. Each slot step starts below slot `hi`, and `hi` is
below `2 ^ 64`, so no slot increment wraps. -/
theorem ChainRun.stateCkptOrd {hi : Nat} {steps : List ChainStep} {v w : BeaconState}
    (h : ChainRun hi steps v w) (hhi : hi ≤ 2 ^ 64 - 1) (hv : StateCkptOrd v) :
    StateCkptOrd w := by
  induction h with
  | nil => exact hv
  | @slot _ st _ _ hlt hstep _ ih =>
    exact ih (hstep.stateCkptOrd (by change st.slot.toNat < hi at hlt; omega) hv)
  | block sb vr hstep _ ih => exact ih (hstep.stateCkptOrd hv)

end

/-! ## Relations kept by a run -/

section Grows
variable {σ ε : Type}

/-- `GrowsAt R x`: every successful run of `x` relates its start state to its end state by
`R`. `KeepsAt` is the case of a relation that compares one view. -/
def GrowsAt {α : Type} (R : σ → σ → Prop) (x : StateT σ (Except ε) α) : Prop :=
  ∀ (s : σ) (a : α) (s' : σ), x.run s = .ok (a, s') → R s s'

variable {R : σ → σ → Prop}

/-- `pure` relates a state to itself. -/
theorem GrowsAt.pure {α : Type} (hR : ∀ s, R s s) (a : α) :
    GrowsAt R (Pure.pure a : StateT σ (Except ε) α) := by
  intro s b s' h
  rw [run_pure_state_eq a b s s' h]
  exact hR s

/-- A run that keeps the whole state relates a state to itself. -/
theorem GrowsAt.of_keeps {α : Type} (hR : ∀ s, R s s) {x : StateT σ (Except ε) α}
    (hx : ∀ v, KeepsAt (fun s : σ => s) v x) : GrowsAt R x := by
  intro s a s' h
  have e : s' = s := hx s s a s' rfl h
  subst e
  exact hR s'

/-- A bind relates the start to the end when `R` is transitive. -/
theorem GrowsAt.bind {α β : Type} (htrans : ∀ a b c, R a b → R b c → R a c)
    {x : StateT σ (Except ε) α} {k : α → StateT σ (Except ε) β} (hx : GrowsAt R x)
    (hk : ∀ a, GrowsAt R (k a)) : GrowsAt R (x >>= k) := by
  intro s c s' h
  obtain ⟨a, s1, h1, h2⟩ := run_bind_eq_ok x k s (c, s') h
  exact htrans _ _ _ (hx s a s1 h1) (hk a s1 c s' h2)

/-- A `get` passes the start state to the rest. -/
theorem GrowsAt.get_bind {β : Type} {k : σ → StateT σ (Except ε) β}
    (hk : ∀ s0, GrowsAt R (k s0)) :
    GrowsAt R ((MonadStateOf.get : StateT σ (Except ε) σ) >>= k) := by
  intro s c s' h
  exact hk s s c s' (run_get_bind_eq_ok k s (c, s') h)

/-- `get`, then an action `x` on the state it read, then a `set` of the store that `x`
returns. The relation holds when `x s0` returns a store related to `s0`. -/
theorem GrowsAt.get_ret_set {β : Type} (htrans : ∀ a b c, R a b → R b c → R a c)
    {x : σ → StateT σ (Except ε) σ} {k : PUnit → StateT σ (Except ε) β}
    (hx : ∀ s0 p s s', (x s0).run s = .ok (p, s') → R s0 p) (hk : GrowsAt R (k PUnit.unit)) :
    GrowsAt R ((MonadStateOf.get : StateT σ (Except ε) σ) >>= fun s0 =>
      x s0 >>= fun p => (MonadStateOf.set p : StateT σ (Except ε) PUnit) >>= k) := by
  intro s c s' h
  have h := run_get_bind_eq_ok _ s (c, s') h
  obtain ⟨p, s1, h1, h⟩ := run_bind_eq_ok _ _ s (c, s') h
  obtain ⟨u, s2, h2, h⟩ := run_bind_eq_ok _ _ s1 (c, s') h
  have e := run_set_state_eq p s1 u s2 h2
  rw [e] at h
  exact htrans _ _ _ (hx s p s s1 h1) (hk p c s' h)

/-- An `if` relates the start to the end when both branches do. -/
theorem GrowsAt.ite {α : Type} {c : Prop} [Decidable c] {x y : StateT σ (Except ε) α}
    (hx : GrowsAt R x) (hy : GrowsAt R y) : GrowsAt R (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-- `fuelIterateM!` relates the start to the end when each step does. -/
theorem GrowsAt.fuelIterateM! {α : Type} [EthCLLib.Spec.SpecReject ε]
    (hR : ∀ s, R s s) (htrans : ∀ a b c, R a b → R b c → R a c)
    (what : String) (step : α → StateT σ (Except ε) (EthCLLib.Spec.Step α α))
    (hstep : ∀ b, GrowsAt R (step b)) :
    ∀ (fuel : Nat) (init : α), GrowsAt R (EthCLLib.Spec.fuelIterateM! fuel init what step) := by
  intro fuel
  induction fuel with
  | zero =>
    intro init s a s' hrun
    cases hrun
  | succ fuel ih =>
    intro init
    simp only [EthCLLib.Spec.fuelIterateM!]
    refine GrowsAt.bind htrans (hstep init) fun st => ?_
    cases st with
    | done a => exact GrowsAt.pure hR a
    | next b => exact ih b

end Grows

/-! ## The store checkpoints -/

section Store
variable [Preset] [HasherTag] {map : MapKind}

/-- The four checkpoint epochs of `post` are at least those of `pre`. -/
def CkptGrows (pre post : Store map) : Prop :=
  pre.justifiedCheckpoint.epoch ≤ post.justifiedCheckpoint.epoch ∧
  pre.finalizedCheckpoint.epoch ≤ post.finalizedCheckpoint.epoch ∧
  pre.unrealizedJustifiedCheckpoint.epoch ≤ post.unrealizedJustifiedCheckpoint.epoch ∧
  pre.unrealizedFinalizedCheckpoint.epoch ≤ post.unrealizedFinalizedCheckpoint.epoch

/-- `CkptGrows` relates a store to itself. -/
theorem CkptGrows.refl (s : Store map) : CkptGrows s s :=
  ⟨UInt64.le_refl _, UInt64.le_refl _, UInt64.le_refl _, UInt64.le_refl _⟩

/-- `CkptGrows` is transitive: `UInt64.le_trans` on each part. -/
theorem CkptGrows.trans {a b c : Store map} (h1 : CkptGrows a b) (h2 : CkptGrows b c) :
    CkptGrows a c :=
  ⟨UInt64.le_trans h1.1 h2.1, UInt64.le_trans h1.2.1 h2.2.1, UInt64.le_trans h1.2.2.1 h2.2.2.1,
    UInt64.le_trans h1.2.2.2 h2.2.2.2⟩

/-- The four checkpoints of a store. -/
def storeCkpts (s : Store map) : Checkpoint × Checkpoint × Checkpoint × Checkpoint :=
  (s.justifiedCheckpoint, s.finalizedCheckpoint, s.unrealizedJustifiedCheckpoint,
    s.unrealizedFinalizedCheckpoint)

/-- Two stores with the same four checkpoints are related by `CkptGrows`. -/
theorem CkptGrows.of_eq {a b : Store map} (h : storeCkpts b = storeCkpts a) :
    CkptGrows a b := by
  simp only [storeCkpts, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [CkptGrows, h1, h2, h3, h4]
  exact CkptGrows.refl a

/-- The checkpoint that `update_checkpoints` writes for one candidate: the candidate when its
epoch is greater, else the old checkpoint. -/
def ckptPick (old c : Checkpoint) : Checkpoint :=
  if c.epoch > old.epoch then c else old

omit [HasherTag] in
/-- `ckptPick` is no lower than the old checkpoint. -/
theorem ckptPick_ge_old (old c : Checkpoint) : old.epoch ≤ (ckptPick old c).epoch := by
  unfold ckptPick
  split
  · exact UInt64.le_of_lt ‹_›
  · exact UInt64.le_refl _

omit [HasherTag] in
/-- `ckptPick` is no lower than the candidate. -/
theorem ckptPick_ge_new (old c : Checkpoint) : c.epoch ≤ (ckptPick old c).epoch := by
  unfold ckptPick
  split
  · exact UInt64.le_refl _
  · exact UInt64.not_lt.mp ‹_›

omit [HasherTag] in
/-- `ckptPick` is the old checkpoint or the candidate. -/
theorem ckptPick_cases (old c : Checkpoint) : ckptPick old c = old ∨ ckptPick old c = c := by
  unfold ckptPick
  split
  · exact .inr rfl
  · exact .inl rfl

omit [HasherTag] in
/-- A write of an ordered pair onto an ordered pair gives an ordered pair. -/
theorem ckptPick_ord {j f j' f' : Checkpoint} (h : f.epoch ≤ j.epoch)
    (h' : f'.epoch ≤ j'.epoch) : (ckptPick f f').epoch ≤ (ckptPick j j').epoch := by
  rcases ckptPick_cases f f' with e | e <;> rw [e]
  · exact UInt64.le_trans h (ckptPick_ge_old j j')
  · exact UInt64.le_trans h' (ckptPick_ge_new j j')

variable [FcMap map] [Config]

/-- `updateCheckpoints` is a record update of the two realized checkpoints, each with
`ckptPick`. The two writes are separate, so the new justified checkpoint need not descend
from the new finalized one. `ckptPick_ord` keeps the order of their epochs. -/
@[characterizes EthCLSpecs.Heze.updateCheckpoints]
theorem updateCheckpoints_eq_pick (s : Store map) (j f : Checkpoint) :
    updateCheckpoints s j f = { s with
      justifiedCheckpoint := ckptPick s.justifiedCheckpoint j
      finalizedCheckpoint := ckptPick s.finalizedCheckpoint f } :=
  updateCheckpoints_eq s j f

/-- `updateCheckpoints` writes `ckptPick` into the two realized checkpoints. -/
theorem updateCheckpoints_ckpt (s : Store map) (j f : Checkpoint) :
    (updateCheckpoints s j f).justifiedCheckpoint = ckptPick s.justifiedCheckpoint j ∧
    (updateCheckpoints s j f).finalizedCheckpoint = ckptPick s.finalizedCheckpoint f ∧
    (updateCheckpoints s j f).unrealizedJustifiedCheckpoint = s.unrealizedJustifiedCheckpoint ∧
    (updateCheckpoints s j f).unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint ∧
    (updateCheckpoints s j f).blocks = s.blocks ∧
    (updateCheckpoints s j f).blockStates = s.blockStates := by
  rw [updateCheckpoints_eq_pick]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `updateUnrealizedCheckpoints` writes `ckptPick` into the two unrealized checkpoints. -/
theorem updateUnrealizedCheckpoints_ckpt (s : Store map) (j f : Checkpoint) :
    (updateUnrealizedCheckpoints s j f).justifiedCheckpoint = s.justifiedCheckpoint ∧
    (updateUnrealizedCheckpoints s j f).finalizedCheckpoint = s.finalizedCheckpoint ∧
    (updateUnrealizedCheckpoints s j f).unrealizedJustifiedCheckpoint =
      ckptPick s.unrealizedJustifiedCheckpoint j ∧
    (updateUnrealizedCheckpoints s j f).unrealizedFinalizedCheckpoint =
      ckptPick s.unrealizedFinalizedCheckpoint f ∧
    (updateUnrealizedCheckpoints s j f).blocks = s.blocks ∧
    (updateUnrealizedCheckpoints s j f).blockStates = s.blockStates := by
  rw [updateUnrealizedCheckpoints_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Store

/-! ## `onTick` -/

section Tick
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- A per-slot tick keeps the unrealized pair. It keeps the realized pair, or it writes the
unrealized pair onto it with `update_checkpoints`. -/
theorem onTickPerSlot_run_ckpt (store post st st' : Store map) (time : UInt64)
    (h : (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store time).run st
      = .ok (post, st')) :
    post.unrealizedJustifiedCheckpoint = store.unrealizedJustifiedCheckpoint ∧
    post.unrealizedFinalizedCheckpoint = store.unrealizedFinalizedCheckpoint ∧
    ((post.justifiedCheckpoint = store.justifiedCheckpoint ∧
        post.finalizedCheckpoint = store.finalizedCheckpoint) ∨
      (post.justifiedCheckpoint =
          ckptPick store.justifiedCheckpoint store.unrealizedJustifiedCheckpoint ∧
        post.finalizedCheckpoint =
          ckptPick store.finalizedCheckpoint store.unrealizedFinalizedCheckpoint)) := by
  simp only [onTickPerSlot, EthCLLib.Proofs.run_bind] at h
  cases h1 : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run st
    with
  | error e => rw [h1] at h; exact nomatch h
  | ok p =>
    rw [h1, EthCLLib.Proofs.except_bind_ok] at h
    cases h2 : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
        { store with time := time }).run p.2 with
    | error e => rw [h2] at h; exact nomatch h
    | ok q =>
      rw [h2, EthCLLib.Proofs.except_bind_ok] at h
      -- The slots since the epoch start, through the checked start slot.
      cases h3 : (onTickPerSlot.computeSlotsSinceEpochStart
          (StoreTransition := ForkChoiceStoreRun (Store map)) q.1).run q.2 with
      | error e => rw [h3] at h; exact nomatch h
      | ok k =>
      rw [h3, EthCLLib.Proofs.except_bind_ok, EthCLLib.Proofs.run_pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      -- The outer `if` decides the write, and the inner `if` writes the boost root only.
      (repeat' split) <;> (try rw [updateCheckpoints_eq]) <;>
        first
          | exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
          | exact ⟨rfl, rfl, .inr ⟨rfl, rfl⟩⟩

/-- The relation of a store to the store after an `onTick` run. The tick keeps the
unrealized pair and raises no epoch. Each realized checkpoint stays or takes the unrealized
one of its kind. The finalized epoch stays at most the justified epoch, when both pairs are
ordered at the start. -/
def TickRel (s s' : Store map) : Prop :=
  CkptGrows s s' ∧
  s'.unrealizedJustifiedCheckpoint = s.unrealizedJustifiedCheckpoint ∧
  s'.unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint ∧
  (s'.justifiedCheckpoint = s.justifiedCheckpoint ∨
    s'.justifiedCheckpoint = s.unrealizedJustifiedCheckpoint) ∧
  (s'.finalizedCheckpoint = s.finalizedCheckpoint ∨
    s'.finalizedCheckpoint = s.unrealizedFinalizedCheckpoint) ∧
  (s.finalizedCheckpoint.epoch ≤ s.justifiedCheckpoint.epoch →
    s.unrealizedFinalizedCheckpoint.epoch ≤ s.unrealizedJustifiedCheckpoint.epoch →
    s'.finalizedCheckpoint.epoch ≤ s'.justifiedCheckpoint.epoch)

omit [Config] [FcMap map] in
/-- `TickRel` relates a store to itself. -/
theorem TickRel.refl (s : Store map) : TickRel s s :=
  ⟨CkptGrows.refl s, rfl, rfl, .inl rfl, .inl rfl, fun h _ => h⟩

omit [Config] [FcMap map] in
/-- `TickRel` is transitive. The unrealized pair stays, so a checkpoint copied in the second
step is the unrealized checkpoint of the start. -/
theorem TickRel.trans (a b c : Store map) (h1 : TickRel a b) (h2 : TickRel b c) :
    TickRel a c := by
  obtain ⟨g1, uj1, uf1, j1, f1, o1⟩ := h1
  obtain ⟨g2, uj2, uf2, j2, f2, o2⟩ := h2
  refine ⟨g1.trans g2, uj2.trans uj1, uf2.trans uf1, ?_, ?_, fun ho hu => ?_⟩
  · rcases j2 with e | e <;> rw [e]
    · exact j1
    · exact .inr uj1
  · rcases f2 with e | e <;> rw [e]
    · exact f1
    · exact .inr uf1
  · exact o2 (o1 ho hu) (by rw [uj1, uf1]; exact hu)

/-- A per-slot tick relates its store argument to the store it returns. -/
theorem TickRel.of_perSlot (store post st st' : Store map) (time : UInt64)
    (h : (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store time).run st
      = .ok (post, st')) :
    TickRel store post := by
  obtain ⟨huj, huf, hc⟩ := onTickPerSlot_run_ckpt store post st st' time h
  rcases hc with ⟨hj, hf⟩ | ⟨hj, hf⟩
  · refine ⟨?_, huj, huf, .inl hj, .inl hf, fun ho _ => by rw [hj, hf]; exact ho⟩
    exact CkptGrows.of_eq (by simp only [storeCkpts, hj, hf, huj, huf])
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, huj, huf, ?_, ?_, fun ho hu => ?_⟩
    · rw [hj]; exact ckptPick_ge_old _ _
    · rw [hf]; exact ckptPick_ge_old _ _
    · rw [huj]; exact UInt64.le_refl _
    · rw [huf]; exact UInt64.le_refl _
    · rw [hj]
      rcases ckptPick_cases store.justifiedCheckpoint store.unrealizedJustifiedCheckpoint
        with e | e <;> rw [e]
      · exact .inl rfl
      · exact .inr rfl
    · rw [hf]
      rcases ckptPick_cases store.finalizedCheckpoint store.unrealizedFinalizedCheckpoint
        with e | e <;> rw [e]
      · exact .inl rfl
      · exact .inr rfl
    · rw [hj, hf]
      exact ckptPick_ord ho hu

/-- One step of a `GrowsAt TickRel` proof over the body of `onTick`. -/
syntax "tick_step" : tactic
macro_rules
  | `(tactic| tick_step) => `(tactic| first
      | with_reducible_and_instances
          refine GrowsAt.get_ret_set TickRel.trans
            (fun s0 p s s' h => TickRel.of_perSlot s0 p s s' _ h) ?_
      | with_reducible_and_instances refine GrowsAt.get_bind fun _ => ?_
      | with_reducible_and_instances exact GrowsAt.pure TickRel.refl _
      | with_reducible_and_instances refine GrowsAt.ite ?_ ?_
      | with_reducible_and_instances
          refine GrowsAt.fuelIterateM! TickRel.refl TickRel.trans _ _ (fun _ => ?_) _ _
      | (with_reducible_and_instances
          refine GrowsAt.bind TickRel.trans (GrowsAt.of_keeps TickRel.refl fun _ => ?_)
            fun _ => ?_
         focus keeps_solve)
      | split
      | (dsimp only; fail_if_success done))

/-- `onTick` relates its start store to its end store by `TickRel`. The loop runs
`onTickPerSlot` on the store it reads and sets the result. -/
theorem onTick_growsAt (time : UInt64) :
    GrowsAt TickRel (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      time) := by
  unfold onTick
  (repeat' tick_step) <;> done

end Tick

/-! ## `onBlock` -/

section Block
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- The block maps and the four checkpoints of a store. -/
def ckptMaps (s : Store map) :=
  (s.blocks, s.blockStates, storeCkpts s)

omit [Config] in
/-- A successful `getOrThrow` read found its value at the key, and kept the store. -/
theorem getOrThrow_run_eq_ok {V : Type} (mp : map Root V) (k : Root) (s s' : Store map) (v : V)
    (h : (FcMap.getOrThrow mp k : ForkChoiceStoreRun (Store map) V).run s = .ok (v, s')) :
    FcMap.lookup mp k = some v ∧ s' = s := by
  unfold FcMap.getOrThrow FcMap.getOrThrowKey at h
  split at h
  · rename_i v' hv
    injection h with h
    injection h with hv' hs
    exact ⟨hv'.symm ▸ hv, hs.symm⟩
  · cases h

omit [FcMap map] in
/-- `getCurrentStoreEpoch` reads the store only. -/
theorem getCurrentStoreEpoch_keeps (st : Store map) (v : Store map) :
    KeepsAt (fun s : Store map => s) v
      (getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map)) st) := by
  unfold getCurrentStoreEpoch
  keeps_solve

/-- `recordBlockTimeliness` returns a store with the block maps and the checkpoints of its
argument. -/
theorem recordBlockTimeliness_returns (store : Store map) (root : Root) (v : _)
    (hs : ckptMaps store = v) :
    EthCLLib.Proofs.Returns ckptMaps v
      (recordBlockTimeliness (StoreTransition := ForkChoiceStoreRun (Store map)) store root) := by
  unfold recordBlockTimeliness
  keeps_solve

/-- `updateProposerBoostRoot` returns a store with the block maps and the checkpoints of its
argument. -/
theorem updateProposerBoostRoot_returns (store : Store map) (head root : Root) (v : _)
    (hs : ckptMaps store = v) :
    EthCLLib.Proofs.Returns ckptMaps v
      (updateProposerBoostRoot (StoreTransition := ForkChoiceStoreRun (Store map)) store head
        root) := by
  unfold updateProposerBoostRoot
  keeps_solve

variable [CryptoBackend]

/-- `notifyPtcMessages` keeps the block maps and the checkpoints. It reads the state of the
block, a plain state after the state transition. -/
theorem notifyPtcMessages_keeps_ckptMaps (state : BeaconState)
    (pas : Array EthCLSpecs.Heze.PayloadAttestation) (v : _) :
    KeepsAt ckptMaps v
      (notifyPtcMessages (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        (pureState state) pas) := by
  unfold notifyPtcMessages
  keeps_solve

/-- `computePulledUpTip` on a root whose stored state is the uncached box of `w`. The run
pulls `w` up with `processJustificationAndFinalization` to `pulled`. It writes the pair of
`pulled` onto the unrealized pair, and it keeps the realized pair or writes the pair of
`pulled` onto it. It keeps the block maps. -/
theorem computePulledUpTip_run_ok (root : Root) (w : BeaconState) (u post : Store map)
    (hl : FcMap.lookup u.blockStates root = some (pureState w))
    (h : (computePulledUpTip (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      root).run u = .ok ((), post)) :
    ∃ pulled : BeaconState,
      runPure (processJustificationAndFinalization (StateTransition := HezeRun)) w
        = .ok ((), pulled) ∧
      post.blocks = u.blocks ∧ post.blockStates = u.blockStates ∧
      post.unrealizedJustifiedCheckpoint =
        ckptPick u.unrealizedJustifiedCheckpoint pulled.currentJustifiedCheckpoint ∧
      post.unrealizedFinalizedCheckpoint =
        ckptPick u.unrealizedFinalizedCheckpoint pulled.finalizedCheckpoint ∧
      ((post.justifiedCheckpoint = u.justifiedCheckpoint ∧
          post.finalizedCheckpoint = u.finalizedCheckpoint) ∨
        (post.justifiedCheckpoint =
            ckptPick u.justifiedCheckpoint pulled.currentJustifiedCheckpoint ∧
          post.finalizedCheckpoint = ckptPick u.finalizedCheckpoint pulled.finalizedCheckpoint)) := by
  unfold computePulledUpTip at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The stored state, then the pull-up.
  obtain ⟨st, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hl', e0⟩ := getOrThrow_run_eq_ok _ _ _ _ _ hread
  rw [e0] at h
  rw [hl] at hl'
  injection hl' with hl'
  subst hl'
  obtain ⟨pulled, hjf, h⟩ := runNestedStateTransition_bind_eq_ok w _
    keepsUncached_processJustificationAndFinalization _ _ _ h
  refine ⟨pulled, runPure_of_run_ok hjf, ?_⟩
  -- The record of the unrealized justification, then the unrealized pair.
  obtain ⟨⟨⟩, t1, hs1, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e1 := run_set_state_eq _ _ _ _ hs1
  subst e1
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨⟨⟩, t2, hs2, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2 := run_set_state_eq _ _ _ _ hs2
  subst e2
  -- The block read and the store epoch keep the store.
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, t3, hb, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := getOrThrow_run_eq_ok _ _ _ _ _ hb
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, t4, he, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e4 := getCurrentStoreEpoch_keeps _ _ _ _ _ rfl he
  subst e4
  -- The store after the record of the unrealized justification.
  let u1 : Store map := { u with unrealizedJustifications :=
    (FcMap.insert u.unrealizedJustifications root pulled.currentJustifiedCheckpoint) }
  obtain ⟨uj, uf, ujs, ufs, ub, ubs⟩ := updateUnrealizedCheckpoints_ckpt u1
    pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · -- A block from an earlier epoch: the realized pair takes the pair of `pulled` too.
    have h := run_get_bind_eq_ok _ _ _ h
    have e := run_set_state_eq _ _ _ _ h
    subst e
    obtain ⟨j', f', uj', uf', b', bs'⟩ := updateCheckpoints_ckpt
      (updateUnrealizedCheckpoints u1 pulled.currentJustifiedCheckpoint
        pulled.finalizedCheckpoint)
      pulled.currentJustifiedCheckpoint pulled.finalizedCheckpoint
    refine ⟨b'.trans ub, bs'.trans ubs, uj'.trans ujs, uf'.trans ufs, .inr ⟨?_, ?_⟩⟩
    · exact j'.trans (by rw [uj])
    · exact f'.trans (by rw [uf])
  · have e := run_pure_state_eq _ _ _ _ h
    subst e
    exact ⟨ub, ubs, ujs, ufs, .inl ⟨uj, uf⟩⟩

/-- A successful `onBlock` run, with its checkpoint writes. It read the parent state `pv`
and ran the state transition to `w`. The store `u` has the block and the uncached box of
`w` at the block root, and the four checkpoints of `pre`. The rest of the run writes the
pair of `w` onto the realized pair of `u`, then runs `computePulledUpTip` at the block
root. -/
theorem onBlock_run_ckpt (sb : SignedBeaconBlock) (pre post : Store map)
    (hp : BlockStatesPure pre)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    ∃ (pv w : BeaconState) (u : Store map),
      FcMap.lookup pre.blockStates sb.message.parentRoot = some (pureState pv) ∧
      (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb).run (pureState pv)
        = .ok ((), pureState w) ∧
      u.blocks = FcMap.insert pre.blocks (htr sb.message) sb.message ∧
      u.blockStates = FcMap.insert pre.blockStates (htr sb.message) (pureState w) ∧
      storeCkpts u = storeCkpts pre ∧
      (computePulledUpTip (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        (htr sb.message)).run
          (updateCheckpoints u w.currentJustifiedCheckpoint w.finalizedCheckpoint)
        = .ok ((), post) := by
  unfold onBlock at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The parent state, as in `onBlock_run_ok`.
  obtain ⟨parentState, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlookup, -⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  obtain ⟨pv, hpv⟩ := hp.lookup _ (by rw [hlookup]; rfl)
  rw [hpv] at hlookup
  injection hlookup with hlookup
  subst hlookup
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨w, htrans, h⟩ :=
    runNestedStateTransition_bind_eq_ok pv _ (keepsUncached_stateTransition sb true) _ _ _ h
  -- The head, then the insert.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, t, hset, h⟩ := run_bind_eq_ok _ _ _ _ h
  have ht := run_set_state_eq _ _ _ _ hset
  subst ht
  -- The vote replay, the timeliness record, and the boost keep the block maps and the
  -- checkpoints.
  obtain ⟨⟨⟩, t1, hn, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e1 := notifyPtcMessages_keeps_ckptMaps _ _ _ _ () _ rfl hn
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨st2, t2, hr, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2 := recordBlockTimeliness_returns t1 _ _ rfl _ _ _ hr
  obtain ⟨⟨⟩, t3, hs3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 := run_set_state_eq _ _ _ _ hs3
  subst e3
  obtain ⟨st4, t4, hu, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e4 := updateProposerBoostRoot_returns _ _ _ _ rfl _ _ _ hu
  obtain ⟨⟨⟩, t5, hs5, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e5 := run_set_state_eq _ _ _ _ hs5
  subst e5
  -- The write of the pair of `w`, then the pull-up.
  obtain ⟨⟨⟩, t6, hs6, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e6 := run_set_state_eq _ _ _ _ hs6
  subst e6
  have e := e4.trans (e2.trans e1)
  simp only [ckptMaps, Prod.mk.injEq] at e
  obtain ⟨eb, ebs, eck⟩ := e
  exact ⟨pv, w, _, hpv, htrans, eb, ebs, eck, h⟩

end Block

/-! ## The handler events -/

section Events
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]

/-- `onAttestation` keeps the four checkpoints. -/
theorem onAttestation_keeps_ckpts (v : _) (att : EthCLSpecs.Heze.Attestation)
    (isFromBlock : Bool) :
    KeepsAt storeCkpts v
      (EthCLSpecs.Heze.onAttestation (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) att isFromBlock) := by
  unfold EthCLSpecs.Heze.onAttestation
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the four checkpoints. -/
theorem onAttesterSlashing_keeps_ckpts (v : _) (asl : EthCLSpecs.Heze.AttesterSlashing) :
    KeepsAt storeCkpts v
      (EthCLSpecs.Heze.onAttesterSlashing (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) asl) := by
  unfold EthCLSpecs.Heze.onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the four checkpoints. -/
theorem onPayloadAttestationMessage_keeps_ckpts (v : _)
    (msg : EthCLSpecs.Heze.PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt storeCkpts v
      (EthCLSpecs.Heze.onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold EthCLSpecs.Heze.onPayloadAttestationMessage
  keeps_solve

variable [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps the four checkpoints. -/
theorem onExecutionPayloadEnvelope_keeps_ckpts (v : _)
    (signedEnv : EthCLSpecs.Heze.SignedExecutionPayloadEnvelope) :
    KeepsAt storeCkpts v
      (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold EthCLSpecs.Heze.onExecutionPayloadEnvelope
  keeps_solve

variable [LawfulFcMap map Root]

omit [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability] in
/-- `onBlock` raises no checkpoint epoch. Each write uses `ckptPick`. -/
theorem onBlock_ckptGrows (sb : SignedBeaconBlock) (pre post : Store map)
    (hp : BlockStatesPure pre)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    CkptGrows pre post := by
  obtain ⟨_, w, u, -, -, -, hbs, hck, hpull⟩ := onBlock_run_ckpt sb pre post hp h
  obtain ⟨j1, f1, uj1, uf1, -, bs1⟩ :=
    updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
  have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
      w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
    rw [bs1, hbs, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
  obtain ⟨pulled, -, -, -, puj, puf, hj⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
  simp only [storeCkpts, Prod.mk.injEq] at hck
  obtain ⟨cj, cf, cuj, cuf⟩ := hck
  -- The realized pair of the store between the two writes.
  have gj : pre.justifiedCheckpoint.epoch ≤
      (updateCheckpoints u w.currentJustifiedCheckpoint
        w.finalizedCheckpoint).justifiedCheckpoint.epoch := by
    rw [j1, cj]; exact ckptPick_ge_old _ _
  have gf : pre.finalizedCheckpoint.epoch ≤
      (updateCheckpoints u w.currentJustifiedCheckpoint
        w.finalizedCheckpoint).finalizedCheckpoint.epoch := by
    rw [f1, cf]; exact ckptPick_ge_old _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hj with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
    · exact gj
    · exact UInt64.le_trans gj (ckptPick_ge_old _ _)
  · rcases hj with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact gf
    · exact UInt64.le_trans gf (ckptPick_ge_old _ _)
  · rw [puj, uj1, cuj]; exact ckptPick_ge_old _ _
  · rw [puf, uf1, cuf]; exact ckptPick_ge_old _ _

/-- A handler event raises no checkpoint epoch of the store. -/
theorem HandlerEvent.run_ckptGrows (e : HandlerEvent) (s s' : Store map)
    (hp : BlockStatesPure s)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) : CkptGrows s s' := by
  cases e with
  | tick time => exact (onTick_growsAt time s () s' h).1
  | block sb => exact onBlock_ckptGrows sb s s' hp h
  | attestation att isFromBlock =>
    exact CkptGrows.of_eq (onAttestation_keeps_ckpts _ att isFromBlock s () s' rfl h)
  | attesterSlashing asl =>
    exact CkptGrows.of_eq (onAttesterSlashing_keeps_ckpts _ asl s () s' rfl h)
  | payloadAttestation msg isFromBlock =>
    exact CkptGrows.of_eq (onPayloadAttestationMessage_keeps_ckpts _ msg isFromBlock s () s' rfl h)
  | envelope signedEnv =>
    exact CkptGrows.of_eq (onExecutionPayloadEnvelope_keeps_ckpts _ signedEnv s () s' rfl h)

/-- A trace raises no checkpoint epoch of the store. The trace starts at a store whose
block states are uncached boxes, as every store on a trace from the anchor store is
(`NodeTrace.blockStatesPure`). An inclusion-list event writes the IL store only. -/
theorem NodeTrace.ckptGrows {s s' : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s events arrivals s') (hp : BlockStatesPure s) : CkptGrows s s' := by
  induction h with
  | nil => exact CkptGrows.refl _
  | handler e htr hrun ih =>
    exact ih.trans (e.run_ckptGrows _ _ (htr.blockStatesPure hp) hrun)
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

end Events

end EthCLSpecs.Proofs.Heze
