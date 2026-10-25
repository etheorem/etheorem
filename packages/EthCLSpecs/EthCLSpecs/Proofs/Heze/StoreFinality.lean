import EthCLSpecs.Proofs.Heze.FinalizationProgress
import EthCLSpecs.Proofs.Heze.ClockedTrace
import EthCLSpecs.Proofs.Heze.StoreChainState

/-!
# `EthCLSpecs.Proofs.Heze.StoreFinality`: an honest store finalizes with the chain

## The first tick of an epoch

`onTick` advances the store clock one slot at a time. Each step runs `onTickPerSlot` at the
start of the next slot. A step that reaches the first slot of an epoch copies the unrealized
pair into the realized pair (`onTickPerSlot_realize`). So a tick that moves the current slot
from below the first slot `S` of an epoch to `S` or later gives a finalized epoch of at least
the unrealized finalized epoch before the tick (`onTick_realizes`). The proof keeps the
relation `RealizeRel` through the loop by the rules of `GrowsAt`. The slot length is a whole
number of seconds, so the start time of slot `k + 1` reads as slot `k + 1`.

## The pull-up of the last block

The state after the block at the last slot of `E₁ + 3` is the weigh state of `E₁ + 3`, since the
next step is a slot step. `onBlock` runs `process_justification_and_finalization` on it, which
is the last weigh step of the honest chain. So the pull-up finalizes `E₁` or later
(`HonestChain.pullup_finalizes`).

## The store

An honest store receives that block before `E₁ + 4` starts. The store traces to the anchor
of the chain, so it stores the chain's state after the block (`onBlock_stores_chainState`).
Its unrealized finalized epoch is then `E₁` or later. Until the clock reaches
the first slot of `E₁ + 4`, every event keeps that (`FinalizesBy`). The tick that reaches the
slot realizes it. So from that slot on, the finalized epoch is `E₁` or later
(`honestStore_finalizes`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure run_bind_eq_ok run_get_bind_eq_ok
  run_pure_eq_ok run_pure_state_eq run_set_state_eq run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store Checkpoint getCurrentSlot onTickPerSlot onTick
  updateCheckpoints)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotDurationMs)

section Tick
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- The current slot of a store, from its clock: the milliseconds since genesis divided by the
slot length. -/
def storeSlot (st : Store map) : Nat :=
  (st.time.toNat - st.genesisTime.toNat) * 1000 / slotDurationMs.toNat

/-- A successful `getCurrentSlot` read returns `storeSlot`. -/
theorem getCurrentSlot_storeSlot {st s s' : Store map} {cs : UInt64}
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s')) : cs.toNat = storeSlot st := by
  obtain ⟨hle, -, hcs⟩ := getCurrentSlot_run_ok st s s' cs h
  rw [hcs, UInt64.toNat_sub_of_le _ _ hle]
  rfl

omit [HasherTag] [Config] in
/-- The slots since the start of the epoch of `x`, as `on_tick_per_slot` computes them, are
zero at the first slot of an epoch. The start slot `r` is the one that the checked
`compute_start_slot_at_epoch` returns, the product `epoch * SLOTS_PER_EPOCH`
(`computeStartSlotAtEpoch_ok_eq`). -/
theorem slotsSinceEpochStart_zero {x r : UInt64} (hx : x.toNat % slotsPerEpoch = 0)
    (hr : (EthCLSpecs.Heze.computeStartSlotAtEpoch (EthCLSpecs.Heze.computeEpochAtSlot x)
      : Except StateTransitionError UInt64) = .ok r) :
    x - r = 0 := by
  have hp := slotsPerEpochPos
  have hlt := EthCLSpecs.Heze.Const.slotsPerEpochLt
  have hk : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    EthCLLib.Proofs.toNat_ofNat_lt64 hlt
  have hdm : x.toNat / slotsPerEpoch * slotsPerEpoch = x.toNat := by
    have := Nat.div_add_mod x.toNat slotsPerEpoch
    rw [hx, Nat.add_zero, Nat.mul_comm] at this
    exact this
  have hm : r.toNat = x.toNat := by
    rw [computeStartSlotAtEpoch_ok_eq hr]
    unfold EthCLSpecs.Heze.computeEpochAtSlot
    rw [UInt64.toNat_mul, UInt64.toNat_div, hk, hdm, Nat.mod_eq_of_lt x.toNat_lt]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hm]; exact Nat.le_refl _), hm,
    Nat.sub_self]
  rfl

/-- A per-slot tick sets the clock, keeps the genesis time, and keeps the unrealized pair. -/
theorem onTickPerSlot_run_clock (store post st st' : Store map) (time : UInt64)
    (h : (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store time).run st
      = .ok (post, st')) :
    post.time = time ∧ post.genesisTime = store.genesisTime := by
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
      (repeat' split) <;> (try rw [updateCheckpoints_eq]) <;> exact ⟨rfl, rfl⟩

/-- **A per-slot tick that reaches the first slot of an epoch realizes the unrealized
checkpoints.** The current slot of the new clock is above the current slot of the old clock,
and it is the first slot of an epoch. -/
theorem onTickPerSlot_realize (store post st st' : Store map) (time : UInt64)
    (h : (onTickPerSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store time).run st
      = .ok (post, st'))
    (hlt : storeSlot store < storeSlot { store with time := time })
    (hz : storeSlot { store with time := time } % slotsPerEpoch = 0) :
    post.finalizedCheckpoint =
      ckptPick store.finalizedCheckpoint store.unrealizedFinalizedCheckpoint := by
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
      have e1 := getCurrentSlot_storeSlot h1
      have e2 := getCurrentSlot_storeSlot h2
      have hgt : q.1 > p.1 := UInt64.lt_iff_toNat_lt.mpr (by omega)
      -- The first slot of an epoch is zero slots past the epoch start.
      have hz' : k.1 = 0 := by
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
          rw [← congrArg Prod.fst h3]
          exact slotsSinceEpochStart_zero (by rw [e2]; exact hz) hr
      rw [if_pos (by simp [hgt, hz']), updateCheckpoints_eq]
      split <;> rfl

/-- The relation that `onTick` keeps toward the first slot `S` of an epoch, for the genesis
time `g`. The genesis time stays, `TickRel` holds, and a run that moves the current slot from
below `S` to `S` or later realizes the unrealized finalized checkpoint. -/
def RealizeRel (g : UInt64) (S : Nat) (s s' : Store map) : Prop :=
  s'.genesisTime = s.genesisTime ∧ TickRel s s' ∧
  (s.genesisTime = g → storeSlot s < S → S ≤ storeSlot s' →
    s.unrealizedFinalizedCheckpoint.epoch ≤ s'.finalizedCheckpoint.epoch)

/-- `RealizeRel` relates a store to itself. -/
theorem RealizeRel.refl (g : UInt64) (S : Nat) (s : Store map) : RealizeRel g S s s :=
  ⟨rfl, TickRel.refl s, fun _ h1 h2 => absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)⟩

/-- `RealizeRel` is transitive. When the middle store is still below `S`, the second run
realizes the unrealized checkpoint, which the first run kept. Otherwise the first run realized
it, and the second run keeps the finalized epoch from going down. -/
theorem RealizeRel.trans (g : UInt64) (S : Nat) (a b c : Store map) (h1 : RealizeRel g S a b)
    (h2 : RealizeRel g S b c) : RealizeRel g S a c := by
  obtain ⟨g1, t1, r1⟩ := h1
  obtain ⟨g2, t2, r2⟩ := h2
  refine ⟨g2.trans g1, TickRel.trans _ _ _ t1 t2, fun hg ha hc => ?_⟩
  by_cases hb : storeSlot b < S
  · have := r2 (g1.trans hg) hb hc
    rw [t1.2.2.1] at this
    exact this
  · exact UInt64.le_trans (r1 hg ha (Nat.le_of_not_lt hb)) t2.1.2.1

omit [Preset] [HasherTag] [Config] [FcMap map] in
/-- A successful checked addition in the store runner keeps the store, returns the sum, and does
not wrap. -/
theorem store_checkedAdd_ok {σ : Type} {a b : UInt64} {d : String} {s s' : σ} {r : UInt64}
    (h : (checkedAdd (m := ForkChoiceStoreRun σ) a b d).run s = .ok (r, s')) :
    s' = s ∧ r = a + b ∧ a.toNat + b.toNat < 2 ^ 64 := by
  unfold checkedAdd at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, h⟩
  · rw [EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run] at h
    cases h
  · rw [EthCLLib.Proofs.run_pure] at h
    injection h with h
    injection h with h1 h2
    refine ⟨h2.symm, h1.symm, ?_⟩
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hc
    have := UInt64.toNat_lt a
    have := UInt64.toNat_lt b
    omega

omit [Preset] [HasherTag] [Config] [FcMap map] in
/-- A successful checked subtraction in the store runner keeps the store, returns the
difference, and does not underflow. -/
theorem store_checkedSub_ok {σ : Type} {a b : UInt64} {d : String} {s s' : σ} {r : UInt64}
    (h : (checkedSub (m := ForkChoiceStoreRun σ) a b d).run s = .ok (r, s')) :
    s' = s ∧ r = a - b ∧ b ≤ a := by
  unfold checkedSub at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, h⟩
  · rw [EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run] at h
    cases h
  · rw [EthCLLib.Proofs.run_pure] at h
    injection h with h
    injection h with h1 h2
    exact ⟨h2.symm, h1.symm, UInt64.not_lt.mp hc⟩

omit [Preset] [HasherTag] [Config] [FcMap map] in
/-- A successful checked product in the store runner keeps the store, returns the product, and
does not wrap. -/
theorem store_checkedMul_ok {σ : Type} {a b : UInt64} {d : String} {s s' : σ} {r : UInt64}
    (h : (checkedMul (m := ForkChoiceStoreRun σ) a b d).run s = .ok (r, s')) :
    s' = s ∧ r = a * b ∧ a.toNat * b.toNat < 2 ^ 64 := by
  unfold checkedMul at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, h⟩
  · rw [EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run] at h
    cases h
  · rw [EthCLLib.Proofs.run_pure] at h
    injection h with h
    injection h with h1 h2
    refine ⟨h2.symm, h1.symm, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
    by_cases ha : a = 0
    · subst ha
      simp
    · have hq := hc ha
      have hb := UInt64.toNat_lt b
      have hpos : 0 < a.toNat := by
        rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) ha
        · exact h0
      have e := congrArg UInt64.toNat hq
      rw [UInt64.toNat_div, UInt64.toNat_mul] at e
      refine Classical.byContradiction fun hn => ?_
      have hge : 2 ^ 64 ≤ a.toNat * b.toNat := Nat.le_of_not_lt hn
      have hlt := Nat.mod_lt (a.toNat * b.toNat) (show 0 < 2 ^ 64 by decide)
      have hdiv : (a.toNat * b.toNat % 2 ^ 64) / a.toNat < b.toNat := by
        rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm b.toNat]
        exact Nat.lt_of_lt_of_le hlt hge
      omega

/-- **A tick that reaches the first slot `S` of an epoch realizes the unrealized finalized
checkpoint.** The slot length is a positive whole number of seconds. Each step of the loop
sets the clock to the start of the next slot, so the step that reaches `S` lands on it. The
final step sets the clock to `time`, whose slot is the tick slot, at or below the current
slot. -/
theorem onTick_realizes (hD : 1000 ∣ slotDurationMs.toNat) (hD0 : 0 < slotDurationMs.toNat)
    {S : Nat} (hS : S % slotsPerEpoch = 0) (time : UInt64) {pre post : Store map}
    (h : (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time).run pre
      = .ok ((), post)) :
    RealizeRel pre.genesisTime S pre post := by
  unfold onTick at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨elapsed, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨e1, he1, hge⟩ := store_checkedSub_ok h1
  rw [e1] at h
  obtain ⟨tickMs, s2, h2, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨e2, he2, hfit⟩ := store_checkedMul_ok h2
  rw [e2] at h
  obtain ⟨cur, s3, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 : s3 = pre := getCurrentSlot_keeps pre pre pre cur s3 rfl h3
  rw [e3] at h
  have hgle := UInt64.le_iff_toNat_le.mp hge
  obtain ⟨d, hd⟩ := hD
  have hd0 : 0 < d := by omega
  -- The slot of a clock, from the genesis time of `pre`.
  have hslot : ∀ s : Store map, s.genesisTime = pre.genesisTime → ∀ t : UInt64,
      storeSlot { s with time := t } = (t.toNat - pre.genesisTime.toNat) * 1000 /
        slotDurationMs.toNat := by
    intro s hs t
    unfold storeSlot
    rw [show ({ s with time := t } : Store map).genesisTime = s.genesisTime from rfl, hs]
  -- A store with the clock and the genesis time of another store has its slot.
  have hsame : ∀ a b : Store map, a.time = b.time → a.genesisTime = b.genesisTime →
      storeSlot a = storeSlot b := by
    intro a b ht hg
    unfold storeSlot
    rw [ht, hg]
  refine GrowsAt.fuelIterateM! (RealizeRel.refl pre.genesisTime S)
    (RealizeRel.trans pre.genesisTime S) _ _ ?_ _ _ pre () post h
  intro b s a s' hr
  have hr := run_get_bind_eq_ok _ _ _ hr
  obtain ⟨cs, t1, hc, hr⟩ := run_bind_eq_ok _ _ _ _ hr
  have et1 : t1 = s := getCurrentSlot_keeps s s s cs t1 rfl hc
  rw [et1] at hr
  have hcs := getCurrentSlot_storeSlot hc
  rcases run_ite_eq_ok hr with ⟨hlt, hr⟩ | ⟨hnl, hr⟩
  · -- A step to the start of the next slot.
    obtain ⟨bumped, t2, hb, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨eb, hbv, hbfit⟩ := store_checkedAdd_ok hb
    rw [eb] at hr
    obtain ⟨scaled, t3, hsc, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨esc, hscv, hscfit⟩ := store_checkedMul_ok hsc
    rw [esc] at hr
    obtain ⟨nt, t4, hnt, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨ent, hntv, hntfit⟩ := store_checkedAdd_ok hnt
    rw [ent] at hr
    have hr := run_get_bind_eq_ok _ _ _ hr
    obtain ⟨p, t5, hp, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨u, t6, hu, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    have e6 := run_set_state_eq _ _ _ _ hu
    rw [e6] at hr
    have e7 := run_pure_state_eq _ _ _ _ hr
    subst e7
    obtain ⟨hpt, hpg⟩ := onTickPerSlot_run_clock _ _ _ _ _ hp
    refine ⟨hpg, TickRel.of_perSlot s s' s t5 nt hp, fun hg hlo hhi => ?_⟩
    -- The new clock reads as slot `cs + 1`.
    have hbfit' : cs.toNat + 1 < 2 ^ 64 := by simpa using hbfit
    have hb1 : bumped.toNat = cs.toNat + 1 := by
      rw [hbv, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hbfit']
    have hcs1 : storeSlot { s with time := nt } = cs.toNat + 1 := by
      rw [hslot s hg nt, hntv, UInt64.toNat_add, Nat.mod_eq_of_lt hntfit, Nat.add_sub_cancel_left,
        UInt64.toNat_div, hscv, UInt64.toNat_mul, Nat.mod_eq_of_lt hscfit, hb1]
      show (cs.toNat + 1) * slotDurationMs.toNat / 1000 * 1000 / slotDurationMs.toNat = _
      rw [hd, Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by decide : 0 < 1000),
        Nat.mul_comm (_ * d) 1000, Nat.mul_div_mul_left _ _ (by decide : 0 < 1000),
        Nat.mul_div_cancel _ hd0]
    have hps : storeSlot s' = storeSlot { s with time := nt } := hsame _ _ hpt hpg
    rw [hps, hcs1] at hhi
    rw [hcs] at hcs1
    have heq : storeSlot { s with time := nt } = S := by rw [hcs1]; omega
    have hfin := onTickPerSlot_realize s s' s t5 nt hp (by omega) (by rw [heq]; exact hS)
    rw [hfin]
    exact ckptPick_ge_new _ _
  · -- The last step: the clock is `time`, whose slot is the tick slot.
    have hr := run_get_bind_eq_ok _ _ _ hr
    obtain ⟨p, t5, hp, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    obtain ⟨u, t6, hu, hr⟩ := run_bind_eq_ok _ _ _ _ hr
    have e6 := run_set_state_eq _ _ _ _ hu
    rw [e6] at hr
    have e7 := run_pure_state_eq _ _ _ _ hr
    subst e7
    obtain ⟨hpt, hpg⟩ := onTickPerSlot_run_clock _ _ _ _ _ hp
    refine ⟨hpg, TickRel.of_perSlot s s' s t5 time hp, fun hg hlo hhi => ?_⟩
    exfalso
    have hps : storeSlot s' = storeSlot { s with time := time } := hsame _ _ hpt hpg
    rw [hps, hslot s hg time] at hhi
    have htick : (tickMs / slotDurationMs).toNat =
        (time.toNat - pre.genesisTime.toNat) * 1000 / slotDurationMs.toNat := by
      rw [UInt64.toNat_div, he2, UInt64.toNat_mul, Nat.mod_eq_of_lt hfit, he1,
        UInt64.toNat_sub_of_le _ _ hge]
      rfl
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hnl)
    omega

end Tick

/-! ## The pull-up of the last block -/

section PullUp
variable [Preset] [HasherTag] [Config] [CryptoBackend]

open EthCLSpecs.Heze (BeaconState Epoch ValidatorIndex SignedBeaconBlock currentEpochOf)

/-- **The pull-up of the block at the last slot of `E₁ + 3` finalizes `E₁`.** The state `w`
after that block is the weigh state of `E₁ + 3`, since the next step is a slot step. So
`process_justification_and_finalization` on `w` is the last weigh step of the honest chain,
and `finalize_tail` applies. -/
theorem HonestChain.pullup_finalizes {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} {honestOf : ValidatorIndex → Bool} {E₁ : Nat}
    (H : HonestChain hi steps st₀ st vals honestOf E₁) {p q : List ChainStep}
    {sb : SignedBeaconBlock} {v : Bool} {u w : BeaconState}
    (hs : steps = p ++ .block sb v :: .slot :: q) (hu : ChainRun hi p st₀ u)
    (hstep : BlockStep sb v u w) (hlast : (u.slot.toNat + 1) % slotsPerEpoch = 0)
    (hep : u.slot.toNat / slotsPerEpoch = E₁ + 3) {pulled : BeaconState}
    (hjf : runPure (EthCLSpecs.Heze.processJustificationAndFinalization
      (StateTransition := HezeRun)) w = .ok ((), pulled)) :
    E₁ ≤ pulled.finalizedCheckpoint.epoch.toNat ∧
      (pulled.finalizedCheckpoint.epoch.toNat = E₁ →
        toCp pulled.finalizedCheckpoint = cpOf st₀ steps E₁) := by
  have hhi := H.ref.hhi
  obtain ⟨W3, hW3, -, hb1, hb2, hP, hC, hcur⟩ := H.end_facts
  -- The state after the block is the weigh state of `E₁ + 3`.
  obtain ⟨hsl, -⟩ := hstep.slot
  have hWw : WeighAt hi steps st₀ (E₁ + 2 + 1) w :=
    ⟨p ++ [.block sb v], q, by rw [hs]; simp, hu.append (.block sb v hstep (.nil _)),
      by rw [hsl]; exact hlast, by rw [hsl, hep]⟩
  have e := hW3.unique hhi hWw
  subst e
  have hjp := (H.weigh (k := 2) (by decide))
  obtain ⟨W, hW, jpW⟩ := hjp
  have e' := hW.unique hhi hWw
  subst e'
  -- The pull-up is the weigh step on `W`.
  rw [processJustificationAndFinalization_run_eq, if_neg (by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    rw [hcur] at this
    simp [EthCLSpecs.Heze.Const.genesisEpoch] at this)] at hjf
  -- The five reads succeed, and the weigh step runs on their values.
  obtain ⟨prevIdx, h1, hjf⟩ := except_bind_eq_ok hjf
  obtain ⟨currIdx, -, hjf⟩ := except_bind_eq_ok hjf
  obtain ⟨tot, h3, hjf⟩ := except_bind_eq_ok hjf
  obtain ⟨prev, h4, hjf⟩ := except_bind_eq_ok hjf
  obtain ⟨curr, -, hjf⟩ := except_bind_eq_ok hjf
  obtain ⟨pr, cr, -, -, -, hf, -, -⟩ := weighJustificationAndFinalization_run_ok _ _ _ _ _ hjf
  have hjp' : decide (prev.toNat * 3 ≥ tot.toNat * 2) = true := by
    rw [← totBal_of_ok h3, ← tgtBal_of_ok h1 h4]
    exact jpW
  rw [hf]
  simp only [hjp', if_true]
  exact finalize_tail hb1 hb2 hP hC hcur _

end PullUp

/-! ## The store -/

section Store
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

open EthCLSpecs.Heze (SignedBeaconBlock Attestation AttesterSlashing PayloadAttestationMessage
  SignedExecutionPayloadEnvelope SignedInclusionList ExecutionPayload ExecutionRequests Transaction
  onBlock onAttestation onAttesterSlashing onPayloadAttestationMessage onExecutionPayloadEnvelope)

/-- `onBlock` keeps the store clock. -/
theorem onBlock_keeps_time (v : UInt64) (signedBlock : SignedBeaconBlock) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.time) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

/-- `onAttestation` keeps the store clock. -/
theorem onAttestation_keeps_time (v : UInt64) (att : Attestation) (isFromBlock : Bool) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.time) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the store clock. -/
theorem onAttesterSlashing_keeps_time (v : UInt64) (asl : AttesterSlashing) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.time) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the store clock. -/
theorem onPayloadAttestationMessage_keeps_time (v : UInt64) (msg : PayloadAttestationMessage)
    (isFromBlock : Bool) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.time) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root]

/-- `onExecutionPayloadEnvelope` keeps the store clock. -/
theorem onExecutionPayloadEnvelope_keeps_time (v : UInt64)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    EthCLLib.Proofs.KeepsAt (fun st : Store map => st.time) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- The invariant of a store after the block of the last slot of `E₁ + 3`, toward the first
slot `S` of `E₁ + 4`. The clock is before `S`, with the genesis time `g`, and the unrealized
finalized epoch is at least `E`. Or the finalized epoch is at least `E`. -/
def FinalizesBy (g : UInt64) (S E : Nat) (s : Store map) : Prop :=
  (s.genesisTime = g ∧ storeSlot s < S ∧ E ≤ s.unrealizedFinalizedCheckpoint.epoch.toNat) ∨
    E ≤ s.finalizedCheckpoint.epoch.toNat

/-- **A trace keeps `FinalizesBy`.** A tick that reaches `S` realizes the unrealized finalized
checkpoint (`onTick_realizes`). A tick that stays before `S` keeps the unrealized pair. The
other events keep the clock and do not lower a checkpoint. -/
theorem NodeTrace.finalizesBy (hD : 1000 ∣ slotDurationMs.toNat)
    (hD0 : 0 < slotDurationMs.toNat) {S E : Nat} (hS : S % slotsPerEpoch = 0) {g : UInt64}
    {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (hp : BlockStatesPure s0) (h0 : FinalizesBy g S E s0) : FinalizesBy g S E s := by
  induction h with
  | nil => exact h0
  | @handler events arrivals s s' e htr hrun ih =>
    have hps := htr.blockStatesPure hp
    have hg := CkptGrows.refl s
    have hgrow := e.run_ckptGrows _ _ hps hrun
    rcases ih with ⟨hgs, hlt, hu⟩ | hf
    · -- An event other than a tick keeps the clock and the genesis time.
      have keepClock : s'.time = s.time → FinalizesBy g S E s' := fun htime => by
        have hgen := HandlerEvent.run_keeps_genesisTime _ _ _ hrun
        refine .inl ⟨hgen.trans hgs, ?_, Nat.le_trans hu
          (UInt64.le_iff_toNat_le.mp hgrow.2.2.2)⟩
        have : storeSlot s' = storeSlot s := by unfold storeSlot; rw [htime, hgen]
        rw [this]
        exact hlt
      cases e with
      | tick time =>
        obtain ⟨gk, tk, rk⟩ := onTick_realizes (map := map) hD hD0 hS time hrun
        by_cases hs' : storeSlot s' < S
        · refine .inl ⟨gk.trans hgs, hs', ?_⟩
          rw [tk.2.2.1]
          exact hu
        · exact .inr (Nat.le_trans hu (UInt64.le_iff_toNat_le.mp
            (rk rfl hlt (Nat.le_of_not_lt hs'))))
      | block sb => exact keepClock (onBlock_keeps_time _ sb s () s' rfl hrun)
      | attestation att b => exact keepClock (onAttestation_keeps_time _ att b s () s' rfl hrun)
      | attesterSlashing asl => exact keepClock (onAttesterSlashing_keeps_time _ asl s () s' rfl hrun)
      | payloadAttestation msg b =>
        exact keepClock (onPayloadAttestationMessage_keeps_time _ msg b s () s' rfl hrun)
      | envelope env =>
        exact keepClock (onExecutionPayloadEnvelope_keeps_time _ env s () s' rfl hrun)
    · exact .inr (Nat.le_trans hf (UInt64.le_iff_toNat_le.mp hgrow.2.1))
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

/-- **An honest store finalizes `E₁` from the first slot of `E₁ + 4`.** The store traces to
the anchor state `st₀` of the honest chain and to the anchor block `a` (`CkptInv`). The anchor
state has the header of `a`, with a filled state root when the header slot is below the state
slot. The store receives the block of the last slot of `E₁ + 3` before `E₁ + 4` starts.
Without a block collision, it stores the chain's state `w` after that block
(`onBlock_stores_chainState`). `onBlock` computes the pull-up of `w`, so the unrealized
finalized epoch is `E₁` or later (`HonestChain.pullup_finalizes`).
The tick that reaches the first slot of `E₁ + 4` realizes it, and the later events do not
lower it (`NodeTrace.finalizesBy`). -/
theorem honestStore_finalizes (hD : 1000 ∣ slotDurationMs.toNat)
    (hD0 : 0 < slotDurationMs.toNat) (hc : ¬ HtrCollision EthCLSpecs.Heze.BeaconBlock)
    {hi : Nat} {steps : List ChainStep}
    {st₀ st : EthCLSpecs.Heze.BeaconState} {vals : List EthCLSpecs.Heze.ValidatorIndex}
    {honestOf : EthCLSpecs.Heze.ValidatorIndex → Bool} {E₁ : Nat}
    (H : HonestChain hi steps st₀ st vals honestOf E₁) {a : EthCLSpecs.Heze.BeaconBlock}
    (hfill₀ : HdrFilled st₀) (hanc : filledHeader st₀ = headerOf a) {p q : List ChainStep}
    {sb : SignedBeaconBlock} {v : Bool} {u w : EthCLSpecs.Heze.BeaconState}
    (hs : steps = p ++ .block sb v :: .slot :: q) (hu : ChainRun hi p st₀ u)
    (hstep : BlockStep sb v u w) (hlast : (u.slot.toNat + 1) % slotsPerEpoch = 0)
    (hep : u.slot.toNat / slotsPerEpoch = E₁ + 3)
    {sA sB s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (hinv : CkptInv st₀ a sA)
    (hblk : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run sA
      = .ok ((), sB))
    (hA : storeSlot sA < (E₁ + 4) * slotsPerEpoch) (htrace : NodeTrace sB events arrivals s)
    (hS : (E₁ + 4) * slotsPerEpoch ≤ storeSlot s) :
    E₁ ≤ s.finalizedCheckpoint.epoch.toNat := by
  have hpA : BlockStatesPure sA := hinv.slot.statesPure
  have hval : ValidatedSteps p := fun sb' v' hm =>
    H.ref.val sb' v' (by rw [hs]; exact List.mem_append_left _ hm)
  have hstate := onBlock_stores_chainState H.ref.hw hc H.ref.hhi H.ref.roots hfill₀ hanc hu hval
    hstep hinv hblk
  obtain ⟨pv, w', u', -, -, -, hbsu, -, hpull⟩ := onBlock_run_ckpt sb sA sB hpA hblk
  obtain ⟨-, -, -, -, -, bs1⟩ :=
    updateCheckpoints_ckpt u' w'.currentJustifiedCheckpoint w'.finalizedCheckpoint
  have hl : FcMap.lookup (updateCheckpoints u' w'.currentJustifiedCheckpoint
      w'.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w') := by
    rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
  obtain ⟨pulled, hjf, -, pbs, -, puf, -⟩ := computePulledUpTip_run_ok _ w' _ sB hl hpull
  -- The stored state is the chain's state `w`.
  have hw : w' = w := by
    rw [pbs, hl] at hstate
    exact pureState_inj (Option.some.inj hstate)
  subst hw
  obtain ⟨hfin, -⟩ := H.pullup_finalizes hs hu hstep hlast hep hjf
  -- After the block, the store meets `FinalizesBy`.
  have htime : sB.time = sA.time := onBlock_keeps_time _ sb sA () sB rfl hblk
  have hgen : sB.genesisTime = sA.genesisTime := onBlock_keeps_genesisTime _ sb sA () sB rfl hblk
  have h0 : FinalizesBy sB.genesisTime ((E₁ + 4) * slotsPerEpoch) E₁ sB := by
    refine .inl ⟨rfl, ?_, ?_⟩
    · have : storeSlot sB = storeSlot sA := by unfold storeSlot; rw [htime, hgen]
      rw [this]
      exact hA
    · rw [puf]
      exact Nat.le_trans hfin (UInt64.le_iff_toNat_le.mp (ckptPick_ge_new _ _))
  rcases htrace.finalizesBy hD hD0 (Nat.mul_mod_left _ _) (hpA.handler (.block sb) hblk) h0 with
    ⟨-, hlt, -⟩ | hf
  · omega
  · exact hf

end Store

end EthCLSpecs.Proofs.Heze
