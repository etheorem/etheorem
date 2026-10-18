import EthCLSpecs.Proofs.Heze.BlockRootsRun

/-!
# `EthCLSpecs.Proofs.Heze.RunWeighs`: the weigh steps of a chain run

`process_justification_and_finalization` runs once per epoch, in the slot step that ends the
epoch. This module states the facts about a chain run that the FFG refinement
(`FFGRefines.lean`) reads off these steps.

## The run is a function

`SlotStep` and `BlockStep` are relations, but each spec function is a function. So a run
from one state through one list of steps ends in one state (`ChainRun.det`). A run splits at
any point of its list of steps (`ChainRun.split`).

## Slots and epochs

A slot step adds one to the slot, and a block step keeps it (`SlotStep.slot`,
`BlockStep.slot`). Below the bound `2 ^ 64 - 1` no increment wraps. So the slot does not go
down along a run, and every block of a run has a slot at or after the start slot
(`ChainRun.slot_le`, `ChainRun.blocks_slot_ge`).

Only the slot step at the end of an epoch changes the four checkpoint fields. So two states
of a run in one epoch have the same fields (`ChainRun.ckView_of_epoch`).

## The weigh state

`WeighAt hi steps st₀ e u`: the run reaches `u` at the last slot of epoch `e`, and the next
step is a slot step. The state `u` is unique (`WeighAt.unique`). In the next slot step,
`processSlot` gives `slotWrite u`, and `process_justification_and_finalization` runs on it
(`SlotStep.boundary`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_bind_eq_ok run_bind_eq_ok_pure
  runPure_of_run_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Slot)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The run is a function -/

omit [Config] [CryptoBackend] in
/-- Two successful runs of one action from one box end in one state value. -/
theorem state_eq_of_run {x : HezeRun Unit} {u a b : BeaconState}
    (ha : x.run (pureState u) = .ok ((), pureState a))
    (hb : x.run (pureState u) = .ok ((), pureState b)) : a = b := by
  rw [ha] at hb
  injection hb with hb
  injection hb with _ hb
  exact pureState_inj hb

/-- A slot step is a function of its start state. -/
theorem SlotStep.det {u x y : BeaconState} (hx : SlotStep u x) (hy : SlotStep u y) : x = y := by
  obtain ⟨a1, a2, h1, h2, h3⟩ := hx
  obtain ⟨b1, b2, k1, k2, k3⟩ := hy
  have e1 := state_eq_of_run h1 k1
  subst e1
  have e2 : a2 = b2 := by
    split at h2
    · rename_i hc
      rw [if_pos hc] at k2
      exact state_eq_of_run h2 k2
    · rename_i hc
      rw [if_neg hc] at k2
      rw [h2, k2]
  subst e2
  exact pureState_inj (h3.trans k3.symm)

/-- A block step is a function of its start state. -/
theorem BlockStep.det {sb : EthCLSpecs.Heze.SignedBeaconBlock} {v : Bool} {u x y : BeaconState}
    (hx : BlockStep sb v u x) (hy : BlockStep sb v u y) : x = y :=
  state_eq_of_run hx.2.1 hy.2.1

/-- A chain run is a function of its start state and its steps. -/
theorem ChainRun.det {hi : Nat} {q : List ChainStep} {u x y : BeaconState}
    (hx : ChainRun hi q u x) (hy : ChainRun hi q u y) : x = y := by
  induction hx generalizing y with
  | nil => cases hy; rfl
  | slot _ hstep _ ih =>
    cases hy with
    | slot _ hstep' hrest' =>
      rw [hstep.det hstep'] at ih
      exact ih hrest'
  | block sb v hstep _ ih =>
    cases hy with
    | block _ _ hstep' hrest' =>
      rw [hstep.det hstep'] at ih
      exact ih hrest'

/-- A run splits at any point of its steps. -/
theorem ChainRun.split {hi : Nat} {p q : List ChainStep} {u w : BeaconState}
    (h : ChainRun hi (p ++ q) u w) : ∃ m, ChainRun hi p u m ∧ ChainRun hi q m w := by
  induction p generalizing u with
  | nil => exact ⟨u, .nil u, h⟩
  | cons x p ih =>
    cases h with
    | slot hlt hstep hrest =>
      obtain ⟨m, h1, h2⟩ := ih hrest
      exact ⟨m, .slot hlt hstep h1, h2⟩
    | block sb v hstep hrest =>
      obtain ⟨m, h1, h2⟩ := ih hrest
      exact ⟨m, .block sb v hstep h1, h2⟩

/-! ## Slots and epochs -/

/-- A slot step adds one to the slot. -/
theorem SlotStep.slot {u u' : BeaconState} (h : SlotStep u u') (hlt : u.slot.toNat + 1 < 2 ^ 64) :
    u'.slot.toNat = u.slot.toNat + 1 := by
  rw [h.hdr.2.2, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]

/-- A block step keeps the slot, and the block slot is the slot. -/
theorem BlockStep.slot {sb : EthCLSpecs.Heze.SignedBeaconBlock} {vr : Bool} {u u' : BeaconState}
    (h : BlockStep sb vr u u') :
    u'.slot.toNat = u.slot.toNat ∧ sb.message.slot.toNat = u.slot.toNat := by
  obtain ⟨hs, -, -, -, es⟩ := h.hdr
  exact ⟨congrArg UInt64.toNat es, congrArg UInt64.toNat hs⟩

/-- Along a run below the bound, the slot does not decrease, and each block of the run has a
slot at or after the start slot. -/
theorem ChainRun.slot_le {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    u.slot.toNat ≤ w.slot.toNat ∧ ∀ b ∈ blocksOf q, u.slot.toNat ≤ b.slot.toNat ∧
      b.slot.toNat ≤ w.slot.toNat := by
  induction h with
  | nil => exact ⟨Nat.le_refl _, fun b hb => absurd hb List.not_mem_nil⟩
  | @slot _ st _ _ hlt hstep _ ih =>
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    refine ⟨by omega, fun b hb => ?_⟩
    have := ih.2 b hb
    omega
  | block sb v hstep _ ih =>
    obtain ⟨hs, hb⟩ := hstep.slot
    refine ⟨by omega, fun b hm => ?_⟩
    rcases List.mem_cons.mp hm with he | hm
    · rw [he]
      omega
    · have := ih.2 b hm
      omega

/-- The blocks of a run below the bound have slots at or after the start slot. -/
theorem ChainRun.blocks_slot_ge {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    ∀ b ∈ blocksOf q, u.slot.toNat ≤ b.slot.toNat := fun b hb => ((h.slot_le hhi).2 b hb).1

/-- A slot step keeps the four checkpoint fields when it does not end an epoch. -/
theorem SlotStep.ckView_of_not_boundary {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch ≠ 0) :
    ckView (pureState u') = ckView (pureState u) := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := congrArg Prod.fst (processSlot_frame_ord h1)
  have s1 := congrArg Prod.snd (processSlot_frame_ord h1)
  change ckView (pureState st1) = ckView (pureState u) at e1
  change st1.slot = u.slot at s1
  split at h2
  · rename_i htest
    exact absurd ((epochTest_iff st1.slot (by rw [s1]; exact hlt)).mp htest) (by rw [s1]; exact hb)
  · subst h2
    rw [← e1, hst']
    rfl

omit [HasherTag] [Config] [CryptoBackend] in
/-- At a slot step that does not end an epoch, the epoch stays. -/
theorem epoch_succ_of_not_boundary {x : Nat} (hb : (x + 1) % slotsPerEpoch ≠ 0) :
    (x + 1) / slotsPerEpoch = x / slotsPerEpoch :=
  succ_div_of_mod_ne hb

/-- Along a run below the bound, the epoch does not decrease. -/
theorem ChainRun.epoch_le {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    u.slot.toNat / slotsPerEpoch ≤ w.slot.toNat / slotsPerEpoch :=
  Nat.div_le_div_right (h.slot_le hhi).1

/-- Two states of a run in one epoch have the same four checkpoint fields. A slot step that
ends an epoch moves to the next epoch, and the epoch does not decrease after it. -/
theorem ChainRun.ckView_of_epoch {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w)
    (he : u.slot.toNat / slotsPerEpoch = w.slot.toNat / slotsPerEpoch) :
    ckView (pureState w) = ckView (pureState u) := by
  revert he
  induction h with
  | nil => intro _; rfl
  | @slot _ st st1 _ hlt hstep hrest ih =>
    intro he
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    have hle := hrest.epoch_le hhi
    by_cases hb : (st.slot.toNat + 1) % slotsPerEpoch = 0
    · exfalso
      have := succ_div_of_mod_eq hb
      rw [← hs] at this
      omega
    · have hep := epoch_succ_of_not_boundary hb
      rw [← hs] at hep
      rw [ih (by omega), hstep.ckView_of_not_boundary (by omega) hb]
  | block sb v hstep _ ih =>
    intro he
    have e := processBlock_frame_ord hstep.2.1
    simp only [ordView, Prod.mk.injEq] at e
    obtain ⟨hs, -⟩ := hstep.slot
    rw [ih (by rw [hs]; exact he), e.1]

/-! ## The weigh state -/

/-- The run reaches `u` at the last slot of epoch `e`, and the next step is a slot step. -/
def WeighAt (hi : Nat) (steps : List ChainStep) (st₀ : BeaconState) (e : Nat)
    (u : BeaconState) : Prop :=
  ∃ s₁ s₂, steps = s₁ ++ .slot :: s₂ ∧ ChainRun hi s₁ st₀ u ∧
    (u.slot.toNat + 1) % slotsPerEpoch = 0 ∧ u.slot.toNat / slotsPerEpoch = e

omit [HasherTag] [Config] [CryptoBackend] in
/-- The last slot of an epoch is fixed by the epoch. -/
theorem slot_of_last {x y : Nat} (hx : (x + 1) % slotsPerEpoch = 0)
    (hy : (y + 1) % slotsPerEpoch = 0) (he : x / slotsPerEpoch = y / slotsPerEpoch) : x = y := by
  have := slotsPerEpochPos
  have ex := Nat.div_add_mod (x + 1) slotsPerEpoch
  have ey := Nat.div_add_mod (y + 1) slotsPerEpoch
  rw [hx, Nat.add_zero, succ_div_of_mod_eq hx] at ex
  rw [hy, Nat.add_zero, succ_div_of_mod_eq hy] at ey
  rw [he] at ex
  omega

/-- The weigh state of an epoch is unique. Two prefixes that reach the last slot of one epoch
are the same prefix, since a slot step adds one to the slot and the slot does not decrease. -/
theorem WeighAt.unique {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ : BeaconState} {e : Nat} {u u' : BeaconState} (h : WeighAt hi steps st₀ e u)
    (h' : WeighAt hi steps st₀ e u') : u = u' := by
  obtain ⟨s₁, s₂, hs, hr, hb, he⟩ := h
  obtain ⟨t₁, t₂, ht, hr', hb', he'⟩ := h'
  have hsl := slot_of_last hb hb' (he.trans he'.symm)
  -- A prefix that ends at a slot step followed by more steps reaches a later slot.
  have later : ∀ {a b : List ChainStep} {x y : BeaconState} (m : List ChainStep),
      b = a ++ .slot :: m → ChainRun hi a st₀ x → ChainRun hi b st₀ y →
      x.slot.toNat < y.slot.toNat := by
    intro a b x y m hab ha hb
    rw [hab] at hb
    obtain ⟨z, hz, hm⟩ := hb.split
    rw [ha.det hz] at *
    cases hm with
    | slot hlt hstep hrest =>
      have hlt' : z.slot.toNat < hi := hlt
      have h1 := hstep.slot (by omega)
      have h2 := (hrest.slot_le hhi).1
      omega
  rw [hs] at ht
  rcases List.append_eq_append_iff.mp ht with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
  · -- `t₁ = s₁ ++ m`.
    cases m with
    | nil =>
      rw [List.append_nil] at hm
      subst hm
      exact hr.det hr'
    | cons x m =>
      cases x with
      | slot =>
        have := later m hm hr hr'
        omega
      | block sb v =>
        simp at hm'
  · -- `s₁ = t₁ ++ m`.
    cases m with
    | nil =>
      rw [List.append_nil] at hm
      subst hm
      exact hr.det hr'
    | cons x m =>
      cases x with
      | slot =>
        have := later m hm hr' hr
        omega
      | block sb v =>
        simp at hm'

/-! ## The weigh step -/

/-- The target balance of epoch `e` in `u`: the total effective balance of the unslashed
validators with the target flag for `e`. Both reads are `Except`. When one of them faults, the
value is `0`. A weigh step whose run succeeds reads both without a fault (`SlotStep.weigh`), so
it never weighs that `0`. -/
def tgtBal (u : BeaconState) (e : EthCLSpecs.Heze.Epoch) : EthCLSpecs.Heze.Gwei :=
  match EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e with
  | .ok idx =>
    match EthCLSpecs.Heze.getTotalBalance (pureState u) idx with
    | .ok g => g
    | .error _ => 0
  | .error _ => 0

/-- The total active balance of `u`. The read is `Except`, and a fault gives `0`, as in
`tgtBal`. -/
def totBal (u : BeaconState) : EthCLSpecs.Heze.Gwei :=
  match EthCLSpecs.Heze.getTotalActiveBalance (pureState u) with
  | .ok g => g
  | .error _ => 0

omit [Config] [CryptoBackend] in
/-- A successful read of the total active balance returns `totBal`. -/
theorem totBal_of_ok {u : BeaconState} {g : EthCLSpecs.Heze.Gwei}
    (h : EthCLSpecs.Heze.getTotalActiveBalance (pureState u) = .ok g) : totBal u = g := by
  unfold totBal
  rw [h]

omit [Config] [CryptoBackend] in
/-- Two successful reads of a target balance return `tgtBal`. -/
theorem tgtBal_of_ok {u : BeaconState} {e : EthCLSpecs.Heze.Epoch}
    {idx : Array EthCLSpecs.Heze.ValidatorIndex} {g : EthCLSpecs.Heze.Gwei}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e = .ok idx)
    (hg : EthCLSpecs.Heze.getTotalBalance (pureState u) idx = .ok g) : tgtBal u e = g := by
  unfold tgtBal
  rw [hidx]
  dsimp only
  rw [hg]

omit [Config] [CryptoBackend] in
/-- `slotWrite` keeps the fields that the total active balance reads. -/
theorem getTotalActiveBalance_slotWrite (u : BeaconState) :
    EthCLSpecs.Heze.getTotalActiveBalance (pureState (slotWrite u)) =
      EthCLSpecs.Heze.getTotalActiveBalance (pureState u) := rfl

omit [Config] [CryptoBackend] in
/-- `slotWrite` keeps the fields that the participant read reads. -/
theorem getUnslashedParticipatingIndices_slotWrite (u : BeaconState) (flag : Nat)
    (e : EthCLSpecs.Heze.Epoch) :
    EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState (slotWrite u)) flag e =
      EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u) flag e := rfl

omit [Config] [CryptoBackend] in
/-- `slotWrite` keeps the fields that a balance sum reads. -/
theorem getTotalBalance_slotWrite (u : BeaconState)
    (idx : Array EthCLSpecs.Heze.ValidatorIndex) :
    EthCLSpecs.Heze.getTotalBalance (pureState (slotWrite u)) idx =
      EthCLSpecs.Heze.getTotalBalance (pureState u) idx := rfl

omit [Config] [CryptoBackend] in
/-- `slotWrite` keeps the fields that a target balance reads. -/
theorem tgtBal_slotWrite (u : BeaconState) (e : EthCLSpecs.Heze.Epoch) :
    tgtBal (slotWrite u) e = tgtBal u e := rfl

/-- At the end of an epoch, a slot step runs `processJustificationAndFinalization` on
`slotWrite u`. The four checkpoint fields of the end state are those that it writes. -/
theorem SlotStep.boundary {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch = 0) :
    ∃ mid, runPure (EthCLSpecs.Heze.processJustificationAndFinalization
        (StateTransition := HezeRun)) (slotWrite u) = .ok ((), mid) ∧
      ckView (pureState u') = ckView (pureState mid) := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := processSlot_run_eq h1
  subst e1
  split at h2
  rotate_left
  · rename_i hc
    exact absurd ((epochTest_iff u.slot hlt).mpr hb) hc
  rw [processEpoch_eq_jf] at h2
  obtain ⟨⟨⟩, mid, hjf, hrest⟩ :=
    run_bind_eq_ok_pure keepsUncached_processJustificationAndFinalization h2
  have er := congrArg Prod.fst (processEpochAfterJF_frame_ord hrest)
  refine ⟨mid, runPure_of_run_ok hjf, ?_⟩
  have hck : ckView (pureState u') = ckView (pureState st2) := by
    rw [hst']
    rfl
  exact hck.trans er

/-- A slot step at the end of epoch `E`. In the first two epochs the four checkpoint fields
stay. After them the weigh step writes them, on the balances of `u`. The run reads the three
balances without a fault, so they are `totBal` and `tgtBal`. The two `getBlockRoot` reads run
on `slotWrite u`. -/
theorem SlotStep.weigh {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch = 0) :
    (u.slot.toNat / slotsPerEpoch ≤ 1 ∧ ckView (pureState u') = ckView (pureState u)) ∨
    (2 ≤ u.slot.toNat / slotsPerEpoch ∧ ∃ pr cr : EthCLSpecs.Heze.Root,
      let tot := totBal u
      let jp := decide ((tgtBal u (EthCLSpecs.Heze.previousEpochOf (pureState u))).toNat * 3 ≥
        tot.toNat * 2)
      let jc := decide ((tgtBal u (EthCLSpecs.Heze.currentEpochOf (pureState u))).toNat * 3 ≥
        tot.toNat * 2)
      let bits1 : Bitvector EthCLSpecs.Heze.Const.justificationBitsLength :=
        { data := u.justificationBits.data <<< 1 }
      let bits2 := if jp then bitSet bits1 1 true else bits1
      let bits3 := if jc then bitSet bits2 0 true else bits2
      u'.previousJustifiedCheckpoint = u.currentJustifiedCheckpoint ∧
      u'.currentJustifiedCheckpoint =
        (if jc then { epoch := EthCLSpecs.Heze.currentEpochOf (pureState u), root := cr }
         else if jp then { epoch := EthCLSpecs.Heze.previousEpochOf (pureState u), root := pr }
         else u.currentJustifiedCheckpoint) ∧
      u'.justificationBits = bits3 ∧
      u'.finalizedCheckpoint = finalizeRules bits3 u.previousJustifiedCheckpoint
        u.currentJustifiedCheckpoint u.finalizedCheckpoint
        (EthCLSpecs.Heze.currentEpochOf (pureState u)) ∧
      (jp = true → runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun)
        (pureState (slotWrite u)) (EthCLSpecs.Heze.previousEpochOf (pureState u))) (slotWrite u)
          = .ok (pr, slotWrite u)) ∧
      (jc = true → runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun)
        (pureState (slotWrite u)) (EthCLSpecs.Heze.currentEpochOf (pureState u))) (slotWrite u)
          = .ok (cr, slotWrite u))) := by
  obtain ⟨mid, hjf, hck⟩ := h.boundary hlt hb
  simp only [ckView, Prod.mk.injEq] at hck
  obtain ⟨ep, ec, ef, eb⟩ := hck
  change u'.previousJustifiedCheckpoint = mid.previousJustifiedCheckpoint at ep
  change u'.currentJustifiedCheckpoint = mid.currentJustifiedCheckpoint at ec
  change u'.finalizedCheckpoint = mid.finalizedCheckpoint at ef
  change u'.justificationBits = mid.justificationBits at eb
  have hE := currentEpochOf_toNat u
  change (EthCLSpecs.Heze.currentEpochOf (pureState u)).toNat = u.slot.toNat / slotsPerEpoch at hE
  by_cases hg : EthCLSpecs.Heze.currentEpochOf (pureState (slotWrite u)) ≤
      EthCLSpecs.Heze.Const.genesisEpoch + 1
  · rw [processJustificationAndFinalization_run_eq, if_pos hg] at hjf
    injection hjf with hjf
    injection hjf with _ hm
    subst hm
    refine .inl ⟨?_, ?_⟩
    · have hg' := UInt64.le_iff_toNat_le.mp hg
      change (EthCLSpecs.Heze.currentEpochOf (pureState u)).toNat ≤ _ at hg'
      rw [hE] at hg'
      simpa [EthCLSpecs.Heze.Const.genesisEpoch] using hg'
    · simp only [ckView, Prod.mk.injEq]
      exact ⟨ep, ec, ef, eb⟩
  · refine .inr ⟨?_, ?_⟩
    · have hg' : ¬ (EthCLSpecs.Heze.currentEpochOf (pureState u)).toNat ≤ 1 := fun h' =>
        hg (UInt64.le_iff_toNat_le.mpr (by simpa [EthCLSpecs.Heze.Const.genesisEpoch] using h'))
      omega
    -- The five reads succeed. `slotWrite` keeps what they read, so they are the reads of `u`.
    obtain ⟨prevIdx, currIdx, tot, prev, curr, h1, h2, h3, h4, h5, hjf⟩ :=
      processJustificationAndFinalization_run_ok hjf hg
    rw [getUnslashedParticipatingIndices_slotWrite] at h1 h2
    rw [getTotalActiveBalance_slotWrite] at h3
    rw [getTotalBalance_slotWrite] at h4 h5
    have et : totBal u = tot := totBal_of_ok h3
    have etp : tgtBal u (EthCLSpecs.Heze.previousEpochOf (pureState u)) = prev :=
      tgtBal_of_ok h1 h4
    have etc : tgtBal u (EthCLSpecs.Heze.currentEpochOf (pureState u)) = curr :=
      tgtBal_of_ok h2 h5
    obtain ⟨pr, cr, hw⟩ := weighJustificationAndFinalization_run_ok _ _ _ _ _ hjf
    refine ⟨pr, cr, ?_⟩
    simp only [et, etp, etc]
    exact ⟨ep.trans hw.1, ec.trans hw.2.1, eb.trans hw.2.2.1, ef.trans hw.2.2.2.1,
      hw.2.2.2.2.1, hw.2.2.2.2.2⟩

/-- Across one epoch boundary after the first two epochs, the previous justified checkpoint
is the old current one. The weigh step writes it, and the steps in each epoch keep it. -/
theorem ChainRun.prevJ_next_epoch {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {x y : BeaconState} (h : ChainRun hi q x y)
    (he : y.slot.toNat / slotsPerEpoch = x.slot.toNat / slotsPerEpoch + 1)
    (h2 : 2 ≤ x.slot.toNat / slotsPerEpoch) :
    y.previousJustifiedCheckpoint = x.currentJustifiedCheckpoint := by
  revert he h2
  induction h with
  | nil => intro he; omega
  | @slot _ st st1 _ hlt hstep hrest ih =>
    intro he h2
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    by_cases hb : (st.slot.toNat + 1) % slotsPerEpoch = 0
    · have hep := succ_div_of_mod_eq hb
      rw [← hs] at hep
      rcases hstep.weigh (by omega) hb with ⟨h1, -⟩ | ⟨-, pr, cr, hw⟩
      · omega
      · have hck := hrest.ckView_of_epoch hhi (by omega)
        simp only [ckView, Prod.mk.injEq] at hck
        exact hck.1.trans hw.1
    · have hep := epoch_succ_of_not_boundary hb
      rw [← hs] at hep
      have hck := hstep.ckView_of_not_boundary (by omega) hb
      simp only [ckView, Prod.mk.injEq] at hck
      rw [ih (by omega) (by omega)]
      exact hck.2.1
  | block sb v hstep _ ih =>
    intro he h2
    have e := processBlock_frame_ord hstep.2.1
    simp only [ordView, ckView, Prod.mk.injEq] at e
    obtain ⟨hs, -⟩ := hstep.slot
    rw [ih (by rw [hs]; exact he) (by rw [hs]; exact h2)]
    exact e.1.2.1

end

end EthCLSpecs.Proofs.Heze
