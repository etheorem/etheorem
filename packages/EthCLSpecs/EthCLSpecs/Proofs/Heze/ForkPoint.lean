import EthCLSpecs.Proofs.Heze.FFGRefines

/-!
# `EthCLSpecs.Proofs.Heze.ForkPoint`: two chain runs split at their fork point

Two chain runs start at the anchor state. Their steps agree up to a point and then differ.
This module names that point and states what the two runs share before it.

## The steps up to the fork

A block step reads only the message of its block. The signature and the `validateResult` flag
change no state. So this module compares two steps by `stepMsg`: a slot step, or the message of
a block. `fork_split` cuts two step lists at the end
of their longest common prefix under `stepMsg`. Two runs from one state through two prefixes
with one `stepMsg` list end in one state (`ChainRun.det_msg`). That state is the fork point
`st₀` (`ForkAt`).

## What the two runs share

Every block after the fork has a slot at or after the slot of `st₀`. So the two runs have one
root at each slot before the slot of `st₀` (`ForkAt.rootAtSlot_eq`). A weigh state before the
slot of `st₀` is a state of both prefixes. So the two runs have one weigh state at its epoch
(`ForkAt.weighAt`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState BeaconBlock SignedBeaconBlock)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

/-! ## Steps by their message -/

section Msg
variable [Preset]

/-- A step without its signature: `none` for a slot step, the block message for a block
step. -/
def stepMsg : ChainStep → Option BeaconBlock
  | .slot => none
  | .block sb _ => some sb.message

/-- The blocks of a run are the messages of its block steps. -/
theorem blocksOf_eq_filterMap : ∀ steps : List ChainStep, blocksOf steps = steps.filterMap stepMsg
  | [] => rfl
  | .slot :: rest => blocksOf_eq_filterMap rest
  | .block sb _ :: rest => congrArg (sb.message :: ·) (blocksOf_eq_filterMap rest)

/-- Two step lists with one list of messages have one list of blocks. -/
theorem blocksOf_eq_of_msg {p q : List ChainStep} (h : p.map stepMsg = q.map stepMsg) :
    blocksOf p = blocksOf q := by
  rw [blocksOf_eq_filterMap, blocksOf_eq_filterMap]
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons _ _ => cases h
  | cons x p ih =>
    cases q with
    | nil => cases h
    | cons y q =>
      obtain ⟨hxy, hpq⟩ := List.cons.inj h
      rw [List.filterMap_cons, List.filterMap_cons, hxy, ih hpq]

/-- The first steps of two lists differ by their messages, or a list ends. -/
def Diverge (r₁ r₂ : List ChainStep) : Prop :=
  ∀ x₁ x₂ t₁ t₂, r₁ = x₁ :: t₁ → r₂ = x₂ :: t₂ → stepMsg x₁ ≠ stepMsg x₂

/-- Two step lists split at the end of their longest common prefix under `stepMsg`. -/
theorem fork_split : ∀ steps₁ steps₂ : List ChainStep, ∃ p₁ r₁ p₂ r₂,
    steps₁ = p₁ ++ r₁ ∧ steps₂ = p₂ ++ r₂ ∧ p₁.map stepMsg = p₂.map stepMsg ∧ Diverge r₁ r₂
  | [], steps₂ => ⟨[], [], [], steps₂, rfl, rfl, rfl, fun _ _ _ _ h => by cases h⟩
  | x₁ :: t₁, [] => ⟨[], x₁ :: t₁, [], [], rfl, rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
  | x₁ :: t₁, x₂ :: t₂ => by
    by_cases hx : stepMsg x₁ = stepMsg x₂
    · obtain ⟨p₁, r₁, p₂, r₂, e₁, e₂, hm, hd⟩ := fork_split t₁ t₂
      refine ⟨x₁ :: p₁, r₁, x₂ :: p₂, r₂, by rw [e₁]; rfl, by rw [e₂]; rfl, ?_, hd⟩
      simp only [List.map_cons, hx, hm]
    · refine ⟨[], x₁ :: t₁, [], x₂ :: t₂, rfl, rfl, rfl, fun y₁ y₂ u₁ u₂ h₁ h₂ => ?_⟩
      cases h₁
      cases h₂
      exact hx

end Msg

/-! ## Runs by their messages -/

section Runs
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- Two block steps of one message from one state end in one state, whatever the signatures
and the flags. -/
theorem BlockStep.det_msg {sb sb' : SignedBeaconBlock} {v v' : Bool} {u x y : BeaconState}
    (hx : BlockStep sb v u x) (hy : BlockStep sb' v' u y) (hm : sb.message = sb'.message) :
    x = y := by
  have h2 := hy.2.1
  rw [← hm] at h2
  exact state_eq_of_run hx.2.1 h2

/-- Two runs from one state through two step lists with one list of messages end in one
state. -/
theorem ChainRun.det_msg {hi : Nat} {p : List ChainStep} {u x : BeaconState}
    (hx : ChainRun hi p u x) :
    ∀ {q : List ChainStep} {y : BeaconState}, ChainRun hi q u y →
      p.map stepMsg = q.map stepMsg → x = y := by
  induction hx with
  | nil =>
    intro q y hy hm
    cases q with
    | nil => cases hy; rfl
    | cons _ _ => cases hm
  | slot _ hstep _ ih =>
    intro q y hy hm
    cases hy with
    | nil => cases hm
    | slot _ hstep' hrest' =>
      rw [hstep.det hstep'] at ih
      exact ih hrest' (List.cons.inj hm).2
    | block sb v _ _ => cases (List.cons.inj hm).1
  | block sb v hstep _ ih =>
    intro q y hy hm
    cases hy with
    | nil => cases hm
    | slot _ _ _ => cases (List.cons.inj hm).1
    | block sb' v' hstep' hrest' =>
      have hmsg : sb.message = sb'.message := Option.some.inj (List.cons.inj hm).1
      rw [hstep.det_msg hstep' hmsg] at ih
      exact ih hrest' (List.cons.inj hm).2

/-- The fork point of two runs. Both runs reach the state `st₀` at the end of the longest
common prefix of their steps under `stepMsg`. Run `i` has the steps `pᵢ ++ rᵢ`. -/
structure ForkAt (hi : Nat) (A : BeaconState) (steps₁ steps₂ : List ChainStep)
    (st₀ : BeaconState) (p₁ r₁ p₂ r₂ : List ChainStep) : Prop where
  eq₁ : steps₁ = p₁ ++ r₁
  eq₂ : steps₂ = p₂ ++ r₂
  msg : p₁.map stepMsg = p₂.map stepMsg
  run₁ : ChainRun hi p₁ A st₀
  run₂ : ChainRun hi p₂ A st₀
  div : Diverge r₁ r₂

/-- Two runs from one state have a fork point. -/
theorem ChainRun.forkAt {hi : Nat} {A X Y : BeaconState} {steps₁ steps₂ : List ChainStep}
    (h₁ : ChainRun hi steps₁ A X) (h₂ : ChainRun hi steps₂ A Y) :
    ∃ st₀ p₁ r₁ p₂ r₂, ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂ := by
  obtain ⟨p₁, r₁, p₂, r₂, e₁, e₂, hm, hd⟩ := fork_split steps₁ steps₂
  rw [e₁] at h₁
  rw [e₂] at h₂
  obtain ⟨m₁, hp₁, -⟩ := h₁.split
  obtain ⟨m₂, hp₂, -⟩ := h₂.split
  have he : m₁ = m₂ := hp₁.det_msg hp₂ hm
  subst he
  exact ⟨m₁, p₁, r₁, p₂, r₂, ⟨e₁, e₂, hm, hp₁, hp₂, hd⟩⟩

/-- The fork point with the two runs swapped. -/
theorem ForkAt.symm {hi : Nat} {A st₀ : BeaconState} {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) :
    ForkAt hi A steps₂ steps₁ st₀ p₂ r₂ p₁ r₁ :=
  ⟨F.eq₂, F.eq₁, F.msg.symm, F.run₂, F.run₁,
    fun x₂ x₁ t₂ t₁ h₂ h₁ he => F.div x₁ x₂ t₁ t₂ h₁ h₂ he.symm⟩

/-- The rest of run 1 after the fork point runs from `st₀`. -/
theorem ForkAt.rest₁ {hi : Nat} {A X st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h : ChainRun hi steps₁ A X) :
    ChainRun hi r₁ st₀ X := by
  rw [F.eq₁] at h
  obtain ⟨m, hm, hr⟩ := h.split
  rw [← F.run₁.det hm] at hr
  exact hr

/-- Before the slot of the fork point, the two runs have one root at each slot. -/
theorem ForkAt.rootAtSlot_eq {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X Y st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X)
    (h₂ : ChainRun hi steps₂ A Y) {s : Nat} (hs : s < st₀.slot.toNat) :
    rootAtSlot A steps₁ s = rootAtSlot A steps₂ s := by
  have g₁ := (F.rest₁ h₁).blocks_slot_ge hhi
  have g₂ := (F.symm.rest₁ h₂).blocks_slot_ge hhi
  rw [F.eq₁, F.eq₂, rootAtSlot_append_of_lt A p₁ r₁ s (fun b hb => by have := g₁ b hb; omega),
    rootAtSlot_append_of_lt A p₂ r₂ s (fun b hb => by have := g₂ b hb; omega)]
  unfold rootAtSlot
  rw [blocksOf_eq_of_msg F.msg]

/-- A weigh state of run 1 before the slot of the fork point is the weigh state of run 2 at
its epoch. The prefix of the weigh state ends before the fork. So run 2 has a prefix with the
same messages. -/
theorem ForkAt.weighAt {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) {e : Nat} {u : BeaconState} (hw : WeighAt hi steps₁ A e u)
    (hlt : u.slot.toNat < st₀.slot.toNat) : WeighAt hi steps₂ A e u := by
  obtain ⟨s₁, s₂, hs, hr, hb, he⟩ := hw
  rw [F.eq₁] at hs
  rcases List.append_eq_append_iff.mp hs with ⟨m, hm, -⟩ | ⟨m, hm, hm'⟩
  · -- `s₁ = p₁ ++ m`: then `u` comes after `st₀`, a contradiction.
    rw [hm] at hr
    obtain ⟨z, hz, hrest⟩ := hr.split
    rw [← F.run₁.det hz] at hrest
    have := (hrest.slot_le hhi).1
    omega
  · -- `p₁ = s₁ ++ m`. Then `m` starts with the slot step after `u`.
    cases m with
    | nil =>
      rw [List.append_nil] at hm
      subst hm
      rw [hr.det F.run₁] at hlt
      exact absurd hlt (Nat.lt_irrefl _)
    | cons x m =>
      have hx : x = .slot := (List.cons.inj hm').1.symm
      subst hx
      -- Find the prefix of run 2 with the messages of `s₁ ++ .slot :: m`.
      have hmap := F.msg
      rw [hm, List.map_append] at hmap
      obtain ⟨q₁, q₂, hq, hq₁, hq₂⟩ := List.map_eq_append_iff.mp hmap.symm
      cases q₂ with
      | nil => cases hq₂
      | cons y q₂ =>
        have hy : stepMsg y = none := (List.cons.inj hq₂).1
        have hys : y = .slot := by
          cases y with
          | slot => rfl
          | block _ _ => cases hy
        subst hys
        have hrun₂ := F.run₂
        rw [hq] at hrun₂
        obtain ⟨u', hu', -⟩ := hrun₂.split
        have e' : u = u' := hr.det_msg hu' hq₁.symm
        subst e'
        exact ⟨q₁, q₂ ++ r₂, by rw [F.eq₂, hq]; simp, hu', hb, he⟩

/-! ## The weigh states of the shared prefix -/

omit [HasherTag] [Config] [CryptoBackend] in
/-- The last slot of epoch `e` ends the epoch and lies in `e`. -/
theorem lastSlot_facts (e : Nat) :
    ((e + 1) * slotsPerEpoch - 1 + 1) % slotsPerEpoch = 0 ∧
      ((e + 1) * slotsPerEpoch - 1) / slotsPerEpoch = e := by
  have hp := slotsPerEpochPos
  have h1 : (e + 1) * slotsPerEpoch - 1 + 1 = (e + 1) * slotsPerEpoch :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos e) hp)
  have k : (e + 1) * slotsPerEpoch = e * slotsPerEpoch + slotsPerEpoch := by
    rw [Nat.add_mul, Nat.one_mul]
  refine ⟨by rw [h1]; exact Nat.mul_mod_left _ _, Nat.div_eq_of_lt_le ?_ ?_⟩
  · omega
  · omega

/-- A run has a weigh state at epoch `e` when it starts at or before the last slot of `e` and
ends after that slot. -/
theorem ChainRun.weighAt_of_cross {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi steps u w) (e : Nat)
    (hu : u.slot.toNat ≤ (e + 1) * slotsPerEpoch - 1)
    (hw : (e + 1) * slotsPerEpoch ≤ w.slot.toNat) : ∃ v, WeighAt hi steps u e v := by
  obtain ⟨hb, he⟩ := lastSlot_facts e
  have hT1 : 1 ≤ (e + 1) * slotsPerEpoch := Nat.mul_pos (Nat.succ_pos e) slotsPerEpochPos
  -- Name the product, so that `omega` reads it as one number.
  generalize hT : (e + 1) * slotsPerEpoch = T at hu hw hb he hT1
  revert hu hw
  induction h with
  | nil => intro hu hw; omega
  | @slot steps st st1 _ hlt hstep hrest ih =>
    intro hu hw
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    by_cases heq : st.slot.toNat = T - 1
    · exact ⟨st, [], steps, rfl, .nil _, by rw [heq]; exact hb, by rw [heq]; exact he⟩
    · obtain ⟨v, s₁, s₂, hss, hr, hvb, hve⟩ := ih (by omega) hw
      exact ⟨v, .slot :: s₁, s₂, by rw [hss]; rfl, .slot hlt hstep hr, hvb, hve⟩
  | block sb v hstep hrest ih =>
    intro hu hw
    obtain ⟨hs, -⟩ := hstep.slot
    obtain ⟨x, s₁, s₂, hss, hr, hvb, hve⟩ := ih (by omega) hw
    exact ⟨x, .block sb v :: s₁, s₂, by rw [hss]; rfl, .block sb v hstep hr, hvb, hve⟩

/-- At an epoch whose weigh state comes before the slot of the fork point, the two runs weigh
with one state. -/
theorem ForkAt.stakeState_eq {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) {e : Nat} {u : BeaconState}
    (hw : WeighAt hi steps₁ A e u) (hlt : u.slot.toNat < st₀.slot.toNat) :
    stakeState hi steps₁ A e = stakeState hi steps₂ A e := by
  rw [stakeState_of_weigh hhi hw, stakeState_of_weigh hhi (F.weighAt hhi hw hlt)]

/-- At an epoch that starts before the slot of the fork point, the two runs have one
checkpoint. -/
theorem ForkAt.cpOf_eq {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X Y st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X)
    (h₂ : ChainRun hi steps₂ A Y) {e : Nat} (he : e * slotsPerEpoch < st₀.slot.toNat) :
    cpOf A steps₁ e = cpOf A steps₂ e := by
  unfold cpOf chainRoot
  by_cases h0 : e = 0
  · subst h0
    simp only [if_true]
    split
    · rfl
    · exact congrArg (fun r : EthCLSpecs.Heze.Root => ({ epoch := 0, root := r } : Cp))
        (F.rootAtSlot_eq hhi h₁ h₂ (s := 0) (by omega))
  · simp only [if_neg h0]
    rw [F.rootAtSlot_eq hhi h₁ h₂ he]

/-- More steps keep a weigh state. -/
theorem WeighAt.append {hi : Nat} {steps : List ChainStep} {A : BeaconState} {e : Nat}
    {u : BeaconState} (h : WeighAt hi steps A e u) (r : List ChainStep) :
    WeighAt hi (steps ++ r) A e u := by
  obtain ⟨s₁, s₂, hs, hr, hb, he⟩ := h
  exact ⟨s₁, s₂ ++ r, by rw [hs]; simp, hr, hb, he⟩

/-- Take an epoch `e` from the anchor epoch on that ends before the slot of the fork point.
Its weigh step justifies the same checkpoints in the two runs. -/
theorem ForkAt.weighCps_eq {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X Y st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X)
    (h₂ : ChainRun hi steps₂ A Y) {e : Nat} (hA : epochOf A ≤ e)
    (he : (e + 1) * slotsPerEpoch ≤ st₀.slot.toNat) :
    weighCps hi steps₁ A e = weighCps hi steps₂ A e := by
  have hp := slotsPerEpochPos
  have k : (e + 1) * slotsPerEpoch = e * slotsPerEpoch + slotsPerEpoch := by
    rw [Nat.add_mul, Nat.one_mul]
  -- Find the weigh state of `e` in the prefix of run 1.
  have hA' : A.slot.toNat ≤ (e + 1) * slotsPerEpoch - 1 := by
    have h1 := Nat.lt_mul_div_succ A.slot.toNat hp
    have h2 : (A.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤ (e + 1) * slotsPerEpoch :=
      Nat.mul_le_mul_right _ (by unfold epochOf at hA; omega)
    rw [Nat.mul_comm] at h1
    omega
  obtain ⟨u, hw⟩ := F.run₁.weighAt_of_cross hhi e hA' he
  have hw₁ : WeighAt hi steps₁ A e u := F.eq₁ ▸ hw.append r₁
  have hu : u.slot.toNat < st₀.slot.toNat := by
    obtain ⟨-, -, -, -, hb, hue⟩ := hw
    obtain ⟨hb', he'⟩ := lastSlot_facts e
    have := slot_of_last hb hb' (hue.trans he'.symm)
    omega
  have hs := F.stakeState_eq hhi hw₁ hu
  have hc₀ := F.cpOf_eq hhi h₁ h₂ (e := e) (by omega)
  have hc₁ := F.cpOf_eq hhi h₁ h₂ (e := e - 1) (by
    have : (e - 1) * slotsPerEpoch ≤ e * slotsPerEpoch := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega)
  unfold weighCps
  rw [hs, hc₀, hc₁]

/-- The blocks below slot `T` of a run that starts below `T` with a step `x`. A block step puts
its block first. After a slot step, every block has a slot past the start slot. -/
theorem ChainRun.filter_head {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {x : ChainStep}
    {t : List ChainStep} {u w : BeaconState} (h : ChainRun hi (x :: t) u w) {T : Nat}
    (hT : u.slot.toNat < T) :
    (∀ sb v, x = .block sb v → ∃ l, (blocksOf (x :: t)).filter (fun b => b.slot.toNat < T)
      = sb.message :: l ∧ sb.message.slot.toNat = u.slot.toNat) ∧
    (x = .slot → ∀ b ∈ (blocksOf (x :: t)).filter (fun b => b.slot.toNat < T),
      u.slot.toNat < b.slot.toNat) := by
  cases h with
  | slot hlt hstep hrest =>
    refine ⟨fun _ _ hx => (by cases hx), fun _ b hb => ?_⟩
    have hlt' : u.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    have := hrest.blocks_slot_ge hhi b (List.mem_filter.mp hb).1
    omega
  | block sb v hstep hrest =>
    refine ⟨fun sb' v' hx => ?_, fun hx => (by cases hx)⟩
    cases hx
    obtain ⟨-, hb⟩ := hstep.slot
    refine ⟨(blocksOf t).filter (fun b => b.slot.toNat < T), ?_, hb⟩
    change (sb.message :: blocksOf t).filter _ = _
    rw [List.filter_cons_of_pos (by simpa [hb] using hT)]

/-- **The fork point comes late.** The two runs reach slot `T`, and their blocks below `T`
agree. Then the fork point is at or after `T`. A fork before `T` starts with two different
blocks, or with a slot step and a block. Then the blocks below `T` differ. -/
theorem ForkAt.slot_ge {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X Y st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X)
    (h₂ : ChainRun hi steps₂ A Y) {T : Nat} (hX : T ≤ X.slot.toNat) (hY : T ≤ Y.slot.toNat)
    (hagree : (blocksOf steps₁).filter (fun b => b.slot.toNat < T) =
      (blocksOf steps₂).filter (fun b => b.slot.toNat < T)) :
    T ≤ st₀.slot.toNat := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have R₁ := F.rest₁ h₁
  have R₂ := F.symm.rest₁ h₂
  -- The blocks below `T` after the fork agree.
  have hrest : (blocksOf r₁).filter (fun b => b.slot.toNat < T) =
      (blocksOf r₂).filter (fun b => b.slot.toNat < T) := by
    rw [F.eq₁, F.eq₂, blocksOf_append, blocksOf_append, List.filter_append, List.filter_append,
      blocksOf_eq_of_msg F.msg] at hagree
    exact List.append_cancel_left hagree
  -- Both runs continue after the fork.
  cases r₁ with
  | nil => cases R₁; omega
  | cons x₁ t₁ =>
    cases r₂ with
    | nil => cases R₂; omega
    | cons x₂ t₂ =>
      have hd := F.div x₁ x₂ t₁ t₂ rfl rfl
      obtain ⟨b₁, s₁⟩ := R₁.filter_head hhi hlt
      obtain ⟨b₂, s₂⟩ := R₂.filter_head hhi hlt
      cases x₁ with
      | slot =>
        cases x₂ with
        | slot => exact hd rfl
        | block sb v =>
          obtain ⟨l, hl, hsl⟩ := b₂ sb v rfl
          have := s₁ rfl sb.message (by rw [hrest, hl]; exact List.mem_cons_self)
          omega
      | block sb v =>
        obtain ⟨l, hl, hsl⟩ := b₁ sb v rfl
        cases x₂ with
        | slot =>
          have := s₂ rfl sb.message (by rw [← hrest, hl]; exact List.mem_cons_self)
          omega
        | block sb' v' =>
          obtain ⟨l', hl', -⟩ := b₂ sb' v' rfl
          rw [hl, hl'] at hrest
          exact hd (congrArg some (List.cons.inj hrest).1)

/-- **The common base.** The fork point comes at or after the first slot of epoch
`max (e₀ + 2) 3`, where `e₀` is the anchor epoch. Then the two chains have one base. Each base
checkpoint is on both chains, before every epoch from `max (e₀ + 2) 3` on. -/
theorem ForkAt.commonBase {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {A X Y st₀ : BeaconState}
    {steps₁ steps₂ p₁ r₁ p₂ r₂ : List ChainStep}
    (F : ForkAt hi A steps₁ steps₂ st₀ p₁ r₁ p₂ r₂) (h₁ : ChainRun hi steps₁ A X)
    (h₂ : ChainRun hi steps₂ A Y) (vals : List EthCLSpecs.Heze.ValidatorIndex)
    (hcps : AnchorCps A) (hord : StateCkptOrd A)
    (hX : max (epochOf A + 2) 3 * slotsPerEpoch ≤ st₀.slot.toNat) {b : Cp}
    (hb : max (epochOf A + 2) 3 ≤ b.epoch) :
    EthCLLib.Proofs.FFG.CommonBase (ffgChain hi steps₁ A vals) (ffgChain hi steps₂ A vals) b := by
  have hm₁ := ffgChain_matches (hi := hi) (vals := vals) hcps hord (h₁.blocks_slot_ge hhi)
  have hm₂ := ffgChain_matches (hi := hi) (vals := vals) hcps hord (h₂.blocks_slot_ge hhi)
  -- The weigh steps of the base end before the fork point.
  have hcross : ∀ e, e + 1 ≤ max (epochOf A + 2) 3 → (e + 1) * slotsPerEpoch ≤ st₀.slot.toNat :=
    fun e he => Nat.le_trans (Nat.mul_le_mul_right _ he) hX
  have hbase : (ffgChain hi steps₁ A vals).base = (ffgChain hi steps₂ A vals).base := by
    change chainBase hi steps₁ A = chainBase hi steps₂ A
    unfold chainBase
    rw [F.weighCps_eq hhi h₁ h₂ (Nat.le_refl _) (hcross _ (by omega)),
      F.weighCps_eq hhi h₁ h₂ (Nat.le_succ _) (hcross _ (by omega))]
    split
    · rename_i h2
      rw [F.weighCps_eq hhi h₁ h₂ h2 (hcross _ (by omega))]
    · rfl
  refine ⟨hbase, fun x hx => ?_⟩
  obtain ⟨hxe, hx₁⟩ := hm₁.base x hx
  have hK : anchorK A = max (epochOf A + 1) 2 := rfl
  exact ⟨by omega, hx₁, (hm₂.base x (hbase ▸ hx)).2⟩

end Runs

/-! ## One list of validators -/

section Vals
variable [Preset]

/-- The validator indices below `VALIDATOR_REGISTRY_LIMIT`, and below `2 ^ 64`. A registry
holds at most `VALIDATOR_REGISTRY_LIMIT` validators, so every index of every state is here. -/
def regVals : List EthCLSpecs.Heze.ValidatorIndex :=
  (List.range (min EthCLSpecs.Heze.Const.validatorRegistryLimit (2 ^ 64))).map UInt64.ofNat

/-- `regVals` has no duplicate: `UInt64.ofNat` is one-to-one below `2 ^ 64`. -/
theorem regVals_nodup : regVals.Nodup := by
  unfold regVals
  rw [List.Nodup, List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {x y} hx hy hne hxy => hne ?_) List.nodup_range
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  have := congrArg UInt64.toNat hxy
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- Every registry index of a state is in `regVals`. -/
theorem mem_regVals (u : BeaconState) {i : Nat} (hi : i < u.validators.val.size) :
    UInt64.ofNat i ∈ regVals := by
  have hcap := u.validators.property
  refine List.mem_map.mpr ⟨i % 2 ^ 64, List.mem_range.mpr ?_, ?_⟩
  · have := Nat.mod_le i (2 ^ 64)
    have := Nat.mod_lt i (show 0 < 2 ^ 64 by decide)
    simp only [Nat.lt_min]
    exact ⟨by omega, this⟩
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_mod]

end Vals

end EthCLSpecs.Proofs.Heze
