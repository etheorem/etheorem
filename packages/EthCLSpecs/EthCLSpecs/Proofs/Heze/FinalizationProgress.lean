import EthCLSpecs.Proofs.Heze.CommitteeFrame
import EthCLSpecs.Proofs.Heze.FFGRefines
import EthCLSpecs.Proofs.Heze.ForkPoint
import EthCLSpecs.Proofs.Heze.FinalityLock
import EthCLSpecs.Proofs.Heze.HeadBelowJustified

/-!
# `EthCLSpecs.Proofs.Heze.FinalizationProgress`: the honest chain justifies and finalizes

On a chain that includes the honest votes of three epochs, the weigh steps justify the three
epochs and finalize the first one.

## A vote reaches the weigh step

A placed vote (`PlacedVote`) is an attestation of a block of the run. At the state before the
block, the validator is an attesting index, and the target root is the block root of the
target epoch. The block sets the target flag (`processBlock_sets_flag`). The flag stays set
until the weigh step of the epoch after the target epoch (`ChainRun.targetFlag_carry`). A vote
included in the target epoch crosses one epoch step. That step moves the flag to the previous
list (`SlotStep.targetFlag_moves`).

## The honest stake passes the test

`honestList u honestOf e` holds the registry indices that are honest, active at `e`, and not
slashed. When each one has its target flag, each one is a counted index of the target test,
so the target balance holds their stake (`honestStake_le_tgtBal`).

## The honest chain

`HonestChain` names the run, its window, and two premises for the epochs `E₁`, `E₁ + 1`, and
`E₁ + 2`. Each honest validator that the test can count has a placed vote. These validators
hold two thirds of the total active balance at the weigh state. So each of the three weigh
steps passes the test of its previous epoch (`HonestChain.weigh`).

The weigh step at the end of `E₁ + 1` justifies `E₁`, or `E₁ + 1` when its current test passes
too. At the end of `E₁ + 3`, bits 1, 2, and 3 are set. The previous justified checkpoint is two
or three epochs back, so a finalization test passes (`finalizeRules_fires`). So the end state
in epoch `E₁ + 4` has a finalized epoch of `E₁` or later. A finalized checkpoint of epoch `E₁`
is the chain's checkpoint of `E₁` (`HonestChain.finalizes`).

## The heads

`getHead` walks from the pending node of the justified root. So when the justified block is on
the EMPTY side of `r`, no head is below `full r` (`heads_stay_of_justified_empty`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState Epoch ValidatorIndex SignedBeaconBlock
  Attestation currentEpochOf previousEpochOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## A vote reaches the weigh step -/

/-- A vote of validator `i` with target epoch `e`, placed in a block of the run. The run of
the prefix `s₁` reaches `u`, and the next step is the block that carries the attestation. At
`u`, `i` is an attesting index of the attestation, the target root is the block root of `e`,
and the window of the committees of `e` holds. The validator is a registry index of `u`. -/
def PlacedVote (hi : Nat) (st₀ : BeaconState) (steps : List ChainStep) (i : ValidatorIndex)
    (e : Epoch) : Prop :=
  ∃ (s₁ s₂ : List ChainStep) (sb : SignedBeaconBlock) (v : Bool) (u : BeaconState)
    (att : Attestation) (idx : Array ValidatorIndex),
    steps = s₁ ++ .block sb v :: s₂ ∧ ChainRun hi s₁ st₀ u ∧
    att ∈ sb.message.body.attestations.toArray ∧ att.data.target.epoch = e ∧
    EthCLSpecs.Heze.computeEpochAtSlot att.data.slot = e ∧
    EthCLSpecs.Heze.getAttestingIndices (pureState u) att = .ok idx ∧ i ∈ idx ∧
    runPure (EthCLSpecs.Heze.getBlockRoot (StateTransition := HezeRun) (pureState u) e) u
      = .ok (att.data.target.root, u) ∧
    CommitteeWindow e (pureState u) ∧ i.toNat < u.validators.val.size

omit [Config] [CryptoBackend] in
/-- A target flag of the current epoch is in the current list. -/
theorem TargetFlagSet.cur_bit {st : BeaconState} {j : Nat} {e : Epoch}
    (hf : TargetFlagSet st j e) (he : e = currentEpochOf (pureState st)) :
    partBit true j (pureState st) = true := by
  rcases hf with ⟨-, hb⟩ | ⟨-, hne, -⟩
  · exact hb
  · exact absurd he hne

/-- **A target flag lasts to the weigh step of the next epoch.** The run starts in epoch `e`
or `e + 1` and ends in epoch `e + 1` at the latest. A slot step that ends epoch `e` moves the
flag from the current list to the previous list. That needs a registry index while the run is
in epoch `e`. The other steps keep the flag. -/
theorem ChainRun.targetFlag_carry {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {x y : BeaconState} (h : ChainRun hi q x y) {j : Nat} {e : Epoch}
    (hx : e.toNat ≤ epochOf x) (hy : epochOf y ≤ e.toNat + 1) (hf : TargetFlagSet x j e)
    (hj : epochOf x = e.toNat → j < x.validators.val.size) : TargetFlagSet y j e := by
  induction h with
  | nil => exact hf
  | @slot _ st st1 _ hlt hstep hrest ih =>
    have hlt' : st.slot.toNat < hi := hlt
    have hs := hstep.slot (by omega)
    have hle := hrest.epoch_le hhi
    by_cases hb : (st.slot.toNat + 1) % slotsPerEpoch = 0
    · -- The step ends the epoch of `st`, which is `e`.
      have hep := succ_div_of_mod_eq hb
      rw [← hs] at hep
      have hst : epochOf st = e.toNat := by unfold epochOf at *; omega
      have hcur : e = currentEpochOf (pureState st) := by
        apply UInt64.toNat_inj.mp
        rw [currentEpochOf_epochOf, hst]
      have hm := hstep.targetFlag_moves (by omega) hb (hj hst) hcur (hf.cur_bit hcur)
      refine ih (by unfold epochOf at *; omega) (by unfold epochOf at *; omega) hm ?_
      intro h'
      unfold epochOf at *
      omega
    · have hep := epoch_succ_of_not_boundary hb
      rw [← hs] at hep
      refine ih (by unfold epochOf at *; omega) hy (hstep.targetFlag_keep (by omega) hb hf) ?_
      intro h'
      rw [size_of_keyView (hstep.keyView_of_not_boundary (by omega) hb)]
      exact hj (by unfold epochOf at *; omega)
  | block sb v hstep _ ih =>
    obtain ⟨hs, -⟩ := hstep.slot
    have hsz := size_of_keyView (processBlock_frame_key hstep.2.1)
    refine ih (by unfold epochOf at *; rw [hs]; exact hx) hy (hstep.keeps hf) ?_
    intro h'
    rw [hsz]
    exact hj (by unfold epochOf at *; rw [← hs]; exact h')

/-- **A placed vote is a target flag at the weigh step of the next epoch.** The block of the
vote comes before the weigh state of epoch `e + 1`, since the block state is in epoch `e` or
`e + 1`. The block sets the flag, and the flag lasts to the weigh state. -/
theorem PlacedVote.flag_at_weigh {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {st₀ : BeaconState}
    {steps : List ChainStep} {i : ValidatorIndex} {e : Epoch} (hv : PlacedVote hi st₀ steps i e)
    {W : BeaconState} (hW : WeighAt hi steps st₀ (e.toNat + 1) W) :
    TargetFlagSet W i.toNat e := by
  obtain ⟨s₁, s₂, sb, v, u, att, idx, hs, hu, ha, hte, hse, hidx, hi', htgt, hwin, hsz⟩ := hv
  obtain ⟨w₁, w₂, hws, hrW, hbW, heW⟩ := hW
  have hcu : (currentEpochOf (pureState u)).toNat = epochOf u := currentEpochOf_epochOf u
  have hwin1 := hwin.1
  have hwin2 := hwin.2.1
  rw [hcu] at hwin1 hwin2
  -- The block of the vote comes before the weigh state.
  rw [hs] at hws
  rcases List.append_eq_append_iff.mp hws with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
  · cases m with
    | nil => simp at hm'
    | cons x m =>
      obtain ⟨rfl, -⟩ := List.cons.inj hm'.symm
      -- `w₁ = s₁ ++ block :: m`.
      rw [hm] at hrW
      obtain ⟨u0, hr0, hrest⟩ := hrW.split
      rw [← hu.det hr0] at hrest
      cases hrest with
      | block _ _ hstep hrest =>
        rename_i u'
        have hf : TargetFlagSet u' i.toNat e := by
          rw [← hte]
          refine processBlock_sets_flag sb.message hstep.2.1 ha hidx hi' (hte ▸ htgt) ?_
          rw [hse, ← hte]
          exact hte ▸ hwin
        obtain ⟨hsl, -⟩ := hstep.slot
        have hsz' := size_of_keyView (processBlock_frame_key hstep.2.1)
        refine hrest.targetFlag_carry hhi ?_ (by unfold epochOf; omega) hf ?_
        · unfold epochOf at *
          rw [hsl]
          exact hwin1
        · intro _
          rw [hsz']
          exact hsz
  · -- The block after the weigh state is in a later epoch.
    exfalso
    cases m with
    | nil =>
      rw [List.append_nil] at hm
      simp at hm'
    | cons x m =>
      obtain ⟨rfl, -⟩ := List.cons.inj hm'
      rw [hm] at hu
      obtain ⟨w, hw1, hw2⟩ := hu.split
      rw [← hrW.det hw1] at hw2
      cases hw2 with
      | slot hlt hstep hrest =>
        have hlt' : W.slot.toNat < hi := hlt
        have h1 := hstep.slot (by omega)
        have h2 := (hrest.slot_le hhi).1
        have hep := succ_div_of_mod_eq hbW
        unfold epochOf at hwin1 hwin2
        have : (W.slot.toNat + 1) / slotsPerEpoch ≤ u.slot.toNat / slotsPerEpoch :=
          Nat.div_le_div_right (by omega)
        omega

/-! ## The honest stake passes the target test -/

/-- The honest validators that the target test of epoch `e` at `u` can count: registry
indices that are honest, active at `e`, and not slashed. -/
def honestList (u : BeaconState) (honestOf : ValidatorIndex → Bool) (e : Epoch) :
    List ValidatorIndex :=
  ((List.range u.validators.val.size).filter fun j =>
    honestOf (UInt64.ofNat j) && EthCLSpecs.Heze.isActiveValidator u.validators.val[j]! e &&
      !(u.validators.val[j]!).slashed).map UInt64.ofNat

/-- The effective balance of the honest validators of `honestList`. -/
def honestStake (u : BeaconState) (honestOf : ValidatorIndex → Bool) (e : Epoch) : Nat :=
  ((honestList u honestOf e).map fun x => (u.validators.val[x.toNat]!).effectiveBalance.toNat).sum

omit [Config] [CryptoBackend] in
/-- A member of `honestList` is a registry index that is honest, active at `e`, and not
slashed. -/
theorem mem_honestList {u : BeaconState} {honestOf : ValidatorIndex → Bool} {e : Epoch}
    (h64 : u.validators.val.size < 2 ^ 64) {x : ValidatorIndex}
    (hx : x ∈ honestList u honestOf e) :
    x.toNat < u.validators.val.size ∧ honestOf x = true ∧
      EthCLSpecs.Heze.isActiveValidator u.validators.val[x.toNat]! e = true ∧
      (u.validators.val[x.toNat]!).slashed = false := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hr, hf⟩ := List.mem_filter.mp hj
  have hr' := List.mem_range.mp hr
  rw [EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
  exact ⟨hr', hf.1.1, hf.1.2, hf.2⟩

omit [Config] [CryptoBackend] in
/-- The members of `honestList` are distinct. -/
theorem honestList_nodup {u : BeaconState} {honestOf : ValidatorIndex → Bool} {e : Epoch}
    (h64 : u.validators.val.size < 2 ^ 64) : (honestList u honestOf e).Nodup := by
  refine EthCLLib.Proofs.nodup_map_of_injOn (List.nodup_range.filter _) ?_
  intro a ha b hb hab
  have ha' := List.mem_range.mp (List.mem_filter.mp ha).1
  have hb' := List.mem_range.mp (List.mem_filter.mp hb).1
  have := congrArg UInt64.toNat hab
  rwa [EthCLLib.Proofs.toNat_ofNat_lt64 (by omega), EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)]
    at this

omit [Config] [CryptoBackend] in
/-- **The target balance holds the honest stake.** Under `RunTotals`, take a successful read of
the counted indices of `e`. When every validator of `honestList` has its target flag for `e`,
each one is a counted index of the target test. The counted indices are distinct, so their
effective balances sum to at least the honest stake. -/
theorem honestStake_le_tgtBal {u : BeaconState} (ht : RunTotals u)
    {honestOf : ValidatorIndex → Bool} {e : Epoch} {idx : Array ValidatorIndex}
    (hidx : EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex e = .ok idx)
    (hflags : ∀ x ∈ honestList u honestOf e, TargetFlagSet u x.toNat e) :
    honestStake u honestOf e ≤ (tgtBal u e).toNat := by
  rw [tgtBal_toNat ht hidx]
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  have h64 := ht.2.2
  unfold honestStake
  show _ ≤ (idx.toList.map fun x => (u.validators.val[x.toNat]!).effectiveBalance.toNat).sum
  refine sum_map_le_of_subset _ _ _ (honestList_nodup h64) fun x hx => ?_
  obtain ⟨hlt, -, hact, hsl⟩ := mem_honestList h64 hx
  have hf := hflags x hx
  rw [getUnslashedParticipatingIndices_ok_toList hidx, List.mem_filter,
    getActiveValidatorIndices_toList]
  refine ⟨List.mem_map.mpr ⟨x.toNat, List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩,
    UInt64.ofNat_toNat⟩, ?_⟩
  · simpa using hact
  · rw [Bool.and_eq_true]
    refine ⟨?_, by rw [sszList_getElem!_eq, hsl]; rfl⟩
    rcases hf with ⟨he, hb⟩ | ⟨-, hne, hb⟩
    · rw [if_pos (by simp [he])]
      exact hb
    · rw [if_neg (by simpa using hne)]
      exact hb

/-! ## The weigh steps of the run -/

/-- After a weigh state, the run takes the slot step that ends the epoch, then the rest of the
steps to the end state. -/
theorem WeighAt.next {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ st : BeaconState} {E : Nat} {u : BeaconState} (h : WeighAt hi steps st₀ E u)
    (hrun : ChainRun hi steps st₀ st) :
    ∃ (p q : List ChainStep) (u' : BeaconState), steps = p ++ .slot :: q ∧ ChainRun hi p st₀ u ∧
      u.slot.toNat + 1 < 2 ^ 64 ∧ SlotStep u u' ∧ ChainRun hi q u' st ∧
      epochOf u' = E + 1 := by
  obtain ⟨p, q, hs, hr, hb, he⟩ := h
  have hrun' := hrun
  rw [hs] at hrun'
  obtain ⟨m, hm1, hm2⟩ := hrun'.split
  rw [← hr.det hm1] at hm2
  cases hm2 with
  | slot hlt hstep hrest =>
    rename_i u'
    have hlt' : u.slot.toNat < hi := hlt
    have h1 := hstep.slot (by omega)
    refine ⟨p, q, u', hs, hr, by omega, hstep, hrest, ?_⟩
    unfold epochOf
    rw [h1, succ_div_of_mod_eq hb, he]

/-- Two weigh states of the run, of epochs `E < E'`. The run reaches the second one after the
slot step that ends `E`. -/
theorem WeighAt.before {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {steps : List ChainStep}
    {st₀ : BeaconState} {E E' : Nat} {u w : BeaconState} (hu : WeighAt hi steps st₀ E u)
    (hw : WeighAt hi steps st₀ E' w) (hE : E < E') :
    ∃ (m : List ChainStep) (u' : BeaconState), u.slot.toNat + 1 < 2 ^ 64 ∧ SlotStep u u' ∧
      ChainRun hi m u' w ∧ epochOf u' = E + 1 := by
  obtain ⟨p, q, hs, hr, hb, he⟩ := hu
  obtain ⟨p', q', hs', hr', hb', he'⟩ := hw
  rw [hs] at hs'
  rcases List.append_eq_append_iff.mp hs' with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
  · -- `p' = p ++ m`.
    cases m with
    | nil =>
      rw [List.append_nil] at hm
      subst hm
      have := hr.det hr'
      subst this
      omega
    | cons x m =>
      obtain ⟨rfl, -⟩ := List.cons.inj hm'.symm
      rw [hm] at hr'
      obtain ⟨y, hy1, hy2⟩ := hr'.split
      rw [← hr.det hy1] at hy2
      cases hy2 with
      | slot hlt hstep hrest =>
        rename_i u'
        have hlt' : u.slot.toNat < hi := hlt
        have h1 := hstep.slot (by omega)
        refine ⟨m, u', by omega, hstep, hrest, ?_⟩
        unfold epochOf
        rw [h1, succ_div_of_mod_eq hb, he]
  · -- `p = p' ++ m`: the first weigh state comes after the second.
    exfalso
    rw [hm] at hr
    obtain ⟨y, hy1, hy2⟩ := hr.split
    rw [← hr'.det hy1] at hy2
    have := hy2.epoch_le hhi
    omega

/-- **One weigh step on the run.** At the weigh state `W` of epoch `E`, after the first two
epochs, the slot step to `W'` shifts the previous justified checkpoint, writes the new current
one and the bits from the two tests, and runs the four finalization tests. The roots that it
reads are the chain's roots at `E` and `E - 1` (`RefSetting.weigh_root`). -/
theorem RefSetting.weigh_rec {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} (S : RefSetting hi steps st₀ st vals) {E : Nat}
    {W W' : BeaconState} (hW : WeighAt hi steps st₀ E W) (hE : 2 ≤ E) (hstep : SlotStep W W')
    (hlt : W.slot.toNat + 1 < 2 ^ 64) :
    W'.previousJustifiedCheckpoint = W.currentJustifiedCheckpoint ∧
    W'.currentJustifiedCheckpoint =
      (if jcOf W = true then { epoch := currentEpochOf (pureState W), root := chainRoot st₀ steps E }
       else if jpOf W = true then
         { epoch := previousEpochOf (pureState W), root := chainRoot st₀ steps (E - 1) }
       else W.currentJustifiedCheckpoint) ∧
    W'.justificationBits = weighBits W.justificationBits (jpOf W) (jcOf W) ∧
    W'.finalizedCheckpoint = finalizeRules (weighBits W.justificationBits (jpOf W) (jcOf W))
      W.previousJustifiedCheckpoint W.currentJustifiedCheckpoint W.finalizedCheckpoint
      (currentEpochOf (pureState W)) := by
  obtain ⟨p, q, hs, hr, hb, he⟩ := hW
  rcases hstep.weigh hlt hb with ⟨h1, -⟩ | ⟨-, pr, cr, hp, hc, hbits, hf, hRp, hRc⟩
  · omega
  have hEp : epochOf W = E := he
  have hprev : (previousEpochOf (pureState W)).toNat = E - 1 := by
    rw [previousEpochOf_epochOf, hEp]
  have hcurr : (currentEpochOf (pureState W)).toNat = E := by
    rw [currentEpochOf_epochOf, hEp]
  have rc : jcOf W = true → cr = chainRoot st₀ steps E := fun h => by
    have := S.weigh_root hs hr hb (n := currentEpochOf (pureState W)) (.inr (by rw [hcurr, hEp]))
      (by omega) (hRc h)
    rw [this, hcurr]
  have rp : jpOf W = true → pr = chainRoot st₀ steps (E - 1) := fun h => by
    have := S.weigh_root hs hr hb (n := previousEpochOf (pureState W))
      (.inl (by rw [hprev, hEp]; omega)) (by omega) (hRp h)
    rw [this, hprev]
  refine ⟨hp, ?_, hbits, hf⟩
  rw [hc]
  show (if jcOf W = true then _ else if jpOf W = true then _ else _) = _
  by_cases hjc : jcOf W = true
  · rw [if_pos hjc, if_pos hjc, rc hjc]
  · rw [if_neg hjc, if_neg hjc]
    by_cases hjp : jpOf W = true
    · rw [if_pos hjp, if_pos hjp, rp hjp]
    · rw [if_neg hjp, if_neg hjp]

omit [HasherTag] [Config] [CryptoBackend] in
/-- With bits 1, 2 and 3 set, and the old previous justified checkpoint two or three epochs
back, a finalization test passes. The result is one of the two old justified checkpoints. -/
theorem finalizeRules_fires (bits : Bitvector EthCLSpecs.Heze.Const.justificationBitsLength)
    (op oc fin : EthCLSpecs.Heze.Checkpoint) (ce : UInt64) (h1 : bitGet bits 1 = true)
    (h2 : bitGet bits 2 = true) (h3 : bitGet bits 3 = true)
    (hop : op.epoch.toNat + 2 = ce.toNat ∨ op.epoch.toNat + 3 = ce.toNat) :
    finalizeRules bits op oc fin ce = oc ∨ finalizeRules bits op oc fin ce = op := by
  have hce := ce.toNat_lt
  have e2 : op.epoch.toNat + 2 = ce.toNat → (op.epoch + 2 == ce) = true := by
    intro h
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
    simpa using h
  have e3 : op.epoch.toNat + 3 = ce.toNat → (op.epoch + 3 == ce) = true := by
    intro h
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]
    simpa using h
  unfold finalizeRules
  split
  · exact .inl rfl
  split
  · exact .inl rfl
  rcases hop with hop | hop
  · rw [if_pos (by simp [h1, h2, e2 hop])]
    exact .inr rfl
  · split
    · exact .inr rfl
    · rw [if_pos (by simp [h1, h2, h3, e3 hop])]
      exact .inr rfl

/-- At the end of an epoch after the first two, a slot step read the counted indices of the
previous epoch without a fault. The weigh step reads them on `slotWrite u`, which keeps what
the read reads (`processJustificationAndFinalization_run_ok`). -/
theorem SlotStep.prev_read_ok {u u' : BeaconState} (h : SlotStep u u')
    (hlt : u.slot.toNat + 1 < 2 ^ 64) (hb : (u.slot.toNat + 1) % slotsPerEpoch = 0)
    (h2 : 2 ≤ u.slot.toNat / slotsPerEpoch) :
    ∃ idx, EthCLSpecs.Heze.getUnslashedParticipatingIndices (pureState u)
      EthCLSpecs.Heze.Const.timelyTargetFlagIndex (previousEpochOf (pureState u)) = .ok idx := by
  obtain ⟨mid, hjf, -⟩ := h.boundary hlt hb
  have hE := currentEpochOf_toNat u
  change (currentEpochOf (pureState u)).toNat = u.slot.toNat / slotsPerEpoch at hE
  have hg : ¬ currentEpochOf (pureState (slotWrite u)) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1 := by
    intro h'
    have hg' := UInt64.le_iff_toNat_le.mp h'
    change (currentEpochOf (pureState u)).toNat ≤ _ at hg'
    rw [hE] at hg'
    simp [EthCLSpecs.Heze.Const.genesisEpoch] at hg'
    omega
  obtain ⟨prevIdx, -, -, -, -, h1, -⟩ := processJustificationAndFinalization_run_ok hjf hg
  rw [getUnslashedParticipatingIndices_slotWrite] at h1
  exact ⟨prevIdx, h1⟩

/-! ## The honest chain -/

/-- **The honest chain of the finality window.** A run from `st₀` to `st` with the premises of
the FFG refinement (`RefSetting`). It starts by epoch `E₁` and ends in epoch `E₁ + 4`. For
each epoch `e` of `E₁`, `E₁ + 1`, and `E₁ + 2`:

- every honest validator that the target test of `e` can count at the weigh state of `e + 1`
  has a vote for `e` placed on the run (`PlacedVote`);
- these validators hold two thirds of the total active balance there. -/
structure HonestChain (hi : Nat) (steps : List ChainStep) (st₀ st : BeaconState)
    (vals : List ValidatorIndex) (honestOf : ValidatorIndex → Bool) (E₁ : Nat) : Prop where
  ref : RefSetting hi steps st₀ st vals
  low : 1 ≤ E₁
  start : epochOf st₀ ≤ E₁
  ends : epochOf st = E₁ + 4
  included : ∀ k, k < 3 → ∀ W, WeighAt hi steps st₀ (E₁ + k + 1) W →
    ∀ x ∈ honestList W honestOf (previousEpochOf (pureState W)),
      PlacedVote hi st₀ steps x (previousEpochOf (pureState W))
  stake : ∀ k, k < 3 → ∀ W, WeighAt hi steps st₀ (E₁ + k + 1) W →
    3 * honestStake W honestOf (previousEpochOf (pureState W)) ≥ 2 * (totBal W).toNat

/-- The honest chain has a weigh state at each of the three epochs, and each one passes the
target test of its previous epoch. -/
theorem HonestChain.weigh {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} {honestOf : ValidatorIndex → Bool} {E₁ : Nat}
    (H : HonestChain hi steps st₀ st vals honestOf E₁) {k : Nat} (hk : k < 3) :
    ∃ W, WeighAt hi steps st₀ (E₁ + k + 1) W ∧ jpOf W = true := by
  have hhi := H.ref.hhi
  have hp := slotsPerEpochPos
  obtain ⟨W, hW⟩ := H.ref.run.weighAt_of_cross hhi (E₁ + k + 1)
    (by
      have := H.start
      unfold epochOf at this
      have h1 := Nat.lt_succ_of_le this
      have h2 : st₀.slot.toNat < (E₁ + 1) * slotsPerEpoch := by
        rw [Nat.lt_iff_add_one_le] at h1 ⊢
        have := (Nat.div_lt_iff_lt_mul hp).mp (by omega : st₀.slot.toNat / slotsPerEpoch < E₁ + 1)
        omega
      have h3 : (E₁ + 1) * slotsPerEpoch ≤ (E₁ + k + 1 + 1) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
    (by
      have := H.ends
      unfold epochOf at this
      have h1 : (E₁ + 4) * slotsPerEpoch ≤ st.slot.toNat := by
        rw [← this]
        exact Nat.div_mul_le_self _ _
      have h3 : (E₁ + k + 1 + 1) * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  refine ⟨W, hW, ?_⟩
  obtain ⟨p, q, hs, hr, -, -⟩ := id hW
  have ht := H.ref.tot p (.slot :: q) W hs hr
  -- Each honest validator of the test has its flag, so the honest stake counts.
  have hflags : ∀ x ∈ honestList W honestOf (previousEpochOf (pureState W)),
      TargetFlagSet W x.toNat (previousEpochOf (pureState W)) := by
    intro x hx
    have hv := H.included k hk W hW x hx
    have hep : (previousEpochOf (pureState W)).toNat + 1 = E₁ + k + 1 := by
      obtain ⟨-, -, -, -, -, he⟩ := id hW
      rw [previousEpochOf_epochOf]
      unfold epochOf
      rw [he]
      omega
    exact hv.flag_at_weigh hhi (hep ▸ hW)
  -- The slot step after `W` weighs, so its read of the counted indices succeeded.
  obtain ⟨-, -, u', -, -, hlt, hstep, -, -⟩ := hW.next hhi H.ref.run
  have hbW : (W.slot.toNat + 1) % slotsPerEpoch = 0 := by
    obtain ⟨-, -, -, -, hb, -⟩ := id hW
    exact hb
  have h2W : 2 ≤ W.slot.toNat / slotsPerEpoch := by
    obtain ⟨-, -, -, -, -, he⟩ := id hW
    have hlow := H.low
    omega
  obtain ⟨idx, hidx⟩ := hstep.prev_read_ok hlt hbW h2W
  have hle := honestStake_le_tgtBal ht hidx hflags
  have hst := H.stake k hk W hW
  unfold jpOf
  exact decide_eq_true (by omega)

/-- The four checkpoint fields of a state, read off an equality of `ckView`. -/
theorem fields_of_ckView {a b : BeaconState} (h : ckView (pureState a) = ckView (pureState b)) :
    a.previousJustifiedCheckpoint = b.previousJustifiedCheckpoint ∧
    a.currentJustifiedCheckpoint = b.currentJustifiedCheckpoint ∧
    a.finalizedCheckpoint = b.finalizedCheckpoint ∧ a.justificationBits = b.justificationBits := by
  simp only [ckView, Prod.mk.injEq] at h
  exact h

/-- The previous justified checkpoint at the end of `E₁ + 3`: the chain's checkpoint of
`E₁ + 1`, or of `E₁`. -/
def PrevAtEnd (st₀ : BeaconState) (steps : List ChainStep) (E₁ : Nat)
    (c : EthCLSpecs.Heze.Checkpoint) : Prop :=
  (c.epoch.toNat = E₁ + 1 ∧ c.root = chainRoot st₀ steps (E₁ + 1)) ∨
    (c.epoch.toNat = E₁ ∧ c.root = chainRoot st₀ steps E₁)

omit [Config] [CryptoBackend] in
/-- **The last weigh step finalizes `E₁`.** Take a state `x` of epoch `E₁ + 3` whose bits 1 and
2 are set, whose previous justified checkpoint is the chain's checkpoint of `E₁` or `E₁ + 1`, and
whose current justified epoch is at least `E₁ + 1`. A weigh step on `x` that justifies the
previous epoch sets bits 1, 2, and 3. Its previous justified checkpoint is two or three epochs
back, so a finalization test passes (`finalizeRules_fires`). The new finalized checkpoint has an
epoch of `E₁` or later. With epoch `E₁` it is the chain's checkpoint of `E₁`. -/
theorem finalize_tail {st₀ : BeaconState} {steps : List ChainStep} {E₁ : Nat} {x : BeaconState}
    (hb1 : bitGet x.justificationBits 1 = true) (hb2 : bitGet x.justificationBits 2 = true)
    (hP : PrevAtEnd st₀ steps E₁ x.previousJustifiedCheckpoint)
    (hC : E₁ + 1 ≤ x.currentJustifiedCheckpoint.epoch.toNat)
    (hcur : (currentEpochOf (pureState x)).toNat = E₁ + 3) (jc : Bool) :
    E₁ ≤ (finalizeRules (weighBits x.justificationBits true jc) x.previousJustifiedCheckpoint
        x.currentJustifiedCheckpoint x.finalizedCheckpoint (currentEpochOf (pureState x))).epoch.toNat ∧
      ((finalizeRules (weighBits x.justificationBits true jc) x.previousJustifiedCheckpoint
          x.currentJustifiedCheckpoint x.finalizedCheckpoint
          (currentEpochOf (pureState x))).epoch.toNat = E₁ →
        toCp (finalizeRules (weighBits x.justificationBits true jc) x.previousJustifiedCheckpoint
          x.currentJustifiedCheckpoint x.finalizedCheckpoint (currentEpochOf (pureState x))) =
          cpOf st₀ steps E₁) := by
  have g := weighBits_get x.justificationBits true jc
  have b1 : bitGet (weighBits x.justificationBits true jc) 1 = true := by rw [g.2.1]; rfl
  have b2 : bitGet (weighBits x.justificationBits true jc) 2 = true := by rw [g.2.2.1, hb1]
  have b3 : bitGet (weighBits x.justificationBits true jc) 3 = true := by rw [g.2.2.2, hb2]
  have hop : x.previousJustifiedCheckpoint.epoch.toNat + 2 =
        (currentEpochOf (pureState x)).toNat ∨
      x.previousJustifiedCheckpoint.epoch.toNat + 3 = (currentEpochOf (pureState x)).toNat := by
    rcases hP with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rcases finalizeRules_fires _ _ _ _ _ b1 b2 b3 hop with h | h <;> rw [h]
  · exact ⟨by omega, fun h' => by omega⟩
  · rcases hP with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact ⟨by omega, fun h' => by omega⟩
    · refine ⟨by omega, fun _ => ?_⟩
      unfold toCp cpOf
      rw [h1, h2]

/-- **The weigh state of `E₁ + 3` on the honest chain.** The weigh steps at the ends of
`E₁ + 1` and `E₁ + 2` justify `E₁` and `E₁ + 1` (`HonestChain.weigh`). So at the weigh state of
`E₁ + 3`, bits 1 and 2 are set. The previous justified checkpoint is the one that the first
weigh step wrote: the chain's checkpoint of `E₁`, or of `E₁ + 1`. The current justified epoch
is `E₁ + 1` or later. The weigh state passes the test of its previous epoch. -/
theorem HonestChain.end_facts {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} {honestOf : ValidatorIndex → Bool} {E₁ : Nat}
    (H : HonestChain hi steps st₀ st vals honestOf E₁) :
    ∃ W3, WeighAt hi steps st₀ (E₁ + 2 + 1) W3 ∧ jpOf W3 = true ∧
      bitGet W3.justificationBits 1 = true ∧ bitGet W3.justificationBits 2 = true ∧
      PrevAtEnd st₀ steps E₁ W3.previousJustifiedCheckpoint ∧
      E₁ + 1 ≤ W3.currentJustifiedCheckpoint.epoch.toNat ∧
      (currentEpochOf (pureState W3)).toNat = E₁ + 3 := by
  have S := H.ref
  have hhi := S.hhi
  obtain ⟨W1, hW1, jp1⟩ := H.weigh (k := 0) (by decide)
  obtain ⟨W2, hW2, jp2⟩ := H.weigh (k := 1) (by decide)
  obtain ⟨W3, hW3, jp3⟩ := H.weigh (k := 2) (by decide)
  rw [Nat.add_zero] at hW1
  have e1 : epochOf W1 = E₁ + 1 := by obtain ⟨-, -, -, -, -, he⟩ := id hW1; exact he
  have e2 : epochOf W2 = E₁ + 1 + 1 := by obtain ⟨-, -, -, -, -, he⟩ := id hW2; exact he
  have e3 : epochOf W3 = E₁ + 2 + 1 := by obtain ⟨-, -, -, -, -, he⟩ := id hW3; exact he
  -- The steps between the weigh states.
  obtain ⟨m1, a1, hl1, hs1, hm1, ea1⟩ := hW1.before hhi hW2 (by omega)
  obtain ⟨m2, a2, hl2, hs2, hm2, ea2⟩ := hW2.before hhi hW3 (by omega)
  have hlow := H.low
  obtain ⟨p1, c1, b1, f1⟩ := S.weigh_rec hW1 (by omega) hs1 hl1
  obtain ⟨p2, c2, b2, f2⟩ := S.weigh_rec hW2 (by omega) hs2 hl2
  -- The states in one epoch have one set of checkpoint fields.
  obtain ⟨k1p, k1c, -, k1b⟩ := fields_of_ckView (hm1.ckView_of_epoch hhi (by
    unfold epochOf at ea1 e2; omega))
  obtain ⟨k2p, k2c, -, k2b⟩ := fields_of_ckView (hm2.ckView_of_epoch hhi (by
    unfold epochOf at ea2 e3; omega))
  -- The epochs of the three weigh states.
  have cur1 : (currentEpochOf (pureState W1)).toNat = E₁ + 1 := by
    rw [currentEpochOf_epochOf, e1]
  have prev1 : (previousEpochOf (pureState W1)).toNat = E₁ := by
    rw [previousEpochOf_epochOf, e1]; omega
  have cur2 : (currentEpochOf (pureState W2)).toNat = E₁ + 2 := by
    rw [currentEpochOf_epochOf, e2]
  have prev2 : (previousEpochOf (pureState W2)).toNat = E₁ + 1 := by
    rw [previousEpochOf_epochOf, e2]; omega
  have cur3 : (currentEpochOf (pureState W3)).toNat = E₁ + 3 := by
    rw [currentEpochOf_epochOf, e3]
  rw [if_pos jp1] at c1
  rw [if_pos jp2] at c2
  rw [jp1] at b1
  rw [jp2] at b2
  -- The bits at the end of `E₁ + 3`.
  have bW3 : W3.justificationBits = weighBits (weighBits W1.justificationBits true (jcOf W1))
      true (jcOf W2) := by rw [k2b, b2, k1b, b1]
  have g2 := weighBits_get (weighBits W1.justificationBits true (jcOf W1)) true (jcOf W2)
  have g3 := weighBits_get W1.justificationBits true (jcOf W1)
  have hb1 : bitGet W3.justificationBits 1 = true := by rw [bW3, g2.2.1]; rfl
  have hb2 : bitGet W3.justificationBits 2 = true := by rw [bW3, g2.2.2.1, g3.2.1]; rfl
  -- The two old justified checkpoints at the end of `E₁ + 3`.
  have hP : W3.previousJustifiedCheckpoint = a1.currentJustifiedCheckpoint := by
    rw [k2p, p2, k1c]
  have hC : W3.currentJustifiedCheckpoint = a2.currentJustifiedCheckpoint := k2c
  have hP1 : PrevAtEnd st₀ steps E₁ W3.previousJustifiedCheckpoint := by
    unfold PrevAtEnd
    rw [hP, c1]
    by_cases hj : jcOf W1 = true
    · rw [if_pos hj]
      exact .inl ⟨cur1, rfl⟩
    · rw [if_neg hj]
      exact .inr ⟨prev1, by
        show chainRoot st₀ steps (E₁ + 1 - 1) = chainRoot st₀ steps E₁
        rw [Nat.add_sub_cancel]⟩
  have hC1 : E₁ + 1 ≤ W3.currentJustifiedCheckpoint.epoch.toNat := by
    rw [hC, c2]
    by_cases hj : jcOf W2 = true
    · rw [if_pos hj]; show E₁ + 1 ≤ (currentEpochOf (pureState W2)).toNat; omega
    · rw [if_neg hj]; show E₁ + 1 ≤ (previousEpochOf (pureState W2)).toNat; omega
  exact ⟨W3, hW3, jp3, hb1, hb2, hP1, hC1, cur3⟩

/-- **The honest chain finalizes `E₁`.** At the weigh state of `E₁ + 3`, the weigh step meets
`finalize_tail` (`HonestChain.end_facts`). So the end state in epoch `E₁ + 4` has a finalized
epoch of `E₁` or later. When it is `E₁`, the finalized checkpoint is the chain's checkpoint of
`E₁`. -/
theorem HonestChain.finalizes {hi : Nat} {steps : List ChainStep} {st₀ st : BeaconState}
    {vals : List ValidatorIndex} {honestOf : ValidatorIndex → Bool} {E₁ : Nat}
    (H : HonestChain hi steps st₀ st vals honestOf E₁) :
    E₁ ≤ st.finalizedCheckpoint.epoch.toNat ∧
      (st.finalizedCheckpoint.epoch.toNat = E₁ → toCp st.finalizedCheckpoint = cpOf st₀ steps E₁) := by
  have S := H.ref
  have hhi := S.hhi
  obtain ⟨W3, hW3, jp3, hb1, hb2, hP, hC, hcur⟩ := H.end_facts
  have e3 : epochOf W3 = E₁ + 2 + 1 := by obtain ⟨-, -, -, -, -, he⟩ := id hW3; exact he
  obtain ⟨-, q3, a3, -, -, hl3, hs3, hq3, ea3⟩ := hW3.next hhi S.run
  have hlow := H.low
  obtain ⟨-, -, -, f3⟩ := S.weigh_rec hW3 (by omega) hs3 hl3
  obtain ⟨-, -, kf, -⟩ := fields_of_ckView (hq3.ckView_of_epoch hhi (by
    have := H.ends
    unfold epochOf at ea3 this; omega))
  rw [jp3] at f3
  rw [kf, f3]
  exact finalize_tail hb1 hb2 hP hC hcur _

end

/-! ## The heads after a justification on the EMPTY side -/

section
variable {map : EthCLLib.Spec.MapKind} [Preset] [HasherTag] [Config] [EthCLLib.Spec.FcMap map]

/-- **After the justified checkpoint moves to the EMPTY side of `r`, the heads stay there.**
`getHead` starts its walk at the pending node of the justified root, so its head lies below
that node (`getHead_run_below_justified`). A node below a block on the EMPTY side of `r` is not
below `full r` (`below_emptySide_not_full`). -/
theorem heads_stay_of_justified_empty (store runnerStore s' : EthCLSpecs.Heze.Store map)
    (hslots : SlotsIncrease store) (head : EthCLSpecs.Heze.ForkChoiceNode)
    (r : EthCLSpecs.Heze.Root) (rb : EthCLSpecs.Heze.BeaconBlock)
    (hrb : EthCLLib.Spec.FcMap.lookup store.blocks r = some rb)
    (hj : OnEmptySide store r store.justifiedCheckpoint.root)
    (hrun : (EthCLSpecs.Heze.getHead
      (StoreTransition := EthCLLib.Proofs.ForkChoiceStoreRun (EthCLSpecs.Heze.Store map))
      store).run runnerStore = .ok (head, s')) :
    ¬ NodeBelow store (.full r) head :=
  below_emptySide_not_full store hslots r rb hrb _ head hj
    (getHead_run_below_justified store runnerStore s' head hrun)

end

end EthCLSpecs.Proofs.Heze
