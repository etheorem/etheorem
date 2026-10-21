import EthCLSpecs.Proofs.Heze.RunVotes

/-!
# `EthCLSpecs.Proofs.Heze.ParticipationKeep`: a set target flag stays set

`Participation.lean` reads a target flag backward: a flag at the end of a run comes from a
vote of the run. This module reads it forward. A flag that is set stays set until the epoch
step moves its list.

- `processAttestation` only adds flags (`processAttestation_keeps`). Every other function of
  a block step keeps the target bits (`ParticipationFrame.lean`). So a block step keeps each
  set bit (`BlockStep.keeps`).
- A slot step that does not end an epoch keeps the target bits and the epochs
  (`SlotStep.targetFlag_keep`).
- So a run inside one epoch keeps each target flag (`ChainRun.targetFlag_keep`).

A loop rule places one element of an operation loop (`forIn_list_ops_at`). The loop state
before that element satisfies the loop invariant. A fact that the element makes true, and
that the later elements keep, holds at the end of the loop.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok_pure run_pure_state_eq
  run_assert_bind_eq_ok keepsUncached_bind keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Epoch BeaconBlock SignedBeaconBlock
  currentEpochOf previousEpochOf)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

section
variable [Preset] [HasherTag]

/-! ## One element of an operation loop -/

/-- A run of `op` over a list, placed at one element `d₀`. Each run of `op` keeps `I`, and
each run from a state with `I` keeps `Q`. When the run of `op d₀` from a state with `I` ends
with `Q`, the loop ends with `Q`. -/
theorem forIn_list_ops_at {δ : Type} (I Q : BeaconState → Prop) (op : δ → HezeRun PUnit)
    (hk : ∀ d, KeepsUncached (op d)) (d₀ : δ) :
    ∀ (l : List δ), d₀ ∈ l →
      (∀ d ∈ l, ∀ s s' : BeaconState, I s →
        (op d).run (pureState s) = .ok ((), pureState s') → I s' ∧ (Q s → Q s')) →
      (∀ s s' : BeaconState, I s →
        (op d₀).run (pureState s) = .ok ((), pureState s') → Q s') →
      ∀ s s' : BeaconState, I s →
        (forIn l PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
          : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s') → Q s' := by
  intro l
  induction l with
  | nil => intro hm; exact absurd hm List.not_mem_nil
  | cons d rest ih =>
    intro hm hop h0 s s' hs h
    rw [List.forIn_cons] at h
    obtain ⟨step, s1, hb, hr⟩ :=
      run_bind_eq_ok_pure (keepsUncached_bind (hk d) (fun _ => keepsUncached_pure _)) h
    obtain ⟨⟨⟩, s0, hop1, hp⟩ := run_bind_eq_ok_pure (hk d) hb
    injection hp with hp
    injection hp with hstep hs1
    subst hstep
    rw [← pureState_inj hs1] at hr
    have hrest : ∀ d' ∈ rest, ∀ s s' : BeaconState, I s →
        (op d').run (pureState s) = .ok ((), pureState s') → I s' ∧ (Q s → Q s') :=
      fun d' hd' => hop d' (List.mem_cons_of_mem _ hd')
    have hI0 := (hop d List.mem_cons_self s s0 hs hop1).1
    by_cases hmr : d₀ ∈ rest
    · exact ih hmr hrest h0 s0 s' hI0 hr
    · -- `d₀` is the head: the head run makes `Q`, and the rest keeps it.
      have hd : d₀ = d := by
        rcases List.mem_cons.mp hm with he | he
        · exact he
        · exact absurd he hmr
      subst hd
      exact (forIn_list_ops_inv (fun s => I s ∧ Q s) op hk rest
        (fun d' hd' a b hab hr' => ⟨(hrest d' hd' a b hab.1 hr').1,
          (hrest d' hd' a b hab.1 hr').2 hab.2⟩)
        s0 s' ⟨hI0, h0 s s0 hs hop1⟩ hr).2

/-- `forIn_list_ops_at` for an array. -/
theorem forIn_array_ops_at {δ : Type} (I Q : BeaconState → Prop) (op : δ → HezeRun PUnit)
    (hk : ∀ d, KeepsUncached (op d)) (xs : Array δ) (d₀ : δ) (hm : d₀ ∈ xs)
    (hop : ∀ d ∈ xs, ∀ s s' : BeaconState, I s →
      (op d).run (pureState s) = .ok ((), pureState s') → I s' ∧ (Q s → Q s'))
    (h0 : ∀ s s' : BeaconState, I s →
      (op d₀).run (pureState s) = .ok ((), pureState s') → Q s')
    (s s' : BeaconState) (hs : I s)
    (h : (forIn xs PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
      : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s')) : Q s' := by
  rw [← Array.forIn_toList] at h
  exact forIn_list_ops_at I Q op hk d₀ xs.toList (Array.mem_toList_iff.mpr hm)
    (fun d hd => hop d (Array.mem_toList_iff.mp hd)) h0 s s' hs h

/-! ## The block step -/

/-- Every target bit of `st` is set in `st'`. -/
def BitsKept (st st' : BeaconState) : Prop :=
  ∀ w j, partBit w j (pureState st) = true → partBit w j (pureState st') = true

/-- A state keeps its own bits. -/
theorem BitsKept.refl (st : BeaconState) : BitsKept st st :=
  fun _ _ h => h

/-- Kept bits compose. -/
theorem BitsKept.trans {a b c : BeaconState} (h1 : BitsKept a b)
    (h2 : BitsKept b c) : BitsKept a c :=
  fun w j h => h2 w j (h1 w j h)

/-- Two states with one `partView` for every bit keep each other's bits. -/
theorem BitsKept.of_partView {s s' : BeaconState}
    (h : ∀ w j, partView w j (pureState s') = partView w j (pureState s)) : BitsKept s s' :=
  fun w j hb => (congrArg Prod.fst (h w j)).trans hb

variable [Config] [CryptoBackend]

/-- `processAttestation` keeps every set target bit. -/
theorem processAttestation_keeps (att : EthCLSpecs.Heze.Attestation) {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState st) = .ok ((), pureState st')) : BitsKept st st' := by
  obtain ⟨-, -, -, -, -, -, hmono, -⟩ := processAttestation_run_flags att st st' h
  exact hmono

/-- `processOperations` keeps every set target bit. Only the attestation loop writes the
participation lists, and it only adds flags. -/
theorem processOperations_keeps (body : EthCLSpecs.Heze.BeaconBlockBody) {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run (pureState st)
      = .ok ((), pureState st')) : BitsKept st st' := by
  let P : BeaconState → Prop := fun s => BitsKept st s
  have keep : ∀ s s' : BeaconState, P s →
      (∀ w j, partView w j (pureState s') = partView w j (pureState s)) → P s' :=
    fun s s' hs hb => hs.trans (BitsKept.of_partView hb)
  unfold EthCLSpecs.Heze.processOperations at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun ps _ =>
    keepsUncached_bind (keepsUncached_processProposerSlashing ps)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t1 : P s1 := forIn_array_ops_inv P _ keepsUncached_processProposerSlashing
    body.proposerSlashings.val
    (fun _ _ s s' hs hr => keep s s' hs fun w j =>
      processProposerSlashing_frame_part (cur := w) (i := j) hr)
    st s1 (BitsKept.refl st) h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttesterSlashing a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t2 : P s2 := forIn_array_ops_inv P _ keepsUncached_processAttesterSlashing
    body.attesterSlashings.val
    (fun _ _ s s' hs hr => keep s s' hs fun w j =>
      processAttesterSlashing_frame_part (cur := w) (i := j) hr)
    s1 s2 t1 h2
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t3 : P s3 := forIn_array_ops_inv P _ keepsUncached_processAttestation
    body.attestations.val
    (fun a _ s s' hs hr => hs.trans (processAttestation_keeps a hr))
    s2 s3 t2 h3
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processVoluntaryExit a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t4 : P s4 := forIn_array_ops_inv P _ keepsUncached_processVoluntaryExit
    body.voluntaryExits.val
    (fun _ _ s s' hs hr => keep s s' hs fun w j =>
      processVoluntaryExit_frame_part (cur := w) (i := j) hr)
    s3 s4 t3 h4
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processBlsToExecutionChange a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t5 : P s5 := forIn_array_ops_inv P _ keepsUncached_processBlsToExecutionChange
    body.blsToExecutionChanges.val
    (fun _ _ s s' hs hr => keep s s' hs fun w j =>
      processBlsToExecutionChange_frame_part (cur := w) (i := j) hr)
    s4 s5 t4 h5
  obtain ⟨⟨⟩, s6, h6, hp⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processPayloadAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  rw [pureState_inj (run_pure_state_eq _ _ _ _ hp)]
  exact forIn_array_ops_inv P _ keepsUncached_processPayloadAttestation
    body.payloadAttestations.val
    (fun _ _ s s' hs hr => keep s s' hs fun _ _ =>
      frame_of_reads (processPayloadAttestation_frame hr))
    s5 s6 t5 h6

/-- `processBlock` keeps every set target bit. -/
theorem processBlock_keeps (b : BeaconBlock) {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState st)
      = .ok ((), pureState st')) : BitsKept st st' := by
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  obtain ⟨⟨⟩, s7, h7, h8⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  refine (BitsKept.of_partView fun w j =>
    processParentExecutionPayload_frame_part (cur := w) (i := j) h1).trans ?_
  refine (BitsKept.of_partView fun w j =>
    processBlockHeader_frame_part (cur := w) (i := j) h2).trans ?_
  refine (BitsKept.of_partView fun w j =>
    processWithdrawals_frame_part (cur := w) (i := j) h3).trans ?_
  refine (BitsKept.of_partView fun w j =>
    processExecutionPayloadBid_frame_part (cur := w) (i := j) h4).trans ?_
  refine (BitsKept.of_partView fun w j =>
    processRandao_frame_part (cur := w) (i := j) h5).trans ?_
  refine (BitsKept.of_partView fun w j =>
    processEth1Data_frame_part (cur := w) (i := j) h6).trans ?_
  exact (processOperations_keeps b.body h7).trans (BitsKept.of_partView fun w j =>
    processSyncAggregate_frame_part (cur := w) (i := j) h8)

omit [Config] [CryptoBackend] in
/-- A state with the slot of `st` and the bits of `st` has the target flags of `st`. -/
theorem TargetFlagSet.of_bitsKept {st st' : BeaconState} {i : Nat} {e : Epoch}
    (hk : BitsKept st st') (hs : st'.slot = st.slot) (hf : TargetFlagSet st i e) :
    TargetFlagSet st' i e := by
  obtain ⟨hc, hp⟩ := epochs_eq_of_toNat (a := st') (b := st) (by rw [hs])
  rcases hf with ⟨he, hb⟩ | ⟨he, hne, hb⟩
  · exact .inl ⟨he.trans hc.symm, hk true i hb⟩
  · exact .inr ⟨he.trans hp.symm, by rw [hc]; exact hne, hk false i hb⟩

/-- A block step keeps each target flag. -/
theorem BlockStep.keeps {sb : SignedBeaconBlock} {v : Bool} {st st' : BeaconState}
    (h : BlockStep sb v st st') {i : Nat} {e : Epoch} (hf : TargetFlagSet st i e) :
    TargetFlagSet st' i e :=
  hf.of_bitsKept (processBlock_keeps sb.message h.2.1) (UInt64.toNat_inj.mp h.slot.1)

/-! ## The slot step and the run -/

/-- A slot step that does not end an epoch keeps each target flag. -/
theorem SlotStep.targetFlag_keep {st st' : BeaconState} (h : SlotStep st st')
    (hlt : st.slot.toNat + 1 < 2 ^ 64) (hb : (st.slot.toNat + 1) % slotsPerEpoch ≠ 0)
    {i : Nat} {e : Epoch} (hf : TargetFlagSet st i e) : TargetFlagSet st' i e := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 : ∀ w, partView w i (pureState st1) = partView w i (pureState st) := fun w =>
    processSlot_frame_part (cur := w) h1
  have sl1 : st1.slot = st.slot := congrArg Prod.snd (e1 true)
  have b' : ∀ w, partBit w i (pureState st') = partBit w i (pureState st2) := by
    intro w
    rw [hst']
    rfl
  have sl' : st'.slot = st2.slot + 1 := by
    change sszGet (pureState st') slot = _
    rw [hst']
    rfl
  split at h2
  · rename_i htest
    exact absurd ((epochTest_iff st1.slot (by rw [sl1]; exact hlt)).mp htest) (by rw [sl1]; exact hb)
  · rw [h2] at sl' b'
    have hsn : st'.slot.toNat = st.slot.toNat + 1 := by
      rw [sl', sl1, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    obtain ⟨hcur, hprev⟩ := epochs_eq_of_toNat (a := st') (b := st)
      (by rw [hsn, succ_div_of_mod_ne hb])
    have b1 : ∀ w, partBit w i (pureState st1) = partBit w i (pureState st) := fun w =>
      congrArg Prod.fst (e1 w)
    unfold TargetFlagSet at hf ⊢
    rw [hcur, hprev, b', b', b1, b1]
    exact hf

/-- A run inside one epoch keeps each target flag. Every slot step of the run is inside the
epoch, so none of them ends it. -/
theorem ChainRun.targetFlag_keep {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w)
    (he : u.slot.toNat / slotsPerEpoch = w.slot.toNat / slotsPerEpoch)
    {i : Nat} {e : Epoch} (hf : TargetFlagSet u i e) : TargetFlagSet w i e := by
  revert he hf
  induction h with
  | nil => intro _ hf; exact hf
  | @slot _ st st1 _ hlt hstep hrest ih =>
    intro he hf
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
      exact ih (by omega) (hstep.targetFlag_keep (by omega) hb hf)
  | block sb v hstep _ ih =>
    intro he hf
    obtain ⟨hs, -⟩ := hstep.slot
    exact ih (by rw [hs]; exact he) (hstep.keeps hf)

end

end EthCLSpecs.Proofs.Heze
