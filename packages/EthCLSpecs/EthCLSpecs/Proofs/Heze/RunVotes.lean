import EthCLSpecs.Proofs.Heze.KeyFrame
import EthCLSpecs.Proofs.Heze.Participation
import EthCLSpecs.Proofs.Heze.RunWeighs

/-!
# `EthCLSpecs.Proofs.Heze.RunVotes`: each target flag comes from a vote at a run state

`ChainRun.flag_explained` (`Participation.lean`) ties each target flag of a run to an
`IncludedVote`. That vote names the state `pre` on which `processAttestation` accepted the
attestation, but not where `pre` sits on the run. The FFG refinement needs more: the source
of the vote is a checkpoint of the run, and its target root is a block root of the run.

`RunVote` places the vote. The run reaches a state `u` before the block that includes the
attestation, and `pre` has the checkpoints, the slot, and the block roots of `u`
(`locView`). Every function of a block step before and inside the attestation loop keeps
these fields (`CheckpointFrame.lean`, `HeaderFrame.lean`), and `processBlockHeader` writes the
header only. `pre` also has the public keys, the fork, and the genesis validators root of `u`
(`keyView`, `KeyFrame.lean`). So an attestation that is valid on `pre` is valid on `u`. The
target epoch of the vote is the current or the previous epoch of `u`.

`ChainRun.flag_located` gives a `RunVote` for each target flag of an epoch after the epoch of
the start state, as `ChainRun.flag_explained` does for `IncludedVote`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_bind_eq_ok run_bind_eq_ok_pure
  run_assert_bind_eq_ok keepsUncached_bind keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Epoch Attestation AttestationData
  ValidatorIndex SignedBeaconBlock BeaconBlock currentEpochOf previousEpochOf)

section
variable [Preset] [HasherTag]

/-- The checkpoints, the slot, and the block roots. -/
def locView (st : State) :=
  (ordView st, sszGet st blockRoots)

variable [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- Two states with one `ordView` and one `hdrView` have one `locView`. -/
theorem locView_of_frames {s s' : BeaconState}
    (ho : ordView (pureState s') = ordView (pureState s))
    (hh : hdrView (pureState s') = hdrView (pureState s)) :
    locView (pureState s') = locView (pureState s) := by
  have e2 := congrArg Prod.snd hh
  simp only [locView, Prod.mk.injEq]
  exact ⟨ho, e2⟩

/-- A target flag after `processOperations` was set before it, or an attestation of the body
set it on a state with the `locView` and the `keyView` of the start state. -/
theorem processOperations_flags_at (body : EthCLSpecs.Heze.BeaconBlockBody)
    {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run (pureState st)
      = .ok ((), pureState st')) {j : Nat} {e : Epoch} (hf : TargetFlagSet st' j e) :
    TargetFlagSet st j e ∨ ∃ att ∈ body.attestations.toArray, ∃ pre post : BeaconState,
      att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j) ∧
      locView (pureState pre) = locView (pureState st) ∧
      keyView (pureState pre) = keyView (pureState st) := by
  -- The predicate: the state keeps `locView`, and a flag of `(j, e)` comes from `st` or from
  -- an attestation of the body on a state with the two views of `st`.
  let P : BeaconState → Prop := fun s => locView (pureState s) = locView (pureState st) ∧
    (TargetFlagSet s j e → TargetFlagSet st j e ∨
      ∃ att ∈ body.attestations.toArray, ∃ pre post : BeaconState,
        att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j) ∧
        locView (pureState pre) = locView (pureState st) ∧
        keyView (pureState pre) = keyView (pureState st))
  -- The state before each attestation also keeps `keyView`.
  let K : BeaconState → Prop := fun s => keyView (pureState s) = keyView (pureState st)
  have keep : ∀ s s' : BeaconState, P s →
      locView (pureState s') = locView (pureState s) →
      (∀ w, partView w j (pureState s') = partView w j (pureState s)) → P s' :=
    fun s s' hs hl hb => ⟨hl.trans hs.1, fun hf' => hs.2 (hf'.of_partView hb)⟩
  unfold EthCLSpecs.Heze.processOperations at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun ps _ =>
    keepsUncached_bind (keepsUncached_processProposerSlashing ps)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t1 : P s1 := forIn_array_ops_inv P _ keepsUncached_processProposerSlashing
    body.proposerSlashings.val
    (fun ps _ s s' hs hr => keep s s' hs
      (locView_of_frames (processProposerSlashing_frame_ord hr)
        (processProposerSlashing_frame_hdr hr))
      fun w => processProposerSlashing_frame_part (cur := w) (i := j) hr)
    st s1 ⟨rfl, fun h0 => .inl h0⟩ h1
  have k1 : K s1 := forIn_array_ops_inv K _ keepsUncached_processProposerSlashing
    body.proposerSlashings.val (fun _ _ _ _ hs hr => (processProposerSlashing_frame_key hr).trans hs)
    st s1 rfl h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttesterSlashing a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t2 : P s2 := forIn_array_ops_inv P _ keepsUncached_processAttesterSlashing
    body.attesterSlashings.val
    (fun a _ s s' hs hr => keep s s' hs
      (locView_of_frames (processAttesterSlashing_frame_ord hr)
        (processAttesterSlashing_frame_hdr hr))
      fun w => processAttesterSlashing_frame_part (cur := w) (i := j) hr)
    s1 s2 t1 h2
  have k2 : K s2 := forIn_array_ops_inv K _ keepsUncached_processAttesterSlashing
    body.attesterSlashings.val
    (fun _ _ _ _ hs hr => (processAttesterSlashing_frame_key hr).trans hs) s1 s2 k1 h2
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  -- The attestation loop: a new flag comes from the attestation that sets it, on a state with
  -- the two views of `st`.
  have t3 : P s3 ∧ K s3 := forIn_array_ops_inv (fun s => P s ∧ K s) _
    keepsUncached_processAttestation body.attestations.val
    (fun a ha s s' hs hr => by
      refine ⟨⟨(locView_of_frames (processAttestation_frame_ord hr)
        (processAttestation_frame_hdr hr)).trans hs.1.1, fun hf' => ?_⟩,
        (processAttestation_frame_key hr).trans hs.2⟩
      rcases processAttestation_explained a hr hf' with h0 | ⟨he, hv⟩
      · exact hs.1.2 h0
      · exact .inr ⟨a, ha, s, s', he, hv, hs.1.1, hs.2⟩)
    s2 s3 ⟨t2, k2⟩ h3
  replace t3 := t3.1
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processVoluntaryExit a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t4 : P s4 := forIn_array_ops_inv P _ keepsUncached_processVoluntaryExit
    body.voluntaryExits.val
    (fun a _ s s' hs hr => keep s s' hs
      (locView_of_frames (processVoluntaryExit_frame_ord hr) (processVoluntaryExit_frame_hdr hr))
      fun w => processVoluntaryExit_frame_part (cur := w) (i := j) hr)
    s3 s4 t3 h4
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processBlsToExecutionChange a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t5 : P s5 := forIn_array_ops_inv P _ keepsUncached_processBlsToExecutionChange
    body.blsToExecutionChanges.val
    (fun a _ s s' hs hr => keep s s' hs
      (locView_of_frames (processBlsToExecutionChange_frame_ord hr)
        (processBlsToExecutionChange_frame_hdr hr))
      fun w => processBlsToExecutionChange_frame_part (cur := w) (i := j) hr)
    s4 s5 t4 h5
  obtain ⟨⟨⟩, s6, h6, hp⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processPayloadAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  rw [pureState_inj (EthCLLib.Proofs.run_pure_state_eq _ _ _ _ hp)] at hf
  exact (forIn_array_ops_inv P _ keepsUncached_processPayloadAttestation
    body.payloadAttestations.val
    (fun a _ s s' hs hr => keep s s' hs
      (locView_of_frames (frame_of_reads (processPayloadAttestation_frame hr))
        (frame_of_reads (processPayloadAttestation_frame hr)))
      fun _ => frame_of_reads (processPayloadAttestation_frame hr))
    s5 s6 t5 h6).2 hf

/-- A target flag after `processBlock` was set before it, or an attestation of the block body
set it on a state with the `locView` and the `keyView` of the start state. -/
theorem processBlock_flags_at (b : BeaconBlock) {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState st)
      = .ok ((), pureState st')) {j : Nat} {e : Epoch} (hf : TargetFlagSet st' j e) :
    TargetFlagSet st j e ∨ ∃ att ∈ b.body.attestations.toArray, ∃ pre post : BeaconState,
      att.data.target.epoch = e ∧ VoteAt pre post att (UInt64.ofNat j) ∧
      locView (pureState pre) = locView (pureState st) ∧
      keyView (pureState pre) = keyView (pureState st) := by
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  obtain ⟨⟨⟩, s7, h7, h8⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  -- The steps before the operations keep `locView`. The header step writes the header only.
  have l1 := locView_of_frames (processParentExecutionPayload_frame_ord h1)
    (processParentExecutionPayload_frame_hdr h1)
  have l2 : locView (pureState s2) = locView (pureState s1) := by
    have e1 := processBlockHeader_frame_ord h2
    obtain ⟨-, -, -, e2, -⟩ := processBlockHeader_run_hdr _ _ _ h2
    simp only [locView, Prod.mk.injEq]
    exact ⟨e1, e2⟩
  have l3 := locView_of_frames (processWithdrawals_frame_ord h3) (processWithdrawals_frame_hdr h3)
  have l4 := locView_of_frames (processExecutionPayloadBid_frame_ord h4)
    (processExecutionPayloadBid_frame_hdr h4)
  have l5 := locView_of_frames (processRandao_frame_ord h5) (processRandao_frame_hdr h5)
  have l6 := locView_of_frames (processEth1Data_frame_ord h6) (processEth1Data_frame_hdr h6)
  have l16 := l6.trans (l5.trans (l4.trans (l3.trans (l2.trans l1))))
  -- The same steps keep `keyView`.
  have k16 := (processEth1Data_frame_key h6).trans ((processRandao_frame_key h5).trans
    ((processExecutionPayloadBid_frame_key h4).trans ((processWithdrawals_frame_key h3).trans
      ((processBlockHeader_frame_key h2).trans (processParentExecutionPayload_frame_key h1)))))
  have f8 := hf.of_partView fun w => processSyncAggregate_frame_part (cur := w) (i := j) h8
  rcases processOperations_flags_at b.body h7 f8 with f7 | ⟨att, ha, pre, post, he, hv, hl, hk⟩
  · refine .inl ?_
    have f6 := f7.of_partView fun w => processEth1Data_frame_part (cur := w) (i := j) h6
    have f5 := f6.of_partView fun w => processRandao_frame_part (cur := w) (i := j) h5
    have f4 := f5.of_partView fun w =>
      processExecutionPayloadBid_frame_part (cur := w) (i := j) h4
    have f3 := f4.of_partView fun w => processWithdrawals_frame_part (cur := w) (i := j) h3
    have f2 := f3.of_partView fun w => processBlockHeader_frame_part (cur := w) (i := j) h2
    exact f2.of_partView fun w =>
      processParentExecutionPayload_frame_part (cur := w) (i := j) h1
  · exact .inr ⟨att, ha, pre, post, he, hv, hl.trans l16, hk.trans k16⟩

/-- A vote of validator `i` with the data `data`, placed on the run. The run of the prefix
`s₁` reaches `u`, and the next step is the block that includes the attestation.
`processAttestation` accepted it on a state `pre` with the `locView` and the `keyView` of `u`.
The target epoch is the current or the previous epoch of `u`. -/
def RunVote (hi : Nat) (st₀ : BeaconState) (steps : List ChainStep) (i : ValidatorIndex)
    (data : AttestationData) : Prop :=
  ∃ (s₁ s₂ : List ChainStep) (sb : SignedBeaconBlock) (v : Bool) (u pre post : BeaconState)
    (att : Attestation),
    steps = s₁ ++ .block sb v :: s₂ ∧ ChainRun hi s₁ st₀ u ∧
    att ∈ sb.message.body.attestations.toArray ∧ att.data = data ∧ VoteAt pre post att i ∧
    locView (pureState pre) = locView (pureState u) ∧
    keyView (pureState pre) = keyView (pureState u) ∧
    (data.target.epoch = currentEpochOf (pureState u) ∨
      data.target.epoch = previousEpochOf (pureState u))

/-- A placed vote stays placed when more steps follow. -/
theorem RunVote.append {hi : Nat} {st₀ : BeaconState} {steps : List ChainStep}
    {i : ValidatorIndex} {data : AttestationData} (h : RunVote hi st₀ steps i data)
    (q : List ChainStep) : RunVote hi st₀ (steps ++ q) i data := by
  obtain ⟨s₁, s₂, sb, v, u, pre, post, att, hs, rest⟩ := h
  exact ⟨s₁, s₂ ++ q, sb, v, u, pre, post, att, by rw [hs]; simp, rest⟩

omit [Config] [CryptoBackend] in
/-- A target flag of epoch `e` names the current or the previous epoch. -/
theorem TargetFlagSet.epoch_cases {st : BeaconState} {j : Nat} {e : Epoch}
    (hf : TargetFlagSet st j e) :
    e = currentEpochOf (pureState st) ∨ e = previousEpochOf (pureState st) := by
  rcases hf with ⟨he, -⟩ | ⟨he, -, -⟩
  · exact .inl he
  · exact .inr he

/-- Along a run, a target flag at the end was set at the start, or a placed vote of the run
with that target epoch set it. The run starts after the prefix `p` from `st₀`. -/
theorem ChainRun.flag_located {hi : Nat} {st₀ : BeaconState} {q : List ChainStep}
    {u st : BeaconState} (h : ChainRun hi q u st) :
    ∀ {p : List ChainStep}, ChainRun hi p st₀ u → ∀ (i : Nat) (e : Epoch),
      TargetFlagSet st i e → TargetFlagSet u i e ∨
        ∃ data : AttestationData, data.target.epoch = e ∧
          RunVote hi st₀ (p ++ q) (UInt64.ofNat i) data := by
  induction h with
  | nil => exact fun _ _ _ hf => .inl hf
  | @slot steps st1 st2 _ hlt hstep hrest ih =>
    intro p hp i e hf
    rcases ih (p := p ++ [.slot]) (hp.append (.slot hlt hstep (.nil _))) i e hf with
      h1 | ⟨d, hd, hv⟩
    · exact .inl (hstep.targetFlag h1)
    · refine .inr ⟨d, hd, ?_⟩
      rwa [List.append_assoc, List.singleton_append] at hv
  | @block steps st1 st2 _ sb v hstep hrest ih =>
    intro p hp i e hf
    rcases ih (p := p ++ [.block sb v]) (hp.append (.block sb v hstep (.nil _))) i e hf with
      h1 | ⟨d, hd, hv⟩
    · rcases processBlock_flags_at sb.message hstep.2.1 h1 with
        h2 | ⟨att, ha, pre, post, he, hv, hl⟩
      · exact .inl h2
      · refine .inr ⟨att.data, he, p, steps, sb, v, st1, pre, post, att, rfl, hp, ha, rfl, hv,
          hl.1, hl.2, ?_⟩
        -- The flag after the block names an epoch there, and the block step keeps the slot.
        obtain ⟨hc, hpv⟩ := epochs_eq_of_toNat (a := st2) (b := st1) (by rw [hstep.slot.1])
        rcases h1.epoch_cases with h' | h'
        · exact .inl (he.trans (h'.trans hc))
        · exact .inr (he.trans (h'.trans hpv))
    · refine .inr ⟨d, hd, ?_⟩
      rwa [List.append_assoc, List.singleton_append] at hv

end

end EthCLSpecs.Proofs.Heze
