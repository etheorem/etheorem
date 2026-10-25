import EthCLSpecs.Proofs.Heze.Accountable
import EthCLSpecs.Proofs.Heze.PayloadRaceExec

/-!
# `EthCLSpecs.Proofs.Heze.StoreClock`: blocks, votes, and checkpoints before the clock

A head run of slot `t` reads a store whose blocks and checkpoints are no later than `t`.

## Blocks

A block of a traced store is the anchor block, or the block of an `onBlock` event of the trace
(`NodeTrace.blocks_origin`). `onBlock` checks that the current slot is at least the block slot
(`onBlock_run_ok_currentSlot`). The wall times of a clocked trace do not decrease, so that
current slot is at most `t` (`ClockedTrace.block_slot_le`). So every block of the store has a
slot of at most `t` (`HeadRun.Base.block_slot_le`).

## Votes

`process_attestation` asserts `data.slot + MIN_ATTESTATION_INCLUSION_DELAY <= state.slot`
(`processAttestation_run_slot`). The state is at the slot of the block that carries the vote.
So a placed vote is from a slot before its block (`RunVote.slot_lt_block`).

## Checkpoints

The epoch of each checkpoint of a traced store is at most the anchor epoch, or at most the
epoch of a block event of the trace (`NodeTrace.ckptWit`). `onBlock` writes the checkpoints of
the state after the block and of its pull-up. Their epochs are at most the epoch of that state
(`ckpt_epoch_le`, `pullup_epoch_le`). The slot of that state is the block slot. A tick copies
the unrealized checkpoints into the realized ones. The other events keep the checkpoints.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState runPure LawfulFcMap KeepsAt
  run_get_bind_eq_ok run_assert_bind_eq_ok run_bind_eq_ok_pure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint Slot
  AttestationData Attestation SignedBeaconBlock SignedInclusionList ValidatorIndex
  ExecutionPayload Transaction ExecutionRequests getCurrentSlot onBlock updateCheckpoints)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

/-! ## Blocks -/

section Blocks
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root]

/-- The anchor store holds the anchor block alone. -/
theorem getForkchoiceStore_blocks (A : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0) {k : Root}
    {b : BeaconBlock} (hb : FcMap.lookup s0.blocks k = some b) : b = a := by
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  by_cases hk : htr a = k
  · subst hk
    rw [LawfulFcMap.lookup_insert_self] at hb
    exact (Option.some.inj hb).symm
  · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk, LawfulFcMap.lookup_empty] at hb
    cases hb

/-- The four checkpoints of the anchor store are the anchor checkpoint. Its epoch is the
current epoch of the anchor state. -/
theorem getForkchoiceStore_ckpts (A : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0) :
    s0.justifiedCheckpoint.epoch.toNat = epochOf A ∧
    s0.finalizedCheckpoint.epoch.toNat = epochOf A ∧
    s0.unrealizedJustifiedCheckpoint.epoch.toNat = epochOf A ∧
    s0.unrealizedFinalizedCheckpoint.epoch.toNat = epochOf A := by
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  have e := currentEpochOf_epochOf A
  exact ⟨e, e, e, e⟩

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- **Where a block of a traced store comes from.** It is a block of the seed, or the block of
an `onBlock` event of the trace. The theorem names the trace before that event and the store
the event ran on. -/
theorem NodeTrace.blocks_origin {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    {k : Root} {b : BeaconBlock} (hb : FcMap.lookup s.blocks k = some b) :
    FcMap.lookup s0.blocks k = some b ∨
      ∃ (es1 es2 : List TraceEvent) (sb : SignedBeaconBlock)
        (arr1 : List (SignedInclusionList × UInt64)) (mid mid' : Store map),
        events = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧ NodeTrace s0 es1 arr1 mid ∧
        (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run mid
          = .ok ((), mid') ∧ sb.message = b := by
  induction h generalizing b with
  | nil => exact .inl hb
  | @handler events arrs pre post e htrace hrun ih =>
    -- An event that keeps `blocks` keeps the origin of each block.
    have hshift : FcMap.lookup pre.blocks k = some b →
        FcMap.lookup s0.blocks k = some b ∨
        ∃ (es1 es2 : List TraceEvent) (sb : SignedBeaconBlock)
          (arr1 : List (SignedInclusionList × UInt64)) (mid mid' : Store map),
          events ++ [TraceEvent.handler e] = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧
          NodeTrace s0 es1 arr1 mid ∧
          (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run mid
            = .ok ((), mid') ∧ sb.message = b := fun hpre => by
      rcases ih hpre with h0 | ⟨es1, es2, sb, arr1, mid, mid', hes, h1, h2, h3⟩
      · exact .inl h0
      · exact .inr ⟨es1, es2 ++ [.handler e], sb, arr1, mid, mid', by rw [hes]; simp, h1, h2, h3⟩
    have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
        KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
          (pre.blocks, pre.blockStates) x →
        x.run pre = .ok ((), post) → FcMap.lookup pre.blocks k = some b := by
      intro x hx hrunx
      have hmaps := hx pre () post rfl hrunx
      injection hmaps with hblocks _
      rw [← hblocks]
      exact hb
    cases e with
    | tick time => exact hshift (hkeep _ (onTick_keeps_blockMaps _ time) hrun)
    | attestation att isFromBlock =>
      exact hshift (hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock) hrun)
    | attesterSlashing asl =>
      exact hshift (hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl) hrun)
    | payloadAttestation msg isFromBlock =>
      exact hshift (hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) hrun)
    | envelope signedEnv =>
      obtain ⟨hblocks, -⟩ := onExecutionPayloadEnvelope_run_keys signedEnv pre post hrun
      exact hshift (hblocks ▸ hb)
    | block sb =>
      obtain ⟨hblocks, -⟩ := onBlock_run_maps sb pre post hrun
      rw [hblocks] at hb
      by_cases hk : htr sb.message = k
      · subst hk
        rw [LawfulFcMap.lookup_insert_self] at hb
        exact .inr ⟨events, [], sb, arrs, pre, post, rfl, htrace, hrun, Option.some.inj hb⟩
      · rw [LawfulFcMap.lookup_insert_ne _ _ _ _ hk] at hb
        exact hshift hb
  | @inclusionList events arrs pre post signed t htrace hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    rcases ih hb with h0 | ⟨es1, es2, sb, arr1, mid, mid', hes, h1, h2, h3⟩
    · exact .inl h0
    · exact .inr ⟨es1, es2 ++ [.inclusionList signed], sb, arr1, mid, mid', by rw [hes]; simp,
        h1, h2, h3⟩

/-- A block event of a clocked trace ran at a current slot no greater than the current slot
of a later query. This is `ClockedTrace.attestation_slot_le` for a block event. -/
theorem ClockedTrace.block_slot_le {s0 s σ : Store map} {tevs P rest : List (TraceEvent × Nat)}
    {arrivals arr : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    (hsplit : tevs = P ++ rest) (hσ : NodeTrace s0 (P.map Prod.fst) arr σ) {w : Nat}
    (hwall : ∀ y ∈ P, y.2 ≤ w) (htime : σ.time.toNat = w / 1000)
    {es1 es2 : List TraceEvent} {sb : SignedBeaconBlock}
    (hes : P.map Prod.fst = es1 ++ TraceEvent.handler (.block sb) :: es2)
    {arr1 : List (SignedInclusionList × UInt64)} {mid : Store map}
    (hmid : NodeTrace s0 es1 arr1 mid) {u₁ u₁' u₂ u₂' : Store map} {cs₁ cs₂ : Slot}
    (h₁ : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) mid).run u₁
      = .ok (cs₁, u₁'))
    (h₂ : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) σ).run u₂
      = .ok (cs₂, u₂')) :
    cs₁.toNat ≤ cs₂.toNat := by
  obtain ⟨P1, P2', hP, hP1, hP2'⟩ := List.map_eq_append_iff.mp hes
  obtain ⟨x, P2, rfl, hx, -⟩ := List.map_eq_cons_iff.mp hP2'
  have hclock := hct.clock P1 x (P2 ++ rest) (by rw [hsplit, hP]; simp) arr1 mid (hP1 ▸ hmid)
  have hmidTime : mid.time.toNat = x.2 / 1000 := by
    unfold ClockAt at hclock
    rw [hx] at hclock
    exact hclock
  have hxw : x.2 ≤ w := hwall x (by rw [hP]; simp)
  have hg : mid.genesisTime = σ.genesisTime := hmid.genesisTime.trans hσ.genesisTime.symm
  refine getCurrentSlot_le_of_time mid σ hg ?_ h₁ h₂
  rw [hmidTime, htime]
  exact Nat.div_le_div_right hxw

/-- **A block of a head-run store is no later than the slot of the run.** The block is the
anchor block, no later than `rb`, or the block of an `onBlock` event of the prefix. -/
theorem HeadRun.Base.block_slot_le {n : NodeRun map} {q : HeadRun map} {r : Root}
    {rb : BeaconBlock} {t : Nat} (hn : n.Honest rb) (hq : q.Base n r rb t)
    (hlo : rb.slot.toNat < t) {k : Root} {b : BeaconBlock}
    (hb : FcMap.lookup q.store.blocks k = some b) : b.slot.toNat ≤ t := by
  obtain ⟨cs, hcs, hcur⟩ := hq.slot
  rcases hq.trace.blocks_origin hb with h0 | ⟨es1, es2, sb, arr1, mid, mid', hes, h1, h2, rfl⟩
  · have := getForkchoiceStore_blocks _ _ _ hn.anchorStore h0
    subst this
    have := UInt64.le_iff_toNat_le.mp hn.anchorSlot
    omega
  · obtain ⟨cs₁, u, u', hcs₁, hge⟩ := onBlock_run_ok_currentSlot sb mid mid' h2
    obtain ⟨rest, hsplit⟩ := hq.isPrefix
    have hle := hn.clocked.block_slot_le hsplit hq.trace hq.wall hq.time hes h1 hcs₁ hcur
    have := UInt64.le_iff_toNat_le.mp hge
    omega

/-- **A block event of the prefix of a head run is no later than the slot of the run.**
`onBlock` checked the block slot against the current slot of the store it ran on. -/
theorem HeadRun.Base.event_slot_le {n : NodeRun map} {q : HeadRun map} {r : Root}
    {rb : BeaconBlock} {t : Nat} (hn : n.Honest rb) (hq : q.Base n r rb t)
    {sb : SignedBeaconBlock} (hm : TraceEvent.handler (.block sb) ∈ q.events.map Prod.fst) :
    sb.message.slot.toNat ≤ t := by
  obtain ⟨cs, hcs, hcur⟩ := hq.slot
  obtain ⟨es1, es2, hes⟩ := List.append_of_mem hm
  obtain ⟨mid, arr1, arr2, h1, h2, -⟩ := hq.trace.split hes
  obtain ⟨post, a1, a2, hsingle, -, -⟩ :=
    h2.split (es1 := [TraceEvent.handler (.block sb)]) (es2 := es2) rfl
  have hrun := hsingle.single_handler
  obtain ⟨cs₁, u, u', hcs₁, hge⟩ := onBlock_run_ok_currentSlot sb mid post hrun
  obtain ⟨rest, hsplit⟩ := hq.isPrefix
  have hle := hn.clocked.block_slot_le hsplit hq.trace hq.wall hq.time hes h1 hcs₁ hcur
  have := UInt64.le_iff_toNat_le.mp hge
  omega

/-- A block of an ancestor path is in the store, at some root. -/
theorem AncestorPath.mem_lookup {a : BeaconBlock} {s : Store map} {k : Root}
    {bs : List BeaconBlock} (h : AncestorPath a s k bs) {x : BeaconBlock} (hx : x ∈ bs) :
    ∃ k', FcMap.lookup s.blocks k' = some x := by
  induction h with
  | anchor => exact absurd hx List.not_mem_nil
  | @cons k b bs hk _ _ ih =>
    rcases List.mem_append.mp hx with hx | hx
    · exact ih hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨k, hk⟩

end Blocks

/-! ## Votes -/

section Votes
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- A successful `processAttestation` passed two checks. The target epoch is the epoch of the
attestation slot. The attestation slot plus the inclusion delay is at most the state slot. -/
theorem processAttestation_run_slot (att : Attestation) (st : BeaconState)
    {r : PUnit × EthCLSpecs.Heze.State}
    (h : (EthCLSpecs.Heze.processAttestation (StateTransition := HezeRun) att).run
      (pureState st) = .ok r) :
    att.data.target.epoch = EthCLSpecs.Heze.computeEpochAtSlot att.data.slot ∧
    att.data.slot.toNat + EthCLSpecs.Heze.Const.minAttestationInclusionDelay.toNat ≤
      st.slot.toNat := by
  unfold EthCLSpecs.Heze.processAttestation at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hep, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨incl, s1, hincl, h⟩ := run_bind_eq_ok_pure (by frame_keeps) h
  obtain ⟨-, hv, hfit⟩ := checkedAdd_run_ok hincl
  obtain ⟨hle, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  have hle' := UInt64.le_iff_toNat_le.mp hle
  rw [hv, UInt64.toNat_add, Nat.mod_eq_of_lt hfit] at hle'
  exact ⟨beq_iff_eq.mp hep, hle'⟩

/-- The block of a run step is a block of the run. -/
theorem mem_blocksOf_block (s₁ s₂ : List ChainStep) (sb : SignedBeaconBlock) (v : Bool) :
    sb.message ∈ blocksOf (s₁ ++ .block sb v :: s₂) := by
  rw [blocksOf_append]
  exact List.mem_append_right _ List.mem_cons_self

/-- **A placed vote is from a slot before its block.** The target epoch is the epoch of the
vote slot. The block of the vote is a block of the run. The state before the block is at the
block slot, and `processAttestation` ran on a state with that slot. -/
theorem RunVote.slot_lt_block {hi : Nat} {st₀ v : BeaconState} {steps : List ChainStep}
    {i : ValidatorIndex} {d : AttestationData} (hv : RunVote hi st₀ steps i d)
    (hrun : ChainRun hi steps st₀ v) :
    d.target.epoch.toNat = d.slot.toNat / slotsPerEpoch ∧
    ∃ b ∈ blocksOf steps, d.slot.toNat +
      EthCLSpecs.Heze.Const.minAttestationInclusionDelay.toNat ≤ b.slot.toNat := by
  obtain ⟨s₁, s₂, sb, vb, u, pre, post, att, hs, hr, -, hd, hvote, hloc, -⟩ := hv
  obtain ⟨hpa, -⟩ := hvote
  obtain ⟨s, hs', -⟩ := runPure_ok_run hpa
  obtain ⟨hep, hslot⟩ := processAttestation_run_slot att pre hs'
  rw [hd] at hslot hep
  refine ⟨by rw [hep, computeEpochAtSlot_toNat], ?_⟩
  have hpre : pre.slot = u.slot := (locView_eq hloc).2.1
  -- The block step after `s₁` starts at `u`.
  rw [hs] at hrun
  obtain ⟨m, hm1, hm2⟩ := hrun.split
  rw [← hr.det hm1] at hm2
  cases hm2 with
  | block _ _ hstep _ =>
    obtain ⟨-, hsb⟩ := hstep.slot
    refine ⟨sb.message, hs ▸ mem_blocksOf_block s₁ s₂ sb vb, ?_⟩
    rw [hsb, ← hpre]
    exact hslot

end Votes

/-! ## Checkpoints -/

section Ckpts
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The epoch `x` is at most the epoch of the anchor state, or at most the epoch of a block
event of `events`. -/
def EpochWit (A : BeaconState) (events : List TraceEvent) (x : Nat) : Prop :=
  x ≤ epochOf A ∨ ∃ sb : SignedBeaconBlock, TraceEvent.handler (.block sb) ∈ events ∧
    x ≤ sb.message.slot.toNat / slotsPerEpoch

/-- Each of the four checkpoint epochs of `s` has a witness in `events`. -/
def CkptWit (A : BeaconState) (events : List TraceEvent) (s : Store map) : Prop :=
  EpochWit A events s.justifiedCheckpoint.epoch.toNat ∧
  EpochWit A events s.finalizedCheckpoint.epoch.toNat ∧
  EpochWit A events s.unrealizedJustifiedCheckpoint.epoch.toNat ∧
  EpochWit A events s.unrealizedFinalizedCheckpoint.epoch.toNat

omit [HasherTag] [Config] [CryptoBackend] in
/-- A witness stays a witness when more events follow. -/
theorem EpochWit.mono {A : BeaconState} {es es' : List TraceEvent} {x : Nat}
    (hsub : ∀ e ∈ es, e ∈ es') (h : EpochWit A es x) : EpochWit A es' x := by
  rcases h with h | ⟨sb, hm, h⟩
  · exact .inl h
  · exact .inr ⟨sb, hsub _ hm, h⟩

omit [HasherTag] [Config] [CryptoBackend] in
/-- A `ckptPick` of two checkpoints with witnesses has a witness. -/
theorem EpochWit.pick {A : BeaconState} {es : List TraceEvent} {old c : Checkpoint}
    (h1 : EpochWit A es old.epoch.toNat) (h2 : EpochWit A es c.epoch.toNat) :
    EpochWit A es (ckptPick old c).epoch.toNat := by
  rcases ckptPick_cases old c with e | e <;> rw [e]
  · exact h1
  · exact h2

/-- **The checkpoint witnesses along a trace.** The epoch of each checkpoint of a traced store is
at most the anchor epoch, or at most the epoch of a block event of the trace. The store before
each event meets `CkptInv`. -/
theorem NodeTrace.ckptWit {A : BeaconState} {a : BeaconBlock} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (hord : StateCkptOrd A)
    (hinv : ∀ es1 es2 arr1 mid, events = es1 ++ es2 → NodeTrace s0 es1 arr1 mid →
      CkptInv A a mid)
    (h0 : CkptWit A [] s0) : CkptWit A events s := by
  induction h with
  | nil => exact h0
  | @handler events arrs pre post e htrace hrun ih =>
    have ih := ih fun es1 es2 arr1 mid hes h1 => hinv es1 (es2 ++ [.handler e]) arr1 mid
      (by rw [hes]; simp) h1
    have hsub : ∀ x ∈ events, x ∈ events ++ [TraceEvent.handler e] :=
      fun x hx => List.mem_append_left _ hx
    obtain ⟨wj, wf, wuj, wuf⟩ := ih
    have wj := wj.mono hsub
    have wf := wf.mono hsub
    have wuj := wuj.mono hsub
    have wuf := wuf.mono hsub
    -- An event that keeps the four checkpoints keeps the witnesses.
    have hkeep : storeCkpts post = storeCkpts pre →
        CkptWit A (events ++ [TraceEvent.handler e]) post := fun hck => by
      simp only [storeCkpts, Prod.mk.injEq] at hck
      obtain ⟨c1, c2, c3, c4⟩ := hck
      rw [CkptWit, c1, c2, c3, c4]
      exact ⟨wj, wf, wuj, wuf⟩
    cases e with
    | tick time =>
      obtain ⟨-, uj, uf, j, f, -⟩ := onTick_growsAt time pre () post hrun
      refine ⟨?_, ?_, by rw [uj]; exact wuj, by rw [uf]; exact wuf⟩
      · rcases j with e | e <;> rw [e]
        · exact wj
        · exact wuj
      · rcases f with e | e <;> rw [e]
        · exact wf
        · exact wuf
    | attestation att isFromBlock =>
      exact hkeep (onAttestation_keeps_ckpts _ att isFromBlock pre () post rfl hrun)
    | attesterSlashing asl =>
      exact hkeep (onAttesterSlashing_keeps_ckpts _ asl pre () post rfl hrun)
    | payloadAttestation msg isFromBlock =>
      exact hkeep (onPayloadAttestationMessage_keeps_ckpts _ msg isFromBlock pre () post rfl hrun)
    | envelope signedEnv =>
      exact hkeep (onExecutionPayloadEnvelope_keeps_ckpts _ signedEnv pre () post rfl hrun)
    | block sb =>
      have hpre := hinv events [.handler (.block sb)] arrs pre rfl htrace
      obtain ⟨pv, w, u, hps, htrans, -, hbsu, hck, hpull⟩ :=
        onBlock_run_ckpt sb pre post hpre.slot.statesPure hrun
      obtain ⟨j1, f1, uj1, uf1, -, bs1⟩ :=
        updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, LawfulFcMap.lookup_insert_self]
      obtain ⟨pulled, hjf, -, -, puj, puf, hj⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
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
      have hmem : TraceEvent.handler (.block sb) ∈ events ++ [TraceEvent.handler (.block sb)] :=
        List.mem_append_right _ List.mem_cons_self
      have hwE : ∀ x, x ≤ epochOf w →
          EpochWit A (events ++ [TraceEvent.handler (.block sb)]) x := fun x hx =>
        .inr ⟨sb, hmem, by unfold epochOf at hx; rw [hwslot] at hx; exact hx⟩
      obtain ⟨ef, ej⟩ := ckpt_epoch_le hrunW hord
      obtain ⟨pf, pj⟩ := pullup_epoch_le hrunW hord hjf
      simp only [storeCkpts, Prod.mk.injEq] at hck
      obtain ⟨cj, cf, cuj, cuf⟩ := hck
      -- The realized pair between the two writes.
      have mj : EpochWit A (events ++ [TraceEvent.handler (.block sb)])
          (updateCheckpoints u w.currentJustifiedCheckpoint
            w.finalizedCheckpoint).justifiedCheckpoint.epoch.toNat := by
        rw [j1, cj]
        exact EpochWit.pick wj (hwE _ ej)
      have mf : EpochWit A (events ++ [TraceEvent.handler (.block sb)])
          (updateCheckpoints u w.currentJustifiedCheckpoint
            w.finalizedCheckpoint).finalizedCheckpoint.epoch.toNat := by
        rw [f1, cf]
        exact EpochWit.pick wf (hwE _ ef)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hj with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
        · exact mj
        · exact EpochWit.pick mj (hwE _ pj)
      · rcases hj with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
        · exact mf
        · exact EpochWit.pick mf (hwE _ pf)
      · rw [puj, uj1, cuj]
        exact EpochWit.pick wuj (hwE _ pj)
      · rw [puf, uf1, cuf]
        exact EpochWit.pick wuf (hwE _ pf)
  | @inclusionList events arrs pre post signed t htrace hclock hrun ih =>
    have ih := ih fun es1 es2 arr1 mid hes h1 => hinv es1 (es2 ++ [.inclusionList signed]) arr1
      mid (by rw [hes]; simp) h1
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    have hsub : ∀ x ∈ events, x ∈ events ++ [TraceEvent.inclusionList signed] :=
      fun x hx => List.mem_append_left _ hx
    obtain ⟨wj, wf, wuj, wuf⟩ := ih
    exact ⟨wj.mono hsub, wf.mono hsub, wuj.mono hsub, wuf.mono hsub⟩

/-- The checkpoint `c` is the anchor checkpoint of `A` and `a`, or it is from a later epoch
than the anchor state. -/
def Above (A : BeaconState) (a : BeaconBlock) (c : Checkpoint) : Prop :=
  c = { epoch := EthCLSpecs.Heze.currentEpochOf (pureState A), root := htr a } ∨
    epochOf A < c.epoch.toNat

omit [Config] [CryptoBackend] [FcMap map] [LawfulFcMap map Root]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- `ckptPick` keeps `Above`: it keeps the old checkpoint, or it takes one of a greater
epoch. -/
theorem Above.pick {A : BeaconState} {a : BeaconBlock} {old c : Checkpoint}
    (h : Above A a old) : Above A a (ckptPick old c) := by
  unfold ckptPick
  split
  · rename_i hgt
    refine .inr ?_
    have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
    rcases h with rfl | h
    · rw [currentEpochOf_epochOf] at hgt'
      exact hgt'
    · omega
  · exact h

omit [Config] [CryptoBackend] [FcMap map] [LawfulFcMap map Root]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- A checkpoint with `Above` is no earlier than the anchor epoch. -/
theorem Above.epoch_ge {A : BeaconState} {a : BeaconBlock} {c : Checkpoint}
    (h : Above A a c) : epochOf A ≤ c.epoch.toNat := by
  rcases h with rfl | h
  · exact Nat.le_of_eq (currentEpochOf_epochOf A).symm
  · exact Nat.le_of_lt h

/-- The four checkpoints of `s` meet `Above`. -/
def CkptAbove (A : BeaconState) (a : BeaconBlock) (s : Store map) : Prop :=
  Above A a s.justifiedCheckpoint ∧ Above A a s.finalizedCheckpoint ∧
    Above A a s.unrealizedJustifiedCheckpoint ∧ Above A a s.unrealizedFinalizedCheckpoint

omit [LawfulFcMap map Root] in
/-- The anchor store meets `CkptAbove`: its four checkpoints are the anchor checkpoint. -/
theorem CkptAbove.anchor (A : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : EthCLSpecs.Heze.getForkchoiceStore (pureState A) a = .ok s0) : CkptAbove A a s0 := by
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  exact ⟨.inl rfl, .inl rfl, .inl rfl, .inl rfl⟩

/-- **`CkptAbove` along a trace.** Every write of a checkpoint is a `ckptPick` or a copy of an
unrealized checkpoint into a realized one. The store before each event has uncached block
states. -/
theorem NodeTrace.ckptAbove {A : BeaconState} {a : BeaconBlock} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (hp : BlockStatesPure s0) (h0 : CkptAbove A a s0) :
    CkptAbove A a s := by
  induction h with
  | nil => exact h0
  | @handler events arrs pre post e htrace hrun ih =>
    obtain ⟨wj, wf, wuj, wuf⟩ := ih
    have hpre := htrace.blockStatesPure hp
    have hkeep : storeCkpts post = storeCkpts pre → CkptAbove A a post := fun hck => by
      simp only [storeCkpts, Prod.mk.injEq] at hck
      obtain ⟨c1, c2, c3, c4⟩ := hck
      rw [CkptAbove, c1, c2, c3, c4]
      exact ⟨wj, wf, wuj, wuf⟩
    cases e with
    | tick time =>
      obtain ⟨-, uj, uf, j, f, -⟩ := onTick_growsAt time pre () post hrun
      refine ⟨?_, ?_, by rw [uj]; exact wuj, by rw [uf]; exact wuf⟩
      · rcases j with e | e <;> rw [e]
        · exact wj
        · exact wuj
      · rcases f with e | e <;> rw [e]
        · exact wf
        · exact wuf
    | attestation att isFromBlock =>
      exact hkeep (onAttestation_keeps_ckpts _ att isFromBlock pre () post rfl hrun)
    | attesterSlashing asl =>
      exact hkeep (onAttesterSlashing_keeps_ckpts _ asl pre () post rfl hrun)
    | payloadAttestation msg isFromBlock =>
      exact hkeep (onPayloadAttestationMessage_keeps_ckpts _ msg isFromBlock pre () post rfl hrun)
    | envelope signedEnv =>
      exact hkeep (onExecutionPayloadEnvelope_keeps_ckpts _ signedEnv pre () post rfl hrun)
    | block sb =>
      obtain ⟨pv, w, u, -, -, -, hbsu, hck, hpull⟩ := onBlock_run_ckpt sb pre post hpre hrun
      obtain ⟨j1, f1, uj1, uf1, -, bs1⟩ :=
        updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
      have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
        rw [bs1, hbsu, LawfulFcMap.lookup_insert_self]
      obtain ⟨pulled, -, -, -, puj, puf, hj⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
      simp only [storeCkpts, Prod.mk.injEq] at hck
      obtain ⟨cj, cf, cuj, cuf⟩ := hck
      have mj : Above A a (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).justifiedCheckpoint := by
        rw [j1, cj]; exact wj.pick
      have mf : Above A a (updateCheckpoints u w.currentJustifiedCheckpoint
          w.finalizedCheckpoint).finalizedCheckpoint := by
        rw [f1, cf]; exact wf.pick
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hj with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
        · exact mj
        · exact mj.pick
      · rcases hj with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
        · exact mf
        · exact mf.pick
      · rw [puj, uj1, cuj]; exact wuj.pick
      · rw [puf, uf1, cuf]; exact wuf.pick
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

end Ckpts

end EthCLSpecs.Proofs.Heze
