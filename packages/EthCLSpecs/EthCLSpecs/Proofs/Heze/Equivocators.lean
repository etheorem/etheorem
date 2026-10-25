import EthCLLib.Proofs.ArrayUnion
import EthCLSpecs.Proofs.Heze.RootFrames
import EthCLSpecs.Proofs.Heze.StorePure

/-!
# `EthCLSpecs.Proofs.Heze.Equivocators`: an honest signer is never an equivocator

The score skips every index in `equivocating_indices`. `storeSide` (`PayloadRaceRefines.lean`)
puts such an index on `neither`. This module proves that an index enters the set only
through an attester slashing that marks it. The link from `latestMessages` to the votes
of a validator is a separate fact, and this module does not state it.

`on_attester_slashing` (phase0 `fork-choice.md:979`) is the only handler that writes the
set. It adds the indices common to two attestations. The data must be slashable, and both
attestations must pass `is_valid_indexed_attestation` against the justified state.
`onAttesterSlashing_run_ok` states the result of one run, and
`onAttesterSlashing_new_member` reads it for one index (`SlashingMarks`). The five other
handlers keep the set, by `keeps_solve`. `onInclusionList` writes only the IL store.

`NodeTrace.equivocator_source` lifts this to a trace. An index in the final set was in the
seed, or an attester slashing of the trace marks it in the store before that event.
`getForkchoiceStore` seeds the set empty.

The justified state is a box in `blockStates`. Under `BlockStatesPure` it is the uncached
box of a plain value, so the statements bind that value. The trace lemmas take the
predicate at the seed, and `NodeTrace.blockStatesPure` carries it along the trace.

`honest_not_equivocating` concludes that `i` is not in the set. Its hypothesis
`HonestSigner` says that no attester slashing of the trace marks `i` in the store before
it. That holds when `i` never signs two slashable attestation data and no one forges its
signature. The theorem takes it as a hypothesis, so `#axioms` shows no signature
assumption.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt LawfulFcMap pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState Root Attestation AttesterSlashing BeaconBlock
  SignedBeaconBlock PayloadAttestationMessage SignedExecutionPayloadEnvelope ExecutionPayload
  ExecutionRequests Transaction SignedInclusionList ValidatorIndex onTick onBlock onAttestation
  onAttesterSlashing onPayloadAttestationMessage onExecutionPayloadEnvelope getForkchoiceStore
  isSlashableAttestationData isValidIndexedAttestation)

/-- A member of `arrayInter xs ys` is in both arrays. -/
theorem mem_arrayInter {xs ys : Array ValidatorIndex} {i : ValidatorIndex}
    (h : i ∈ arrayInter xs ys) : i ∈ xs ∧ i ∈ ys := by
  unfold arrayInter at h
  rw [Array.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

section
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]

/-- The attester slashing `asl` marks `i` against the state `st`: the two data are
slashable, both attestations pass `isValidIndexedAttestation`, and `i` is in both. -/
def SlashingMarks (st : BeaconState) (asl : AttesterSlashing) (i : ValidatorIndex) : Prop :=
  isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true ∧
  isValidIndexedAttestation (pureState st) asl.attestation1 = .ok true ∧
  isValidIndexedAttestation (pureState st) asl.attestation2 = .ok true ∧
  i ∈ asl.attestation1.attestingIndices.toArray ∧
  i ∈ asl.attestation2.attestingIndices.toArray

omit [Config] in
/-- The contract of `on_attester_slashing`. A successful run passed its three checks
against the justified state of the store before the run, and wrote one field: the old set
joined with the indices common to the two attestations. Under `BlockStatesPure`, the
justified state is the uncached box of `st`. -/
@[characterizes EthCLSpecs.Heze.onAttesterSlashing]
theorem onAttesterSlashing_run_ok (asl : AttesterSlashing) (s s' : Store map)
    (hp : BlockStatesPure s)
    (h : (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      asl).run s = .ok ((), s')) :
    ∃ st : BeaconState,
      FcMap.lookup s.blockStates s.justifiedCheckpoint.root = some (pureState st) ∧
      isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true ∧
      isValidIndexedAttestation (pureState st) asl.attestation1 = .ok true ∧
      isValidIndexedAttestation (pureState st) asl.attestation2 = .ok true ∧
      s' = { s with
        equivocatingIndices := arrayUnion s.equivocatingIndices
          (arrayInter asl.attestation1.attestingIndices.toArray
            asl.attestation2.attestingIndices.toArray) } := by
  unfold onAttesterSlashing at h
  cases hst : FcMap.lookup s.blockStates s.justifiedCheckpoint.root with
  | none =>
    by_cases hsl : isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true <;>
      simp [hsl, hst, FcMap.getOrThrow, FcMap.getOrThrowKey] at h <;> cases h
  | some st0 =>
    -- The justified state is the uncached box of a value `st`.
    obtain ⟨st, hst'⟩ := hp.lookup _ (by rw [hst]; rfl)
    rw [hst] at hst'
    injection hst' with hst'
    subst hst'
    by_cases hsl : isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true
    · -- Each validity check is an `Except` read: a fault or `false` ends the run.
      cases hv1 : isValidIndexedAttestation (pureState st) asl.attestation1 with
      | error e =>
        simp [hsl, hst, hv1, FcMap.getOrThrow, FcMap.getOrThrowKey, liftErr, Except.mapError,
          MonadExcept.ofExcept] at h <;> cases h
      | ok b1 =>
        cases hv2 : isValidIndexedAttestation (pureState st) asl.attestation2 with
        | error e =>
          cases b1 <;>
            simp [hsl, hst, hv1, hv2, FcMap.getOrThrow, FcMap.getOrThrowKey, liftErr,
              Except.mapError, MonadExcept.ofExcept] at h <;> cases h
        | ok b2 =>
          -- `cases h` on the success run names the written store.
          cases b1 <;> cases b2 <;>
            simp [hsl, hst, hv1, hv2, FcMap.getOrThrow, FcMap.getOrThrowKey, liftErr,
              Except.mapError, MonadExcept.ofExcept] at h <;> cases h
          exact ⟨st, rfl, hsl, hv1, hv2, rfl⟩
    · simp [hsl, FcMap.getOrThrow, FcMap.getOrThrowKey] at h
      cases h

omit [Config] in
/-- After a successful `onAttesterSlashing`, the slashing marks each new member of
`equivocatingIndices`, against the justified state of the store before the run. -/
theorem onAttesterSlashing_new_member (asl : AttesterSlashing) (s s' : Store map)
    (i : ValidatorIndex) (hp : BlockStatesPure s)
    (h : (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      asl).run s = .ok ((), s'))
    (hnew : i ∈ s'.equivocatingIndices) (hold : i ∉ s.equivocatingIndices) :
    ∃ st : BeaconState,
      FcMap.lookup s.blockStates s.justifiedCheckpoint.root = some (pureState st) ∧
      SlashingMarks st asl i := by
  obtain ⟨st, hst, hsl, hv1, hv2, rfl⟩ := onAttesterSlashing_run_ok asl s s' hp h
  rcases (EthCLLib.Proofs.mem_arrayUnion _ _ _).mp hnew with h' | h'
  · exact absurd h' hold
  · obtain ⟨h1, h2⟩ := mem_arrayInter h'
    exact ⟨st, hst, hsl, hv1, hv2, h1, h2⟩

omit [CryptoBackend] in
/-- `onTick` keeps `equivocatingIndices`. -/
theorem onTick_keeps_equivocating (v : Array ValidatorIndex) (time : UInt64) :
    KeepsAt (fun st : Store map => st.equivocatingIndices) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps `equivocatingIndices`. -/
theorem onBlock_keeps_equivocating (v : Array ValidatorIndex) (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => st.equivocatingIndices) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

/-- `onAttestation` keeps `equivocatingIndices`. It reads the set to skip equivocators. -/
theorem onAttestation_keeps_equivocating (v : Array ValidatorIndex) (att : Attestation)
    (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.equivocatingIndices) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

/-- `onPayloadAttestationMessage` keeps `equivocatingIndices`. -/
theorem onPayloadAttestationMessage_keeps_equivocating (v : Array ValidatorIndex)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.equivocatingIndices) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

section EngineSeam
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps `equivocatingIndices`. -/
theorem onExecutionPayloadEnvelope_keeps_equivocating (v : Array ValidatorIndex)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => st.equivocatingIndices) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- A member of `equivocatingIndices` after one handler event was a member before, or the
event is an attester slashing that marks it against the justified state of the store
before the event. -/
theorem HandlerEvent.run_equivocating (e : HandlerEvent) (s s' : Store map) (i : ValidatorIndex)
    (hp : BlockStatesPure s) (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s'))
    (hi : i ∈ s'.equivocatingIndices) :
    i ∈ s.equivocatingIndices ∨ ∃ (asl : AttesterSlashing) (st : BeaconState),
      e = .attesterSlashing asl ∧
      FcMap.lookup s.blockStates s.justifiedCheckpoint.root = some (pureState st) ∧
      SlashingMarks st asl i := by
  have keep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      KeepsAt (fun st : Store map => st.equivocatingIndices) s.equivocatingIndices x →
      x.run s = .ok ((), s') → i ∈ s.equivocatingIndices := fun x hk hx =>
    (hk s () s' rfl hx) ▸ hi
  cases e with
  | tick time => exact .inl (keep _ (onTick_keeps_equivocating _ time) h)
  | block signedBlock => exact .inl (keep _ (onBlock_keeps_equivocating _ signedBlock) h)
  | attestation att isFromBlock =>
    exact .inl (keep _ (onAttestation_keeps_equivocating _ att isFromBlock) h)
  | attesterSlashing asl =>
    by_cases hold : i ∈ s.equivocatingIndices
    · exact .inl hold
    · obtain ⟨st, hst, hm⟩ := onAttesterSlashing_new_member asl s s' i hp h hi hold
      exact .inr ⟨asl, st, rfl, hst, hm⟩
  | payloadAttestation msg isFromBlock =>
    exact .inl (keep _ (onPayloadAttestationMessage_keeps_equivocating _ msg isFromBlock) h)
  | envelope signedEnv =>
    exact .inl (keep _ (onExecutionPayloadEnvelope_keeps_equivocating _ signedEnv) h)

/-- Where a member of `equivocatingIndices` at the end of a trace comes from: the seed, or
an attester slashing of the trace that marks it in the store before that event. The seed
holds only uncached boxes in `blockStates`. -/
theorem NodeTrace.equivocator_source [LawfulFcMap map Root] {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (h0 : BlockStatesPure s0)
    (i : ValidatorIndex) (hi : i ∈ s.equivocatingIndices) :
    i ∈ s0.equivocatingIndices ∨
      ∃ (es1 es2 : List TraceEvent) (asl : AttesterSlashing) (pre : Store map)
        (arr : List (SignedInclusionList × UInt64)) (st : BeaconState),
        events = es1 ++ TraceEvent.handler (.attesterSlashing asl) :: es2 ∧
        NodeTrace s0 es1 arr pre ∧
        FcMap.lookup pre.blockStates pre.justifiedCheckpoint.root = some (pureState st) ∧
        SlashingMarks st asl i := by
  revert hi
  induction h with
  | nil => exact .inl
  | handler e htrace hrun ih =>
    intro hi
    rcases HandlerEvent.run_equivocating e _ _ i (htrace.blockStatesPure h0) hrun hi with
      hprev | ⟨asl, st, rfl, hst, hm⟩
    · rcases ih hprev with h0 | ⟨es1, es2, asl, pre, arr, st, hev, htr, hst, hm⟩
      · exact .inl h0
      · exact .inr ⟨es1, es2 ++ [.handler e], asl, pre, arr, st, by simp [hev], htr, hst, hm⟩
    · exact .inr ⟨_, [], asl, _, _, st, rfl, htrace, hst, hm⟩
  | inclusionList signed t _ hclock hrun ih =>
    intro hi
    -- `onInclusionList` writes only the IL store.
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    rcases ih hi with h0 | ⟨es1, es2, asl, pre, arr, st, hev, htr, hst, hm⟩
    · exact .inl h0
    · exact .inr ⟨es1, es2 ++ [.inclusionList signed], asl, pre, arr, st, by simp [hev], htr,
        hst, hm⟩

/-- No attester slashing of the trace marks `i` in the store before it. This holds when
`i` never signs two slashable attestation data and no one forges its signature. -/
def HonestSigner (s0 : Store map) (events : List TraceEvent) (i : ValidatorIndex) : Prop :=
  ∀ (es1 es2 : List TraceEvent) (asl : AttesterSlashing) (pre : Store map)
    (arr : List (SignedInclusionList × UInt64)) (st : BeaconState),
    events = es1 ++ TraceEvent.handler (.attesterSlashing asl) :: es2 →
    NodeTrace s0 es1 arr pre →
    FcMap.lookup pre.blockStates pre.justifiedCheckpoint.root = some (pureState st) →
    ¬ SlashingMarks st asl i

end EngineSeam

end

section
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- The seed of `getForkchoiceStore` has no equivocator. -/
theorem getForkchoiceStore_equivocating (anchorState : BeaconState) (anchorBlock : BeaconBlock)
    (s0 : Store map) (h : getForkchoiceStore (pureState anchorState) anchorBlock = .ok s0) :
    s0.equivocatingIndices = #[] := by
  simp only [getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  rfl

variable [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] [LawfulFcMap map Root]

/-- An honest signer is never an equivocator in a store reached from the anchor. -/
theorem honest_not_equivocating {anchorState : BeaconState} {anchorBlock : BeaconBlock}
    {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)}
    (hanchor : getForkchoiceStore (pureState anchorState) anchorBlock = .ok s0)
    (h : NodeTrace s0 events arrivals s) (i : ValidatorIndex)
    (hhon : HonestSigner s0 events i) : i ∉ s.equivocatingIndices := by
  intro hi
  rcases h.equivocator_source (BlockStatesPure.anchor _ _ _ hanchor) i hi with
    h0 | ⟨es1, es2, asl, pre, arr, st, hev, htr, hst, hm⟩
  · rw [getForkchoiceStore_equivocating anchorState anchorBlock s0 hanchor] at h0
    simp at h0
  · exact hhon es1 es2 asl pre arr st hev htr hst hm

end

end EthCLSpecs.Proofs.Heze
