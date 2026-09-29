import EthCLSpecs.Proofs.Heze.HandlerFrames

/-!
# `EthCLSpecs.Proofs.Heze.NodeTrace`: the IL store is the fold of the arrivals

`InclusionDichotomy.lean` assumes that the IL store at the time of the envelope is
`ilStoreOfArrivals` of an arrival list. This module derives that assumption from the
handler runs of one node.

`NodeTrace s0 events arrivals s` records the successful handler runs of one node from the
store `s0` to the store `s`, in order. A rejected run leaves the store unchanged, so the
trace omits it. An inclusion-list event also records its arrival: the list, and the
timeliness bit of its `onInclusionList` run. The bit is `true` exactly when the list is
timely at the store the run reads (`InclusionListTimely`), so the trace fixes it.

`NodeTrace.ilStore` states the result. From a seed with the empty IL store, the IL store
after a trace is `ilStoreOfArrivals` of the arrivals of the trace. The proof is an
induction on the trace. An inclusion-list event is one step of the fold
(`onInclusionList_run_ok`), and every other event keeps the IL store
(`HandlerFrames.lean`). `getForkchoiceStore_ilStore` shows that the anchor store of
`getForkchoiceStore` is such a seed.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState InclusionListStore Attestation
  AttesterSlashing BeaconBlock SignedBeaconBlock PayloadAttestationMessage
  SignedExecutionPayloadEnvelope SignedInclusionList ExecutionPayload ExecutionRequests
  Transaction onTick onBlock onAttestation onAttesterSlashing onPayloadAttestationMessage
  onExecutionPayloadEnvelope onInclusionList getForkchoiceStore)

section
variable [Preset] [HasherTag]

/-- A handler event other than an inclusion list. -/
inductive HandlerEvent where
  | tick (time : UInt64)
  | block (signedBlock : SignedBeaconBlock)
  | attestation (att : Attestation) (isFromBlock : Bool)
  | attesterSlashing (asl : AttesterSlashing)
  | payloadAttestation (msg : PayloadAttestationMessage) (isFromBlock : Bool)
  | envelope (signedEnv : SignedExecutionPayloadEnvelope)

/-- One event of a node trace: a handler event or an inclusion list. -/
inductive TraceEvent where
  | handler (e : HandlerEvent)
  | inclusionList (signed : SignedInclusionList)

variable [Config] [CryptoBackend] {map : MapKind} [FcMap map]
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The handler run of an event. -/
def HandlerEvent.run : HandlerEvent → ForkChoiceStoreRun (Store map) Unit
  | .tick time =>
    onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time
  | .block signedBlock =>
    onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock
  | .attestation att isFromBlock =>
    onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
      isFromBlock
  | .attesterSlashing asl =>
    onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) asl
  | .payloadAttestation msg isFromBlock =>
    onPayloadAttestationMessage (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      msg isFromBlock
  | .envelope signedEnv =>
    onExecutionPayloadEnvelope (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      signedEnv

/-- A handler event keeps the IL store. -/
theorem HandlerEvent.run_keeps_ilStore (e : HandlerEvent) (s s' : Store map)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) :
    s'.inclusionListStore = s.inclusionListStore := by
  have hk : KeepsAt (fun st : Store map => st.inclusionListStore) s.inclusionListStore
      (HandlerEvent.run (map := map) e) := by
    cases e with
    | tick time => exact onTick_keeps_ilStore _ time
    | block signedBlock => exact onBlock_keeps_ilStore _ signedBlock
    | attestation att isFromBlock => exact onAttestation_keeps_ilStore _ att isFromBlock
    | attesterSlashing asl => exact onAttesterSlashing_keeps_ilStore _ asl
    | payloadAttestation msg isFromBlock =>
      exact onPayloadAttestationMessage_keeps_ilStore _ msg isFromBlock
    | envelope signedEnv => exact onExecutionPayloadEnvelope_keeps_ilStore _ signedEnv
  exact hk s () s' rfl h

/-- The successful handler runs of one node, from the store `s0`. The trace records its
events in order, and the IL arrivals with the timeliness bit of each. The bit is `true`
exactly when the list is timely at the store the run reads. A rejected event leaves the
store unchanged, so the trace omits it. -/
inductive NodeTrace (s0 : Store map) :
    List TraceEvent → List (SignedInclusionList × Bool) → Store map → Prop where
  | nil : NodeTrace s0 [] [] s0
  | handler {events arrivals s s'} (e : HandlerEvent) :
      NodeTrace s0 events arrivals s →
      (HandlerEvent.run (map := map) e).run s = .ok ((), s') →
      NodeTrace s0 (events ++ [.handler e]) arrivals s'
  | inclusionList {events arrivals s s'} (signed : SignedInclusionList) (b : Bool) :
      NodeTrace s0 events arrivals s →
      (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        signed).run s = .ok ((), s') →
      (b = true ↔ InclusionListTimely s signed.message.slot) →
      NodeTrace s0 (events ++ [.inclusionList signed]) (arrivals ++ [(signed, b)]) s'

/-- The IL store along a trace. From a seed with the empty IL store, the IL store after a
trace is the fold of `processInclusionList` over the IL arrivals of the trace
(`ilStoreOfArrivals`). No handler other than `onInclusionList` writes it. The run of an
inclusion-list event writes its timeliness bit, and the bit of the trace is the same one,
since both are `true` exactly when the list is timely. -/
theorem NodeTrace.ilStore {s0 : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} {s : Store map}
    (h : NodeTrace s0 events arrivals s)
    (hseed : s0.inclusionListStore = InclusionListStore.empty) :
    s.inclusionListStore = ilStoreOfArrivals arrivals := by
  induction h with
  | nil => exact hseed
  | handler e _ hrun ih => exact (HandlerEvent.run_keeps_ilStore e _ _ hrun).trans ih
  | inclusionList signed b _ hrun hb ih =>
    obtain ⟨b', hs', hb'⟩ := onInclusionList_run_ok _ _ signed hrun
    have hbb : b' = b := Bool.eq_iff_iff.mpr (hb'.trans hb.symm)
    subst hbb
    rw [hs']
    simp only [ilStoreOfArrivals, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← ilStoreOfArrivals, ← ih]
    rfl

end

/-- A successful `Except` bind: the first action succeeded, and the continuation succeeded
from its value. -/
theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A successful `Except` map: the mapped action succeeded, and the result is its image. -/
theorem except_map_eq_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : f <$> x = .ok b) : ∃ a, x = .ok a ∧ b = f a := by
  cases x with
  | error e => cases h
  | ok a =>
    injection h with h
    exact ⟨a, rfl, h.symm⟩

section
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- The seed of `getForkchoiceStore` has the empty IL store. -/
theorem getForkchoiceStore_ilStore (anchorState : BeaconState) (anchorBlock : BeaconBlock)
    (s0 : Store map) (h : getForkchoiceStore (pureState anchorState) anchorBlock = .ok s0) :
    s0.inclusionListStore = InclusionListStore.empty := by
  simp only [getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  cases h
  rfl

end

end EthCLSpecs.Proofs.Heze
