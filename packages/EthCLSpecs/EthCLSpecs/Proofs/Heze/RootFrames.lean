import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.HeadAvoidsFull

/-!
# `EthCLSpecs.Proofs.Heze.RootFrames`: the block and the answer at one root along a trace

`LaterStore` (`InclusionDichotomy.lean`) asks a later store for the block at the root `r`
and for the answer of the envelope handler at `r`. This module derives both from a node
trace that starts after the envelope handler. Three maps matter at `r`: `blocks`,
`payloads`, and `payloadInclusionListSatisfaction` (the answer map). `rootView r` reads
the three lookups at `r` together.

## Which handlers write the three maps

- `onBlock` inserts its block at the root of the block. Every other handler keeps
  `blocks`.
- `onExecutionPayloadEnvelope` inserts the envelope into `payloads` at the root of the
  envelope. It inserts the answer into the answer map at the same root. Every other
  handler keeps both maps.
- `onInclusionList` writes only the IL store (`onInclusionList_run_eq`).

The frame facts are per key. A handler keeps the lookup at `r` when it writes another
key. It also keeps the lookup when it writes the value that the lookup returns. So a
second copy of the block at `r` keeps the lookup. A second envelope for `r` can change
the answer, because it reads the IL store of its own time. Two conditions on one event
exclude the writes that change a lookup: `HandlerEvent.KeepsBlockAt` and
`HandlerEvent.NotEnvelopeAt`.

The proofs walk each handler body with `keeps_solve` (`HandlerFrames.lean`). One theorem
covers one handler, because the heartbeat limit applies to each declaration.
`HandlerEvent.run_keeps_rootView` joins the handler theorems with `KeepsAt.prod`.

## The trace results

`NodeTrace.rootView_eq` lifts the frames to a trace. `NodeTrace.laterStore` gives
`LaterStore` at the end of a trace from the store after the envelope handler. The clock
condition stays a hypothesis. It is a fact about the time of the node, and no frame
gives it.

`NodeTrace.append` joins two traces. `NodeTrace.split` cuts a trace at a point of its
event list. `NodeTrace.ilStore_of_anchor` gives the `ils` field of `DichotomyHypotheses`
from a trace that starts at the anchor store.

`inclusionList_missing_tx_trace` composes the dichotomy with the trace results. Take a
trace after the envelope handler with no second envelope for `r` and no other block at
`r`. In the slot after the block, `UnsatisfiedPayload` holds at the end of the trace. The
head of that store avoids the payload.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec
open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt LawfulFcMap pureState)
open EthCLSpecs.Heze (Preset Config Store Root BeaconBlock SignedBeaconBlock Attestation
  AttesterSlashing PayloadAttestationMessage SignedExecutionPayloadEnvelope
  ExecutionPayloadEnvelope ExecutionPayload ExecutionRequests Transaction SignedInclusionList
  onTick onBlock onAttestation onAttesterSlashing onPayloadAttestationMessage
  onExecutionPayloadEnvelope onInclusionList timeIntoSlotMs getCurrentSlot getHead
  getForkchoiceStore)

section
variable [Preset] [HasherTag]

/-- The event keeps the lookup `v` at `r` of the block map. A block event writes its block
at the root of the block. So it keeps `v` when that root is not `r`, or when `v` is the
block. Every other event keeps the block map. -/
def HandlerEvent.KeepsBlockAt (r : Root) (v : Option BeaconBlock) : HandlerEvent → Prop
  | .block signedBlock => htr signedBlock.message ≠ r ∨ v = some signedBlock.message
  | _ => True

/-- The event is not an envelope for `r`. -/
def HandlerEvent.NotEnvelopeAt (r : Root) : HandlerEvent → Prop
  | .envelope signedEnv => signedEnv.message.beaconBlockRoot ≠ r
  | _ => True

end

section
variable [Preset] [HasherTag] {map : MapKind} [FcMap map]

/-- The lookups at `r` of the three maps: the block, the envelope, and the answer. -/
def rootView (r : Root) (st : Store map) :
    Option BeaconBlock × Option ExecutionPayloadEnvelope × Option Bool :=
  (FcMap.lookup st.blocks r, FcMap.lookup st.payloads r,
    FcMap.lookup st.payloadInclusionListSatisfaction r)

variable [Config] [CryptoBackend] [LawfulFcMap map Root]

omit [CryptoBackend] [LawfulFcMap map Root] in
/-- `onTick` keeps the three lookups at `r`. -/
theorem onTick_keeps_rootView (r : Root) (v : _) (time : UInt64) :
    KeepsAt (rootView (map := map) r) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps the lookup `v` at `r` of the block map, when its block has another root
or is `v`. -/
theorem onBlock_keeps_block (r : Root) (v : Option BeaconBlock)
    (signedBlock : SignedBeaconBlock)
    (h : htr signedBlock.message ≠ r ∨ v = some signedBlock.message) :
    KeepsAt (fun st : Store map => FcMap.lookup st.blocks r) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

omit [LawfulFcMap map Root] in
/-- `onBlock` keeps the lookups at `r` of the envelope and answer maps. -/
theorem onBlock_keeps_payloadAnswer (r : Root) (v : _) (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => (FcMap.lookup st.payloads r,
        FcMap.lookup st.payloadInclusionListSatisfaction r)) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

omit [LawfulFcMap map Root] in
/-- `onAttestation` keeps the three lookups at `r`. -/
theorem onAttestation_keeps_rootView (r : Root) (v : _) (att : Attestation)
    (isFromBlock : Bool) :
    KeepsAt (rootView (map := map) r) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

omit [Config] [LawfulFcMap map Root] in
/-- `onAttesterSlashing` keeps the three lookups at `r`. -/
theorem onAttesterSlashing_keeps_rootView (r : Root) (v : _) (asl : AttesterSlashing) :
    KeepsAt (rootView (map := map) r) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

omit [LawfulFcMap map Root] in
/-- `onPayloadAttestationMessage` keeps the three lookups at `r`. -/
theorem onPayloadAttestationMessage_keeps_rootView (r : Root) (v : _)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (rootView (map := map) r) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

section EngineSeam
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

omit [LawfulFcMap map Root] in
/-- `onExecutionPayloadEnvelope` keeps the block map. -/
theorem onExecutionPayloadEnvelope_keeps_block (r : Root) (v : Option BeaconBlock)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => FcMap.lookup st.blocks r) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- `onExecutionPayloadEnvelope` keeps the lookup at `r` of the envelope map, for an
envelope at another root. -/
theorem onExecutionPayloadEnvelope_keeps_payload (r : Root)
    (v : Option ExecutionPayloadEnvelope) (signedEnv : SignedExecutionPayloadEnvelope)
    (h : signedEnv.message.beaconBlockRoot ≠ r) :
    KeepsAt (fun st : Store map => FcMap.lookup st.payloads r) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- `onExecutionPayloadEnvelope` keeps the lookup at `r` of the answer map, for an envelope
at another root. -/
theorem onExecutionPayloadEnvelope_keeps_answer (r : Root) (v : Option Bool)
    (signedEnv : SignedExecutionPayloadEnvelope) (h : signedEnv.message.beaconBlockRoot ≠ r) :
    KeepsAt (fun st : Store map => FcMap.lookup st.payloadInclusionListSatisfaction r) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- A handler event keeps the three lookups at `r`, when it keeps the block lookup
(`HandlerEvent.KeepsBlockAt`) and is not an envelope for `r`. -/
theorem HandlerEvent.run_keeps_rootView (r : Root)
    (v : Option BeaconBlock × Option ExecutionPayloadEnvelope × Option Bool)
    (e : HandlerEvent) (hblock : e.KeepsBlockAt r v.1) (henv : e.NotEnvelopeAt r) :
    KeepsAt (rootView (map := map) r) v (HandlerEvent.run (map := map) e) := by
  obtain ⟨vb, vp, va⟩ := v
  cases e with
  | tick time => exact onTick_keeps_rootView r _ time
  | block signedBlock =>
    exact KeepsAt.prod (onBlock_keeps_block r vb signedBlock hblock)
      (onBlock_keeps_payloadAnswer r (vp, va) signedBlock)
  | attestation att isFromBlock => exact onAttestation_keeps_rootView r _ att isFromBlock
  | attesterSlashing asl => exact onAttesterSlashing_keeps_rootView r _ asl
  | payloadAttestation msg isFromBlock =>
    exact onPayloadAttestationMessage_keeps_rootView r _ msg isFromBlock
  | envelope signedEnv =>
    exact KeepsAt.prod (onExecutionPayloadEnvelope_keeps_block r vb signedEnv)
      (KeepsAt.prod (onExecutionPayloadEnvelope_keeps_payload r vp signedEnv henv)
        (onExecutionPayloadEnvelope_keeps_answer r va signedEnv henv))

end EngineSeam

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- Two traces join: the second starts at the store where the first ends. -/
theorem NodeTrace.append {s0 mid s : Store map} {es1 es2 : List TraceEvent}
    {arr1 arr2 : List (SignedInclusionList × UInt64)} (h1 : NodeTrace s0 es1 arr1 mid)
    (h2 : NodeTrace mid es2 arr2 s) : NodeTrace s0 (es1 ++ es2) (arr1 ++ arr2) s := by
  induction h2 with
  | nil => simpa using h1
  | handler e _ hrun ih =>
    rw [← List.append_assoc]
    exact .handler e ih hrun
  | inclusionList signed t _ hclock hrun ih =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact .inclusionList signed t ih hclock hrun

/-- A trace splits at any point of its event list. The first part ends at a store `mid`,
and the second part starts there. The arrivals split the same way.

The proof is an induction on the trace. A trace grows at its end, so the last event of
the trace is the last event of the second part, unless the second part is empty. -/
theorem NodeTrace.split {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s) :
    ∀ {es1 es2 : List TraceEvent}, events = es1 ++ es2 →
      ∃ (mid : Store map) (arr1 arr2 : List (SignedInclusionList × UInt64)),
        NodeTrace s0 es1 arr1 mid ∧ NodeTrace mid es2 arr2 s ∧ arrivals = arr1 ++ arr2 := by
  induction h with
  | nil =>
    intro es1 es2 hev
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hev.symm
    exact ⟨s0, [], [], .nil, .nil, rfl⟩
  | handler e htrace hrun ih =>
    intro es1 es2 hev
    rcases List.eq_nil_or_concat es2 with rfl | ⟨es2', y, rfl⟩
    · rw [List.append_nil] at hev
      subst hev
      exact ⟨_, _, [], .handler e htrace hrun, .nil, by simp⟩
    · simp only [List.concat_eq_append] at hev ⊢
      rw [← List.append_assoc] at hev
      obtain ⟨hpre, hy⟩ := List.append_inj' hev rfl
      obtain rfl := List.singleton_inj.mp hy
      obtain ⟨mid, arr1, arr2, h1, h2, rfl⟩ := ih hpre
      exact ⟨mid, arr1, arr2, h1, .handler e h2 hrun, rfl⟩
  | inclusionList signed t htrace hclock hrun ih =>
    intro es1 es2 hev
    rcases List.eq_nil_or_concat es2 with rfl | ⟨es2', y, rfl⟩
    · rw [List.append_nil] at hev
      subst hev
      exact ⟨_, _, [], .inclusionList signed t htrace hclock hrun, .nil, by simp⟩
    · simp only [List.concat_eq_append] at hev ⊢
      rw [← List.append_assoc] at hev
      obtain ⟨hpre, hy⟩ := List.append_inj' hev rfl
      obtain rfl := List.singleton_inj.mp hy
      obtain ⟨mid, arr1, arr2, h1, h2, rfl⟩ := ih hpre
      exact ⟨mid, arr1, arr2 ++ [(signed, t)], h1, .inclusionList signed t h2 hclock hrun,
        by simp⟩

/-- From the anchor store of `getForkchoiceStore`, the IL store after a trace is
`ilStoreOfArrivals` of its arrivals. This is the `ils` field of `DichotomyHypotheses`. -/
theorem NodeTrace.ilStore_of_anchor {anchorState : EthCLSpecs.Heze.BeaconState}
    {anchorBlock : BeaconBlock} {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)}
    (hanchor : getForkchoiceStore (pureState anchorState) anchorBlock = .ok s0)
    (h : NodeTrace s0 events arrivals s) :
    s.inclusionListStore = ilStoreOfArrivals arrivals :=
  h.ilStore (getForkchoiceStore_ilStore anchorState anchorBlock s0 hanchor)

variable [LawfulFcMap map Root]

/-- The three lookups at `r` along a trace. Every handler event keeps the block lookup of
the seed (`HandlerEvent.KeepsBlockAt`), and no handler event is an envelope for `r`.
Then the store at the end of the trace has the lookups at `r` of the seed. -/
theorem NodeTrace.rootView_eq {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (r : Root)
    (hblock : ∀ e, TraceEvent.handler e ∈ events →
      e.KeepsBlockAt r (FcMap.lookup s0.blocks r))
    (henv : ∀ e, TraceEvent.handler e ∈ events → e.NotEnvelopeAt r) :
    rootView r s = rootView r s0 := by
  revert hblock henv
  induction h with
  | nil => intro _ _; rfl
  | handler e _ hrun ih =>
    intro hblock henv
    have hs := ih (fun e' he' => hblock e' (List.mem_append_left _ he'))
      (fun e' he' => henv e' (List.mem_append_left _ he'))
    exact HandlerEvent.run_keeps_rootView r (rootView r s0) e
      (hblock e (List.mem_append_right _ (List.mem_singleton_self _)))
      (henv e (List.mem_append_right _ (List.mem_singleton_self _))) _ () _ hs hrun
  | inclusionList signed t _ hclock hrun ih =>
    intro hblock henv
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih (fun e' he' => hblock e' (List.mem_append_left _ he'))
      (fun e' he' => henv e' (List.mem_append_left _ he'))

/-- `LaterStore` from a trace. The trace starts at the store `post` after the envelope
handler, and `post` holds the block at `r`. Every block event of the trace at `r` carries
the same block, and no event is a second envelope for `r`. Then the store at the end of
the trace meets `LaterStore`, when its current slot is the slot after the block. -/
theorem NodeTrace.laterStore {post s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace post events arrivals s)
    {r : Root} {rootBlock : BeaconBlock} (hpost : FcMap.lookup post.blocks r = some rootBlock)
    (hblock : ∀ e, TraceEvent.handler e ∈ events → e.KeepsBlockAt r (some rootBlock))
    (henv : ∀ e, TraceEvent.handler e ∈ events → e.NotEnvelopeAt r)
    (hslot : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) s).run s
      = .ok (rootBlock.slot + 1, s))
    (hnooverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot)) :
    LaterStore s post r rootBlock := by
  have hv := h.rootView_eq r (hpost ▸ hblock) henv
  simp only [rootView, Prod.mk.injEq] at hv
  exact ⟨hv.1.trans hpost, hv.2.2, hslot, hnooverflow⟩

/-- The trace form of `inclusionList_missing_tx_head_avoids_full`. Take a missing
transaction with no valid omission, under `DichotomyHypotheses`, and let `pre` hold the
block at `r`. The envelope handler succeeds. Take any trace from the store after it, in
which every block event at `r` carries the same block and no event is a second envelope
for `r`. At the end of the trace, in the slot after the block, `UnsatisfiedPayload` holds.
When the justified root is not below the FULL node of `r`, the head that `getHead`
returns is not below it either. -/
theorem inclusionList_missing_tx_trace
    {isValidOmission : ExecutionPayload → Transaction → Prop} {pre : Store map}
    {signedEnv : SignedExecutionPayloadEnvelope} {state : EthCLSpecs.Heze.BeaconState}
    {committee : Vector EthCLSpecs.Heze.ValidatorIndex
      EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {before after : List (SignedInclusionList × UInt64)} {signed : SignedInclusionList}
    {t : UInt64} {il : EthCLSpecs.Heze.InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state committee before after
      signed t il)
    (hpre : FcMap.lookup pre.blocks signedEnv.message.beaconBlockRoot = some rootBlock)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ signedEnv.message.payload.transactions.toArray)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx) :
    ∃ post : Store map,
      (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      ∀ (events : List TraceEvent) (arrivals : List (SignedInclusionList × UInt64))
        (s : Store map), NodeTrace post events arrivals s →
        (∀ e, TraceEvent.handler e ∈ events →
          e.KeepsBlockAt signedEnv.message.beaconBlockRoot (some rootBlock)) →
        (∀ e, TraceEvent.handler e ∈ events → e.NotEnvelopeAt signedEnv.message.beaconBlockRoot) →
        (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) s).run s
          = .ok (rootBlock.slot + 1, s) →
        ¬ (rootBlock.slot + 1 < rootBlock.slot) →
        UnsatisfiedPayload s signedEnv.message.beaconBlockRoot rootBlock ∧
        (¬ NodeBelow s (.full signedEnv.message.beaconBlockRoot)
            (.pending s.justifiedCheckpoint.root) →
          ∀ (runnerStore s' : Store map) (head : EthCLSpecs.Heze.ForkChoiceNode),
            (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s).run runnerStore
              = .ok (head, s') →
            ¬ NodeBelow s (.full signedEnv.message.beaconBlockRoot) head) := by
  obtain ⟨post, hrun, -, hunsat⟩ := inclusionList_missing_tx rootBlock h htx hmissing hinvalid
  -- The envelope handler keeps the block map, so `post` holds the block at `r`.
  have hpost : FcMap.lookup post.blocks signedEnv.message.beaconBlockRoot = some rootBlock :=
    onExecutionPayloadEnvelope_keeps_block _ _ signedEnv pre () post hpre hrun
  refine ⟨post, hrun, fun events arrivals s htrace hblock henv hslot hnooverflow => ?_⟩
  have hs := hunsat s (htrace.laterStore hpost hblock henv hslot hnooverflow)
  exact ⟨hs, fun hjustified runnerStore s' head hhead =>
    unsatisfiedPayload_getHead_avoids_full s _ rootBlock hs hjustified runnerStore s' head hhead⟩

end

end EthCLSpecs.Proofs.Heze
