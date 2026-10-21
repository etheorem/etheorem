import EthCLSpecs.Proofs.Heze.PayloadRaceDecision
import EthCLSpecs.Proofs.Heze.StorePure
import EthCLSpecs.Proofs.Heze.TraceRun

/-!
# `EthCLSpecs.Proofs.Heze.RaceCheck`: the premises of the race as computations

`race_empty_persists_composed` (`PayloadRaceDecision.lean`) quantifies over the events of
each head run and the stores before them. A concrete execution needs a computation for each
of these premises. This module gives the checks, and the lemmas that turn a check into a
premise. `Tests/HezeRaceWitness.lean` runs them on a concrete execution.

- `NodeTrace.checkpointStates_eq`: when every vote of a trace finds its target in the store
  before it, the checkpoint states stay those of the seed. `storeTargetCheckpointState` then
  returns its store. So one justified state serves every store of the trace.
- `traceAll_take` reads a check of `traceAll` at an event of a prefix of the trace. The
  premises of `RaceSetting.Core` name such events.
- `attIndicesB` computes the attesting indices that `AttIndices` names.
- `deliverAt` checks one delivered vote. `deliver_of_check` gives the conclusion of
  `RaceSetting.Fields.deliver` from it.
- `HeadRun.Ok.of_check` gives the fields of one head run with the head `empty r`.
- `honestSigner_of_check` gives `HonestSigner` from a trace with no attester slashing.
- `committeeVotes_eq_any` turns `committeeVotes` into a finite search.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Slot BeaconBlock ValidatorIndex
  Attestation AttesterSlashing SignedBeaconBlock PayloadAttestationMessage
  SignedExecutionPayloadEnvelope SignedInclusionList ExecutionPayload ExecutionRequests
  Transaction Checkpoint onTick onBlock onAttestation onAttesterSlashing
  onPayloadAttestationMessage onExecutionPayloadEnvelope storeTargetCheckpointState
  updateLatestMessages getAttestingIndices getCurrentSlot getHead)

/-! ## The checkpoint states along a trace -/

section Frames
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

/-- With its target present, `storeTargetCheckpointState` returns its store. -/
theorem storeTargetCheckpointState_run_of_contains (st s : Store map) (target : Checkpoint)
    (h : FcMap.contains st.checkpointStates target = true) :
    (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) st
      target).run s = .ok (st, s) := by
  unfold storeTargetCheckpointState
  rw [if_pos h]
  rfl

omit [Config] [CryptoBackend] in
/-- `updateLatestMessages` writes only the latest messages. -/
theorem updateLatestMessages_checkpointStates (st : Store map) (idx : Array ValidatorIndex)
    (att : Attestation) :
    (updateLatestMessages st idx att).checkpointStates = st.checkpointStates := by
  simp only [updateLatestMessages, Id.run]
  rfl

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- A handler event keeps the checkpoint states, when a vote finds its target in the store.
`onAttestation` then runs `storeTargetCheckpointState` without an insert
(`storeTargetCheckpointState_run_of_contains`). -/
theorem HandlerEvent.run_keeps_checkpointStates (e : HandlerEvent) (s s' : Store map)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s'))
    (hatt : ∀ att fb, e = .attestation att fb →
      FcMap.contains s.checkpointStates att.data.target = true) :
    s'.checkpointStates = s.checkpointStates := by
  have keep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      KeepsAt (fun st : Store map => st.checkpointStates) s.checkpointStates x →
      x.run s = .ok ((), s') → s'.checkpointStates = s.checkpointStates := fun x hk hx =>
    hk s () s' rfl hx
  cases e with
  | tick time => exact keep _ (onTick_keeps_checkpointStates _ time) h
  | block signedBlock => exact keep _ (onBlock_keeps_checkpointStates _ signedBlock) h
  | attestation att isFromBlock =>
    obtain ⟨cps, s2, A, hmid, rfl⟩ := onAttestation_run_post att isFromBlock s s' h
    rw [storeTargetCheckpointState_run_of_contains s s _ (hatt att isFromBlock rfl)] at hmid
    injection hmid with hmid
    injection hmid with hmid
    rw [updateLatestMessages_checkpointStates, ← hmid]
  | attesterSlashing asl => exact keep _ (onAttesterSlashing_keeps_checkpointStates _ asl) h
  | payloadAttestation msg isFromBlock =>
    exact keep _ (onPayloadAttestationMessage_keeps_checkpointStates _ msg isFromBlock) h
  | envelope signedEnv =>
    exact keep _ (onExecutionPayloadEnvelope_keeps_checkpointStates _ signedEnv) h

/-- The checkpoint states at the end of a trace are those of the seed, when each vote of the
trace finds its target in the store before it. -/
theorem NodeTrace.checkpointStates_eq {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (hatt : ∀ es1 es2 att fb arr mid,
      events = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 →
      NodeTrace s0 es1 arr mid → FcMap.contains mid.checkpointStates att.data.target = true) :
    s.checkpointStates = s0.checkpointStates := by
  induction h with
  | nil => rfl
  | @handler events arrivals s s' e htr hrun ih =>
    rw [HandlerEvent.run_keeps_checkpointStates e s s' hrun (fun att fb he =>
      hatt events [] att fb arrivals s (by rw [he]) htr)]
    exact ih fun es1 es2 att fb arr mid hev hm =>
      hatt es1 (es2 ++ [.handler e]) att fb arr mid (by simp [hev]) hm
  | @inclusionList events arrivals s s' signed t htr hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih fun es1 es2 att fb arr mid hev hm =>
      hatt es1 (es2 ++ [.inclusionList signed]) att fb arr mid (by simp [hev]) hm

end Frames

/-! ## Checks over a trace -/

section Checks
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

omit [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- A split of the events of a prefix is a split of the timed trace. -/
theorem split_of_take {tevs : List (TraceEvent × Nat)} {n : Nat} {es1 es2 : List TraceEvent}
    {e : TraceEvent} (h : (tevs.take n).map Prod.fst = es1 ++ e :: es2) :
    ∃ pre x post, tevs = pre ++ x :: post ∧ pre.map Prod.fst = es1 ∧ x.1 = e := by
  obtain ⟨l1, l2, hl, h1, h2⟩ := List.map_eq_append_iff.mp h
  obtain ⟨x, post, rfl, hx, -⟩ := List.map_eq_cons_iff.mp h2
  refine ⟨l1, x, post ++ tevs.drop n, ?_, h1, hx⟩
  calc tevs = tevs.take n ++ tevs.drop n := (List.take_append_drop n tevs).symm
    _ = _ := by rw [hl]; simp

/-- `traceAll` gives `q` on each event of a prefix and the store it runs on. -/
theorem traceAll_take {s0 : Store map} {p : Store map → Bool}
    {q : TraceEvent × Nat → Store map → Bool} {tevs : List (TraceEvent × Nat)}
    (h : traceAll p q tevs [] s0 = true) {n : Nat} {es1 es2 : List TraceEvent}
    {e : TraceEvent} (hs : (tevs.take n).map Prod.fst = es1 ++ e :: es2)
    {arr : List (SignedInclusionList × UInt64)} {mid : Store map}
    (hm : NodeTrace s0 es1 arr mid) : ∃ w, q (e, w) mid = true := by
  obtain ⟨pre, x, post, hsplit, hpre, hx⟩ := split_of_take hs
  refine ⟨x.2, ?_⟩
  have := traceAll_event h pre x post hsplit arr mid (hpre ▸ hm)
  rw [← hx]
  exact this

/-- A run, wall times that do not decrease, and a pass that checks the clock beside another
check give a clocked trace. -/
theorem ClockedTrace.of_check_and {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × UInt64)} {p : Store map → Bool}
    {q : TraceEvent × Nat → Store map → Bool}
    (hrun : runTrace s0 (tevs.map Prod.fst) = .ok (arrivals, s))
    (hmono : tevs.Pairwise (fun a b => a.2 ≤ b.2))
    (hcheck : traceAll p (fun x m => decide (ClockAt x.1 x.2 m) && q x m) tevs [] s0 = true) :
    ClockedTrace s0 tevs arrivals s :=
  ⟨NodeTrace.of_runTrace hrun, hmono, fun pre x post hs arr mid hm => by
    have := traceAll_event hcheck pre x post hs arr mid hm
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true this.1⟩

/-- The attesting indices of `att` at `pre`, as a computation: the target-state step of
`onAttestation`, the lookup of the target state, and `getAttestingIndices`. -/
def attIndicesB (pre : Store map) (att : Attestation) : Option (Array ValidatorIndex) :=
  match (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map)) pre
      att.data.target).run pre with
  | .ok (st, _) =>
    match FcMap.lookup st.checkpointStates att.data.target with
    | some ts =>
      match getAttestingIndices ts att with
      | .ok A => some A
      | .error _ => none
    | none => none
  | .error _ => none

omit [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- `AttIndices` names the value of `attIndicesB`. -/
theorem AttIndices.eq_attIndicesB {pre : Store map} {att : Attestation}
    {A : Array ValidatorIndex} (h : AttIndices pre att A) : attIndicesB pre att = some A := by
  obtain ⟨cps, s2, ts, hrun, hts, hA⟩ := h
  simp only [attIndicesB, hrun, hts, hA]

/-- Event `k` of the timed trace is a vote of slot `t`. At the store that the events before
it reach, `i` is one of its attesting indices. -/
def deliverAt (s0 : Store map) (tevs : List (TraceEvent × Nat)) (k t : Nat)
    (i : ValidatorIndex) : Bool :=
  match tevs[k]? with
  | some (.handler (.attestation att _), _) =>
    att.data.slot.toNat == t &&
    match runTrace s0 ((tevs.take k).map Prod.fst) with
    | .ok (_, m) => (attIndicesB m att).any (·.contains i)
    | .error _ => false
  | _ => false

/-- `deliverAt` gives the conclusion of `RaceSetting.Fields.deliver` for a prefix that holds
the vote. A trace is a function of its events (`NodeTrace.det`), so the store before the vote
is the store of the check. -/
theorem deliver_of_check {s0 : Store map} {tevs : List (TraceEvent × Nat)} {k t n : Nat}
    {i : ValidatorIndex} (h : deliverAt s0 tevs k t i = true) (hk : k < n) :
    ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool),
      (tevs.take n).map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
      att.data.slot.toNat = t ∧
      ∀ arr mid, NodeTrace s0 es1 arr mid → ∀ A, AttIndices mid att A → i ∈ A := by
  unfold deliverAt at h
  split at h
  · rename_i att fb w hget
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hslot, hrun⟩ := h
    have hkl : k < tevs.length := by
      rcases Nat.lt_or_ge k tevs.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hget
        cases hget
    refine ⟨(tevs.take k).map Prod.fst, ((tevs.take n).drop (k + 1)).map Prod.fst, att, fb,
      ?_, hslot, ?_⟩
    · have hkn : k < (tevs.take n).length := by
        rw [List.length_take]
        omega
      have hx : (tevs.take n)[k] = (TraceEvent.handler (.attestation att fb), w) := by
        have : (tevs.take n)[k]? = some (TraceEvent.handler (.attestation att fb), w) := by
          rw [List.getElem?_take_of_lt hk]
          exact hget
        rw [List.getElem?_eq_getElem hkn] at this
        exact Option.some.inj this
      have hsplit :
          tevs.take n = tevs.take k ++ (tevs.take n)[k] :: (tevs.take n).drop (k + 1) := by
        conv => lhs; rw [← List.take_append_drop k (tevs.take n)]
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk), List.getElem_cons_drop]
      conv => lhs; rw [hsplit]
      rw [hx, List.map_append, List.map_cons]
    · intro arr mid hm A hA
      split at hrun
      · rename_i a m hr
        obtain ⟨-, rfl⟩ := hm.det (NodeTrace.of_runTrace hr)
        rw [AttIndices.eq_attIndicesB hA] at hrun
        simpa using hrun
      · cases hrun
  · cases h

omit [FcMap map] [CryptoBackend] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability] in
/-- `getCurrentSlot` keeps the runner state. -/
theorem getCurrentSlot_run_self (st s s' : Store map) (cs : Slot)
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s')) : s' = s := by
  have hk : KeepsAt (fun x : Store map => x) s
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st) := by
    simp only [getCurrentSlot]
    keeps_solve
  exact hk s cs s' rfl h

/-- The fields of `HeadRun.Ok` that a computation decides, for the head `empty r`: the wall
time of the prefix, the store time, the current slot, the `getHead` run, the block at `r`,
and the justified block. -/
def headRunB (q : HeadRun map) (r : Root) (rb : BeaconBlock) (t : Nat) : Bool :=
  q.events.all (fun y => decide (y.2 ≤ q.wall)) &&
  q.store.time.toNat == q.wall / 1000 &&
  (match (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      q.store).run q.store with
    | .ok (cs, _) => cs.toNat == t
    | .error _ => false) &&
  (match (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) q.store).run q.store with
    | .ok (h, _) => h.root == r && h.payloadStatus == EthCLSpecs.Heze.Const.payloadStatusEmpty
    | .error _ => false) &&
  decide (FcMap.lookup q.store.blocks r = some rb) &&
  (FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root).any
    (fun jb => decide (jb.slot ≤ rb.slot))

/-- `headRunB`, the run of the prefix, and the justified state give `HeadRun.Ok`, for the
head `empty r`. `NodeEdge.empty` puts `empty r` strictly below `pending r`. -/
theorem HeadRun.Ok.of_check {n : NodeRun map} {q : HeadRun map} {r : Root}
    {rb : BeaconBlock} {jst : BeaconState} {t : Nat}
    (hpre : ∃ rest, n.events = q.events ++ rest)
    (hrun : runTrace n.seed (q.events.map Prod.fst) = .ok (q.arrivals, q.store))
    (hhead : q.head = .empty r)
    (hjst : FcMap.lookup q.store.checkpointStates q.store.justifiedCheckpoint
      = some (pureState jst))
    (h : headRunB q r rb t = true) : q.Ok n r rb jst t := by
  simp only [headRunB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨hwall, htime⟩, hslot⟩, hhd⟩, hblock⟩, hjb⟩ := h
  refine ⟨hpre, NodeTrace.of_runTrace hrun, hwall, htime, ?_, ?_, ?_, hblock, ?_, hjst⟩
  · split at hslot
    · rename_i cs s' hcs
      have := getCurrentSlot_run_self _ _ _ _ hcs
      subst this
      exact ⟨cs, beq_iff_eq.mp hslot, hcs⟩
    · cases hslot
  · split at hhd
    · rename_i h s' hh
      simp only [Bool.and_eq_true, beq_iff_eq] at hhd
      refine ⟨s', ?_⟩
      rw [hhead, ← node_eq_of_root_status _ (.empty r) hhd.1 hhd.2]
      exact hh
    · cases hhd
  · rw [hhead]
    refine ⟨NodeBelow.step _ _ NodeBelow.refl (NodeEdge.empty r), fun h => ?_⟩
    have := congrArg EthCLSpecs.Heze.ForkChoiceNode.payloadStatus h
    simp only [EthCLSpecs.Heze.ForkChoiceNode.empty, EthCLSpecs.Heze.ForkChoiceNode.pending]
      at this
    exact absurd this (by decide)
  · cases hj : FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root with
    | none => rw [hj] at hjb; cases hjb
    | some jb =>
      rw [hj] at hjb
      exact ⟨jb, rfl, by simpa using hjb⟩

/-- No event of `tevs` is an attester slashing. -/
def noSlashingB (tevs : List (TraceEvent × Nat)) : Bool :=
  handlersAll tevs fun e => match e with
    | .attesterSlashing _ => false
    | _ => true

/-- In a trace with no attester slashing, every validator is an honest signer. -/
theorem honestSigner_of_check {s0 : Store map} {tevs : List (TraceEvent × Nat)}
    (h : noSlashingB tevs = true) (n : Nat) (i : ValidatorIndex) :
    HonestSigner s0 ((tevs.take n).map Prod.fst) i := by
  intro es1 es2 asl pre arr st hev _ _
  obtain ⟨pre', x, post, hs, -, hx⟩ := split_of_take hev
  have hm : x ∈ tevs := by rw [hs]; simp
  obtain ⟨e, w⟩ := x
  simp only at hx
  subst hx
  have := handlersAll_spec h _ w hm
  simp at this

end Checks

/-! ## Votes and committees -/

section Votes

/-- With no committee at or above `K t`, `committeeVotes` is a search over the committees
below `K t`. -/
theorem committeeVotes_eq_any [Preset] (committees : Nat → Nat → Array ValidatorIndex)
    (K : Nat → Nat) (hK : ∀ t ci, K t ≤ ci → committees t ci = #[]) :
    committeeVotes committees =
      fun i t => (List.range (K t)).any fun ci => (committees t ci).contains i := by
  funext i t
  simp only [committeeVotes]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.any_eq_true, List.mem_range, Array.contains_iff_mem]
  constructor
  · rintro ⟨ci, hci⟩
    refine ⟨ci, ?_, hci⟩
    rcases Nat.lt_or_ge ci (K t) with h | h
    · exact h
    · rw [hK t ci h] at hci
      exact absurd hci (by simp)
  · rintro ⟨ci, -, hci⟩
    exact ⟨ci, hci⟩

end Votes

end EthCLSpecs.Proofs.Heze
