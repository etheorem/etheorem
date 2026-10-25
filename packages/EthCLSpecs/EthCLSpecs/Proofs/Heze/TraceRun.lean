import EthCLSpecs.Proofs.Heze.NodeViews

/-!
# `EthCLSpecs.Proofs.Heze.TraceRun`: a node trace as a computation

`NodeTrace` (`NodeTrace.lean`) is a relation. The network results quantify over every
derivation of it, for every prefix of a trace: `ClockedTrace.clock`, the fields of
`RootFacts`, and the queries of `honestNodes_duties_avoid_full`. A concrete trace needs a
function form to turn those quantifiers into computation.

`runTrace s0 events` runs the handlers of `events` in order from `s0`. It fails on the
first rejected event. `NodeTrace.iff_runTrace` proves that a trace exists exactly when
`runTrace` succeeds with the same arrivals and store. So the relation is a function
(`NodeTrace.det`).

The rest of the module states the structures of the network results as `Bool` checks:

- `traceAll` makes one pass over a trace. It checks a property of the store after each
  prefix, and a property of each event and the store it runs on.
- `ClockedTrace.of_check`, `RootFacts.of_check`, and `HonestList.of_check` derive each
  structure from its checks. `handlersAll` checks each handler event.

`native_decide` closes the checks on a concrete trace. The pass runs each handler once, so
the cost is linear in the length of the trace.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Slot InclusionList
  SignedInclusionList ExecutionPayload ExecutionRequests Transaction ValidatorIndex timeIntoSlotMs onInclusionList
  getInclusionListCommittee)
open EthCLSpecs.Heze.Const (inclusionListCommitteeSize)

section Run
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- One event of a trace, from the arrivals so far and the store. A handler event runs its
handler. An inclusion-list event reads the time into the slot, runs `onInclusionList`, and
records the arrival. A rejected event fails. -/
def traceStep (acc : List (SignedInclusionList × UInt64) × Store map) :
    TraceEvent →
      Except StoreTransitionError (List (SignedInclusionList × UInt64) × Store map)
  | .handler e =>
    match (HandlerEvent.run (map := map) e).run acc.2 with
    | .ok ((), s') => .ok (acc.1, s')
    | .error err => .error err
  | .inclusionList signed =>
    match (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) acc.2).run
        acc.2 with
    | .error err => .error err
    | .ok (t, _) =>
      match (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
          signed).run acc.2 with
      | .ok ((), s') => .ok (acc.1 ++ [(signed, t)], s')
      | .error err => .error err

/-- The run of a trace from `s0`: the arrivals and the store at the end, or the error of
the first rejected event. -/
def runTrace (s0 : Store map) (events : List TraceEvent) :
    Except StoreTransitionError (List (SignedInclusionList × UInt64) × Store map) :=
  events.foldlM traceStep ([], s0)

/-- A successful step extends a trace by its event. -/
theorem NodeTrace.step {s0 s : Store map} {events : List TraceEvent}
    {arr : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arr s)
    {e : TraceEvent} {acc : List (SignedInclusionList × UInt64) × Store map}
    (hstep : traceStep (arr, s) e = .ok acc) :
    NodeTrace s0 (events ++ [e]) acc.1 acc.2 := by
  cases e with
  | handler e =>
    simp only [traceStep] at hstep
    split at hstep
    · rename_i s' hrun
      cases hstep
      exact .handler e h hrun
    · cases hstep
  | inclusionList signed =>
    simp only [traceStep] at hstep
    split at hstep
    · cases hstep
    · rename_i t s1 hclock
      obtain rfl := timeIntoSlotMs_run_state _ _ _ _ hclock
      split at hstep
      · rename_i s' hrun
        cases hstep
        exact .inclusionList signed t h hclock hrun
      · cases hstep

/-- A successful handler run is a step. -/
theorem traceStep_handler {arr : List (SignedInclusionList × UInt64)} {s s' : Store map}
    {e : HandlerEvent} (hrun : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) :
    traceStep (arr, s) (.handler e) = .ok (arr, s') := by
  simp only [traceStep, hrun]

/-- A successful inclusion-list run is a step. -/
theorem traceStep_inclusionList {arr : List (SignedInclusionList × UInt64)}
    {s s' : Store map} {signed : SignedInclusionList} {t : UInt64}
    (hclock : (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) s).run s
      = .ok (t, s))
    (hrun : (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      signed).run s = .ok ((), s')) :
    traceStep (arr, s) (.inclusionList signed) = .ok (arr ++ [(signed, t)], s') := by
  simp only [traceStep, hclock, hrun]

/-- A trace runs: `runTrace` returns its arrivals and its store. -/
theorem NodeTrace.runTrace_eq {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s) :
    runTrace s0 events = .ok (arrivals, s) := by
  induction h with
  | nil => rfl
  | @handler events arrivals s s' e _ hrun ih =>
    simp only [runTrace, List.foldlM_append] at ih ⊢
    rw [ih]
    change List.foldlM traceStep (arrivals, s) [TraceEvent.handler e] = _
    simp only [List.foldlM_cons, List.foldlM_nil, traceStep_handler hrun, bind_pure]
  | @inclusionList events arrivals s s' signed t _ hclock hrun ih =>
    simp only [runTrace, List.foldlM_append] at ih ⊢
    rw [ih]
    change List.foldlM traceStep (arrivals, s) [TraceEvent.inclusionList signed] = _
    simp only [List.foldlM_cons, List.foldlM_nil, traceStep_inclusionList hclock hrun,
      bind_pure]

/-- A successful fold extends a trace. The fold starts at the end of the trace of `pre`. -/
theorem NodeTrace.of_foldlM {s0 : Store map} :
    ∀ (es pre : List TraceEvent) (arr0 arr : List (SignedInclusionList × UInt64))
      (s s' : Store map),
      NodeTrace s0 pre arr0 s → es.foldlM traceStep (arr0, s) = .ok (arr, s') →
      NodeTrace s0 (pre ++ es) arr s'
  | [], pre, arr0, arr, s, s', h, hrun => by
    simp only [List.foldlM_nil] at hrun
    injection hrun with hrun
    injection hrun with h1 h2
    subst h1 h2
    simpa using h
  | e :: es, pre, arr0, arr, s, s', h, hrun => by
    simp only [List.foldlM_cons] at hrun
    obtain ⟨acc, hstep, hrest⟩ := except_bind_eq_ok hrun
    have h1 := h.step hstep
    have h2 := NodeTrace.of_foldlM es (pre ++ [e]) acc.1 arr acc.2 s' h1 hrest
    simpa using h2

/-- A successful run is a trace. -/
theorem NodeTrace.of_runTrace {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)}
    (h : runTrace s0 events = .ok (arrivals, s)) : NodeTrace s0 events arrivals s := by
  simpa using NodeTrace.of_foldlM events [] [] arrivals s0 s .nil h

/-- A trace exists exactly when the run succeeds with its arrivals and its store. -/
theorem NodeTrace.iff_runTrace {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} :
    NodeTrace s0 events arrivals s ↔ runTrace s0 events = .ok (arrivals, s) :=
  ⟨NodeTrace.runTrace_eq, NodeTrace.of_runTrace⟩

/-- A trace is a function of its seed and its events. -/
theorem NodeTrace.det {s0 s₁ s₂ : Store map} {events : List TraceEvent}
    {a₁ a₂ : List (SignedInclusionList × UInt64)} (h₁ : NodeTrace s0 events a₁ s₁)
    (h₂ : NodeTrace s0 events a₂ s₂) : a₁ = a₂ ∧ s₁ = s₂ := by
  have h := h₁.runTrace_eq.symm.trans h₂.runTrace_eq
  injection h with h
  injection h with ha hs
  exact ⟨ha, hs⟩

/-- A trace extended by one event fixes the step: from the end of the shorter trace,
`traceStep` returns the arrivals and the store of the longer one. -/
theorem traceStep_of_trace {s0 s m : Store map} {pre : List TraceEvent} {e : TraceEvent}
    {arr0 arr : List (SignedInclusionList × UInt64)} (h0 : NodeTrace s0 pre arr0 s)
    (h1 : NodeTrace s0 (pre ++ [e]) arr m) : traceStep (arr0, s) e = .ok (arr, m) := by
  have h := h1.runTrace_eq
  have h0' := h0.runTrace_eq
  simp only [runTrace, List.foldlM_append] at h h0'
  rw [h0'] at h
  change List.foldlM traceStep (arr0, s) [e] = _ at h
  simpa only [List.foldlM_cons, List.foldlM_nil, bind_pure] using h

/-- One pass over the trace `xs`, from the arrivals `arr` and the store `s`. Before each
event, `p` holds on the store, and `q` holds on the event and the store. At the end, `p`
holds on the store. When an event fails, no trace reaches the events after it, so the pass
stops with `true`. -/
def traceAll (p : Store map → Bool) (q : TraceEvent × Nat → Store map → Bool) :
    List (TraceEvent × Nat) → List (SignedInclusionList × UInt64) → Store map → Bool
  | [], _, s => p s
  | x :: xs, arr, s =>
    p s && q x s &&
      match traceStep (arr, s) x.1 with
      | .ok (arr', s') => traceAll p q xs arr' s'
      | .error _ => true

/-- `traceAll` from the end of a trace of `pre0` gives `p` on every store that a trace of
`pre0` and a prefix of `xs` reaches. It gives `q` on every event of `xs` and the store it
runs on. A trace is a function of its events (`NodeTrace.det`), so these stores are the
stores of the pass. -/
theorem traceAll_spec {s0 : Store map} {p : Store map → Bool}
    {q : TraceEvent × Nat → Store map → Bool} :
    ∀ (xs : List (TraceEvent × Nat)) (pre0 : List TraceEvent)
      (arr0 : List (SignedInclusionList × UInt64)) (s : Store map),
      NodeTrace s0 pre0 arr0 s → traceAll p q xs arr0 s = true →
      (∀ (pre rest : List (TraceEvent × Nat)) (arr : List (SignedInclusionList × UInt64))
        (m : Store map), xs = pre ++ rest →
        NodeTrace s0 (pre0 ++ pre.map Prod.fst) arr m → p m = true) ∧
      (∀ (pre : List (TraceEvent × Nat)) (x : TraceEvent × Nat) post,
        xs = pre ++ x :: post → ∀ (arr : List (SignedInclusionList × UInt64)) (mid : Store map),
        NodeTrace s0 (pre0 ++ pre.map Prod.fst) arr mid → q x mid = true)
  | [], pre0, arr0, s, h0, h => by
    simp only [traceAll] at h
    refine ⟨fun pre rest arr m hs hm => ?_, fun pre x post hs => ?_⟩
    · obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hs.symm
      simp only [List.map_nil, List.append_nil] at hm
      obtain ⟨-, rfl⟩ := h0.det hm
      exact h
    · simp at hs
  | x :: xs, pre0, arr0, s, h0, h => by
    simp only [traceAll, Bool.and_eq_true] at h
    obtain ⟨⟨hp, hq⟩, hrest⟩ := h
    -- The pass continues from the store after `x`, which a trace of `pre0 ++ [x.1]` reaches.
    have hnext : ∀ (arr1 : List (SignedInclusionList × UInt64)) (s1 : Store map),
        NodeTrace s0 (pre0 ++ [x.1]) arr1 s1 → traceAll p q xs arr1 s1 = true := by
      intro arr1 s1 h1
      rw [traceStep_of_trace h0 h1] at hrest
      exact hrest
    refine ⟨fun pre rest arr m hs hm => ?_, fun pre y post hs arr mid hm => ?_⟩
    · cases pre with
      | nil =>
        simp only [List.map_nil, List.append_nil] at hm
        obtain ⟨-, rfl⟩ := h0.det hm
        exact hp
      | cons y pre' =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨rfl, hs⟩ := hs
        have hm' : NodeTrace s0 ((pre0 ++ [x.1]) ++ pre'.map Prod.fst) arr m := by
          simpa [List.append_assoc] using hm
        obtain ⟨mid, a1, -, h1, -, -⟩ := hm'.split rfl
        exact (traceAll_spec xs (pre0 ++ [x.1]) a1 mid h1 (hnext a1 mid h1)).1
          pre' rest arr m hs hm'
    · cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        simp only [List.map_nil, List.append_nil] at hm
        obtain ⟨-, rfl⟩ := h0.det hm
        exact hq
      | cons z pre' =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨rfl, hs⟩ := hs
        have hm' : NodeTrace s0 ((pre0 ++ [x.1]) ++ pre'.map Prod.fst) arr mid := by
          simpa [List.append_assoc] using hm
        obtain ⟨mid', a1, -, h1, -, -⟩ := hm'.split rfl
        exact (traceAll_spec xs (pre0 ++ [x.1]) a1 mid' h1 (hnext a1 mid' h1)).2
          pre' y post hs arr mid hm'

/-- `traceAll` from the seed gives `p` on the store after each prefix of the trace. -/
theorem traceAll_prefix {s0 : Store map} {p : Store map → Bool}
    {q : TraceEvent × Nat → Store map → Bool} {tevs : List (TraceEvent × Nat)}
    (h : traceAll p q tevs [] s0 = true) :
    ∀ (pre rest : List (TraceEvent × Nat)) (arr : List (SignedInclusionList × UInt64))
      (m : Store map), tevs = pre ++ rest →
      NodeTrace s0 (pre.map Prod.fst) arr m → p m = true :=
  fun pre rest arr m hs hm =>
    (traceAll_spec tevs [] [] s0 .nil h).1 pre rest arr m hs (by simpa using hm)

/-- `traceAll` from the seed gives `q` on each event and the store it runs on. -/
theorem traceAll_event {s0 : Store map} {p : Store map → Bool}
    {q : TraceEvent × Nat → Store map → Bool} {tevs : List (TraceEvent × Nat)}
    (h : traceAll p q tevs [] s0 = true) :
    ∀ (pre : List (TraceEvent × Nat)) (x : TraceEvent × Nat) post,
      tevs = pre ++ x :: post → ∀ (arr : List (SignedInclusionList × UInt64))
      (mid : Store map), NodeTrace s0 (pre.map Prod.fst) arr mid → q x mid = true :=
  fun pre x post hs arr mid hm =>
    (traceAll_spec tevs [] [] s0 .nil h).2 pre x post hs arr mid (by simpa using hm)

/-- A run, wall times that do not decrease, and the clock check in a pass give a clocked
trace. -/
theorem ClockedTrace.of_check {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × UInt64)} {p : Store map → Bool}
    (hrun : runTrace s0 (tevs.map Prod.fst) = .ok (arrivals, s))
    (hmono : tevs.Pairwise (fun a b => a.2 ≤ b.2))
    (hcheck : traceAll p (fun x m => decide (ClockAt x.1 x.2 m)) tevs [] s0 = true) :
    ClockedTrace s0 tevs arrivals s :=
  ⟨NodeTrace.of_runTrace hrun, hmono, fun pre x post hs arr mid hm =>
    of_decide_eq_true (traceAll_event hcheck pre x post hs arr mid hm)⟩

/-- The committee that `getInclusionListCommittee` returns for `state` and `slot`, or
`none` when it throws. The run reads no store, so a `Unit` runner state replaces one
(`getInclusionListCommittee_run_ok_transfer`). -/
def committeeOf (state : State) (slot : Slot) :
    Option (Vector ValidatorIndex inclusionListCommitteeSize) :=
  match (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun Unit) state
      slot).run () with
  | .ok (c, _) => some c
  | .error _ => none

omit [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- `committeeOf` gives the run of `getInclusionListCommittee` from any store. -/
theorem getInclusionListCommittee_run_of_committeeOf {state : BeaconState} {slot : Slot}
    {c : Vector ValidatorIndex inclusionListCommitteeSize}
    (h : committeeOf (pureState state) slot = some c) (x : Store map) :
    (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun (Store map))
      (pureState state) slot).run x = .ok (c, x) := by
  unfold committeeOf at h
  split at h
  · rename_i c' u heq
    cases u
    exact (Option.some.inj h) ▸ getInclusionListCommittee_run_ok_transfer state slot () x c' heq
  · cases h

/-- The facts of `RootFacts` on one store, as a `Bool`. -/
def rootFactsB (r : Root) (n : Slot)
    (committee : Vector ValidatorIndex inclusionListCommitteeSize) (m : Store map) : Bool :=
  (FcMap.lookup m.blocks r).all (fun b => b.slot == n) &&
  (FcMap.lookup m.blockStates r).all
    (fun st => sszGet st slot == n && committeeOf st (n - 1) == some committee)

/-- A seed with no state at `r`, with only uncached boxes in `blockStates`, and the check
on the store after each prefix, in a pass, give `RootFacts`. -/
theorem RootFacts.of_check {s0 : Store map} {tevs : List (TraceEvent × Nat)} {r : Root}
    {n : Slot} {committee : Vector ValidatorIndex inclusionListCommitteeSize}
    {q : TraceEvent × Nat → Store map → Bool}
    (hanchor : (FcMap.lookup s0.blockStates r).isNone = true) (hpure : BlockStatesPure s0)
    (hcheck : traceAll (rootFactsB r n committee) q tevs [] s0 = true) :
    RootFacts s0 tevs r n committee := by
  refine ⟨Option.isNone_iff_eq_none.mp hanchor, hpure, ?_, ?_, ?_⟩
  · intro pre rest arr m b hs hm hb
    have h := traceAll_prefix hcheck pre rest arr m hs hm
    simp only [rootFactsB, hb, Option.all_some, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  · intro pre rest arr m st hs hm hst
    have h := traceAll_prefix hcheck pre rest arr m hs hm
    simp only [rootFactsB, hst, Option.all_some, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2.1
  · intro pre rest arr m st hs hm hst x
    have h := traceAll_prefix hcheck pre rest arr m hs hm
    simp only [rootFactsB, hst, Option.all_some, Bool.and_eq_true, beq_iff_eq] at h
    exact getInclusionListCommittee_run_of_committeeOf h.2.2 x

/-- `p` holds on each handler event of `tevs`. -/
def handlersAll (tevs : List (TraceEvent × Nat)) (p : HandlerEvent → Bool) : Bool :=
  tevs.all fun x => match x.1 with
    | .handler e => p e
    | .inclusionList _ => true

omit [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- `handlersAll` gives `p` on each handler event. -/
theorem handlersAll_spec {tevs : List (TraceEvent × Nat)} {p : HandlerEvent → Bool}
    (h : handlersAll tevs p = true) :
    ∀ (e : HandlerEvent) (w : Nat), (.handler e, w) ∈ tevs → p e = true := by
  intro e w hm
  simpa using List.all_eq_true.mp h _ hm

/-- The lists of a trace, each with its root. The check of `honestListB` hashes each list
once through this table. -/
def listRoots (tevs : List (TraceEvent × Nat)) : List (InclusionList × Root) :=
  tevs.filterMap fun x => match x.1 with
    | .inclusionList signed => some (signed.message, htr signed.message)
    | .handler _ => none

/-- The four conditions of `HonestList`, as a `Bool`. The synchrony check reads each event
by its index. The events before it are the `take` of that index. The no-collision check
compares the roots in `listRoots`. -/
def honestListB (tevs : List (TraceEvent × Nat)) (il : InclusionList) (tSend Δ : Nat) :
    Bool :=
  tevs.all (fun x => !x.1.Carries il || decide (tSend ≤ x.2)) &&
  (List.range tevs.length).all (fun k => match tevs[k]? with
    | some x => !decide (tSend + Δ < x.2) || (tevs.take k).any (fun y => y.1.Carries il)
    | none => true) &&
  tevs.all (fun x => match x.1 with
    | .inclusionList signed =>
      !(signed.message.validatorIndex == il.validatorIndex &&
        signed.message.inclusionListCommitteeRoot == il.inclusionListCommitteeRoot) ||
      decide (signed.message = il)
    | .handler _ => true) &&
  (let roots := listRoots tevs
   roots.all fun a => roots.all fun b => !(a.2 == b.2) || decide (a.1 = b.1))

omit [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- `honestListB` gives `HonestList`. -/
theorem HonestList.of_check {tevs : List (TraceEvent × Nat)} {il : InclusionList}
    {tSend Δ : Nat} (h : honestListB tevs il tSend Δ = true) :
    HonestList tevs il tSend Δ := by
  simp only [honestListB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcausal, hsync⟩, hgossip⟩, hcoll⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hc
    have := List.all_eq_true.mp hcausal x hx
    simp_all
  · intro pre x post hs hlate
    have hk : pre.length ∈ List.range tevs.length := by
      rw [List.mem_range, hs, List.length_append, List.length_cons]
      omega
    have hx := List.all_eq_true.mp hsync _ hk
    have htake : tevs.take pre.length = pre := by rw [hs, List.take_left]
    have hget : tevs[pre.length]? = some x := by
      rw [hs, List.getElem?_append_right (Nat.le_refl _)]
      simp
    simp only [hget, htake, hlate, decide_true, Bool.not_true, Bool.false_or,
      List.any_eq_true] at hx
    exact hx
  · intro signed w hm hv hk
    have := List.all_eq_true.mp hgossip _ hm
    simp_all
  · intro s₁ s₂ w₁ w₂ h₁ h₂ heq
    have hm : ∀ (s : SignedInclusionList) (w : Nat), (.inclusionList s, w) ∈ tevs →
        (s.message, htr s.message) ∈ listRoots tevs := fun s w h =>
      List.mem_filterMap.mpr ⟨_, h, rfl⟩
    have := List.all_eq_true.mp (List.all_eq_true.mp hcoll _ (hm s₁ w₁ h₁)) _ (hm s₂ w₂ h₂)
    simp_all

end Run

end EthCLSpecs.Proofs.Heze
