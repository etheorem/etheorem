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
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store SignedInclusionList ExecutionPayload ExecutionRequests
  Transaction timeIntoSlotMs onInclusionList)

section Clock
variable {map : MapKind} [Preset] [HasherTag] [Config]

/-- A successful `timeIntoSlotMs` read leaves the runner state as it was. -/
theorem timeIntoSlotMs_run_state (st s s' : Store map) (t : UInt64)
    (h : (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (t, s')) :
    s' = s := by
  simp only [timeIntoSlotMs, checkedSub] at h
  split at h
  · cases h
  · injection h with h
    injection h with _ h
    exact h.symm

end Clock

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

end Run

end EthCLSpecs.Proofs.Heze
