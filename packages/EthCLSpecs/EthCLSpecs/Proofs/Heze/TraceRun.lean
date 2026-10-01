import EthCLSpecs.Proofs.Heze.NodeViews

/-!
# `EthCLSpecs.Proofs.Heze.TraceRun`: a node trace as a computation

`NodeTrace` (`NodeTrace.lean`) is a relation. The network results quantify over every
derivation of it, for every prefix of a trace: `ClockedTrace.clock`, the fields of
`RootFacts`, and the queries of `honestNodes_duties_avoid_full`. A concrete trace needs a
function form to turn those quantifiers into computation.

`runTrace s0 events` runs the handlers of `events` in order from `s0`. It fails on the
first rejected event. An inclusion-list event records its arrival with `timelyBit`, the
timeliness of the list at the store the run reads (`timelyBit_iff`).
`NodeTrace.iff_runTrace` proves that a trace exists exactly when `runTrace` succeeds with
the same arrivals and store. So the relation is a function (`NodeTrace.det`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store Slot SignedInclusionList ExecutionPayload
  ExecutionRequests Transaction getCurrentSlot getTimeIntoSlotMs getInclusionListDueMs
  onInclusionList)

section Clock
variable {map : MapKind} [Preset] [HasherTag] [Config]

/-- The timeliness bit of a list of slot `slot` at `store`, as a computation. The current
slot is `slot`, and the time into the slot is before the deadline. -/
def timelyBit (store : Store map) (slot : Slot) : Bool :=
  match (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store,
      (getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store,
      getInclusionListDueMs with
  | .ok (cs, _), .ok (t, _), .ok d => slot == cs && decide (t < d)
  | _, _, _ => false

/-- `timelyBit` is `true` exactly when the list is timely at the store. Both clock reads
keep the runner state (`getCurrentSlot_stateFree`, `getTimeIntoSlotMs_stateFree`). -/
theorem timelyBit_iff (store : Store map) (slot : Slot) :
    timelyBit store slot = true ↔ InclusionListTimely store slot := by
  unfold timelyBit InclusionListTimely
  cases hcs : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run
      store with
  | error e =>
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h
    cases h
  | ok p =>
    obtain ⟨cs, s1⟩ := p
    have hs1 := ((getCurrentSlot_stateFree store).run_eq hcs).1
    subst s1
    cases ht : (getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map))
        store).run store with
    | error e =>
      simp only [Bool.false_eq_true, false_iff, not_and, not_exists]
      intro _ t d h
      cases h
    | ok q =>
      obtain ⟨t, s2⟩ := q
      have hs2 := ((getTimeIntoSlotMs_stateFree store).run_eq ht).1
      subst s2
      cases hd : (getInclusionListDueMs : Except StateTransitionError UInt64) with
      | error e =>
        simp only [Bool.false_eq_true, false_iff, not_and, not_exists]
        intro _ t' d' _ h
        cases h
      | ok d =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨rfl, hlt⟩
          exact ⟨rfl, t, d, rfl, rfl, hlt⟩
        · rintro ⟨hslot, t', d', ht', hd', hlt⟩
          injection hslot with hslot
          injection hslot with hslot
          injection ht' with ht'
          injection ht' with ht'
          injection hd' with hd'
          subst hslot ht' hd'
          exact ⟨rfl, hlt⟩

end Clock

section Run
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- One event of a trace, from the arrivals so far and the store. A handler event runs its
handler. An inclusion-list event runs `onInclusionList` and records the arrival with its
timeliness bit at the store the run reads (`timelyBit`). A rejected event fails. -/
def traceStep (acc : List (SignedInclusionList × Bool) × Store map) :
    TraceEvent →
      Except StoreTransitionError (List (SignedInclusionList × Bool) × Store map)
  | .handler e =>
    match (HandlerEvent.run (map := map) e).run acc.2 with
    | .ok ((), s') => .ok (acc.1, s')
    | .error err => .error err
  | .inclusionList signed =>
    match (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        signed).run acc.2 with
    | .ok ((), s') => .ok (acc.1 ++ [(signed, timelyBit acc.2 signed.message.slot)], s')
    | .error err => .error err

/-- The run of a trace from `s0`: the arrivals and the store at the end, or the error of
the first rejected event. -/
def runTrace (s0 : Store map) (events : List TraceEvent) :
    Except StoreTransitionError (List (SignedInclusionList × Bool) × Store map) :=
  events.foldlM traceStep ([], s0)

/-- A successful step extends a trace by its event. -/
theorem NodeTrace.step {s0 s : Store map} {events : List TraceEvent}
    {arr : List (SignedInclusionList × Bool)} (h : NodeTrace s0 events arr s)
    {e : TraceEvent} {acc : List (SignedInclusionList × Bool) × Store map}
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
    · rename_i s' hrun
      cases hstep
      exact .inclusionList signed _ h hrun (timelyBit_iff _ _)
    · cases hstep

/-- A successful handler run is a step. -/
theorem traceStep_handler {arr : List (SignedInclusionList × Bool)} {s s' : Store map}
    {e : HandlerEvent} (hrun : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) :
    traceStep (arr, s) (.handler e) = .ok (arr, s') := by
  simp only [traceStep, hrun]

/-- A successful inclusion-list run is a step. -/
theorem traceStep_inclusionList {arr : List (SignedInclusionList × Bool)}
    {s s' : Store map} {signed : SignedInclusionList}
    (hrun : (onInclusionList (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      signed).run s = .ok ((), s')) :
    traceStep (arr, s) (.inclusionList signed)
      = .ok (arr ++ [(signed, timelyBit s signed.message.slot)], s') := by
  simp only [traceStep, hrun]

/-- A trace runs: `runTrace` returns its arrivals and its store. The timeliness bit of each
arrival is `timelyBit`, since both are `true` exactly when the list is timely. -/
theorem NodeTrace.runTrace_eq {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} (h : NodeTrace s0 events arrivals s) :
    runTrace s0 events = .ok (arrivals, s) := by
  induction h with
  | nil => rfl
  | @handler events arrivals s s' e _ hrun ih =>
    simp only [runTrace, List.foldlM_append] at ih ⊢
    rw [ih]
    change List.foldlM traceStep (arrivals, s) [TraceEvent.handler e] = _
    simp only [List.foldlM_cons, List.foldlM_nil, traceStep_handler hrun, bind_pure]
  | @inclusionList events arrivals s s' signed b _ hrun hb ih =>
    have hbit : b = timelyBit s signed.message.slot :=
      Bool.eq_iff_iff.mpr (hb.trans (timelyBit_iff _ _).symm)
    subst hbit
    simp only [runTrace, List.foldlM_append] at ih ⊢
    rw [ih]
    change List.foldlM traceStep (arrivals, s) [TraceEvent.inclusionList signed] = _
    simp only [List.foldlM_cons, List.foldlM_nil, traceStep_inclusionList hrun, bind_pure]

/-- A successful fold extends a trace. The fold starts at the end of the trace of `pre`. -/
theorem NodeTrace.of_foldlM {s0 : Store map} :
    ∀ (es pre : List TraceEvent) (arr0 arr : List (SignedInclusionList × Bool))
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
    {arrivals : List (SignedInclusionList × Bool)}
    (h : runTrace s0 events = .ok (arrivals, s)) : NodeTrace s0 events arrivals s := by
  simpa using NodeTrace.of_foldlM events [] [] arrivals s0 s .nil h

/-- A trace exists exactly when the run succeeds with its arrivals and its store. -/
theorem NodeTrace.iff_runTrace {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} :
    NodeTrace s0 events arrivals s ↔ runTrace s0 events = .ok (arrivals, s) :=
  ⟨NodeTrace.runTrace_eq, NodeTrace.of_runTrace⟩

/-- A trace is a function of its seed and its events. -/
theorem NodeTrace.det {s0 s₁ s₂ : Store map} {events : List TraceEvent}
    {a₁ a₂ : List (SignedInclusionList × Bool)} (h₁ : NodeTrace s0 events a₁ s₁)
    (h₂ : NodeTrace s0 events a₂ s₂) : a₁ = a₂ ∧ s₁ = s₂ := by
  have h := h₁.runTrace_eq.symm.trans h₂.runTrace_eq
  injection h with h
  injection h with ha hs
  exact ⟨ha, hs⟩

end Run

end EthCLSpecs.Proofs.Heze
