import EthCLSpecs.Proofs.Heze.SlotsIncrease
import EthCLSpecs.Proofs.Heze.ILStoreOrder

/-!
# `EthCLSpecs.Proofs.Heze.ClockedTrace`: a node trace on the wall clock

A node trace (`NodeTrace.lean`) records the handler runs of one node. It has no wall time.
The network results of `NodeViews.lean` compare the events of a node with a send time on
the wall clock. This module adds the wall clock.

## The clock of the store

The store clock counts milliseconds (`store.timeMs`, `store.genesisTimeMs`).
`getCurrentSlot` divides the milliseconds since genesis by the slot length.
`getTimeIntoSlotMs` subtracts the start of the current slot. `onTick` can move
`store.timeMs` back. No other handler reads a clock.

`ClockedTrace` gives each event a wall time `w` in milliseconds. The wall times do not
decrease. A tick moves the store time to `w`. Any other event runs on a store whose time is
`w`. So the node ticks to its wall clock before it handles a message. This is the clock of an
honest node.

## The results

- Every handler keeps `genesisTimeMs` (`NodeTrace.genesisTime`).
- `slotStartMs g k` is the start of slot `k` in wall milliseconds.
  `slotStartMs_le_of_getCurrentSlot`: when the current slot is at least `n`, the wall time
  is past the start of slot `n`. `getTimeIntoSlotMs_lt_of_window`: an arrival in the first
  `due` milliseconds of a slot has a time into the slot below `due`.
  `getCurrentSlot_run_eq_of_window`: a wall time in slot `k` gives the current slot `k`.
- `onBlock_run_ok_currentSlot`: a successful `onBlock` for a new block passed its clock
  check. `NodeTrace.blockStates_origin`: a state at a root comes from an `onBlock` event on a
  block with that root.
- `NodeTrace.firstTimely_of_first`: the first event that carries a list sets its first
  timeliness (`Arrivals.firstTimely`, `ILStoreOrder.lean`), the bit of its `onInclusionList`
  run.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Config Store Root Attestation AttesterSlashing SignedBeaconBlock
  PayloadAttestationMessage SignedExecutionPayloadEnvelope SignedInclusionList ExecutionPayload
  ExecutionRequests Transaction onTick onBlock onAttestation onAttesterSlashing
  onPayloadAttestationMessage onExecutionPayloadEnvelope)

section Genesis
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

omit [CryptoBackend] in
/-- `onTick` keeps the genesis time. -/
theorem onTick_keeps_genesisTime (v : UInt64) (timeMs : UInt64) :
    KeepsAt (fun st : Store map => st.genesisTimeMs) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) timeMs) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps the genesis time. -/
theorem onBlock_keeps_genesisTime (v : UInt64) (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => st.genesisTimeMs) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

/-- `onAttestation` keeps the genesis time. -/
theorem onAttestation_keeps_genesisTime (v : UInt64) (att : Attestation) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.genesisTimeMs) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the genesis time. -/
theorem onAttesterSlashing_keeps_genesisTime (v : UInt64) (asl : AttesterSlashing) :
    KeepsAt (fun st : Store map => st.genesisTimeMs) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the genesis time. -/
theorem onPayloadAttestationMessage_keeps_genesisTime (v : UInt64)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.genesisTimeMs) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps the genesis time. -/
theorem onExecutionPayloadEnvelope_keeps_genesisTime (v : UInt64)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => st.genesisTimeMs) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- A handler event keeps the genesis time. -/
theorem HandlerEvent.run_keeps_genesisTime (e : HandlerEvent) (s s' : Store map)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) :
    s'.genesisTimeMs = s.genesisTimeMs := by
  have hk : KeepsAt (fun st : Store map => st.genesisTimeMs) s.genesisTimeMs
      (HandlerEvent.run (map := map) e) := by
    cases e with
    | tick time => exact onTick_keeps_genesisTime _ time
    | block signedBlock => exact onBlock_keeps_genesisTime _ signedBlock
    | attestation att isFromBlock => exact onAttestation_keeps_genesisTime _ att isFromBlock
    | attesterSlashing asl => exact onAttesterSlashing_keeps_genesisTime _ asl
    | payloadAttestation msg isFromBlock =>
      exact onPayloadAttestationMessage_keeps_genesisTime _ msg isFromBlock
    | envelope signedEnv => exact onExecutionPayloadEnvelope_keeps_genesisTime _ signedEnv
  exact hk s () s' rfl h

/-- The genesis time stays the same along a trace. -/
theorem NodeTrace.genesisTime {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} (h : NodeTrace s0 events arrivals s) :
    s.genesisTimeMs = s0.genesisTimeMs := by
  induction h with
  | nil => rfl
  | handler e _ hrun ih => exact (HandlerEvent.run_keeps_genesisTime e _ _ hrun).trans ih
  | inclusionList signed _ _ hrun _ ih =>
    -- `onInclusionList` writes only the IL store.
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs']
    exact ih

end Genesis

section Clock
variable {map : MapKind} [Preset] [HasherTag] [Config]

open EthCLSpecs.Heze (getTimeIntoSlotMs getCurrentSlot)
open EthCLSpecs.Heze.Const (slotDurationMs)
open EthCLLib.Proofs (run_bind_eq_ok run_liftErr_eq_ok checkedAdd_eq_ok checkedSub_eq_ok
  checkedMul_eq_ok run_bind except_bind_ok run_liftErr_of_ok checkedAdd_of_lt checkedSub_of_le
  checkedMul_of_lt)

/-- A successful `getCurrentSlot` read. The store time is not before genesis, and the slot
is the milliseconds since genesis divided by the slot length. The read keeps the runner
state. -/
theorem getCurrentSlot_run_ok (st s s' : Store map) (cs : UInt64)
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s')) :
    st.genesisTimeMs ≤ st.timeMs ∧
      cs.toNat = (st.timeMs.toNat - st.genesisTimeMs.toNat) / slotDurationMs.toNat ∧ s' = s := by
  simp only [getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis] at h
  obtain ⟨hx, hs⟩ := run_liftErr_eq_ok _ _ _ _ h
  unfold EthCLSpecs.Heze.computeSlotAtTimeMs at hx
  cases he : (checkedSub st.timeMs st.genesisTimeMs
      "compute_slot_at_time_ms: time_ms - genesis_time_ms" : Except StateTransitionError UInt64)
    with
  | error e =>
    rw [he] at hx
    cases hx
  | ok e =>
    rw [he] at hx
    injection hx with hx
    obtain ⟨hle, he'⟩ := checkedSub_eq_ok _ _ _ _ he
    refine ⟨hle, ?_, hs⟩
    rw [← hx, UInt64.toNat_div, he']

/-- A successful `getTimeIntoSlotMs` read. The current slot is `cs`, its start is
`genesisTimeMs + cs * SLOT_DURATION_MS` with no overflow, and the time into the slot is the
store time minus that start. -/
theorem getTimeIntoSlotMs_run_ok (st s s' : Store map) (t : UInt64)
    (h : (getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (t, s')) :
    ∃ cs : UInt64,
      st.genesisTimeMs ≤ st.timeMs ∧
      cs.toNat = (st.timeMs.toNat - st.genesisTimeMs.toNat) / slotDurationMs.toNat ∧
      t.toNat = st.timeMs.toNat - (st.genesisTimeMs.toNat + cs.toNat * slotDurationMs.toNat) := by
  unfold getTimeIntoSlotMs at h
  obtain ⟨cs, s1, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hle, hcsv, -⟩ := getCurrentSlot_run_ok st s s1 cs hcs
  obtain ⟨start, s2, hstart, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hstartv, -⟩ := run_liftErr_eq_ok _ _ _ _ hstart
  -- The slot start: a checked product, then a checked sum.
  have hstartN : start.toNat = st.genesisTimeMs.toNat + cs.toNat * slotDurationMs.toNat := by
    unfold EthCLSpecs.Heze.computeTimeAtSlotMs at hstartv
    cases hm : (checkedMul cs slotDurationMs "compute_time_at_slot_ms: slot * SLOT_DURATION_MS"
        : Except StateTransitionError UInt64) with
    | error e =>
      rw [hm] at hstartv
      cases hstartv
    | ok p =>
      rw [hm] at hstartv
      rw [checkedAdd_eq_ok _ _ _ _ hstartv, checkedMul_eq_ok _ _ _ _ hm]
  -- The checked difference.
  cases hd : (checkedSub st.timeMs start
      "get_time_into_slot_ms: time_ms - compute_time_at_slot_ms(genesis_time_ms, current_slot)"
      : Except StateTransitionError UInt64) with
  | error e =>
    simp only [checkedSub] at hd h
    split at hd
    · rename_i hgt
      rw [ite_eq_left hgt] at h
      simp only [throwArithmetic, liftErr, Except.mapError, MonadExcept.ofExcept] at h
      cases h
    · cases hd
  | ok d =>
    have hdv := checkedSub_eq_ok _ _ _ _ hd
    simp only [checkedSub] at hd h
    split at hd
    · cases hd
    · rename_i hng
      rw [ite_eq_right hng] at h
      injection h with h
      injection h with ht _
      refine ⟨cs, hle, hcsv, ?_⟩
      rw [← ht, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hng), hstartN]

/-- The start of slot `k` in wall milliseconds, for the genesis time `g` in milliseconds. -/
def slotStartMs (g : UInt64) (k : Nat) : Nat :=
  g.toNat + k * slotDurationMs.toNat

/-- Take a store whose time is the wall time `w`. When its current slot is at least `n`, the
wall time is at least the start of slot `n`. -/
theorem slotStartMs_le_of_getCurrentSlot (st s s' : Store map) (cs : UInt64) (w n : Nat)
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s'))
    (htime : st.timeMs.toNat = w) (hD : 0 < slotDurationMs.toNat) (hn : n ≤ cs.toNat) :
    slotStartMs st.genesisTimeMs n ≤ w := by
  obtain ⟨hle, hcs, -⟩ := getCurrentSlot_run_ok st s s' cs h
  have hg : st.genesisTimeMs.toNat ≤ w := htime ▸ UInt64.le_iff_toNat_le.mp hle
  rw [htime] at hcs
  rw [hcs] at hn
  have hmul := (Nat.le_div_iff_mul_le hD).mp hn
  unfold slotStartMs
  generalize n * slotDurationMs.toNat = p at hmul ⊢
  omega

/-- An IL arrival inside the timely window of slot `k`. Take a store whose time is the wall
time `w`, with `w` between the start of slot `k` and that start plus `due`, and `due` at most
the slot length. Then the time into the slot is below `due`. -/
theorem getTimeIntoSlotMs_lt_of_window (st s s' : Store map) (t due : UInt64) (w k : Nat)
    (h : (getTimeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (t, s'))
    (htime : st.timeMs.toNat = w) (hdue : due.toNat ≤ slotDurationMs.toNat)
    (hlo : slotStartMs st.genesisTimeMs k ≤ w)
    (hhi : w < slotStartMs st.genesisTimeMs k + due.toNat) :
    t < due := by
  obtain ⟨cs, -, hcs, ht⟩ := getTimeIntoSlotMs_run_ok st s s' t h
  unfold slotStartMs at hlo hhi
  rw [htime] at hcs ht
  rw [UInt64.lt_iff_toNat_lt, ht]
  generalize hD : slotDurationMs.toNat = D at hcs ht hdue hlo hhi
  generalize hg : st.genesisTimeMs.toNat = g at hcs ht hlo hhi
  -- The elapsed time `w - g` is `k` slots plus a remainder below `due ≤ D`, so the current
  -- slot is `k`.
  have hDpos : 0 < D := by omega
  have hsucc : (k + 1) * D = k * D + D := Nat.succ_mul k D
  have hk : cs.toNat = k := by
    rw [hcs]
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [hsucc]; omega
  rw [hk]
  omega

/-- `getCurrentSlot` succeeds once the store time is not before genesis, and keeps the
runner state. -/
theorem getCurrentSlot_run_of_le (st s : Store map) (h : st.genesisTimeMs ≤ st.timeMs) :
    (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok ((st.timeMs - st.genesisTimeMs) / slotDurationMs, s) := by
  simp only [getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis]
  apply run_liftErr_of_ok
  unfold EthCLSpecs.Heze.computeSlotAtTimeMs
  rw [checkedSub_of_le _ _ _ h]
  rfl

/-- The current slot from the wall clock. The store time is the wall time `w`, and `w` lies
in slot `k`: at or after its start, before the start of slot `k + 1`. Then `getCurrentSlot`
returns `k`. -/
theorem getCurrentSlot_run_eq_of_window (st s : Store map) (w k : Nat)
    (htime : st.timeMs.toNat = w) (hlo : slotStartMs st.genesisTimeMs k ≤ w)
    (hhi : w < slotStartMs st.genesisTimeMs (k + 1)) :
    ∃ cs : UInt64, cs.toNat = k ∧
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
        = .ok (cs, s) := by
  unfold slotStartMs at hlo hhi
  have hsucc : (k + 1) * slotDurationMs.toNat = k * slotDurationMs.toNat + slotDurationMs.toNat :=
    Nat.succ_mul _ _
  rw [hsucc] at hhi
  have hle : st.genesisTimeMs ≤ st.timeMs := by rw [UInt64.le_iff_toNat_le]; omega
  refine ⟨_, ?_, getCurrentSlot_run_of_le st s hle⟩
  rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ hle, htime]
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [hsucc]; omega

/-- A list of slot `slot` that arrives inside the timely window of that slot is timely. The
store time is the wall time `w`, between the start of the slot and that start plus `due`.
The deadline `getInclusionListDueMs` is `due`, at most the slot length. Then the current
slot is `slot`, the clock reads succeed, and the time into the slot is below `due`. -/
theorem inclusionListTimely_of_window (st : Store map) (slot due : UInt64) (w : Nat)
    (hdueOk : EthCLSpecs.Heze.getInclusionListDueMs = .ok due)
    (htime : st.timeMs.toNat = w) (hdue : due.toNat ≤ slotDurationMs.toNat)
    (hlo : slotStartMs st.genesisTimeMs slot.toNat ≤ w)
    (hhi : w < slotStartMs st.genesisTimeMs slot.toNat + due.toNat) :
    InclusionListTimely st slot := by
  unfold slotStartMs at hlo hhi
  have hT := st.timeMs.toNat_lt
  have hle : st.genesisTimeMs ≤ st.timeMs := by rw [UInt64.le_iff_toNat_le]; omega
  have hcs := getCurrentSlot_run_of_le st st hle
  -- The current slot is `slot`: the elapsed time is `slot` slots plus a remainder below
  -- `due ≤ D`.
  have hsucc : (slot.toNat + 1) * slotDurationMs.toNat
      = slot.toNat * slotDurationMs.toNat + slotDurationMs.toNat := Nat.succ_mul _ _
  have hk : (st.timeMs - st.genesisTimeMs) / slotDurationMs = slot := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ hle, htime]
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [hsucc]; omega
  rw [hk] at hcs
  refine ⟨hcs, ?_⟩
  -- The slot start fits in `UInt64`, so the checked reads succeed.
  have hmul : slot.toNat * slotDurationMs.toNat < 2 ^ 64 := by omega
  have hmulN : (slot * slotDurationMs).toNat = slot.toNat * slotDurationMs.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hmul]
  have hadd : st.genesisTimeMs.toNat + (slot * slotDurationMs).toNat < 2 ^ 64 := by
    rw [hmulN]; omega
  have hstartN : (st.genesisTimeMs + slot * slotDurationMs).toNat
      = st.genesisTimeMs.toNat + slot.toNat * slotDurationMs.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hadd, hmulN]
  have hstart : EthCLSpecs.Heze.computeTimeAtSlotMs st.genesisTimeMs slot
      = .ok (st.genesisTimeMs + slot * slotDurationMs) := by
    unfold EthCLSpecs.Heze.computeTimeAtSlotMs
    rw [checkedMul_of_lt _ _ _ hmul]
    exact checkedAdd_of_lt _ _ _ hadd
  have hsle : st.genesisTimeMs + slot * slotDurationMs ≤ st.timeMs := by
    rw [UInt64.le_iff_toNat_le, hstartN]; omega
  refine ⟨st.timeMs - (st.genesisTimeMs + slot * slotDurationMs), due, ?_, hdueOk, ?_⟩
  · unfold getTimeIntoSlotMs
    rw [run_bind, hcs, except_bind_ok, run_bind,
      run_liftErr_of_ok _ _ (by rw [hstart]; rfl), except_bind_ok]
    dsimp only
    rw [checkedSub_of_le _ _ _ hsle]
    rfl
  · rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ hsle, hstartN]
    omega

/-- Take a store whose time is the wall time `w`, and whose current slot is `cs`. Then `w`
lies in slot `cs`. The converse direction is `getCurrentSlot_run_eq_of_window`. -/
theorem slot_window_of_getCurrentSlot (st s s' : Store map) (cs : UInt64) (w : Nat)
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s'))
    (htime : st.timeMs.toNat = w) (hD : 0 < slotDurationMs.toNat) :
    slotStartMs st.genesisTimeMs cs.toNat ≤ w ∧
      w < slotStartMs st.genesisTimeMs (cs.toNat + 1) := by
  refine ⟨slotStartMs_le_of_getCurrentSlot st s s' cs w cs.toNat h htime hD (Nat.le_refl _), ?_⟩
  obtain ⟨hle, hcs, -⟩ := getCurrentSlot_run_ok st s s' cs h
  have hg : st.genesisTimeMs.toNat ≤ w := htime ▸ UInt64.le_iff_toNat_le.mp hle
  rw [htime] at hcs
  -- The milliseconds since genesis, `e`, lie below the start of the next slot.
  generalize he : w - st.genesisTimeMs.toNat = e at hcs
  have hlt : e < slotDurationMs.toNat * (e / slotDurationMs.toNat + 1) := by
    have := Nat.lt_mul_div_succ e hD
    simpa [Nat.mul_add] using this
  rw [← hcs] at hlt
  unfold slotStartMs
  rw [Nat.mul_comm (cs.toNat + 1)]
  generalize slotDurationMs.toNat * (cs.toNat + 1) = p at hlt ⊢
  omega

end Clock

section BlockClock
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

open EthCLSpecs.Heze (getCurrentSlot)
open EthCLLib.Proofs (run_bind_eq_ok run_get_bind_eq_ok run_assert_bind_eq_ok)

/-- A successful `onBlock` run for a block that the store does not hold passed the clock
check: the current slot of the store it read is at least the slot of the block. A known
block returns before the check (`onBlock_run_of_known`). -/
theorem onBlock_run_ok_currentSlot (sb : SignedBeaconBlock) (pre post : Store map)
    (hnew : FcMap.contains pre.blocks (htr sb.message) = false)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    ∃ (cs : UInt64) (s s' : Store map),
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) pre).run s
        = .ok (cs, s') ∧ sb.message.slot ≤ cs := by
  unfold onBlock at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rw [ite_eq_right (by rw [hnew]; exact Bool.false_ne_true)] at h
  -- The parent state, the parent-payload check, then the clock read and its check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨cs, s, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hge, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact ⟨cs, _, s, hcs, hge⟩

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  [LawfulFcMap map Root]

/-- Where a key of `blockStates` comes from. The trace starts at a store with no state at
`r` and ends at a store with one. Then an `onBlock` event of the trace ran on a new block
with root `r`. The theorem names the trace before that event and the store the event ran
on. The envelope handler writes `blockStates` only at a key it read, a known block leaves
the store unchanged, and the other handlers keep the map. -/
theorem NodeTrace.blockStates_origin {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} (h : NodeTrace s0 events arrivals s)
    (r : Root) (hnone : FcMap.lookup s0.blockStates r = none)
    (hst : (FcMap.lookup s.blockStates r).isSome) :
    ∃ (es1 es2 : List TraceEvent) (sb : SignedBeaconBlock)
      (arr1 : List (SignedInclusionList × Bool)) (mid mid' : Store map),
      events = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧
      NodeTrace s0 es1 arr1 mid ∧
      FcMap.contains mid.blocks (htr sb.message) = false ∧
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run mid
        = .ok ((), mid') ∧
      htr sb.message = r := by
  revert hst
  induction h with
  | nil => intro hst; rw [hnone] at hst; cases hst
  | @handler events arrivals pre post e htr' hrun ih =>
    intro hst
    -- A state at `r` before the event: the origin is earlier in the trace.
    cases hpre : FcMap.lookup pre.blockStates r with
    | some st0 =>
      obtain ⟨es1, es2, sb, arr1, mid, mid', heq, hmid, hnew, hblk, hroot⟩ :=
        ih (by rw [hpre]; rfl)
      exact ⟨es1, es2 ++ [.handler e], sb, arr1, mid, mid', by simp [heq], hmid, hnew, hblk,
        hroot⟩
    | none =>
      -- No state at `r` before the event: the event itself adds it.
      have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
          KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
            (pre.blocks, pre.blockStates) x →
          x.run pre = .ok ((), post) → False := by
        intro x hx hrunx
        have hmaps := hx pre () post rfl hrunx
        injection hmaps with _ hstates
        rw [hstates, hpre] at hst
        cases hst
      cases e with
      | tick time => exact (hkeep _ (onTick_keeps_blockMaps _ time) hrun).elim
      | attestation att isFromBlock =>
        exact (hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock) hrun).elim
      | attesterSlashing asl => exact (hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl) hrun).elim
      | payloadAttestation msg isFromBlock =>
        exact (hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) hrun).elim
      | block sb =>
        cases hknown : FcMap.contains pre.blocks (htr sb.message)
        · obtain ⟨-, hkeys⟩ := onBlock_run_maps sb pre post hknown hrun
          rcases hkeys r hst with hr | hst'
          · exact ⟨events, [], sb, arrivals, pre, post, rfl, htr', hknown, hrun, hr.symm⟩
          · rw [hpre] at hst'
            cases hst'
        · -- A known block leaves the store unchanged, so no state appears at `r`.
          rw [onBlock_run_of_known sb pre post hknown hrun, hpre] at hst
          cases hst
      | envelope signedEnv =>
        obtain ⟨-, hkeys⟩ := onExecutionPayloadEnvelope_run_keys signedEnv pre post hrun
        have hst' := hkeys r hst
        rw [hpre] at hst'
        cases hst'
  | @inclusionList events arrivals pre post signed b htr' hrun hb ih =>
    intro hst
    -- `onInclusionList` writes only the IL store.
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs'] at hst
    obtain ⟨es1, es2, sb, arr1, mid, mid', heq, hmid, hnew, hblk, hroot⟩ := ih hst
    exact ⟨es1, es2 ++ [.inclusionList signed], sb, arr1, mid, mid', by simp [heq], hmid, hnew,
      hblk, hroot⟩

end BlockClock

section Arrivals
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- A trace with no events has no arrivals and ends at its seed. -/
theorem NodeTrace.nil_inv {s0 s : Store map} {arrivals : List (SignedInclusionList × Bool)}
    (h : NodeTrace s0 [] arrivals s) : arrivals = [] ∧ s = s0 := by
  generalize hes : ([] : List TraceEvent) = es at h
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | handler e _ _ => simp at hes
  | inclusionList signed b _ _ _ => simp at hes

/-- A trace of one inclusion-list event: its one arrival carries the timeliness bit of the
run on the seed. The bit is `true` exactly when the list is timely at the seed. -/
theorem NodeTrace.single_inclusionList {s0 s : Store map} {signed : SignedInclusionList}
    {arrivals : List (SignedInclusionList × Bool)}
    (h : NodeTrace s0 [.inclusionList signed] arrivals s) :
    ∃ b, arrivals = [(signed, b)] ∧ (b = true ↔ InclusionListTimely s0 signed.message.slot) := by
  generalize hes : [TraceEvent.inclusionList signed] = es at h
  cases h with
  | nil => simp at hes
  | handler e _ _ =>
    -- The last event is the inclusion list, so it is no handler event.
    have hlast := congrArg List.getLast? hes
    simp at hlast
  | @inclusionList events arrs prev _ signed' b hprev _ hb =>
    have hlast := congrArg List.getLast? hes
    have hlen := congrArg List.length hes
    simp only [List.getLast?_singleton, List.getLast?_append, Option.some_or,
      Option.some.injEq, TraceEvent.inclusionList.injEq] at hlast
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have hnil : events = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hlast hnil
    obtain ⟨rfl, rfl⟩ := hprev.nil_inv
    exact ⟨b, rfl, hb⟩

/-- Every arrival of a trace comes from an inclusion-list event of the trace. -/
theorem NodeTrace.mem_arrivals {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} (h : NodeTrace s0 events arrivals s)
    {a : SignedInclusionList × Bool} (ha : a ∈ arrivals) :
    TraceEvent.inclusionList a.1 ∈ events := by
  induction h with
  | nil => cases ha
  | handler e _ _ ih => exact List.mem_append_left _ (ih ha)
  | inclusionList signed b _ _ _ ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (ih ha)
    · simp only [List.mem_singleton] at ha
      subst ha
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The first arrival of a list sets its first timeliness. Take an inclusion-list event of
the trace, with no earlier event that carries the same list. The event runs on the store
`mid`, with the timeliness bit `b`. Then the first timeliness of the list is `b`, and `b` is
`true` exactly when the list is timely at `mid`. -/
theorem NodeTrace.firstTimely_of_first {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × Bool)} (h : NodeTrace s0 events arrivals s)
    {es1 es2 : List TraceEvent} {signed : SignedInclusionList}
    (hes : events = es1 ++ .inclusionList signed :: es2)
    (hfirst : ∀ sg, TraceEvent.inclusionList sg ∈ es1 → sg.message ≠ signed.message) :
    ∃ (mid : Store map) (arr1 : List (SignedInclusionList × Bool)) (b : Bool),
      NodeTrace s0 es1 arr1 mid ∧
      (b = true ↔ InclusionListTimely mid signed.message.slot) ∧
      Arrivals.firstTimely arrivals signed.message = some b := by
  obtain ⟨mid, arr1, arr2, h1, h2, rfl⟩ := h.split hes
  obtain ⟨m1, a1, a2, h21, -, rfl⟩ := h2.split (es1 := [.inclusionList signed]) (es2 := es2) rfl
  obtain ⟨b, rfl, hb⟩ := h21.single_inclusionList
  refine ⟨mid, arr1, b, h1, hb, ?_⟩
  -- No arrival before the event carries the list.
  have hnone : arr1.find? (fun a => a.1.message == signed.message) = none := by
    rw [List.find?_eq_none]
    intro a ha
    simpa using hfirst a.1 (h1.mem_arrivals ha)
  unfold Arrivals.firstTimely
  rw [List.find?_append, hnone]
  simp

end Arrivals

section Clocked
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- The clock condition of one event at the wall time `w`, in milliseconds. A tick moves
the store time to `w`. Any other event runs on a store whose time is `w`. -/
def ClockAt : TraceEvent → Nat → Store map → Prop
  | .handler (.tick timeMs), w, _ => timeMs.toNat = w
  | _, w, st => st.timeMs.toNat = w

/-- `ClockAt` is an equality of numbers in each case, so it is decidable. -/
instance ClockAt.decidable (e : TraceEvent) (w : Nat) (st : Store map) :
    Decidable (ClockAt e w st) := by
  unfold ClockAt
  split <;> infer_instance

/-- A node trace on the wall clock. Each event carries its wall time. The wall times do not
decrease, and each event meets `ClockAt` on the store it runs on. So the node ticks to its
wall clock before it handles a message. The condition names the store before an event
through any trace of the events before it, and `NodeTrace.split` gives such a trace. -/
structure ClockedTrace (s0 : Store map) (tevs : List (TraceEvent × Nat))
    (arrivals : List (SignedInclusionList × Bool)) (s : Store map) : Prop where
  /-- The handler runs, without the wall times. -/
  trace : NodeTrace s0 (tevs.map Prod.fst) arrivals s
  /-- The wall times do not decrease. -/
  mono : tevs.Pairwise (fun a b => a.2 ≤ b.2)
  /-- Each event meets the clock condition on the store it runs on. -/
  clock : ∀ (pre : List (TraceEvent × Nat)) (x : TraceEvent × Nat) post,
    tevs = pre ++ x :: post →
    ∀ (arr : List (SignedInclusionList × Bool)) (mid : Store map),
      NodeTrace s0 (pre.map Prod.fst) arr mid → ClockAt x.1 x.2 mid

end Clocked

end EthCLSpecs.Proofs.Heze
