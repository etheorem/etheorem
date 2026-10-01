import EthCLSpecs.Proofs.Heze.SlotsIncrease
import EthCLSpecs.Proofs.Heze.ILStoreOrder

/-!
# `EthCLSpecs.Proofs.Heze.ClockedTrace`: a node trace on the wall clock

A node trace (`NodeTrace.lean`) records the handler runs of one node. It has no wall time.
The network results of `NodeViews.lean` compare the events of a node with a send time on
the wall clock. This module adds the wall clock.

## The clock of the store

`store.time` counts whole seconds. `getCurrentSlot` divides the milliseconds since genesis
by the slot length. `timeIntoSlotMs` takes them modulo the slot length. `onTick` can move
`store.time` back. No other handler reads a clock.

`ClockedTrace` gives each event a wall time `w` in milliseconds. The wall times do not
decrease. A tick moves the store time to `w` in whole seconds. Any other event runs on a
store whose time is `w` in whole seconds. So the node ticks to its wall clock before it
handles a message. This is the clock of an honest node.

## The results

- Every handler keeps `genesisTime` (`NodeTrace.genesisTime`).
- `slotStartMs g k` is the start of slot `k` in wall milliseconds.
  `slotStartMs_le_of_getCurrentSlot`: when the current slot is at least `n`, the wall time
  is past the start of slot `n`. `timeIntoSlotMs_lt_of_window`: an arrival in the first
  `due` milliseconds of a slot is timely. The seconds round the wall time down, so the
  rounding cannot make an arrival late. The lemma needs a slot length of whole seconds.
  Both presets have one (6000 ms and 12000 ms). `getCurrentSlot_run_eq_of_window`: a wall
  time in slot `k` gives the current slot `k`.
- `onBlock_run_ok_currentSlot`: a successful `onBlock` passed its clock check.
  `NodeTrace.blockStates_origin`: a state at a root comes from an `onBlock` event on a
  block with that root.
- `NodeTrace.firstTimely_of_first`: the first event that carries a list sets its first
  timeliness (`Arrivals.firstTimely`, `ILStoreOrder.lean`).
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
theorem onTick_keeps_genesisTime (v : UInt64) (time : UInt64) :
    KeepsAt (fun st : Store map => st.genesisTime) v
      (onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) time) := by
  unfold onTick
  keeps_solve

/-- `onBlock` keeps the genesis time. -/
theorem onBlock_keeps_genesisTime (v : UInt64) (signedBlock : SignedBeaconBlock) :
    KeepsAt (fun st : Store map => st.genesisTime) v
      (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) signedBlock) := by
  unfold onBlock
  keeps_solve

/-- `onAttestation` keeps the genesis time. -/
theorem onAttestation_keeps_genesisTime (v : UInt64) (att : Attestation) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.genesisTime) v
      (onAttestation (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) att
        isFromBlock) := by
  unfold onAttestation
  keeps_solve

omit [Config] in
/-- `onAttesterSlashing` keeps the genesis time. -/
theorem onAttesterSlashing_keeps_genesisTime (v : UInt64) (asl : AttesterSlashing) :
    KeepsAt (fun st : Store map => st.genesisTime) v
      (onAttesterSlashing (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
        asl) := by
  unfold onAttesterSlashing
  keeps_solve

/-- `onPayloadAttestationMessage` keeps the genesis time. -/
theorem onPayloadAttestationMessage_keeps_genesisTime (v : UInt64)
    (msg : PayloadAttestationMessage) (isFromBlock : Bool) :
    KeepsAt (fun st : Store map => st.genesisTime) v
      (onPayloadAttestationMessage (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) msg isFromBlock) := by
  unfold onPayloadAttestationMessage
  keeps_solve

variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- `onExecutionPayloadEnvelope` keeps the genesis time. -/
theorem onExecutionPayloadEnvelope_keeps_genesisTime (v : UInt64)
    (signedEnv : SignedExecutionPayloadEnvelope) :
    KeepsAt (fun st : Store map => st.genesisTime) v
      (onExecutionPayloadEnvelope (map := map)
        (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv) := by
  unfold onExecutionPayloadEnvelope
  keeps_solve

/-- A handler event keeps the genesis time. -/
theorem HandlerEvent.run_keeps_genesisTime (e : HandlerEvent) (s s' : Store map)
    (h : (HandlerEvent.run (map := map) e).run s = .ok ((), s')) :
    s'.genesisTime = s.genesisTime := by
  have hk : KeepsAt (fun st : Store map => st.genesisTime) s.genesisTime
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
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s) :
    s.genesisTime = s0.genesisTime := by
  induction h with
  | nil => rfl
  | handler e _ hrun ih => exact (HandlerEvent.run_keeps_genesisTime e _ _ hrun).trans ih
  | inclusionList signed t _ hclock hrun ih =>
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    exact ih

end Genesis

section Clock
variable {map : MapKind} [Preset] [HasherTag] [Config]

open EthCLSpecs.Heze (timeIntoSlotMs getCurrentSlot)
open EthCLSpecs.Heze.Const (slotDurationMs)
open EthCLLib.Proofs (ForkChoiceStoreRun.throwArithmetic_run run_bind run_pure
  except_bind_error)

omit [Preset] [HasherTag] [Config] in
/-- The overflow guard of `checkedMul e 1000`: `e` is zero, or the truncating product
divides back to `1000`. Then `e * 1000` fits in `UInt64`. -/
theorem toNat_mul_1000_lt (e : UInt64) (h : e = 0 ∨ e * 1000 / e = 1000) :
    e.toNat * 1000 < 2 ^ 64 := by
  rcases h with h | h
  · simp [h]
  · have hpos : 0 < e.toNat := by
      rcases Nat.eq_zero_or_pos e.toNat with h0 | h0
      · have : e = 0 := UInt64.toNat_inj.mp (by simpa using h0)
        subst this
        simp at h
      · exact h0
    have hn := congrArg UInt64.toNat h
    simp only [UInt64.toNat_div, UInt64.toNat_mul] at hn
    -- `p` is the truncated product. It divides back to `1000`, so it is at least
    -- `1000 * e`, and it never exceeds the true product.
    generalize hp : e.toNat * (1000 : UInt64).toNat % 2 ^ 64 = p at hn
    have hlo : 1000 * e.toNat ≤ p := by
      have := (Nat.le_div_iff_mul_le hpos).mp (Nat.le_of_eq hn.symm)
      simpa [Nat.mul_comm] using this
    have hhi : p ≤ e.toNat * 1000 := by
      rw [← hp]
      exact Nat.le_trans (Nat.mod_le _ _) (by simp)
    have hlt : p < 2 ^ 64 := by
      rw [← hp]
      exact Nat.mod_lt _ (by decide)
    omega

/-- A successful `timeIntoSlotMs` read: the store time is not before genesis, and the value
is the elapsed milliseconds modulo the slot length. -/
theorem timeIntoSlotMs_run_ok (st s s' : Store map) (t : UInt64)
    (h : (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (t, s')) :
    st.genesisTime ≤ st.time ∧
      t = EthCLSpecs.Fulu.secondsToMilliseconds (st.time - st.genesisTime) % slotDurationMs := by
  simp only [timeIntoSlotMs, checkedSub] at h
  split at h
  · cases h
  · rename_i hle
    refine ⟨UInt64.not_lt.mp hle, ?_⟩
    injection h with h
    injection h with h
    exact h.symm

/-- A successful `getCurrentSlot` read. The store time is not before genesis, and the
milliseconds since genesis do not overflow. The slot is those milliseconds divided by the
slot length. -/
theorem getCurrentSlot_run_ok (st s s' : Store map) (cs : UInt64)
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s')) :
    st.genesisTime ≤ st.time ∧ (st.time - st.genesisTime).toNat * 1000 < 2 ^ 64 ∧
      cs.toNat = (st.time - st.genesisTime).toNat * 1000 / slotDurationMs.toNat := by
  revert h
  simp only [getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis, checkedSub, checkedMul]
  -- Two checked operations, each a throw or a `pure`. A throw contradicts `h`.
  split
  · intro h
    simp only [run_bind, ForkChoiceStoreRun.throwArithmetic_run, except_bind_error] at h
    cases h
  · rename_i hg
    simp only [pure_bind]
    split
    · intro h
      simp only [run_bind, ForkChoiceStoreRun.throwArithmetic_run, except_bind_error] at h
      cases h
    · rename_i hm
      simp only [pure_bind, run_pure, Except.ok.injEq, Prod.mk.injEq]
      rintro ⟨hcs, -⟩
      -- The guard passed: `e * 1000` did not wrap.
      have hwrap := toNat_mul_1000_lt (st.time - st.genesisTime) (by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hm
        by_cases h0 : st.time - st.genesisTime = 0
        · exact Or.inl h0
        · exact Or.inr (hm h0))
      refine ⟨UInt64.not_lt.mp hg, hwrap, ?_⟩
      rw [← hcs, EthCLSpecs.Heze.Const.genesisSlot]
      simp only [UInt64.zero_add, UInt64.toNat_div, UInt64.toNat_mul]
      rw [Nat.mod_eq_of_lt (by simpa using hwrap)]
      simp

/-- The start of slot `k` in wall milliseconds, for the genesis time `g` in seconds. -/
def slotStartMs (g : UInt64) (k : Nat) : Nat :=
  g.toNat * 1000 + k * slotDurationMs.toNat

/-- `UINT64_MAX / 1000`, the largest whole-seconds time that `secondsToMilliseconds`
multiplies by 1000. Above it, the function returns `UINT64_MAX`. -/
def maxMsSeconds : Nat := 18446744073709551

omit [Preset] [HasherTag] [Config] in
/-- `maxMsSeconds` is `UINT64_MAX / 1000`. -/
theorem maxMsSeconds_eq : ((0xffffffffffffffff : UInt64) / 1000).toNat = maxMsSeconds := by
  decide

/-- Take a store whose time is the wall time `w` in whole seconds. When its current slot is
at least `n`, the wall time is at least the start of slot `n`. -/
theorem slotStartMs_le_of_getCurrentSlot (st s s' : Store map) (cs : UInt64) (w n : Nat)
    (h : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s'))
    (htime : st.time.toNat = w / 1000) (hD : 0 < slotDurationMs.toNat) (hn : n ≤ cs.toNat) :
    slotStartMs st.genesisTime n ≤ w := by
  obtain ⟨hle, -, hcs⟩ := getCurrentSlot_run_ok st s s' cs h
  have hg : st.genesisTime.toNat ≤ w / 1000 := htime ▸ UInt64.le_iff_toNat_le.mp hle
  rw [UInt64.toNat_sub_of_le _ _ hle, htime] at hcs
  rw [hcs] at hn
  have hmul := (Nat.le_div_iff_mul_le hD).mp hn
  unfold slotStartMs
  generalize n * slotDurationMs.toNat = p at hmul ⊢
  omega

/-- An IL arrival inside the timely window of slot `k` is timely. Take a store whose time
is the wall time `w` in whole seconds, with `w` between the start of slot `k` and that
start plus `due`. The slot length is a whole number of seconds, and `due` is at most the
slot length. Then the time into the slot is below `due`. The seconds round `w` down, so
the rounding cannot push an arrival past `due`. `secondsToMilliseconds` returns
`UINT64_MAX` above `UINT64_MAX / 1000` seconds. `hsec` keeps the time at or below that
bound. -/
theorem timeIntoSlotMs_lt_of_window (st s s' : Store map) (t due : UInt64) (w k : Nat)
    (h : (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (t, s'))
    (htime : st.time.toNat = w / 1000) (hD : 1000 ∣ slotDurationMs.toNat)
    (hdue : due.toNat ≤ slotDurationMs.toNat)
    (hlo : slotStartMs st.genesisTime k ≤ w)
    (hhi : w < slotStartMs st.genesisTime k + due.toNat)
    (hsec : w / 1000 ≤ maxMsSeconds) :
    t < due := by
  -- `omega` reads the bound only as a numeral.
  unfold maxMsSeconds at hsec
  obtain ⟨hle, ht⟩ := timeIntoSlotMs_run_ok st s s' t h
  have hg : st.genesisTime.toNat ≤ w / 1000 := htime ▸ UInt64.le_iff_toNat_le.mp hle
  -- The elapsed whole seconds stay at or below `UINT64_MAX / 1000`, so
  -- `secondsToMilliseconds` multiplies by 1000.
  have he : (st.time - st.genesisTime).toNat = w / 1000 - st.genesisTime.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle, htime]
  have hms : EthCLSpecs.Fulu.secondsToMilliseconds (st.time - st.genesisTime)
      = (st.time - st.genesisTime) * 1000 := by
    unfold EthCLSpecs.Fulu.secondsToMilliseconds
    rw [if_neg]
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le, he, maxMsSeconds_eq, maxMsSeconds]
    omega
  obtain ⟨d, hd⟩ := hD
  unfold slotStartMs at hlo hhi
  rw [UInt64.lt_iff_toNat_lt, ht, hms, UInt64.toNat_mod, UInt64.toNat_mul, he,
    UInt64.toNat_ofNat, hd]
  rw [hd] at hlo hhi hdue
  generalize hq : w / 1000 - st.genesisTime.toNat = q
  -- The elapsed milliseconds `q * 1000` fit, and they are `k` slots plus a remainder below
  -- `due`.
  have hfit : q * (1000 % 2 ^ 64) % 2 ^ 64 = q * 1000 := by
    rw [Nat.mod_eq_of_lt (by decide : 1000 < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hfit]
  generalize hm : k * d = m
  have hkm : k * (1000 * d) = 1000 * m := by rw [← hm, Nat.mul_left_comm]
  rw [hkm] at hlo hhi
  have hsplit : q * 1000 = (q * 1000 - 1000 * m) + 1000 * d * k := by
    have : 1000 * d * k = 1000 * m := by rw [← hm, Nat.mul_assoc, Nat.mul_comm d k]
    omega
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

omit [Preset] [HasherTag] [Config] in
/-- When `e * 1000` fits in `UInt64`, the truncating product divides back to `1000`. The
converse of `toNat_mul_1000_lt`. -/
theorem mul_1000_div_self (e : UInt64) (he : e ≠ 0) (hfit : e.toNat * 1000 < 2 ^ 64) :
    e * 1000 / e = 1000 := by
  apply UInt64.toNat_inj.mp
  have hpos : 0 < e.toNat := by
    rcases Nat.eq_zero_or_pos e.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) he
    · exact h0
  rw [UInt64.toNat_div, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt hfit, Nat.mul_comm, Nat.mul_div_cancel _ hpos]

omit [Preset] [HasherTag] [Config] in
/-- A window of wall milliseconds, read in whole seconds. The bounds are whole seconds, so
the rounding of `w / 1000` keeps `w` inside. -/
theorem window_seconds (g m d w : Nat) (hlo : g * 1000 + m * 1000 ≤ w)
    (hhi : w < g * 1000 + (m * 1000 + d * 1000)) :
    g + m ≤ w / 1000 ∧ w / 1000 < g + m + d := by
  omega

omit [Preset] [HasherTag] [Config] in
/-- A window `[s, s + due)` that holds `t + Δ`, with `due ≤ D`, has a positive length `D`. -/
theorem pos_of_window (s t Δ due D : Nat) (hlo : s ≤ t) (hhi : t + Δ < s + due)
    (hdue : due ≤ D) : 0 < D := by
  omega

/-- `getCurrentSlot` succeeds when the store time is not before genesis and the
milliseconds since genesis fit in `UInt64`. It reads nothing else, so the runner state stays
the same. The converse of `getCurrentSlot_run_ok`. -/
theorem getCurrentSlot_run_exists (st s : Store map) (hle : st.genesisTime ≤ st.time)
    (hfit : (st.time - st.genesisTime).toNat * 1000 < 2 ^ 64) :
    ∃ cs, (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
      = .ok (cs, s) := by
  simp only [getCurrentSlot, EthCLSpecs.Heze.getSlotsSinceGenesis, checkedSub, checkedMul]
  split
  · rename_i hg
    exact absurd hle (UInt64.not_le.mpr hg)
  · simp only [pure_bind]
    split
    · rename_i hm
      exfalso
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
      exact hm.2 (mul_1000_div_self _ hm.1 hfit)
    · exact ⟨_, rfl⟩

/-- The current slot from the wall clock. The store time is the wall time `w` in whole
seconds, and `w` lies in slot `k`: at or after its start, before the start of slot
`k + 1`. The slot length is a whole number of seconds. `hsec` keeps the milliseconds since
genesis inside `UInt64`. Then `getCurrentSlot` returns `k`. -/
theorem getCurrentSlot_run_eq_of_window (st s : Store map) (w k : Nat)
    (htime : st.time.toNat = w / 1000) (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hlo : slotStartMs st.genesisTime k ≤ w) (hhi : w < slotStartMs st.genesisTime (k + 1))
    (hsec : w / 1000 ≤ maxMsSeconds) :
    ∃ cs : UInt64, cs.toNat = k ∧
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) st).run s
        = .ok (cs, s) := by
  unfold maxMsSeconds at hsec
  obtain ⟨d, hd⟩ := hDdiv
  unfold slotStartMs at hlo hhi
  rw [hd] at hlo hhi
  -- Name the start of slot `k` in seconds since genesis, `m = k * d`, so `omega` sees
  -- linear terms only.
  have e1 : k * (1000 * d) = k * d * 1000 := by rw [Nat.mul_comm 1000 d, ← Nat.mul_assoc]
  have e2 : (k + 1) * (1000 * d) = k * d * 1000 + d * 1000 := by
    rw [Nat.add_mul, Nat.one_mul, e1, Nat.mul_comm 1000 d]
  rw [e1] at hlo
  rw [e2] at hhi
  generalize hm : k * d = m at hlo hhi
  -- The window in whole seconds: `g + m ≤ w / 1000 < g + m + d`.
  obtain ⟨hlo', hhi'⟩ := window_seconds _ m d w hlo hhi
  have hle : st.genesisTime ≤ st.time := by
    rw [UInt64.le_iff_toNat_le, htime]
    omega
  have he : (st.time - st.genesisTime).toNat = w / 1000 - st.genesisTime.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle, htime]
  have hfit : (st.time - st.genesisTime).toNat * 1000 < 2 ^ 64 := by
    rw [he]
    omega
  obtain ⟨cs, hrun⟩ := getCurrentSlot_run_exists st s hle hfit
  refine ⟨cs, ?_, hrun⟩
  obtain ⟨-, -, hcs⟩ := getCurrentSlot_run_ok st s s cs hrun
  rw [hcs, he, hd, Nat.mul_comm 1000 d, Nat.mul_div_mul_right _ _ (by decide : 0 < 1000)]
  apply Nat.div_eq_of_lt_le
  · rw [hm]
    omega
  · rw [Nat.add_mul, Nat.one_mul, hm]
    omega

end Clock

section BlockClock
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]

open EthCLSpecs.Heze (getCurrentSlot)
open EthCLLib.Proofs (run_bind_eq_ok run_get_bind_eq_ok run_assert_bind_eq_ok)

/-- A successful `onBlock` run passed the clock check: the current slot of the store it
read is at least the slot of the block. -/
theorem onBlock_run_ok_currentSlot (sb : SignedBeaconBlock) (pre post : Store map)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    ∃ (cs : UInt64) (s s' : Store map),
      (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) pre).run s
        = .ok (cs, s') ∧ sb.message.slot ≤ cs := by
  unfold onBlock at h
  have h := run_get_bind_eq_ok _ _ _ h
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
`r` and ends at a store with one. Then an `onBlock` event of the trace ran on a block with
root `r`. The theorem names the trace before that event and the store the event ran on.
The envelope handler writes `blockStates` only at a key it read, and the other handlers
keep the map. -/
theorem NodeTrace.blockStates_origin {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    (r : Root) (hnone : FcMap.lookup s0.blockStates r = none)
    (hst : (FcMap.lookup s.blockStates r).isSome) :
    ∃ (es1 es2 : List TraceEvent) (sb : SignedBeaconBlock)
      (arr1 : List (SignedInclusionList × UInt64)) (mid mid' : Store map),
      events = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧
      NodeTrace s0 es1 arr1 mid ∧
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
      obtain ⟨es1, es2, sb, arr1, mid, mid', heq, hmid, hblk, hroot⟩ := ih (by rw [hpre]; rfl)
      exact ⟨es1, es2 ++ [.handler e], sb, arr1, mid, mid', by simp [heq], hmid, hblk, hroot⟩
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
        obtain ⟨-, hkeys⟩ := onBlock_run_maps sb pre post hrun
        rcases hkeys r hst with hr | hst'
        · exact ⟨events, [], sb, arrivals, pre, post, rfl, htr', hrun, hr.symm⟩
        · rw [hpre] at hst'
          cases hst'
      | envelope signedEnv =>
        obtain ⟨-, hkeys⟩ := onExecutionPayloadEnvelope_run_keys signedEnv pre post hrun
        have hst' := hkeys r hst
        rw [hpre] at hst'
        cases hst'
  | @inclusionList events arrivals pre post signed t htr' hclock hrun ih =>
    intro hst
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
    obtain ⟨es1, es2, sb, arr1, mid, mid', heq, hmid, hblk, hroot⟩ := ih hst
    exact ⟨es1, es2 ++ [.inclusionList signed], sb, arr1, mid, mid', by simp [heq], hmid, hblk,
      hroot⟩

end BlockClock

section Arrivals
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

open EthCLSpecs.Heze (timeIntoSlotMs onInclusionList)

/-- A trace with no events has no arrivals and ends at its seed. -/
theorem NodeTrace.nil_inv {s0 s : Store map} {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 [] arrivals s) : arrivals = [] ∧ s = s0 := by
  generalize hes : ([] : List TraceEvent) = es at h
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | handler e _ _ => simp at hes
  | inclusionList signed t _ _ _ => simp at hes

/-- A trace of one inclusion-list event: its one arrival carries the time into the slot of
the seed. -/
theorem NodeTrace.single_inclusionList {s0 s : Store map} {signed : SignedInclusionList}
    {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 [.inclusionList signed] arrivals s) :
    ∃ t, arrivals = [(signed, t)] ∧
      (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) s0).run s0
        = .ok (t, s0) := by
  generalize hes : [TraceEvent.inclusionList signed] = es at h
  cases h with
  | nil => simp at hes
  | handler e _ _ =>
    -- The last event is the inclusion list, so it is no handler event.
    have hlast := congrArg List.getLast? hes
    simp at hlast
  | @inclusionList events arrs prev _ signed' t hprev hclock _ =>
    have hlast := congrArg List.getLast? hes
    have hlen := congrArg List.length hes
    simp only [List.getLast?_singleton, List.getLast?_append, Option.some_or,
      Option.some.injEq, TraceEvent.inclusionList.injEq] at hlast
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have hnil : events = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hlast hnil
    obtain ⟨rfl, rfl⟩ := hprev.nil_inv
    exact ⟨t, rfl, hclock⟩

/-- Every arrival of a trace comes from an inclusion-list event of the trace. -/
theorem NodeTrace.mem_arrivals {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    {a : SignedInclusionList × UInt64} (ha : a ∈ arrivals) :
    TraceEvent.inclusionList a.1 ∈ events := by
  induction h with
  | nil => cases ha
  | handler e _ _ ih => exact List.mem_append_left _ (ih ha)
  | inclusionList signed t _ _ _ ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (ih ha)
    · simp only [List.mem_singleton] at ha
      subst ha
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The first arrival of a list sets its first timeliness. Take an inclusion-list event of
the trace, with no earlier event that carries the same list. The event runs on the store
`mid`, where the time into the slot is `t`. Then the first timeliness of the list is the
timeliness of `t`. -/
theorem NodeTrace.firstTimely_of_first {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (SignedInclusionList × UInt64)} (h : NodeTrace s0 events arrivals s)
    {es1 es2 : List TraceEvent} {signed : SignedInclusionList}
    (hes : events = es1 ++ .inclusionList signed :: es2)
    (hfirst : ∀ sg, TraceEvent.inclusionList sg ∈ es1 → sg.message ≠ signed.message) :
    ∃ (mid : Store map) (arr1 : List (SignedInclusionList × UInt64)) (t : UInt64),
      NodeTrace s0 es1 arr1 mid ∧
      (timeIntoSlotMs (StoreTransition := ForkChoiceStoreRun (Store map)) mid).run mid
        = .ok (t, mid) ∧
      Arrivals.firstTimely arrivals signed.message
        = some (decide (t < ilDueMs)) := by
  obtain ⟨mid, arr1, arr2, h1, h2, rfl⟩ := h.split hes
  obtain ⟨m1, a1, a2, h21, -, rfl⟩ := h2.split (es1 := [.inclusionList signed]) (es2 := es2) rfl
  obtain ⟨t, rfl, hclock⟩ := h21.single_inclusionList
  refine ⟨mid, arr1, t, h1, hclock, ?_⟩
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
the store time to `w` in whole seconds. Any other event runs on a store whose time is `w`
in whole seconds. -/
def ClockAt : TraceEvent → Nat → Store map → Prop
  | .handler (.tick time), w, _ => time.toNat = w / 1000
  | _, w, st => st.time.toNat = w / 1000

/-- A node trace on the wall clock. Each event carries its wall time. The wall times do not
decrease, and each event meets `ClockAt` on the store it runs on. So the node ticks to its
wall clock before it handles a message. The condition names the store before an event
through any trace of the events before it, and `NodeTrace.split` gives such a trace. -/
structure ClockedTrace (s0 : Store map) (tevs : List (TraceEvent × Nat))
    (arrivals : List (SignedInclusionList × UInt64)) (s : Store map) : Prop where
  /-- The handler runs, without the wall times. -/
  trace : NodeTrace s0 (tevs.map Prod.fst) arrivals s
  /-- The wall times do not decrease. -/
  mono : tevs.Pairwise (fun a b => a.2 ≤ b.2)
  /-- Each event meets the clock condition on the store it runs on. -/
  clock : ∀ (pre : List (TraceEvent × Nat)) (x : TraceEvent × Nat) post,
    tevs = pre ++ x :: post →
    ∀ (arr : List (SignedInclusionList × UInt64)) (mid : Store map),
      NodeTrace s0 (pre.map Prod.fst) arr mid → ClockAt x.1 x.2 mid

end Clocked

end EthCLSpecs.Proofs.Heze
