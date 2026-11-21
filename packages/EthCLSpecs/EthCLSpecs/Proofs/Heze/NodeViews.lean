import EthCLSpecs.Proofs.Heze.ClockedTrace

/-!
# `EthCLSpecs.Proofs.Heze.NodeViews`: every honest node records `false`

Take a block at root `r` in slot `n`, and an honest inclusion list `il` for slot `n - 1`
that carries the transaction `tx`. Take an honest node that runs the envelope handler for
`r` on a payload that omits `tx`, with no valid omission. `honestNode_records_false`
proves that the node records `false` at `r`. A node that never runs that handler lacks
the envelope. `honestNodes_record_false` states the result for every honest node of a
network.

The result holds per envelope event. A second envelope for `r` that omits `tx` records
`false` too. When every envelope for `r` at the node omits `tx`, the answer at `r` never
holds `true` (`honestNode_answer_ne_true`).

## The argument

1. The envelope handler needs a state at `r`. Only `onBlock` adds one
   (`NodeTrace.blockStates_origin`), and that `onBlock` passed its clock check on the block
   of slot `n`. So the envelope event comes at or after the start of slot `n`
   (`ClockedTrace.slotStart_le`).
2. The honest list goes out at `tSend`, and the node receives it by `tSend + Δ`. That is
   before the IL due time of slot `n - 1`, so before slot `n`. So an event that carries
   `il` comes before the envelope. The first such event comes no earlier than `tSend`, in
   slot `n - 1`, the slot of `il`. So it is timely (`ClockedTrace.firstTimely_honest`).
3. Gossip identity excludes a second list from the validator of `il` at its key. So the
   validator does not equivocate. `mem_getInclusionListTransactions_iff_collected`
   (`ILStoreOrder.lean`) puts `tx` in the collected transactions at the key of `il`.
4. `onExecutionPayloadEnvelope_run_answer` reads the answer that the handler recorded, at
   the key `(n - 1, dependent_root)` that the dependent-root walk names.
   `LawfulInclusionList` makes it `false`.

## The hypotheses

- `ClockedTrace`: the node ticks to its wall clock before each message.
- `RootFacts`: every store along the trace of the node agrees that the block at `r` has
  slot `n`, and that the dependent-root walk from `r` for the epoch of `n - 1` returns
  `dr`. The key of `il` is `(n - 1, dr)`.
- `HonestList`: causality, synchrony, and gossip identity for `il`.
- Timing: `il` goes out in slot `n - 1`, and `tSend + Δ` is before the IL due time of that
  slot. The deadline `getInclusionListDueMs` does not raise, and it is at most the slot
  length.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_get_bind_eq_ok pureState)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Heze (Preset Config Store State BeaconState BeaconBlock Root Slot InclusionList
  SignedInclusionList SignedExecutionPayloadEnvelope ExecutionPayload ExecutionRequests
  Transaction ValidatorIndex onExecutionPayloadEnvelope getInclusionListTransactions
  getShufflingDependentRoot computeEpochAtSlot isInclusionListSatisfied
  recordPayloadInclusionListSatisfaction)

section Envelope
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

/-- A successful envelope run recorded the EL answer on the transactions it collected. The
run read a state at the root of the envelope, and the block at that root, of a nonzero slot.
The dependent-root walk for the epoch of the slot before returned `dependentRoot`. The answer
map of `post` holds `isInclusionListSatisfied` on the payload and the timely transactions of
`pre` at `(block.slot - 1, dependentRoot)`. -/
theorem onExecutionPayloadEnvelope_run_answer (signedEnv : SignedExecutionPayloadEnvelope)
    (pre post : Store map)
    (h : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post)) :
    ∃ (block : BeaconBlock) (dependentRoot : Root) (x y : Store map),
      (FcMap.lookup pre.blockStates signedEnv.message.beaconBlockRoot).isSome ∧
      FcMap.lookup pre.blocks signedEnv.message.beaconBlockRoot = some block ∧
      block.slot ≠ 0 ∧
      (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
          pre signedEnv.message.beaconBlockRoot (computeEpochAtSlot (block.slot - 1))).run x
        = .ok (dependentRoot, y) ∧
      FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
        = some (isInclusionListSatisfied signedEnv.message.payload
            (getInclusionListTransactions pre.inclusionListStore (block.slot - 1) dependentRoot
              (onlyTimely := true))) := by
  unfold onExecutionPayloadEnvelope at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨st, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlookup, rfl⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  -- The availability check.
  obtain ⟨_, s2, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases h
  · -- The record step, then the final `set`.
    obtain ⟨store', s3, hrec, hset⟩ := run_bind_eq_ok _ _ _ _ h
    rw [recordPayloadInclusionListSatisfaction_run] at hrec
    split at hrec
    · cases hrec
    · rename_i block hblock
      split at hrec
      · cases hrec
      · rename_i hslot
        split at hrec
        · cases hrec
        · rename_i dependentRoot runner hwalk
          injection hrec with hrec
          injection hrec with hstore _
          have hpost := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
          refine ⟨block, dependentRoot, s2, runner, by rw [hlookup]; rfl, hblock, hslot,
            hwalk, ?_⟩
          rw [hpost, ← hstore]
          exact LawfulFcMap.lookup_insert_self _ _ _

/-- A successful envelope run recorded an EL answer at the envelope root. The form for a
caller that needs only that the answer is there. -/
theorem onExecutionPayloadEnvelope_run_recorded (signedEnv : SignedExecutionPayloadEnvelope)
    (pre post : Store map)
    (h : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post)) :
    ∃ ilTxs : Array Transaction,
      FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
        = some (isInclusionListSatisfied signedEnv.message.payload ilTxs) := by
  obtain ⟨_, _, _, _, -, -, -, -, hans⟩ := onExecutionPayloadEnvelope_run_answer signedEnv pre post h
  exact ⟨_, hans⟩

end Envelope

section Views
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

open EthCLSpecs.Heze.Const (slotDurationMs)
open Arrivals

/-- The event carries the inclusion list `il`. -/
def TraceEvent.Carries (il : InclusionList) : TraceEvent → Bool
  | .inclusionList signed => signed.message == il
  | _ => false

/-- The facts about the block at `r` in slot `n` that every store along the trace `tevs`
agrees on. The seed holds no state at `r`. A block at `r` has slot `n`. The dependent-root
walk from `r` for the epoch of `n - 1` returns `dr`. Each fact covers the store after each
prefix of `tevs`. -/
structure RootFacts (s0 : Store map) (tevs : List (TraceEvent × Nat)) (r : Root) (n : Slot)
    (dr : Root) : Prop where
  /-- The seed holds no state at `r`. -/
  anchor : FcMap.lookup s0.blockStates r = none
  /-- A block at `r` has slot `n`. -/
  block : ∀ (pre rest : List (TraceEvent × Nat)) (arr : List (SignedInclusionList × Bool))
    (m : Store map) (b : BeaconBlock), tevs = pre ++ rest →
    NodeTrace s0 (pre.map Prod.fst) arr m → FcMap.lookup m.blocks r = some b → b.slot = n
  /-- The dependent-root walk from `r` for the epoch of `n - 1` returns `dr`. -/
  dependent : ∀ (pre rest : List (TraceEvent × Nat)) (arr : List (SignedInclusionList × Bool))
    (m x y : Store map) (d : Root), tevs = pre ++ rest →
    NodeTrace s0 (pre.map Prod.fst) arr m →
    (getShufflingDependentRoot (StoreTransition := ForkChoiceStoreRun (Store map))
      m r (computeEpochAtSlot (n - 1))).run x = .ok (d, y) → d = dr

/-- The honest list `il` at one node, sent at the wall time `tSend`:

- causality: every event that carries `il` comes at or after `tSend`.
- synchrony: an event that carries `il` comes before every event later than `tSend + Δ`.
- gossip identity: every list from the validator of `il` at the key of `il` is `il`. -/
structure HonestList (tevs : List (TraceEvent × Nat)) (il : InclusionList) (tSend Δ : Nat) :
    Prop where
  /-- Every event that carries `il` comes at or after `tSend`. -/
  causal : ∀ x ∈ tevs, x.1.Carries il → tSend ≤ x.2
  /-- An event that carries `il` comes before every event later than `tSend + Δ`. -/
  synchrony : ∀ pre x post, tevs = pre ++ x :: post → tSend + Δ < x.2 →
    ∃ y ∈ pre, y.1.Carries il
  /-- Every list from the validator of `il` at the key of `il` is `il`. -/
  gossip : ∀ (signed : SignedInclusionList) (w : Nat), (.inclusionList signed, w) ∈ tevs →
    signed.message.validatorIndex = il.validatorIndex →
    ilKey signed.message = ilKey il →
    signed.message = il

omit [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- In a list with wall times that do not decrease, an earlier event has a wall time no
later than a later event. -/
theorem wall_le_of_split {tevs : List (TraceEvent × Nat)}
    (h : tevs.Pairwise (fun a b => a.2 ≤ b.2)) {p1 p2 p3 : List (TraceEvent × Nat)}
    {a b : TraceEvent × Nat} (hs : tevs = p1 ++ a :: (p2 ++ b :: p3)) : a.2 ≤ b.2 := by
  subst hs
  rw [List.pairwise_append] at h
  exact (List.pairwise_cons.mp h.2.1).1 b (by simp)

variable [LawfulFcMap map Root]

/-- An event after a store with a state at `r` comes at or after the start of slot `n`.
The state at `r` comes from an `onBlock` event (`NodeTrace.blockStates_origin`) on a new
block at `r`, of slot `n`. That event passed the clock check on the wall clock. -/
theorem ClockedTrace.slotStart_le {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrivals s)
    {r : Root} {n : Slot} {dr : Root}
    (hroot : RootFacts s0 tevs r n dr) (hD : 0 < slotDurationMs.toNat)
    {pre post : List (TraceEvent × Nat)} {x : TraceEvent × Nat}
    (hsplit : tevs = pre ++ x :: post) {arr : List (SignedInclusionList × Bool)}
    {mid : Store map} (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid)
    (hst : (FcMap.lookup mid.blockStates r).isSome) :
    slotStartMs s0.genesisTimeMs n.toNat ≤ x.2 := by
  obtain ⟨es1, es2, sb, arr1, midB, midB', heq, hB, hnew, hblk, hroot'⟩ :=
    hmid.blockStates_origin r hroot.anchor hst
  -- Find the block event, with its wall time, inside `pre`.
  obtain ⟨p1, p2, rfl, hp1, hp2⟩ := List.map_eq_append_iff.mp heq
  obtain ⟨xb, p3, rfl, hxb, -⟩ := List.map_eq_cons_iff.mp hp2
  subst hp1
  have htime : midB.timeMs.toNat = xb.2 := by
    have := hct.clock p1 xb (p3 ++ x :: post) (by simp [hsplit]) arr1 midB hB
    rw [hxb] at this
    exact this
  -- The block at `r` has slot `n`, and it passed the clock check.
  obtain ⟨cs, s', s'', hcs, hge⟩ := onBlock_run_ok_currentSlot sb midB midB' hnew hblk
  have hslot : sb.message.slot = n := by
    obtain ⟨hblocks, -⟩ := onBlock_run_maps sb midB midB' hnew hblk
    -- The store after the block event is the store after the prefix `p1 ++ [xb]`.
    refine hroot.block (p1 ++ [xb]) (p3 ++ x :: post) arr1 midB' sb.message
      (by simp [hsplit]) ?_ ?_
    · rw [List.map_append, List.map_singleton, hxb]
      exact NodeTrace.handler (.block sb) hB hblk
    · rw [hblocks, ← hroot']
      exact LawfulFcMap.lookup_insert_self _ _ _
  have hle := slotStartMs_le_of_getCurrentSlot midB s' s'' cs xb.2 n.toNat hcs htime hD
    (UInt64.le_iff_toNat_le.mp (hslot ▸ hge))
  rw [hB.genesisTime] at hle
  exact Nat.le_trans hle
    (wall_le_of_split hct.mono (p1 := p1) (p2 := p3) (p3 := post) (by simp [hsplit]))

omit [LawfulFcMap map Root] in
/-- The first arrival of the honest list is timely. Take an event later than `tSend + Δ`.
Synchrony puts an event that carries `il` before it. The first such event comes at or
after `tSend` (causality) and at or before `tSend + Δ` (synchrony again). That window lies
inside the timely window of the slot of `il`, so the run of that event judged the list
timely (`inclusionListTimely_of_window`). -/
theorem ClockedTrace.firstTimely_honest {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrivals s)
    {il : InclusionList} {tSend Δ : Nat} {due : UInt64} (hil : HonestList tevs il tSend Δ)
    (hdueOk : EthCLSpecs.Heze.getInclusionListDueMs = .ok due)
    (hdue : due.toNat ≤ slotDurationMs.toNat)
    (hlo : slotStartMs s0.genesisTimeMs il.slot.toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTimeMs il.slot.toNat + due.toNat)
    {pre post : List (TraceEvent × Nat)} {x : TraceEvent × Nat}
    (hsplit : tevs = pre ++ x :: post) (hlate : tSend + Δ < x.2)
    {arr : List (SignedInclusionList × Bool)} {mid : Store map}
    (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid) :
    Arrivals.firstTimely arr il = some true := by
  obtain ⟨y, hy, hyc⟩ := hil.synchrony pre x post hsplit hlate
  -- The first event of `pre` that carries `il`.
  obtain ⟨x1, hx1⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨y, hy, hyc⟩ : (pre.find? (fun z => z.1.Carries il)).isSome)
  obtain ⟨hc1, bef, aft, rfl, hbef⟩ := List.find?_eq_some_iff_append.mp hx1
  obtain ⟨e1, w1⟩ := x1
  cases e1 with
  | handler e => simp [TraceEvent.Carries] at hc1
  | inclusionList sg1 =>
    have hsg1 : sg1.message = il := by simpa [TraceEvent.Carries] using hc1
    have hsplit1 : tevs = bef ++ (TraceEvent.inclusionList sg1, w1) :: (aft ++ x :: post) := by
      simp [hsplit]
    -- The first arrival lies between `tSend` and `tSend + Δ`.
    have hw1lo : tSend ≤ w1 := hil.causal _ (by simp [hsplit1]) hc1
    have hw1hi : w1 ≤ tSend + Δ := by
      refine Nat.le_of_not_lt fun hgt => ?_
      obtain ⟨z, hz, hzc⟩ := hil.synchrony _ _ _ hsplit1 hgt
      simpa [hzc] using hbef z hz
    -- Its first timeliness is the timeliness bit of its own run.
    obtain ⟨midI, arrI, b, hI, hb, hft⟩ := hmid.firstTimely_of_first
      (es1 := bef.map Prod.fst) (es2 := aft.map Prod.fst) (signed := sg1) (by simp) (by
        intro sg hsg hmsg
        obtain ⟨z, hz, hz1⟩ := List.mem_map.mp hsg
        have := hbef z hz
        simp [hz1, TraceEvent.Carries, hmsg, hsg1] at this)
    have htime : midI.timeMs.toNat = w1 :=
      hct.clock bef _ _ hsplit1 arrI midI hI
    rw [← hI.genesisTime] at hlo hhi
    have htimely := inclusionListTimely_of_window midI il.slot due w1 hdueOk htime hdue
      (Nat.le_trans hlo hw1lo) (Nat.lt_of_le_of_lt hw1hi hhi)
    rw [hsg1] at hb hft
    rw [hft, hb.mpr htimely]

omit [LawfulFcMap map Root] in
/-- An arrival in the trace before an event comes from an inclusion-list event of the whole
trace. -/
theorem ClockedTrace.arrival_mem {s0 : Store map} {tevs : List (TraceEvent × Nat)}
    {pre post : List (TraceEvent × Nat)}
    {x : TraceEvent × Nat} (hsplit : tevs = pre ++ x :: post)
    {arr : List (SignedInclusionList × Bool)} {mid : Store map}
    (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid) {a : SignedInclusionList × Bool}
    (ha : a ∈ arr) : ∃ w, (TraceEvent.inclusionList a.1, w) ∈ tevs := by
  obtain ⟨z, hz, hz1⟩ := List.mem_map.mp (hmid.mem_arrivals ha)
  refine ⟨z.2, ?_⟩
  rw [hsplit, ← hz1]
  exact List.mem_append_left _ hz

variable [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex]

/-- The main result at one honest node. Take an envelope event for `r` on a payload that
omits the transaction `tx` of the honest list `il`, with no valid omission. The envelope
handler runs on the store `mid` and returns `mid'`. Then `mid'` holds `false` at `r`.

The hypotheses:

- The node trace is on the wall clock (`ClockedTrace`), from a seed with the empty IL
  store.
- `RootFacts`: the block at `r` has slot `n`, and the dependent-root walk from `r` returns
  `dr`.
- `hkey`: the key of `il` is `(n - 1, dr)`.
- `HonestList`: causality, synchrony, and gossip identity for `il`.
- Timing: `il` goes out at `tSend`, within slot `n - 1`, and `tSend + Δ` is before the IL
  due time of that slot.
- The slot length is positive. The deadline `getInclusionListDueMs` is `due`, at most the
  slot length.
- The EL follows `LawfulInclusionList`. -/
theorem honestNode_records_false
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrivals s)
    (hseed : s0.inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {r : Root} {n : Slot} {dr : Root} (hroot : RootFacts s0 tevs r n dr)
    {il : InclusionList} {tSend Δ : Nat} {due : UInt64} (hil : HonestList tevs il tSend Δ)
    (hkey : ilKey il = (n - 1, dr))
    (hlo : slotStartMs s0.genesisTimeMs (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTimeMs (n - 1).toNat + due.toNat)
    (hDpos : 0 < slotDurationMs.toNat)
    (hdueOk : EthCLSpecs.Heze.getInclusionListDueMs = .ok due)
    (hdue : due.toNat ≤ slotDurationMs.toNat)
    {pre post : List (TraceEvent × Nat)} {signedEnv : SignedExecutionPayloadEnvelope}
    {w : Nat} (hsplit : tevs = pre ++ (.handler (.envelope signedEnv), w) :: post)
    (henv : signedEnv.message.beaconBlockRoot = r)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ txs signedEnv.message.payload)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx)
    {arr : List (SignedInclusionList × Bool)} {mid mid' : Store map}
    (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid)
    (hrun : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run mid = .ok ((), mid')) :
    FcMap.lookup mid'.payloadInclusionListSatisfaction r = some false := by
  obtain ⟨b, d, x, y, hst, hblk, hslot0, hwalk, hans⟩ :=
    onExecutionPayloadEnvelope_run_answer signedEnv mid mid' hrun
  rw [henv] at hst hblk hwalk hans
  have hbslot := hroot.block pre _ arr mid b hsplit hmid hblk
  rw [hbslot] at hslot0 hwalk hans
  have hd := hroot.dependent pre _ arr mid x y d hsplit hmid hwalk
  rw [hd] at hans
  -- The key of `il`: its slot is `n - 1`.
  have hilSlot : il.slot = n - 1 := congrArg Prod.fst hkey
  -- The envelope comes after the start of slot `n`, so after `tSend + Δ`.
  have hwN := hct.slotStart_le hroot hDpos hsplit hmid hst
  have hn1 : n.toNat = (n - 1).toNat + 1 := by
    have h1 : (1 : UInt64) ≤ n := by
      rw [UInt64.le_iff_toNat_le]
      have : n.toNat ≠ 0 := fun h => hslot0 (UInt64.toNat_inj.mp (by simpa using h))
      simp
      omega
    rw [UInt64.toNat_sub_of_le _ _ h1]
    have : 1 ≤ n.toNat := UInt64.le_iff_toNat_le.mp h1
    simp
    omega
  have hlate : tSend + Δ < w := by
    unfold slotStartMs at hwN hhi
    rw [hn1, Nat.succ_mul] at hwN
    generalize (n - 1).toNat * slotDurationMs.toNat = p at hwN hhi
    simp only at hwN
    omega
  -- The first arrival of `il` is timely.
  have hft := hct.firstTimely_honest hil hdueOk hdue (hilSlot ▸ hlo) (hilSlot ▸ hhi) hsplit
    hlate hmid
  -- The collected transactions contain `tx`.
  have hsame : ∀ l, Arrived arr l → l.validatorIndex = il.validatorIndex →
      ilKey l = ilKey il → l = il := by
    rintro l ⟨a, ha, rfl⟩ hv hk
    obtain ⟨wa, hwa⟩ := ClockedTrace.arrival_mem hsplit hmid ha
    exact hil.gossip _ _ hwa hv hk
  have hcol : Collected arr (n - 1, dr) tx := by
    refine ⟨il, (arrived_iff_isSome arr il).mpr (by rw [hft]; rfl), hkey, ?_, hft, htx⟩
    rintro ⟨l₁, l₂, h₁, h₂, ⟨hk₁, hv₁⟩, ⟨hk₂, hv₂⟩, hne⟩
    exact hne ((hsame l₁ h₁ hv₁ (hk₁.trans hkey.symm)).trans
      (hsame l₂ h₂ hv₂ (hk₂.trans hkey.symm)).symm)
  have htxIn := (mem_getInclusionListTransactions_iff_collected (map := map) arr (n - 1) dr
    tx).mpr hcol
  rw [← hmid.ilStore hseed] at htxIn
  -- The EL answer is `false`.
  cases hb : isInclusionListSatisfied signedEnv.message.payload
      (getInclusionListTransactions mid.inclusionListStore (n - 1) dr (onlyTimely := true))
  · rw [hans, hb]
  · exfalso
    rcases (hel.satisfied_iff signedEnv.message.payload _).mp hb tx htxIn with h | h
    · exact hmissing h
    · exact hinvalid h

omit [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex] in
/-- A handler event other than an envelope for `r` keeps the lookups at `r` of `payloads`
and of the answer map. -/
theorem HandlerEvent.run_keeps_payloadAnswer (r : Root) (e : HandlerEvent)
    (henv : e.NotEnvelopeAt r) {pre post : Store map}
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) :
    (FcMap.lookup post.payloads r, FcMap.lookup post.payloadInclusionListSatisfaction r)
      = (FcMap.lookup pre.payloads r, FcMap.lookup pre.payloadInclusionListSatisfaction r) := by
  cases e with
  | tick time =>
    exact congrArg Prod.snd (onTick_keeps_rootView r (rootView r pre) time pre () post rfl h)
  | block sb => exact onBlock_keeps_payloadAnswer r _ sb pre () post rfl h
  | attestation att isFromBlock =>
    exact congrArg Prod.snd
      (onAttestation_keeps_rootView r (rootView r pre) att isFromBlock pre () post rfl h)
  | attesterSlashing asl =>
    exact congrArg Prod.snd
      (onAttesterSlashing_keeps_rootView r (rootView r pre) asl pre () post rfl h)
  | payloadAttestation msg isFromBlock =>
    exact congrArg Prod.snd
      (onPayloadAttestationMessage_keeps_rootView r (rootView r pre) msg isFromBlock pre ()
        post rfl h)
  | envelope signedEnv =>
    have hp := onExecutionPayloadEnvelope_keeps_payload r _ signedEnv henv pre () post rfl h
    have ha := onExecutionPayloadEnvelope_keeps_answer r _ signedEnv henv pre () post rfl h
    simp only at hp ha
    rw [hp, ha]

omit [LawfulFcMap map (Slot × Root)] [LawfulFcMap map ValidatorIndex] in
/-- A handler event other than an envelope for `r` keeps the answer at `r`. -/
theorem HandlerEvent.run_keeps_answer (r : Root) (e : HandlerEvent) (henv : e.NotEnvelopeAt r)
    {pre post : Store map} (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) :
    FcMap.lookup post.payloadInclusionListSatisfaction r
      = FcMap.lookup pre.payloadInclusionListSatisfaction r :=
  congrArg Prod.snd (HandlerEvent.run_keeps_payloadAnswer r e henv h)

/-- The answer at `r` never holds `true` at the honest node, when every envelope for `r`
that the node handles omits `tx` with no valid omission. The seed holds no answer at `r`.
Every envelope event for `r` records `false` (`honestNode_records_false`), and every other
event keeps the answer at `r`. The statement covers the store after every prefix of the
trace. -/
theorem honestNode_answer_ne_true
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × Bool)} (hct : ClockedTrace s0 tevs arrivals s)
    (hseed : s0.inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {r : Root} {n : Slot} {dr : Root} (hroot : RootFacts s0 tevs r n dr)
    (hanswer0 : FcMap.lookup s0.payloadInclusionListSatisfaction r = none)
    {il : InclusionList} {tSend Δ : Nat} {due : UInt64} (hil : HonestList tevs il tSend Δ)
    (hkey : ilKey il = (n - 1, dr))
    (hlo : slotStartMs s0.genesisTimeMs (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTimeMs (n - 1).toNat + due.toNat)
    (hDpos : 0 < slotDurationMs.toNat)
    (hdueOk : EthCLSpecs.Heze.getInclusionListDueMs = .ok due)
    (hdue : due.toNat ≤ slotDurationMs.toNat)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (homits : ∀ (signedEnv : SignedExecutionPayloadEnvelope) (w : Nat),
      (.handler (.envelope signedEnv), w) ∈ tevs → signedEnv.message.beaconBlockRoot = r →
      tx ∉ txs signedEnv.message.payload ∧ ¬ isValidOmission signedEnv.message.payload tx)
    (pre rest : List (TraceEvent × Nat)) (hsplit : tevs = pre ++ rest)
    {arr : List (SignedInclusionList × Bool)} {m : Store map}
    (hm : NodeTrace s0 (pre.map Prod.fst) arr m) :
    FcMap.lookup m.payloadInclusionListSatisfaction r ≠ some true := by
  generalize hes : pre.map Prod.fst = es at hm
  induction hm generalizing pre rest with
  | nil =>
    rw [hanswer0]
    simp
  | @handler events arrs prev post e htrace hrun ih =>
    -- The last element of `pre` is the event `e`, with its wall time.
    obtain ⟨pre', last, rfl, hpre', hlast⟩ := List.map_eq_append_iff.mp hes
    obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hlast
    have hsplit' : tevs = pre' ++ x :: rest := by simp [hsplit]
    have hprev := ih pre' (x :: rest) (by simp [hsplit']) hpre'
    by_cases hr : ∃ signedEnv, e = .envelope signedEnv ∧ signedEnv.message.beaconBlockRoot = r
    · obtain ⟨signedEnv, rfl, hroot'⟩ := hr
      obtain ⟨x1, x2⟩ := x
      simp only at hx
      subst hx
      obtain ⟨hmiss, hinv⟩ := homits signedEnv x2 (by simp [hsplit']) hroot'
      rw [honestNode_records_false hel hct hseed hroot hil hkey hlo hhi hDpos hdueOk hdue
        hsplit' hroot' htx hmiss hinv (hpre' ▸ htrace) hrun]
      simp
    · have hnot : e.NotEnvelopeAt r := by
        cases e with
        | envelope signedEnv => exact fun h => hr ⟨signedEnv, rfl, h⟩
        | _ => trivial
      rw [HandlerEvent.run_keeps_answer r e hnot hrun]
      exact hprev
  | @inclusionList events arrs prev post signed b htrace hrun hb ih =>
    obtain ⟨pre', last, rfl, hpre', hlast⟩ := List.map_eq_append_iff.mp hes
    obtain ⟨x, rfl, -⟩ := List.map_eq_singleton_iff.mp hlast
    have hprev := ih pre' (x :: rest) (by simp [hsplit]) hpre'
    -- `onInclusionList` writes only the IL store.
    obtain ⟨_, hs', -⟩ := onInclusionList_run_ok _ _ signed hrun
    rw [hs']
    exact hprev

/-- The network form of `honestNode_records_false`. Each node `v` has a clocked trace
`tevs v` from the seed `s0 v`. The honest nodes share the genesis time `g`. At every honest
node, the seed has the empty IL store, and `RootFacts` and `HonestList` hold. Then every
envelope event for `r` at an honest node, on a payload that omits `tx` with no valid
omission, records `false`. The theorem assumes nothing about the other nodes. -/
theorem honestNodes_record_false {Node : Type} (honest : Node → Prop)
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    (s0 s : Node → Store map) (tevs : Node → List (TraceEvent × Nat))
    (arrivals : Node → List (SignedInclusionList × Bool))
    (hct : ∀ v, honest v → ClockedTrace (s0 v) (tevs v) (arrivals v) (s v))
    (hseed : ∀ v, honest v → (s0 v).inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {g : UInt64} (hgenesis : ∀ v, honest v → (s0 v).genesisTimeMs = g)
    {r : Root} {n : Slot} {dr : Root}
    (hroot : ∀ v, honest v → RootFacts (s0 v) (tevs v) r n dr)
    {il : InclusionList} {tSend Δ : Nat} {due : UInt64}
    (hil : ∀ v, honest v → HonestList (tevs v) il tSend Δ)
    (hkey : ilKey il = (n - 1, dr))
    (hlo : slotStartMs g (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs g (n - 1).toNat + due.toNat)
    (hDpos : 0 < slotDurationMs.toNat)
    (hdueOk : EthCLSpecs.Heze.getInclusionListDueMs = .ok due)
    (hdue : due.toNat ≤ slotDurationMs.toNat)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray) :
    ∀ v, honest v →
      ∀ (pre post : List (TraceEvent × Nat)) (signedEnv : SignedExecutionPayloadEnvelope)
        (w : Nat), tevs v = pre ++ (.handler (.envelope signedEnv), w) :: post →
      signedEnv.message.beaconBlockRoot = r →
      tx ∉ txs signedEnv.message.payload →
      ¬ isValidOmission signedEnv.message.payload tx →
      ∀ (arr : List (SignedInclusionList × Bool)) (mid mid' : Store map),
        NodeTrace (s0 v) (pre.map Prod.fst) arr mid →
        (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run mid
          = .ok ((), mid') →
        FcMap.lookup mid'.payloadInclusionListSatisfaction r = some false := by
  intro v hv pre post signedEnv w hsplit henv hmissing hinvalid arr mid mid' hmid hrun
  have hg := hgenesis v hv
  exact honestNode_records_false hel (hct v hv) (hseed v hv) (hroot v hv) (hil v hv) hkey
    (hg ▸ hlo) (hg ▸ hhi) hDpos hdueOk hdue hsplit henv htx hmissing hinvalid hmid hrun

end Views

section Presets
open EthCLSpecs.Heze.Const (slotDurationMs)

/-- Both presets meet the slot-length hypotheses: the slot length is positive, and the
deadline does not raise and is at most the slot length. Minimal: 6000 ms. -/
example :
    letI : Preset := EthCLSpecs.Heze.minimal
    letI : Config := EthCLSpecs.Heze.minimalConfig
    0 < slotDurationMs.toNat ∧
      (match EthCLSpecs.Heze.getInclusionListDueMs with
        | .ok d => decide (d.toNat ≤ slotDurationMs.toNat)
        | .error _ => false) = true := by
  decide

/-- Mainnet: 12000 ms. -/
example :
    letI : Preset := EthCLSpecs.Heze.mainnet
    letI : Config := EthCLSpecs.Heze.mainnetConfig
    0 < slotDurationMs.toNat ∧
      (match EthCLSpecs.Heze.getInclusionListDueMs with
        | .ok d => decide (d.toNat ≤ slotDurationMs.toNat)
        | .error _ => false) = true := by
  decide

end Presets

end EthCLSpecs.Proofs.Heze
