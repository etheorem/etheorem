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
   `il` comes before the envelope. The first such event comes no earlier than `tSend`, so
   it is timely (`ClockedTrace.firstTimely_honest`).
3. Gossip identity excludes a second list from the validator of `il` at its key. So the
   validator does not equivocate. `getInclusionListTransactions_mem_iff_collected`
   (`ILStoreOrder.lean`) puts `tx` in the collected transactions.
4. `onExecutionPayloadEnvelope_run_answer` reads the answer that the handler recorded.
   `LawfulInclusionList` makes it `false`.

## The hypotheses

- `ClockedTrace`: the node ticks to its wall clock before each message.
- `RootFacts`: every store along the trace of the node agrees that the block at `r` has
  slot `n`, and that a state at `r` gives the committee `committee`. The key of `il` is the root of
  `committee`.
- `HonestList`: causality, synchrony, gossip identity, and no root collision among the
  lists that the node receives.
- Timing: `il` goes out in slot `n - 1`, and `tSend + Δ` is before the IL due time of that
  slot. The slot length is a whole number of seconds, and the IL due time is at most the
  slot length.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_get_bind_eq_ok pureState)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap LawfulInclusionList)
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Slot InclusionList
  SignedInclusionList SignedExecutionPayloadEnvelope ExecutionPayload ExecutionRequests
  Transaction ValidatorIndex onExecutionPayloadEnvelope getInclusionListTransactions
  getInclusionListCommittee isInclusionListSatisfied recordPayloadInclusionListSatisfaction)

section Envelope
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [ExecutionEngine ExecutionPayload Transaction ExecutionRequests]
  [DataAvailability]

/-- A successful envelope run recorded the EL answer on the transactions it collected. The
run read the state at the root of the envelope, which is the uncached box of `state` under
`BlockStatesPure`. The slot of `state` is not zero. The collection from the IL store of
`pre` at the slot before returned `ilTxs`. The answer map of `post` holds
`isInclusionListSatisfied` on the payload and `ilTxs` at the root. -/
theorem onExecutionPayloadEnvelope_run_answer (signedEnv : SignedExecutionPayloadEnvelope)
    (pre post : Store map) (hp : BlockStatesPure pre)
    (h : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre = .ok ((), post)) :
    ∃ (state : BeaconState) (ilTxs : Array Transaction) (x y : Store map),
      FcMap.lookup pre.blockStates signedEnv.message.beaconBlockRoot
        = some (pureState state) ∧
      state.slot ≠ 0 ∧
      (getInclusionListTransactions (StoreTransition := ForkChoiceStoreRun (Store map))
          pre.inclusionListStore (pureState state) (state.slot - 1) (onlyTimely := true)).run x
        = .ok (ilTxs, y) ∧
      FcMap.lookup post.payloadInclusionListSatisfaction signedEnv.message.beaconBlockRoot
        = some (isInclusionListSatisfied signedEnv.message.payload ilTxs) := by
  unfold onExecutionPayloadEnvelope at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨st, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨hlookup, rfl⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  obtain ⟨state, hstate⟩ := hp.lookup _ (by rw [hlookup]; rfl)
  rw [hstate] at hlookup
  injection hlookup with hlookup
  subst hlookup
  -- The availability check.
  obtain ⟨_, s2, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases h
  · -- The record step, then the final `set`.
    obtain ⟨store', s3, hrec, hset⟩ := run_bind_eq_ok _ _ _ _ h
    rw [recordPayloadInclusionListSatisfaction_run] at hrec
    split at hrec
    · cases hrec
    · rename_i hslot
      split at hrec
      · cases hrec
      · rename_i ilTxs runner hget
        injection hrec with hrec
        injection hrec with hstore _
        have hpost := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
        refine ⟨state, ilTxs, s2, runner, hstate, hslot, hget, ?_⟩
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
  unfold onExecutionPayloadEnvelope at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨_, _, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  -- The availability check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases h
  · -- The record step: the slot read, the collection, then the answer write.
    obtain ⟨store', _, hrec, hset⟩ := run_bind_eq_ok _ _ _ _ h
    unfold recordPayloadInclusionListSatisfaction at hrec
    obtain ⟨_, _, -, hrec⟩ := run_bind_eq_ok _ _ _ _ hrec
    obtain ⟨ilTxs, _, -, hrec⟩ := run_bind_eq_ok _ _ _ _ hrec
    have hstore := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hrec
    have hpost := EthCLLib.Proofs.run_set_state_eq _ _ _ _ hset
    refine ⟨ilTxs, ?_⟩
    rw [hpost, hstore]
    exact LawfulFcMap.lookup_insert_self _ _ _

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
agrees on. The seed holds no state at `r`, and every state in its `blockStates` is the
uncached box of a plain value. A block at `r` has slot `n`. A state at `r` has slot `n`,
and its committee of the slot before is `committee`. Each fact covers the store after each
prefix of `tevs`. -/
structure RootFacts (s0 : Store map) (tevs : List (TraceEvent × Nat)) (r : Root) (n : Slot)
    (committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize) :
    Prop where
  /-- The seed holds no state at `r`. -/
  anchor : FcMap.lookup s0.blockStates r = none
  /-- Every state in the `blockStates` of the seed is the uncached box of a plain value. -/
  seedPure : BlockStatesPure s0
  /-- A block at `r` has slot `n`. -/
  block : ∀ (pre rest : List (TraceEvent × Nat)) (arr : List (SignedInclusionList × UInt64))
    (m : Store map) (b : EthCLSpecs.Heze.BeaconBlock), tevs = pre ++ rest →
    NodeTrace s0 (pre.map Prod.fst) arr m → FcMap.lookup m.blocks r = some b → b.slot = n
  /-- A state at `r` has slot `n`. -/
  stateSlot : ∀ (pre rest : List (TraceEvent × Nat))
    (arr : List (SignedInclusionList × UInt64)) (m : Store map) (st : BeaconState),
    tevs = pre ++ rest → NodeTrace s0 (pre.map Prod.fst) arr m →
    FcMap.lookup m.blockStates r = some (pureState st) → st.slot = n
  /-- The committee of the slot before, read from a state at `r`, is `committee`. -/
  committee : ∀ (pre rest : List (TraceEvent × Nat))
    (arr : List (SignedInclusionList × UInt64)) (m : Store map) (st : BeaconState),
    tevs = pre ++ rest → NodeTrace s0 (pre.map Prod.fst) arr m →
    FcMap.lookup m.blockStates r = some (pureState st) → ∀ x : Store map,
    (getInclusionListCommittee (StoreTransition := ForkChoiceStoreRun (Store map))
      (pureState st) (n - 1)).run x = .ok (committee, x)

/-- The honest list `il` at one node, sent at the wall time `tSend`:

- causality: every event that carries `il` comes at or after `tSend`.
- synchrony: an event that carries `il` comes before every event later than `tSend + Δ`.
- gossip identity: every list from the validator of `il` at the key of `il` is `il`.
- no collision: two different lists of the node have different roots. -/
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
    signed.message.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot →
    signed.message = il
  /-- Two different lists of the node have different roots. -/
  noCollision : ∀ (s₁ s₂ : SignedInclusionList) (w₁ w₂ : Nat),
    (.inclusionList s₁, w₁) ∈ tevs → (.inclusionList s₂, w₂) ∈ tevs →
    htr s₁.message = htr s₂.message → s₁.message = s₂.message

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
The state at `r` comes from an `onBlock` event (`NodeTrace.blockStates_origin`) on the
block at `r`, of slot `n`. That event passed the clock check on the wall clock. -/
theorem ClockedTrace.slotStart_le {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    {r : Root} {n : Slot} {committee}
    (hroot : RootFacts s0 tevs r n committee) (hD : 0 < slotDurationMs.toNat)
    {pre post : List (TraceEvent × Nat)} {x : TraceEvent × Nat}
    (hsplit : tevs = pre ++ x :: post) {arr : List (SignedInclusionList × UInt64)}
    {mid : Store map} (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid)
    (hst : (FcMap.lookup mid.blockStates r).isSome) :
    slotStartMs s0.genesisTime n.toNat ≤ x.2 := by
  obtain ⟨es1, es2, sb, arr1, midB, midB', heq, hB, hblk, hroot'⟩ :=
    hmid.blockStates_origin r hroot.anchor hst
  -- Find the block event, with its wall time, inside `pre`.
  obtain ⟨p1, p2, rfl, hp1, hp2⟩ := List.map_eq_append_iff.mp heq
  obtain ⟨xb, p3, rfl, hxb, -⟩ := List.map_eq_cons_iff.mp hp2
  subst hp1
  have htime : midB.time.toNat = xb.2 / 1000 := by
    have := hct.clock p1 xb (p3 ++ x :: post) (by simp [hsplit]) arr1 midB hB
    rw [hxb] at this
    exact this
  -- The block at `r` has slot `n`, and it passed the clock check.
  obtain ⟨cs, s', s'', hcs, hge⟩ := onBlock_run_ok_currentSlot sb midB midB' hblk
  have hslot : sb.message.slot = n := by
    obtain ⟨hblocks, -⟩ := onBlock_run_maps sb midB midB' hblk
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
inside the timely window of slot `k`. -/
theorem ClockedTrace.firstTimely_honest {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    {il : InclusionList} {tSend Δ k : Nat} (hil : HonestList tevs il tSend Δ)
    (hlo : slotStartMs s0.genesisTime k ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTime k + ilDueMs.toNat)
    (hsec : (tSend + Δ) / 1000 ≤ maxMsSeconds)
    (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hdue : ilDueMs.toNat ≤ slotDurationMs.toNat)
    {pre post : List (TraceEvent × Nat)} {x : TraceEvent × Nat}
    (hsplit : tevs = pre ++ x :: post) (hlate : tSend + Δ < x.2)
    {arr : List (SignedInclusionList × UInt64)} {mid : Store map}
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
    -- Its first timeliness is the timeliness of its own arrival.
    obtain ⟨midI, arrI, t, hI, hclock, hft⟩ := hmid.firstTimely_of_first
      (es1 := bef.map Prod.fst) (es2 := aft.map Prod.fst) (signed := sg1) (by simp) (by
        intro sg hsg hmsg
        obtain ⟨z, hz, hz1⟩ := List.mem_map.mp hsg
        have := hbef z hz
        simp [hz1, TraceEvent.Carries, hmsg, hsg1] at this)
    have htime : midI.time.toNat = w1 / 1000 :=
      hct.clock bef _ _ hsplit1 arrI midI hI
    rw [← hI.genesisTime] at hlo hhi
    have hlt := timeIntoSlotMs_lt_of_window midI midI midI t _ w1 k hclock htime hDdiv hdue
      (Nat.le_trans hlo hw1lo) (Nat.lt_of_le_of_lt hw1hi hhi)
      (Nat.le_trans (Nat.div_le_div_right hw1hi) hsec)
    rw [← hsg1, hft]
    simp [hlt]

omit [LawfulFcMap map Root] in
/-- An arrival in the trace before an event comes from an inclusion-list event of the whole
trace. -/
theorem ClockedTrace.arrival_mem {s0 : Store map} {tevs : List (TraceEvent × Nat)}
    {pre post : List (TraceEvent × Nat)}
    {x : TraceEvent × Nat} (hsplit : tevs = pre ++ x :: post)
    {arr : List (SignedInclusionList × UInt64)} {mid : Store map}
    (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid) {a : SignedInclusionList × UInt64}
    (ha : a ∈ arr) : ∃ w, (TraceEvent.inclusionList a.1, w) ∈ tevs := by
  obtain ⟨z, hz, hz1⟩ := List.mem_map.mp (hmid.mem_arrivals ha)
  refine ⟨z.2, ?_⟩
  rw [hsplit, ← hz1]
  exact List.mem_append_left _ hz

/-- The main result at one honest node. Take an envelope event for `r` on a payload that
omits the transaction `tx` of the honest list `il`, with no valid omission. The envelope
handler runs on the store `mid` and returns `mid'`. Then `mid'` holds `false` at `r`.

The hypotheses:

- The node trace is on the wall clock (`ClockedTrace`), from a seed with the empty IL
  store.
- `RootFacts`: the block at `r` has slot `n`, and a state at `r` gives the committee
  `committee`.
- `hkey`: the root of `committee` is the key of `il`.
- `HonestList`: causality, synchrony, gossip identity, and no collision for `il`.
- Timing: `il` goes out at `tSend`, within slot `n - 1`, and `tSend + Δ` is before the IL
  due time of that slot.
- The slot length is positive and a whole number of seconds. The IL due time is at most
  the slot length.
- The EL follows `LawfulInclusionList`. -/
theorem honestNode_records_false
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop}
    (hel : LawfulInclusionList ExecutionPayload Transaction ExecutionRequests txs
      isValidOmission)
    {s0 s : Store map} {tevs : List (TraceEvent × Nat)}
    {arrivals : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    (hseed : s0.inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {r : Root} {n : Slot}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    (hroot : RootFacts s0 tevs r n committee)
    {il : InclusionList} {tSend Δ : Nat} (hil : HonestList tevs il tSend Δ)
    (hkey : il.inclusionListCommitteeRoot = htr committee)
    (hlo : slotStartMs s0.genesisTime (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTime (n - 1).toNat + ilDueMs.toNat)
    (hsec : (tSend + Δ) / 1000 ≤ maxMsSeconds)
    (hDpos : 0 < slotDurationMs.toNat) (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hdue : ilDueMs.toNat ≤ slotDurationMs.toNat)
    {pre post : List (TraceEvent × Nat)} {signedEnv : SignedExecutionPayloadEnvelope}
    {w : Nat} (hsplit : tevs = pre ++ (.handler (.envelope signedEnv), w) :: post)
    (henv : signedEnv.message.beaconBlockRoot = r)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ txs signedEnv.message.payload)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx)
    {arr : List (SignedInclusionList × UInt64)} {mid mid' : Store map}
    (hmid : NodeTrace s0 (pre.map Prod.fst) arr mid)
    (hrun : (onExecutionPayloadEnvelope (map := map)
      (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run mid = .ok ((), mid')) :
    FcMap.lookup mid'.payloadInclusionListSatisfaction r = some false := by
  obtain ⟨st, ilTxs, x, y, hst, hslot0, hget, hans⟩ :=
    onExecutionPayloadEnvelope_run_answer signedEnv mid mid'
      (hmid.blockStatesPure hroot.seedPure) hrun
  rw [henv] at hst hans
  have hstslot := hroot.stateSlot pre _ arr mid st hsplit hmid hst
  -- The envelope comes after the start of slot `n`, so after `tSend + Δ`.
  have hwN := hct.slotStart_le hroot hDpos hsplit hmid (by rw [hst]; rfl)
  have hn1 : n.toNat = (n - 1).toNat + 1 := by
    have hn0 : n ≠ 0 := hstslot ▸ hslot0
    have h1 : (1 : UInt64) ≤ n := by
      rw [UInt64.le_iff_toNat_le]
      have : n.toNat ≠ 0 := fun h => hn0 (UInt64.toNat_inj.mp (by simpa using h))
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
  have hft := hct.firstTimely_honest hil hlo hhi hsec hDdiv hdue hsplit hlate hmid
  -- The collected transactions contain `tx`.
  have hinj : HashInjective arr := by
    rintro l₁ l₂ ⟨a₁, ha₁, rfl⟩ ⟨a₂, ha₂, rfl⟩ hh
    obtain ⟨w₁, hw₁⟩ := ClockedTrace.arrival_mem hsplit hmid ha₁
    obtain ⟨w₂, hw₂⟩ := ClockedTrace.arrival_mem hsplit hmid ha₂
    exact hil.noCollision _ _ _ _ hw₁ hw₂ hh
  have hcomm := hroot.committee pre _ arr mid st hsplit hmid hst x
  obtain ⟨ilTxs', hrun', hmem⟩ := getInclusionListTransactions_mem_iff_collected (map := map)
    arr hinj st (n - 1) x committee hcomm
  rw [hmid.ilStore hseed, hstslot, hrun'] at hget
  injection hget with hget
  injection hget with hget
  subst hget
  have hsame : ∀ l, Arrived arr l → l.validatorIndex = il.validatorIndex →
      l.inclusionListCommitteeRoot = il.inclusionListCommitteeRoot → l = il := by
    rintro l ⟨a, ha, rfl⟩ hv hk
    obtain ⟨wa, hwa⟩ := ClockedTrace.arrival_mem hsplit hmid ha
    exact hil.gossip _ _ hwa hv hk
  have hcol : Collected arr (htr committee) tx := by
    refine ⟨il, (arrived_iff_isSome arr il).mpr (by rw [hft]; rfl), hkey, ?_, hft, htx⟩
    rintro ⟨l₁, l₂, h₁, h₂, ⟨hk₁, hv₁⟩, ⟨hk₂, hv₂⟩, hne⟩
    exact hne ((hsame l₁ h₁ hv₁ (hk₁.trans hkey.symm)).trans
      (hsame l₂ h₂ hv₂ (hk₂.trans hkey.symm)).symm)
  have htxIn : tx ∈ ilTxs' := (hmem tx).mpr hcol
  -- The EL answer is `false`.
  cases hb : isInclusionListSatisfied signedEnv.message.payload ilTxs'
  · rw [hans, hb]
  · exfalso
    rcases (hel.satisfied_iff signedEnv.message.payload ilTxs').mp hb tx htxIn with h | h
    · exact hmissing h
    · exact hinvalid h

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
    {arrivals : List (SignedInclusionList × UInt64)} (hct : ClockedTrace s0 tevs arrivals s)
    (hseed : s0.inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {r : Root} {n : Slot}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    (hroot : RootFacts s0 tevs r n committee)
    (hanswer0 : FcMap.lookup s0.payloadInclusionListSatisfaction r = none)
    {il : InclusionList} {tSend Δ : Nat} (hil : HonestList tevs il tSend Δ)
    (hkey : il.inclusionListCommitteeRoot = htr committee)
    (hlo : slotStartMs s0.genesisTime (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs s0.genesisTime (n - 1).toNat + ilDueMs.toNat)
    (hsec : (tSend + Δ) / 1000 ≤ maxMsSeconds)
    (hDpos : 0 < slotDurationMs.toNat) (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hdue : ilDueMs.toNat ≤ slotDurationMs.toNat)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray)
    (homits : ∀ (signedEnv : SignedExecutionPayloadEnvelope) (w : Nat),
      (.handler (.envelope signedEnv), w) ∈ tevs → signedEnv.message.beaconBlockRoot = r →
      tx ∉ txs signedEnv.message.payload ∧ ¬ isValidOmission signedEnv.message.payload tx)
    (pre rest : List (TraceEvent × Nat)) (hsplit : tevs = pre ++ rest)
    {arr : List (SignedInclusionList × UInt64)} {m : Store map}
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
      rw [honestNode_records_false hel hct hseed hroot hil hkey hlo hhi hsec hDpos hDdiv hdue
        hsplit' hroot' htx hmiss hinv (hpre' ▸ htrace) hrun]
      simp
    · have hnot : e.NotEnvelopeAt r := by
        cases e with
        | envelope signedEnv => exact fun h => hr ⟨signedEnv, rfl, h⟩
        | _ => trivial
      rw [HandlerEvent.run_keeps_answer r e hnot hrun]
      exact hprev
  | @inclusionList events arrs prev post signed t htrace hclock hrun ih =>
    obtain ⟨pre', last, rfl, hpre', hlast⟩ := List.map_eq_append_iff.mp hes
    obtain ⟨x, rfl, -⟩ := List.map_eq_singleton_iff.mp hlast
    have hprev := ih pre' (x :: rest) (by simp [hsplit]) hpre'
    rw [onInclusionList_run_eq _ signed t hclock
      (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
    injection hrun with hrun
    injection hrun with _ hrun
    subst hrun
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
    (arrivals : Node → List (SignedInclusionList × UInt64))
    (hct : ∀ v, honest v → ClockedTrace (s0 v) (tevs v) (arrivals v) (s v))
    (hseed : ∀ v, honest v → (s0 v).inclusionListStore = EthCLSpecs.Heze.InclusionListStore.empty)
    {g : UInt64} (hgenesis : ∀ v, honest v → (s0 v).genesisTime = g)
    {r : Root} {n : Slot}
    {committee : Vector ValidatorIndex EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    (hroot : ∀ v, honest v → RootFacts (s0 v) (tevs v) r n committee)
    {il : InclusionList} {tSend Δ : Nat} (hil : ∀ v, honest v → HonestList (tevs v) il tSend Δ)
    (hkey : il.inclusionListCommitteeRoot = htr committee)
    (hlo : slotStartMs g (n - 1).toNat ≤ tSend)
    (hhi : tSend + Δ < slotStartMs g (n - 1).toNat + ilDueMs.toNat)
    (hsec : (tSend + Δ) / 1000 ≤ maxMsSeconds)
    (hDpos : 0 < slotDurationMs.toNat) (hDdiv : 1000 ∣ slotDurationMs.toNat)
    (hdue : ilDueMs.toNat ≤ slotDurationMs.toNat)
    {tx : Transaction} (htx : tx ∈ il.transactions.toArray) :
    ∀ v, honest v →
      ∀ (pre post : List (TraceEvent × Nat)) (signedEnv : SignedExecutionPayloadEnvelope)
        (w : Nat), tevs v = pre ++ (.handler (.envelope signedEnv), w) :: post →
      signedEnv.message.beaconBlockRoot = r →
      tx ∉ txs signedEnv.message.payload →
      ¬ isValidOmission signedEnv.message.payload tx →
      ∀ (arr : List (SignedInclusionList × UInt64)) (mid mid' : Store map),
        NodeTrace (s0 v) (pre.map Prod.fst) arr mid →
        (onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run mid
          = .ok ((), mid') →
        FcMap.lookup mid'.payloadInclusionListSatisfaction r = some false := by
  intro v hv pre post signedEnv w hsplit henv hmissing hinvalid arr mid mid' hmid hrun
  have hg := hgenesis v hv
  exact honestNode_records_false hel (hct v hv) (hseed v hv) (hroot v hv) (hil v hv) hkey
    (hg ▸ hlo) (hg ▸ hhi) hsec hDpos hDdiv hdue hsplit henv htx hmissing hinvalid hmid hrun

end Views

section Presets
open EthCLSpecs.Heze.Const (slotDurationMs)

/-- Both presets meet the three slot-length hypotheses: the slot length is positive and a
whole number of seconds, and the IL due time is at most the slot length. Minimal: 6000 ms
and 4000 ms. -/
example :
    letI : Preset := EthCLSpecs.Heze.minimal
    letI : Config := EthCLSpecs.Heze.minimalConfig
    0 < slotDurationMs.toNat ∧ 1000 ∣ slotDurationMs.toNat ∧
      ilDueMs.toNat ≤ slotDurationMs.toNat := by
  decide

/-- Mainnet: 12000 ms and 8000 ms. -/
example :
    letI : Preset := EthCLSpecs.Heze.mainnet
    letI : Config := EthCLSpecs.Heze.mainnetConfig
    0 < slotDurationMs.toNat ∧ 1000 ∣ slotDurationMs.toNat ∧
      ilDueMs.toNat ≤ slotDurationMs.toNat := by
  decide

end Presets

end EthCLSpecs.Proofs.Heze
