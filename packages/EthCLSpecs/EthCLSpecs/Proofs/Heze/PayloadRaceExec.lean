import EthCLSpecs.Proofs.Heze.PayloadRaceWalk
import EthCLSpecs.Proofs.Heze.HonestVoteSide
import EthCLSpecs.Proofs.Heze.LatestMessages
import EthCLSpecs.Proofs.Heze.FullSupport
import EthCLSpecs.Proofs.Heze.TraceFacts
import EthCLSpecs.Proofs.Heze.ProposerScore

/-!
# `EthCLSpecs.Proofs.Heze.PayloadRaceExec`: EMPTY stays ahead on the executable spec

`race_empty_persists` (`PayloadRace.lean`) proves tier T2 on an abstract model of the race at
a block `r` of slot `N`. This module proves the same result on the executable fork choice.
Take the honest nodes of slots `N + 1 .. hi`, each with a head run in each slot. Each of these
heads lies strictly below `pending r`. Then each of them lies below `empty r` and not below
`full r`, or a root collision exists (`race_empty_persists_exec`).

## The setting

`NodeRun` holds the clocked trace of one node from its anchor store. `HeadRun` holds one head
run: a prefix of the trace, the store after it, the wall time, and the head. `RaceSetting`
states the premises:

- Each honest node starts at the anchor store of `getForkchoiceStore`. It ticks to its wall
  clock (`ClockedTrace`).
- Each head run of slot `t` holds the block `rb` at `r`, a justified block no later than
  `rb`, and the justified state `jst`. Its head is strictly below `pending r`, as the setting
  of `PayloadRace.lean` assumes. Every proposer score there is `proposerScoreOf jst`
  (`ProposerScore.lean`).
- The heads of slot `N + 1` avoid `full r` (`RaceSetting.first`). `RaceSetting.Core` holds
  the other premises. `PayloadRaceDecision.lean` proves `first` from the premises of tier T1,
  or a root collision.
- A window of several epochs has more than one justified state. `RaceSetting.Long` gives the
  head run of slot `t` the justified state `jstOf t`, and `race_empty_persists_long` states the
  race under it. The window still ends before the justified checkpoint passes `r`, because
  `HeadRun.Ok.justified` asks for a justified block no later than `rb`.
- Every honest validator votes for the head of its node, with the payload flag of
  `honestAttestationIndex` (`HonestData`). Each vote of slot `t` reaches every honest node
  before its head run of a later slot (`deliver`). No attester slashing marks an honest
  validator (`HonestSigner`).
- The committees of every target state of the window are `committees`: the first
  `get_committee_count_per_slot` committees of each slot, and none above. A window vote names
  only those committees. A validator votes in slot `t` when it is in a committee of slot `t`
  (`committeeVotes`).

## The argument

The proof follows the induction of `race_empty_persists`. Assume that every honest head of
the slots before `s` lies below `empty r`. Take an honest head run of slot `s`.

- Take an honest validator with a vote in `[N + 1, s)`. Its latest message is one of its
  votes in that window (`NodeTrace.latest_source`, `onAttestation_delivers`). That vote names
  a head below `empty r`. So the store puts the validator on `empty`
  (`storeSide_empty_of_below`).
- A validator on `full` has a latest message from a slot of `(N, s)` (`fullSupport_slot_gt`,
  `ClockedTrace.attestation_slot_le`). It is an attesting index of that slot, in a committee
  that the vote names (`getAttestingIndices_mem`). That committee is in range, so it is one of
  `committees` of the slot. An honest validator with that vote sits
  on `empty` by the first point, so the validator is adversarial.

So EMPTY holds at least the honest balance that has voted (`honestVoted_le_empty_of`). FULL
holds at most the adversarial balance that has voted (`full_le_advVoted_of`). The counting
inequality and the score refinement (`score_empty_refines`) give `WeightAhead`. Then the walk
goes below `empty r` (`getHead_run_below_empty`).

Stores of different nodes hold different blocks. Two blocks at one root are equal unless they
collide (`SlotInv.atRoot`). So the theorem concludes the head facts or `RootCollision`.

The sort of the handler is a hypothesis (`QsortMem`, `LatestMessages.lean`). The
combine-width law `hw` gives `SlotInv` along the traces.

The anchor state and the justified state `jst` are plain values. Each node starts at the
anchor store of `getForkchoiceStore (pureState anchorState)`, so every store of its trace
holds only uncached boxes (`NodeTrace.storePure`). The justified state of a head run is the
uncached box of `jst`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok pureState)
open EthCLLib.Spec
open EthCLLib.Proofs (LawfulFcMap)
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Checkpoint Slot ForkChoiceNode
  BeaconBlock
  ValidatorIndex LatestMessage Attestation SignedInclusionList ExecutionPayload
  ExecutionRequests Transaction getCurrentSlot getHead getAttestationScore getProposerScore
  getActiveValidatorIndices currentEpochOf getBeaconCommittee storeTargetCheckpointState Gwei
  getCommitteeIndices getCommitteeCountPerSlot computeEpochAtSlot)
open EthCLSpecs.Proofs.Heze.PayloadRace (Side Validator sideWeight balanceSum votedIn
  votedBalance honestVoted advVoted balanceSum_filter_mono votedIn_iff)

/-! ## Counting -/

/-- EMPTY holds at least the honest balance that has voted, when each honest validator with
a vote in `[lo, s)` sits on `empty`. -/
theorem honestVoted_le_empty_of (vs : List Validator) (view : Validator → Side) (lo s : Nat)
    (h : ∀ w ∈ vs, w.honest = true → votedIn w.votes lo s = true → view w = .empty) :
    honestVoted vs lo s ≤ sideWeight vs view .empty := by
  unfold honestVoted votedBalance sideWeight
  apply balanceSum_filter_mono
  intro w hw hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rw [h w hw hp.1 hp.2]
  simp

/-- FULL holds at most the adversarial balance that has voted, when each validator on
`full` is adversarial and has a vote in `[lo, s)`. -/
theorem full_le_advVoted_of (vs : List Validator) (view : Validator → Side) (lo s : Nat)
    (h : ∀ w ∈ vs, view w = .full → w.honest = false ∧ votedIn w.votes lo s = true) :
    sideWeight vs view .full ≤ advVoted vs lo s := by
  unfold advVoted votedBalance sideWeight
  apply balanceSum_filter_mono
  intro w hw hp
  simp only [decide_eq_true_eq] at hp
  obtain ⟨h1, h2⟩ := h w hw hp
  simp [h1, h2]

open Classical in
/-- Validator `i` votes in slot `t`: it is in a committee of slot `t`. -/
noncomputable def committeeVotes (committees : Nat → Nat → Array ValidatorIndex)
    (i : ValidatorIndex) (t : Nat) : Bool :=
  decide (∃ ci, i ∈ committees t ci)

/-- The first slot of the race window, `N + 1` for the block `rb` of slot `N`. -/
def raceLo [Preset] (rb : BeaconBlock) : Nat := rb.slot.toNat + 1

section Store
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- A successful score fold ran `supports` at each unslashed index of its list. -/
theorem scoreFold_supports (store : Store map) (node : ForkChoiceNode) (state : BeaconState) :
    ∀ (l : List ValidatorIndex) (acc : Gwei) (t t' : Store map) (w : Gwei),
      (l.foldlM (scoreStep store node (pureState state)) acc).run t = .ok (w, t') →
      ∀ i ∈ l, slashedB (pureState state) i = false →
        ∃ (b : Bool) (u u' : Store map), (supports store node i).run u = .ok (b, u') := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ i hi; cases hi
  | cons j l ih =>
    intro acc t t' w h i hi hs
    rw [List.foldlM_cons] at h
    obtain ⟨a, t1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    rcases List.mem_cons.mp hi with rfl | hi
    · unfold scoreStep at hstep
      rw [if_neg (by simp [hs])] at hstep
      obtain ⟨b, u, hb, -⟩ := run_bind_eq_ok _ _ _ _ hstep
      exact ⟨b, t, u, hb⟩
    · exact ih a t1 t' w hrest i hi hs

/-- A successful score run ran `supports` at each active unslashed index. Its value at the
store is the value of that run (`supports_stateFree`). -/
theorem getAttestationScore_supports (store : Store map) (node : ForkChoiceNode)
    (state : BeaconState) {t t' : Store map} {w : Gwei}
    (h : (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
      store node (pureState state)).run t = .ok (w, t'))
    (i : ValidatorIndex)
    (hi : i ∈ (getActiveValidatorIndices (pureState state)
      (currentEpochOf (pureState state))).toList)
    (hs : slashedB (pureState state) i = false) :
    ∃ (b : Bool) (u : Store map), (supports store node i).run store = .ok (b, u) := by
  rw [getAttestationScore_eq, ← Array.foldlM_toList] at h
  obtain ⟨b, u, u', hb⟩ := scoreFold_supports store node state _ 0 t t' w h i hi hs
  exact ⟨b, store, ((supports_stateFree store node i).run_eq hb).2 store⟩

/-- A validator of the race is an active unslashed index of the state. -/
theorem mem_raceValidators (state : BeaconState) (honestOf : ValidatorIndex → Bool)
    (votesOf : ValidatorIndex → Nat → Bool) (w : Validator)
    (hw : w ∈ raceValidators (pureState state) honestOf votesOf) :
    ∃ i, i ∈ (getActiveValidatorIndices (pureState state)
        (currentEpochOf (pureState state))).toList ∧
      slashedB (pureState state) i = false ∧
      w = ⟨i.toNat, (bal (pureState state) i).toNat, honestOf i, votesOf i⟩ := by
  unfold raceValidators at hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  obtain ⟨hi, hs⟩ := List.mem_filter.mp hi
  exact ⟨i, hi, by simpa using hs, rfl⟩

/-- Two stores that meet `SlotInv` hold the same block at a shared root, unless two distinct
blocks share that root. -/
theorem SlotInv.block_eq {a a' : BeaconBlock} {X Y : Store map} (hX : SlotInv a X)
    (hY : SlotInv a' Y) (hcol : ¬ HtrCollision BeaconBlock) {k : Root} {x y : BeaconBlock}
    (hx : FcMap.lookup X.blocks k = some x) (hy : FcMap.lookup Y.blocks k = some y) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · exact absurd ⟨x, y, hxy, (hX.atRoot k x hx).trans (hY.atRoot k y hy).symm⟩ hcol

end Store

/-! ## The setting -/

/-- The data of one node: the anchor of its store, and its clocked trace. -/
structure NodeRun (map : MapKind) [Preset] [HasherTag] [FcMap map] where
  /-- The anchor state, a plain value. The anchor store holds its uncached box. -/
  anchorState : BeaconState
  /-- The anchor block. -/
  anchor : BeaconBlock
  /-- The anchor store. -/
  seed : Store map
  /-- The events of the node, with their wall times. -/
  events : List (TraceEvent × Nat)
  /-- The IL arrivals of the trace. -/
  arrivals : List (SignedInclusionList × UInt64)
  /-- The store at the end of the trace. -/
  last : Store map

/-- One head run of a node: the prefix of its trace before the run, the store after the
prefix, the wall time of the run, and the head that `getHead` returns. -/
structure HeadRun (map : MapKind) [Preset] [HasherTag] [FcMap map] where
  /-- The events before the run. -/
  events : List (TraceEvent × Nat)
  /-- The IL arrivals of the prefix. -/
  arrivals : List (SignedInclusionList × UInt64)
  /-- The store of the run. -/
  store : Store map
  /-- The wall time of the run, in milliseconds. -/
  wall : Nat
  /-- The head. -/
  head : ForkChoiceNode

section Setting
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- An honest node starts at the anchor store and ticks to its wall clock. It receives no block
at the parent root of its anchor. The anchor is no later than the block `rb`. -/
structure NodeRun.Honest (n : NodeRun map) (rb : BeaconBlock) : Prop where
  /-- The node starts at the anchor store of `getForkchoiceStore`. -/
  anchorStore : EthCLSpecs.Heze.getForkchoiceStore (pureState n.anchorState) n.anchor = .ok n.seed
  /-- The anchor is not its own parent. -/
  anchorSelf : n.anchor.parentRoot ≠ htr n.anchor
  /-- The anchor is no later than `rb`. -/
  anchorSlot : n.anchor.slot ≤ rb.slot
  /-- The node ticks to its wall clock. -/
  clocked : ClockedTrace n.seed n.events n.arrivals n.last
  /-- No event is a block at the parent root of the anchor. -/
  noAnchorParent : ∀ (e : HandlerEvent) (w : Nat), (.handler e, w) ∈ n.events →
    e.NotAtAnchorParent n.anchor

/-- A head run of slot `t` of the node `n`. The run follows a prefix of the trace of `n`. Its
wall time is in slot `t` and no earlier than the events of the prefix. Its store holds the block
`rb` at `r`, a justified block no later than `rb`, and the uncached box of the justified
state `jst`. The head is strictly below `pending r`. -/
structure HeadRun.Ok (n : NodeRun map) (q : HeadRun map) (r : Root) (rb : BeaconBlock)
    (jst : BeaconState) (t : Nat) : Prop where
  /-- The run follows a prefix of the trace. -/
  isPrefix : ∃ rest, n.events = q.events ++ rest
  /-- The store is the end of the prefix. -/
  trace : NodeTrace n.seed (q.events.map Prod.fst) q.arrivals q.store
  /-- The events of the prefix are no later than the run. -/
  wall : ∀ y ∈ q.events, y.2 ≤ q.wall
  /-- The store time is the wall time in whole seconds. -/
  time : q.store.time.toNat = q.wall / 1000
  /-- The current slot is `t`. -/
  slot : ∃ cs : Slot, cs.toNat = t ∧
    (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) q.store).run q.store
      = .ok (cs, q.store)
  /-- `getHead` returns the head. -/
  headRun : ∃ s', (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) q.store).run
    q.store = .ok (q.head, s')
  /-- The head is strictly below `pending r`. -/
  setting : NodeBelow q.store (.pending r) q.head ∧ q.head ≠ .pending r
  /-- The store holds `rb` at `r`. -/
  block : FcMap.lookup q.store.blocks r = some rb
  /-- The justified block is no later than `rb`. -/
  justified : ∃ jb, FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root = some jb ∧
    jb.slot ≤ rb.slot
  /-- The justified state is the uncached box of `jst`. -/
  justifiedState :
    FcMap.lookup q.store.checkpointStates q.store.justifiedCheckpoint = some (pureState jst)

/-- The attestation `att` is an event of the trace `events` from `s0`, run on the store
`mid`. -/
def AttEventAt (s0 : Store map) (events : List TraceEvent) (att : Attestation) (mid : Store map) :
    Prop :=
  ∃ (es1 es2 : List TraceEvent) (fb : Bool) (arr : List (SignedInclusionList × UInt64)),
    events = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧ NodeTrace s0 es1 arr mid

/-- The data of an honest vote on `head`, at the store `st` of the voter
(phase0 `validator.md:638`, `gloas/validator.md:100-111`): the head root, and the payload flag of
`honestAttestationIndex` at the slot of the head block. -/
def HonestData (st : Store map) (head : ForkChoiceNode) (att : Attestation) : Prop :=
  att.data.beaconBlockRoot = head.root ∧
  ∃ hb : BeaconBlock, FcMap.lookup st.blocks head.root = some hb ∧
    att.data.index = honestAttestationIndex head hb.slot att.data.slot

/-- The premises of the race on the executable spec, for the block `rb` at `r` and the
window `[raceLo rb, hi]`, except the head runs and the first slot. None of them names a
justified state. `RaceSetting.Core` adds the head runs, and `RaceSetting` adds the first
slot. -/
structure RaceSetting.Fields {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (hi : Nat)
    (nodeOf : ValidatorIndex → Node) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) : Prop where
  /-- Each honest node meets `NodeRun.Honest`. -/
  nodeOk : ∀ v, honest v → (node v).Honest rb
  /-- An honest validator runs on an honest node. -/
  honestNode : ∀ i, honestOf i = true → honest (nodeOf i)
  /-- Every target state of a window vote at an honest node gives the committees
  `committees`. Each of the first `get_committee_count_per_slot` committees of the vote slot
  exists in that state (`.ok`), and `committees` holds it. Above them, `committees` is empty.
  The vote names only those committees. A committee index at or above
  the count names a committee of a later slot (`getBeaconCommittee`). Gossip rejects such an
  index (electra `p2p-interface.md:261-264`, `:413-416`), and `process_attestation` asserts
  the bound for an attestation in a block. -/
  committee : ∀ v, honest v → ∀ s, raceLo rb < s → s ≤ hi → ∀ att mid,
    AttEventAt (node v).seed ((run v s).events.map Prod.fst) att mid →
    raceLo rb ≤ att.data.slot.toNat → att.data.slot.toNat < hi →
    ∀ (cps : map Checkpoint State) (s2 : Store map) (ts : BeaconState),
      (storeTargetCheckpointState (StoreTransition := ForkChoiceStoreRun (Store map))
        mid att.data.target).run mid = .ok ({ mid with checkpointStates := cps }, s2) →
      FcMap.lookup cps att.data.target = some (pureState ts) →
      (∀ ci ∈ getCommitteeIndices att.committeeBits,
        ci < getCommitteeCountPerSlot (pureState ts) (computeEpochAtSlot att.data.slot)) ∧
      ∀ ci, if ci < getCommitteeCountPerSlot (pureState ts) (computeEpochAtSlot att.data.slot)
        then getBeaconCommittee (pureState ts) att.data.slot ci
          = .ok (committees att.data.slot.toNat ci)
        else committees att.data.slot.toNat ci = #[]
  /-- An honest validator signs only honest data in the window. -/
  attester : ∀ v, honest v → ∀ s, raceLo rb < s → s ≤ hi → ∀ i, honestOf i = true →
    ∀ att mid, AttEventAt (node v).seed ((run v s).events.map Prod.fst) att mid →
    (∃ A, AttIndices mid att A ∧ i ∈ A) →
    raceLo rb ≤ att.data.slot.toNat → att.data.slot.toNat < hi →
    HonestData (run (nodeOf i) att.data.slot.toNat).store
      (run (nodeOf i) att.data.slot.toNat).head att
  /-- Each window vote of an honest validator reaches every honest node before its head run
  of a later slot. -/
  deliver : ∀ v, honest v → ∀ s, raceLo rb < s → s ≤ hi → ∀ i, honestOf i = true →
    ∀ t, raceLo rb ≤ t → t < s → committeeVotes committees i t = true →
    ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool),
      (run v s).events.map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
      att.data.slot.toNat = t ∧
      ∀ arr mid, NodeTrace (node v).seed es1 arr mid → ∀ A, AttIndices mid att A → i ∈ A
  /-- No attester slashing marks an honest validator. -/
  signer : ∀ v, honest v → ∀ s, raceLo rb < s → s ≤ hi → ∀ i, honestOf i = true →
    HonestSigner (node v).seed ((run v s).events.map Prod.fst) i
  /-- The sort of the handler keeps the members. -/
  sort : QsortMem

/-- The premises of the race on the executable spec, except the first slot: `RaceSetting.Fields`
and the head runs, each with the justified state `jst`. `RaceSetting` adds the first slot. -/
structure RaceSetting.Core {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (hi : Nat)
    (jst : BeaconState) (nodeOf : ValidatorIndex → Node) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) : Prop
    extends RaceSetting.Fields honest node run r rb hi nodeOf honestOf committees where
  /-- Each head run of an honest node in the window meets `HeadRun.Ok` for its slot. -/
  runOk : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
    (run v t).Ok (node v) r rb jst t

/-- The premises of the race on the executable spec: `RaceSetting.Core` and the first slot. -/
structure RaceSetting {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (hi : Nat)
    (jst : BeaconState) (nodeOf : ValidatorIndex → Node) (honestOf : ValidatorIndex → Bool)
    (committees : Nat → Nat → Array ValidatorIndex) : Prop
    extends RaceSetting.Core honest node run r rb hi jst nodeOf honestOf committees where
  /-- The heads of the first slot avoid `full r`. -/
  first : ∀ v, honest v →
    ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head

/-- The premises of the race with one justified state per slot: `RaceSetting.Fields`, the
head runs, and the first slot. The head run of slot `t` has the justified state `jstOf t`. A
window of several epochs needs this form, because the justified checkpoint of a store moves
at an epoch boundary. -/
structure RaceSetting.Long {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (r : Root) (rb : BeaconBlock) (hi : Nat)
    (jstOf : Nat → BeaconState) (nodeOf : ValidatorIndex → Node)
    (honestOf : ValidatorIndex → Bool) (committees : Nat → Nat → Array ValidatorIndex) : Prop
    extends RaceSetting.Fields honest node run r rb hi nodeOf honestOf committees where
  /-- Each head run of an honest node in the window meets `HeadRun.Ok` for its slot, with the
  justified state of that slot. -/
  runOkAt : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
    (run v t).Ok (node v) r rb (jstOf t) t
  /-- The heads of the first slot avoid `full r`. -/
  first : ∀ v, honest v →
    ¬ NodeBelow (run v (raceLo rb)).store (.full r) (run v (raceLo rb)).head

/-- `RaceSetting` is `RaceSetting.Long` with one justified state on every slot. -/
theorem RaceSetting.toLong {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
    {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {hi : Nat} {jst : BeaconState}
    {nodeOf : ValidatorIndex → Node} {honestOf : ValidatorIndex → Bool}
    {committees : Nat → Nat → Array ValidatorIndex}
    (hset : RaceSetting honest node run r rb hi jst nodeOf honestOf committees) :
    RaceSetting.Long honest node run r rb hi (fun _ => jst) nodeOf honestOf committees :=
  { toFields := hset.toFields, runOkAt := hset.runOk, first := hset.first }

end Setting

/-! ## The stores of the window -/

section Stores
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

omit [LawfulFcMap map Root] in
/-- The events of a head run are events of the trace of its node. -/
theorem HeadRun.Ok.mem_events {n : NodeRun map} {q : HeadRun map} {r : Root} {rb : BeaconBlock}
    {jst : BeaconState} {t : Nat} (hq : q.Ok n r rb jst t) (e : HandlerEvent)
    (he : TraceEvent.handler e ∈ q.events.map Prod.fst) :
    ∃ w, (TraceEvent.handler e, w) ∈ n.events := by
  obtain ⟨rest, hsplit⟩ := hq.isPrefix
  obtain ⟨y, hy, hy1⟩ := List.mem_map.mp he
  refine ⟨y.2, ?_⟩
  rw [hsplit, ← hy1]
  exact List.mem_append_left _ hy

include hw in
/-- A store of the trace of an honest node meets `SlotInv` for its anchor, unless a root
collision exists. The store follows a list of events of the trace. -/
theorem NodeRun.Honest.slotInv {n : NodeRun map} {rb : BeaconBlock} (hn : n.Honest rb)
    {es : List TraceEvent}
    (hes : ∀ e, TraceEvent.handler e ∈ es → ∃ w, (TraceEvent.handler e, w) ∈ n.events)
    {arr : List (SignedInclusionList × UInt64)} {m : Store map} (h : NodeTrace n.seed es arr m)
    (hcol : ¬ RootCollision) : SlotInv n.anchor m := by
  rcases h.slotInv hw (SlotInv.anchor n.anchorState n.anchor n.seed hn.anchorStore hn.anchorSelf)
      (fun e he => by
        obtain ⟨w, hw'⟩ := hes e he
        exact hn.noAnchorParent e w hw') with h | h
  · exact h
  · exact absurd h hcol

include hw in
/-- The store of a head run meets `SlotInv`, unless a root collision exists. -/
theorem HeadRun.Ok.slotInv {n : NodeRun map} {q : HeadRun map} {r : Root} {rb : BeaconBlock}
    {jst : BeaconState} {t : Nat} (hn : n.Honest rb) (hq : q.Ok n r rb jst t)
    (hcol : ¬ RootCollision) : SlotInv n.anchor q.store :=
  hn.slotInv hw (hq.mem_events) hq.trace hcol

include hw in
/-- A store inside the prefix of a head run meets `SlotInv`, unless a root collision
exists. -/
theorem HeadRun.Ok.slotInv_mid {n : NodeRun map} {q : HeadRun map} {r : Root}
    {rb : BeaconBlock} {jst : BeaconState} {t : Nat} (hn : n.Honest rb)
    (hq : q.Ok n r rb jst t) {es1 es2 : List TraceEvent} {e : TraceEvent}
    (hes : q.events.map Prod.fst = es1 ++ e :: es2) {arr : List (SignedInclusionList × UInt64)}
    {mid : Store map} (h : NodeTrace n.seed es1 arr mid) (hcol : ¬ RootCollision) :
    SlotInv n.anchor mid :=
  hn.slotInv hw (fun e' he' => hq.mem_events e' (by rw [hes]; exact List.mem_append_left _ he'))
    h hcol

/-- Every store of the trace of an honest node meets `StorePure`: its seed is the anchor
store of `getForkchoiceStore (pureState anchorState)`. -/
theorem NodeRun.Honest.storePure [LawfulFcMap map Checkpoint] {n : NodeRun map} {rb : BeaconBlock} (hn : n.Honest rb) {es : List TraceEvent}
    {arr : List (SignedInclusionList × UInt64)} {m : Store map} (h : NodeTrace n.seed es arr m) :
    StorePure m :=
  h.storePure (StorePure.anchor _ _ _ hn.anchorStore)

end Stores

/-! ## The two sides of the store -/

section Sides
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {hi : Nat}
  {jstOf : Nat → BeaconState}
  {nodeOf : ValidatorIndex → Node} {honestOf : ValidatorIndex → Bool}
  {committees : Nat → Nat → Array ValidatorIndex}

include hw in
/-- The latest message of `i` in a head run of slot `s` comes from an attestation event of
the prefix (`NodeTrace.latest_source`). The vote slot is before `s`
(`ClockedTrace.attestation_slot_le`). The store of the run holds the same block at the vote
root as the store before the event. That block is no later than the vote slot. -/
theorem RaceSetting.Fields.latest_window
    (hset : RaceSetting.Fields honest node run r rb hi nodeOf honestOf committees)
    (hruns : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi → (run v t).Ok (node v) r rb (jstOf t) t)
    (hcol : ¬ RootCollision) (v : Node) (hv : honest v) (s : Nat) (hlos : raceLo rb < s)
    (hs : s ≤ hi) (i : ValidatorIndex) (q : LatestMessage)
    (hq : FcMap.lookup (run v s).store.latestMessages i = some q) :
    ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool) (mid : Store map)
      (arr : List (SignedInclusionList × UInt64)) (b : BeaconBlock),
      (run v s).events.map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
      NodeTrace (node v).seed es1 arr mid ∧ AttWrite mid att i ∧ q = attMessage att ∧
      att.data.slot.toNat < s ∧
      FcMap.lookup (run v s).store.blocks att.data.beaconBlockRoot = some b ∧
      b.slot ≤ att.data.slot := by
  have hBlk : ¬ HtrCollision BeaconBlock := fun h => hcol (Or.inr h)
  have hN := hset.nodeOk v hv
  have hQ := hruns v hv s (Nat.le_of_lt hlos) hs
  obtain ⟨rest, hsplit⟩ := hQ.isPrefix
  rcases hQ.trace.latest_source (StorePure.anchor _ _ _ hN.anchorStore) i q hq with h0 |
      ⟨es1, es2, att, fb, mid, arr, arrS, hes, htr, hsuf, hW, rfl⟩
  · rw [getForkchoiceStore_latest _ _ _ hN.anchorStore] at h0
    cases h0
  -- The clock: the event ran before the current slot of the run.
  obtain ⟨cs1, u1, u1', hcs1, hge1⟩ := hW.clock
  obtain ⟨csB, hcsB, hcurB⟩ := hQ.slot
  have hle := hN.clocked.attestation_slot_le hsplit hQ.trace hQ.wall hQ.time hes htr hcs1 hcurB
  -- The block at the vote root persists, and the two stores agree on it.
  obtain ⟨b0, hb0, hb0slot⟩ := hW.block
  obtain ⟨b', hb'⟩ := hsuf.blocks_persist _ b0 hb0
  have hb0' : b0 = b' :=
    SlotInv.block_eq (hQ.slotInv_mid hw hN hes htr hcol) (hQ.slotInv hw hN hcol) hBlk hb0 hb'
  subst hb0'
  exact ⟨es1, es2, att, fb, mid, arr, b0, hes, htr, hW, rfl, by omega, hb', hb0slot⟩

include hw in
/-- An honest validator with a vote in `[N + 1, s)` sits on `empty` in a head run of slot
`s`, when every honest head before `s` lies below `empty r`.

The vote reaches the node (`deliver`), so the latest message of the validator has at least
its slot (`onAttestation_delivers`, `NodeTrace.latest_mono`). That message comes from an
attestation event of the trace (`NodeTrace.latest_source`), from a slot of `[N + 1, s)`
(`ClockedTrace.attestation_slot_le`). It is honest data, so it names a head below `empty r`.
`NodeBelow.transfer` moves that head to the store of the run. Then
`honest_supported_below_empty` and `storeSide_empty_of_below` give the side. The `supports`
run at `empty r` must succeed. -/
theorem RaceSetting.Fields.storeSide_empty
    (hset : RaceSetting.Fields honest node run r rb hi nodeOf honestOf committees)
    (hruns : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi → (run v t).Ok (node v) r rb (jstOf t) t)
    (hcol : ¬ RootCollision) (v : Node) (hv : honest v) (s : Nat) (hlos : raceLo rb < s)
    (hs : s ≤ hi)
    (hP : ∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
      NodeBelow (run u t).store (.empty r) (run u t).head)
    (i : ValidatorIndex) (hhon : honestOf i = true) (t : Nat) (hlo : raceLo rb ≤ t) (hts : t < s)
    (hvote : committeeVotes committees i t = true)
    (hok : ∃ (b : Bool) (u : Store map),
      (supports (run v s).store (.empty r) i).run (run v s).store = .ok (b, u)) :
    storeSide (run v s).store r i.toNat = .empty := by
  have hBlk : ¬ HtrCollision BeaconBlock := fun h => hcol (Or.inr h)
  have hN := hset.nodeOk v hv
  have hQ := hruns v hv s (Nat.le_of_lt hlos) hs
  have hinvB := hQ.slotInv hw hN hcol
  have hsigner := hset.signer v hv s hlos hs i hhon
  -- The vote of slot `t` reaches the node, so the latest message has at least slot `t`.
  obtain ⟨es1, es2, att, fb, hes, hslot, hatt⟩ := hset.deliver v hv s hlos hs i hhon t hlo hts hvote
  obtain ⟨mid, arr1, arr2, h1, h2, -⟩ := hQ.trace.split hes
  obtain ⟨post, a1, a2, hsingle, hrest, -⟩ :=
    h2.split (es1 := [TraceEvent.handler (.attestation att fb)]) (es2 := es2) rfl
  have hrun := hsingle.single_handler
  have hneMid : mid.equivocatingIndices.contains i = false := by
    have := honest_not_equivocating hN.anchorStore h1 i (by rw [hes] at hsigner; exact hsigner.prefix)
    simpa using this
  obtain ⟨q0, hq0, hle0⟩ :=
    onAttestation_delivers hset.sort att fb mid post (hN.storePure h1) hrun i (hatt arr1 mid h1)
      hneMid
  obtain ⟨q, hq, hle1⟩ := hrest.latest_mono i q0 hq0
  -- The latest message comes from an attestation event of the prefix, before slot `s`.
  obtain ⟨es1', es2', att', fb', mid', arr', b0, hes', htr', hW, rfl, hlt', hb', hb0slot⟩ :=
    hset.latest_window hw hruns hcol v hv s hlos hs i q hq
  have hlo' : raceLo rb ≤ att'.data.slot.toNat := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans hle0 hle1)
    simp only [attMessage] at this
    omega
  -- The message is honest data on the head of its node in its slot.
  obtain ⟨A, hAI, hiA⟩ := hW.indices
  have hHD := hset.attester v hv s hlos hs i hhon att' mid' ⟨es1', es2', fb', arr', hes', htr'⟩
    ⟨A, hAI, (hset.sort A i).mp hiA⟩ hlo' (by omega)
  obtain ⟨hroot, hbA, hhbA, hidx⟩ := hHD
  have hu := hset.honestNode i hhon
  have hQu := hruns (nodeOf i) hu att'.data.slot.toNat hlo' (by omega)
  have hNu := hset.nodeOk (nodeOf i) hu
  have hinvA := hQu.slotInv hw hNu hcol
  have hbelowA := hP (nodeOf i) hu att'.data.slot.toNat hlo' hlt'
  -- The store of the run holds the same block at the head root.
  have hbB : FcMap.lookup (run v s).store.blocks (run (nodeOf i) att'.data.slot.toNat).head.root
      = some b0 := hroot ▸ hb'
  have hbA' : hbA = b0 := SlotInv.block_eq hinvA hinvB hBlk hhbA hbB
  subst hbA'
  -- The head lies below `empty r` in the store of the run.
  have hbelowB : NodeBelow (run v s).store (.empty r) (run (nodeOf i) att'.data.slot.toNat).head :=
    NodeBelow.transfer _ _ hinvA.slots r rb hQu.block (node v).anchor
      (fun k x y hx hy => SlotInv.block_eq hinvA hinvB hBlk hx hy)
      (fun k x hx => hinvB.parentIn k x hx) hN.anchorSlot _ hbelowA (Or.inr ⟨hbA, hbB⟩)
  obtain ⟨sA, hrunA⟩ := hQu.headRun
  have hstatus := getHead_run_status _ _ _ _ hrunA
  refine storeSide_empty_of_below _ hinvB.slots r rb hQ.block i (attMessage att') hq ?_ ?_ hok
  · have := honest_not_equivocating hN.anchorStore hQ.trace i hsigner
    simpa using this
  · intro u0 u0' n hn
    have hmsg : attMessage att' =
        { slot := att'.data.slot, root := (run (nodeOf i) att'.data.slot.toNat).head.root,
          payloadPresent := honestAttestationIndex (run (nodeOf i) att'.data.slot.toNat).head
            hbA.slot att'.data.slot == 1 } := by
      unfold attMessage
      rw [hroot, hidx]
    rw [hmsg] at hn
    refine honest_supported_below_empty _ r rb hQ.block _ hbelowB hstatus hbA hbB
      att'.data.slot hb0slot ?_ hn
    rw [UInt64.lt_iff_toNat_lt]
    unfold raceLo at hlo'
    omega

include hw in
/-- A validator on `full` in a head run of slot `s` has a vote in `[N + 1, s)`: it is in a
committee of the slot of its latest message.

The supported node of the latest message lies below `full r` (`storeSide_full_below`). The
message comes from an attestation event of the trace that checked the slot of its block
(`AttWrite`). So the message slot is after the slot of `r` (`fullSupport_slot_gt`) and before
`s` (`ClockedTrace.attestation_slot_le`). The validator is an attesting index of the event,
in a committee that the vote names (`getAttestingIndices_mem`). `RaceSetting.Fields.committee`
puts that index in range, so the committee is one of `committees` of the slot. -/
theorem RaceSetting.Fields.storeSide_full_voted
    (hset : RaceSetting.Fields honest node run r rb hi nodeOf honestOf committees)
    (hruns : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi → (run v t).Ok (node v) r rb (jstOf t) t)
    (hcol : ¬ RootCollision) (v : Node) (hv : honest v) (s : Nat) (hlos : raceLo rb < s)
    (hs : s ≤ hi) (i : ValidatorIndex)
    (hfull : storeSide (run v s).store r i.toNat = .full) :
    ∃ t, raceLo rb ≤ t ∧ t < s ∧ committeeVotes committees i t = true := by
  have hQ := hruns v hv s (Nat.le_of_lt hlos) hs
  have hinvB := hQ.slotInv hw (hset.nodeOk v hv) hcol
  obtain ⟨lm, n, u, u', hlm, -, hsup, hbelow⟩ := storeSide_full_below _ r i hfull
  obtain ⟨es1', es2', att', fb', mid', arr', b0, hes', htr', hW, rfl, hlt', hb', hb0slot⟩ :=
    hset.latest_window hw hruns hcol v hv s hlos hs i lm hlm
  -- The block at the message root has a slot no greater than the message slot.
  have hmsg : ∀ b, FcMap.lookup (run v s).store.blocks (attMessage att').root = some b →
      b.slot ≤ (attMessage att').slot := by
    intro b hb
    have hb'' : FcMap.lookup (run v s).store.blocks att'.data.beaconBlockRoot = some b := hb
    rw [hb'] at hb''
    cases hb''
    exact hb0slot
  have hgt := fullSupport_slot_gt _ hinvB.slots r rb hQ.block _ hmsg hsup hbelow
  have hlo' : raceLo rb ≤ att'.data.slot.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp hgt
    unfold raceLo
    simp only [attMessage] at this
    omega
  -- The validator is in a committee of the message slot.
  obtain ⟨A, ⟨cps, s2, ts, hmid, hts, hA⟩, hiA⟩ := hW.indices
  obtain ⟨ci, c, hciIn, hc, hic⟩ :=
    getAttestingIndices_mem ts att' A hA i ((hset.sort A i).mp hiA)
  obtain ⟨hrange, hcomm⟩ := hset.committee v hv s hlos hs att' mid'
    ⟨es1', es2', fb', arr', hes', htr'⟩ hlo' (by omega) cps s2 ts hmid hts
  -- The committee index of the vote is in range, so `committees` holds that committee.
  have hcomm' := hcomm ci
  rw [if_pos (hrange ci hciIn)] at hcomm'
  have hceq : c = committees att'.data.slot.toNat ci := by
    have h2 := hc.symm.trans hcomm'
    injection h2
  refine ⟨att'.data.slot.toNat, hlo', hlt', ?_⟩
  simp only [committeeVotes, decide_eq_true_eq]
  exact ⟨ci, hceq ▸ hic⟩

include hw in
/-- EMPTY is ahead on weight in a head run of slot `s > N + 1`, when every honest head
before `s` lies below `empty r` and the counting inequality holds at `s`.

The block `r` is two or more slots back, so both weights are off the decision slot
(`isPreviousSlotPayloadDecision_run_false`). The score of each side is its race weight over
the validators of the justified state `jstOf s` of the run (`score_empty_refines`,
`score_full_refines`). The successful EMPTY score run ran `supports` at every validator
(`getAttestationScore_supports`). Then the two side lemmas bound the race weights. Every
proposer score is `proposerScoreOf (jstOf s)` (`getProposerScore_run_eq`). The counting
inequality puts EMPTY ahead by more than that score (`weightAhead_of_scores`). -/
theorem RaceSetting.Fields.weightAhead
    (hset : RaceSetting.Fields honest node run r rb hi nodeOf honestOf committees)
    (hruns : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi → (run v t).Ok (node v) r rb (jstOf t) t)
    (hcol : ¬ RootCollision) (v : Node) (hv : honest v) (s : Nat) (hlos : raceLo rb < s)
    (hs : s ≤ hi)
    (hcount : advVoted (raceValidators (pureState (jstOf s)) honestOf (committeeVotes committees))
        (raceLo rb) s + proposerScoreOf (pureState (jstOf s))
      < honestVoted (raceValidators (pureState (jstOf s)) honestOf (committeeVotes committees))
        (raceLo rb) s)
    (hP : ∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
      NodeBelow (run u t).store (.empty r) (run u t).head) :
    WeightAhead (run v s).store r := by
  have hQ := hruns v hv s (Nat.le_of_lt hlos) hs
  -- Only the run of slot `s` reads its justified state, so name that state `jst`.
  generalize jstOf s = jst at hQ hcount
  obtain ⟨cs, hcs, hcur⟩ := hQ.slot
  have hlt : rb.slot.toNat + 1 < cs.toNat := by
    unfold raceLo at hlos
    omega
  refine weightAhead_of_scores _ r (proposerScoreOf (pureState jst))
    ((hset.nodeOk v hv).storePure hQ.trace)
    (isPreviousSlotPayloadDecision_run_false _ _ rb cs hQ.block hcur hlt)
    (isPreviousSlotPayloadDecision_run_false _ _ rb cs hQ.block hcur hlt)
    (fun _ _ _ hps => Nat.le_of_eq (getProposerScore_run_eq _ jst hQ.justifiedState hps)) ?_
  intro st sE sF t1 t1' t2 t2' hst hsE hsF
  rw [hQ.justifiedState] at hst
  injection hst with hst
  have e : jst = st := congrArg SizzLean.Cache.SSZ.Box.view hst
  subst e
  rw [score_empty_refines _ jst r honestOf (committeeVotes committees) hsE,
    score_full_refines _ jst r honestOf (committeeVotes committees) hsF]
  have h1 := honestVoted_le_empty_of
    (raceValidators (pureState jst) honestOf (committeeVotes committees))
    (fun w => storeSide (run v s).store r w.index) (raceLo rb) s (by
      intro w hw' hhon hvoted
      obtain ⟨i, hi, hsl, rfl⟩ := mem_raceValidators jst honestOf _ w hw'
      obtain ⟨t, hlo, hts, hvote⟩ := (votedIn_iff _ _ _).mp hvoted
      exact hset.storeSide_empty hw hruns hcol v hv s hlos hs hP i hhon t hlo hts hvote
        (getAttestationScore_supports _ _ jst hsE i hi hsl))
  have h2 := full_le_advVoted_of
    (raceValidators (pureState jst) honestOf (committeeVotes committees))
    (fun w => storeSide (run v s).store r w.index) (raceLo rb) s (by
      intro w hw' hfull
      obtain ⟨i, hi, hsl, rfl⟩ := mem_raceValidators jst honestOf _ w hw'
      obtain ⟨t, hlo, hts, hvote⟩ := hset.storeSide_full_voted hw hruns hcol v hv s hlos hs i hfull
      refine ⟨?_, (votedIn_iff _ _ _).mpr ⟨t, hlo, hts, hvote⟩⟩
      cases hh : honestOf i
      · rfl
      · have hE := hset.storeSide_empty hw hruns hcol v hv s hlos hs hP i hh t hlo hts hvote
          (getAttestationScore_supports _ _ jst hsE i hi hsl)
        have hF : storeSide (run v s).store r i.toNat = .full := hfull
        rw [hE] at hF
        cases hF)
  omega

end Sides

/-! ## The race -/

section Race
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- Tier T2 on the executable spec, with one justified state per slot. Take the block `rb` at
`r`, of slot `N`, and the window of slots `N + 1 .. hi`, under `RaceSetting.Long`. In every
slot `s` of `(N + 1, hi]`, take the validators of `jstOf s`. Their honest balance that has
voted in `[N + 1, s)` is more than their adversarial balance that has voted there, plus the
proposer score of `jstOf s`. Then every honest head of the window lies below `empty r` and
not below `full r`, or a root collision exists.

The proof is the induction of `race_empty_persists`. The first slot is
`RaceSetting.Long.first` with `NodeBelow.pending_split`. A later slot applies
`getHead_run_below_empty` to `RaceSetting.Fields.weightAhead`. -/
theorem race_empty_persists_long {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {hi : Nat} {jstOf : Nat → BeaconState} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : RaceSetting.Long honest node run r rb hi jstOf nodeOf honestOf committees)
    (hcount : ∀ s, raceLo rb < s → s ≤ hi →
      advVoted (raceValidators (pureState (jstOf s)) honestOf (committeeVotes committees))
          (raceLo rb) s + proposerScoreOf (pureState (jstOf s))
        < honestVoted (raceValidators (pureState (jstOf s)) honestOf
          (committeeVotes committees)) (raceLo rb) s) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head := by
  by_cases hcol : RootCollision
  · exact Or.inl hcol
  right
  -- One slot: from the honest heads before `s` to the honest heads of `s`.
  have hstep : ∀ s, raceLo rb ≤ s → s ≤ hi →
      (∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
        NodeBelow (run u t).store (.empty r) (run u t).head) →
      ∀ v, honest v → NodeBelow (run v s).store (.empty r) (run v s).head ∧
        ¬ NodeBelow (run v s).store (.full r) (run v s).head := by
    intro s hlo hs hP v hv
    have hQ := hset.runOkAt v hv s hlo hs
    by_cases hfirst : s = raceLo rb
    · subst hfirst
      have hnf := hset.first v hv
      rcases NodeBelow.pending_split _ r _ hQ.setting.1 hQ.setting.2 with h | h
      · exact ⟨h, hnf⟩
      · exact absurd h hnf
    · have hlos : raceLo rb < s := by omega
      have hahead := hset.weightAhead hw hset.runOkAt hcol v hv s hlos hs (hcount s hlos hs) hP
      have hinv := hQ.slotInv hw (hset.nodeOk v hv) hcol
      obtain ⟨jb, hjb, hjle⟩ := hQ.justified
      obtain ⟨s', hrun⟩ := hQ.headRun
      obtain ⟨havoid, hbelow⟩ := getHead_run_below_empty _ r hahead
        (hinv.justified_not_below hQ.block hjb hjle) _ s' _ hrun
      exact ⟨hbelow hQ.setting.1 hQ.setting.2, havoid⟩
  -- The induction over the slots of the window.
  have hall : ∀ s, s ≤ hi + 1 → ∀ u, honest u → ∀ t, raceLo rb ≤ t → t < s →
      NodeBelow (run u t).store (.empty r) (run u t).head := by
    intro s
    induction s with
    | zero => intro _ u _ t _ ht; omega
    | succ s ih =>
      intro hs u hu t hlo ht
      by_cases hts : t < s
      · exact ih (by omega) u hu t hlo hts
      · have hts' : t = s := by omega
        subst hts'
        exact (hstep t hlo (by omega) (ih (by omega)) u hu).1
  intro v hv t hlo ht
  exact hstep t hlo ht (hall t (by omega)) v hv

include hw in
/-- Tier T2 on the executable spec. Take the block `rb` at `r`, of slot `N`, and the window
of slots `N + 1 .. hi`, under `RaceSetting`. In every slot `s` of `(N + 1, hi]`, the honest
balance that has voted in `[N + 1, s)` is more than the adversarial balance that has voted
there, plus the proposer score `proposerScoreOf jst`. Then every honest head of the window
lies below `empty r` and not below `full r`, or a root collision exists.

This is `race_empty_persists_long` with the justified state `jst` on every slot
(`RaceSetting.toLong`). -/
theorem race_empty_persists_exec {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {hi : Nat} {jst : BeaconState} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : RaceSetting honest node run r rb hi jst nodeOf honestOf committees)
    (hcount : ∀ s, raceLo rb < s → s ≤ hi →
      advVoted (raceValidators (pureState jst) honestOf (committeeVotes committees)) (raceLo rb) s
        + proposerScoreOf (pureState jst)
        < honestVoted (raceValidators (pureState jst) honestOf (committeeVotes committees))
          (raceLo rb) s) :
    RootCollision ∨ ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ hi →
      NodeBelow (run v t).store (.empty r) (run v t).head ∧
        ¬ NodeBelow (run v t).store (.full r) (run v t).head :=
  race_empty_persists_long hw hset.toLong hcount

end Race

end EthCLSpecs.Proofs.Heze
