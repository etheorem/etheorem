import EthCLSpecs.Proofs.Heze.FinalizationLiveness
import EthCLSpecs.Proofs.Heze.ForkSupport

/-!
# `EthCLSpecs.Proofs.Heze.ForkSides`: the weights at the forks of the path to `r`

`get_head` (`gloas/fork-choice.md`) walks from the pending node of the justified root. At each
node `x` of the path to `pending r`, it must pick the path child `a` over every other viable
child `z`. This module proves that `a` is ahead of `z` on weight in an honest store of the
window. It works under `FinalitySetting`, once the honest votes before the slot come from heads
below `empty r` or at `pending r` (`VotesEmpty`). The race at `pending r` is the case
`x = pending r`, `a = empty r`, `z = full r` (`FinalitySetting.raceAhead`).

- `FinalitySetting.honest_latest`: the latest message of an honest validator in a store of the
  window. Its supported node lies below `empty r` when the message is from the window, by the
  induction hypothesis. Before the window, it lies on the path at or above `pending r`, below
  every node of the path that a message of its slot can support (`pathBefore`).
- `FinalitySetting.honest_supports`: an honest validator that votes at `supSlot a` or later
  supports the path child `a`.
- `FinalitySetting.sibling_adversarial`: a validator that supports another child `z` is
  adversarial, with a vote after the block of `x` (`sibling_supporters_late`).
- `FinalitySetting.forkAhead`: `weightAhead_pair` with the count `ForkCount`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState LawfulFcMap run_bind_eq_ok run_pure_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex SignedInclusionList ExecutionPayload Transaction ExecutionRequests Slot
  Attestation LatestMessage Gwei getSupportedNode isAncestor getWeight
  isPreviousSlotPayloadDecision getProposerScore getCurrentSlot getCommitteeIndices
  committeeCountOf getBeaconCommittee computeEpochAtSlot)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)
open EthCLSpecs.Proofs.Heze.PayloadRace (votedIn honestVoted advVoted votedIn_iff)

section Sides
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}

include hw in
/-- The latest message of `i` in a head run of the window comes from an attestation event of
the prefix (`NodeTrace.latest_source`), before the slot of the run
(`ClockedTrace.attestation_slot_le`). The store of the run holds the block at the vote root,
no later than the vote slot. This restates `RaceSetting.Fields.latest_window` under
`FinalitySetting`. -/
theorem FinalitySetting.latest_src
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (i : ValidatorIndex) (q : LatestMessage)
    (hq : FcMap.lookup (run v s).store.latestMessages i = some q) :
    ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool) (mid : Store map)
      (arr : List (SignedInclusionList × Bool)) (b : BeaconBlock),
      (run v s).events.map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
      NodeTrace (node v).seed es1 arr mid ∧ AttWrite mid att i ∧ q = attMessage att ∧
      att.data.slot.toNat < s ∧
      FcMap.lookup (run v s).store.blocks att.data.beaconBlockRoot = some b ∧
      b.slot ≤ att.data.slot := by
  have hBlk : ¬ HtrCollision BeaconBlock := fun h => hcol (Or.inr h)
  have hN := hset.fields.nodeOk v hv
  have hQ := hset.held v hv s hlo hs
  obtain ⟨rest, hsplit⟩ := hQ.isPrefix
  rcases hQ.trace.latest_source (StorePure.anchor _ _ _ hN.anchorStore) i q hq with h0 |
      ⟨es1, es2, att, fb, mid, arr, arrS, hes, htr, hsuf, hW, rfl⟩
  · rw [getForkchoiceStore_latest _ _ _ hN.anchorStore] at h0
    cases h0
  obtain ⟨cs1, u1, u1', hcs1, hge1⟩ := hW.clock
  obtain ⟨csB, hcsB, hcurB⟩ := hQ.slot
  have hle := hN.clocked.attestation_slot_le hsplit hQ.trace hQ.wall hQ.time hes htr hcs1 hcurB
  obtain ⟨b0, hb0, hb0slot⟩ := hW.block
  obtain ⟨b', hb'⟩ := hsuf.blocks_persist _ b0 hb0
  have hb0' : b0 = b' :=
    SlotInv.block_eq (hQ.slotInv_mid hw hN hes htr hcol) (hQ.slotInv hw hN hcol) hBlk hb0 hb'
  subst hb0'
  exact ⟨es1, es2, att, fb, mid, arr, b0, hes, htr, hW, rfl, by omega, hb', hb0slot⟩

include hw in
/-- **The latest message of an honest validator in a store of the window.** Take a head run of
slot `s` of the window, after the honest votes before `s` are on the EMPTY side (`VotesEmpty`).
The message is from the slot of the anchor block or later, and before `s`. When the message is
from the window, its supported node lies below `empty r`. When it is from before the window, its
supported node lies at or above `pending r`. It also lies below every node of the path that a
message of its slot can support (`pathBefore`).

The message is honest data on the head of the voter at its slot (`attester`, or `preDuties`
before the window). The supported node is `honestSupported` of that head (`getSupportedNode_honest`).
In the window, `NodeBelow.transfer` moves the head below `empty r` to the store of the run, and
`honest_supported_below_any` gives the supported node. -/
theorem FinalitySetting.honest_latest
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    (i : ValidatorIndex) (hhon : honestOf i = true) (q : LatestMessage)
    (hq : FcMap.lookup (run v s).store.latestMessages i = some q) :
    a.slot.toNat ≤ q.slot.toNat ∧ q.slot.toNat < s ∧
    ∀ (u u' : Store map) (m : ForkChoiceNode),
      (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
        (run v s).store q).run u = .ok (m, u') →
      (raceLo rb ≤ q.slot.toNat → NodeBelow (run v s).store (.empty r) m) ∧
      (q.slot.toNat < raceLo rb → NodeBelow (run v s).store m (.pending r) ∧
        ∀ y, NodeBelow (run v s).store y (.pending r) →
          supSlot (run v s).store y ≤ q.slot.toNat → NodeBelow (run v s).store y m) := by
  have hBlk : ¬ HtrCollision BeaconBlock := fun h => hcol (Or.inr h)
  have hN := hset.fields.nodeOk v hv
  have hQ := hset.held v hv s hlo hs
  have hinvB := hQ.slotInv hw hN hcol
  obtain ⟨es1', es2', att', fb', mid', arr', b0, hes', htr', hW, rfl, hlt', hb', hb0slot⟩ :=
    hset.latest_src hw hcol hv hlo hs i q hq
  -- The vote is from the slot of the anchor block on: its block is at least the anchor.
  have ha0 : a.slot ≤ b0.slot := by
    have := hinvB.anchor_le_slot _ _ hb'
    rwa [hset.anchorBlock v hv] at this
  have haS : a.slot.toNat ≤ att'.data.slot.toNat :=
    UInt64.le_iff_toNat_le.mp (UInt64.le_trans ha0 hb0slot)
  -- The message is honest data on the head of the voter at the vote slot.
  obtain ⟨A', hAI, hiA⟩ := hW.indices
  have hHD : HonestData (run (nodeOf i) att'.data.slot.toNat).store
      (run (nodeOf i) att'.data.slot.toNat).head att' := by
    by_cases hwin : raceLo rb ≤ att'.data.slot.toNat
    · exact hset.fields.attester v hv s (by omega) hs i hhon att' mid'
        ⟨es1', es2', fb', arr', hes', htr'⟩ ⟨A', hAI, (hset.fields.sort A' i).mp hiA⟩ hwin
        (by omega)
    · exact hset.preDuties.attester v hv s hlo hs i hhon att' mid'
        ⟨es1', es2', fb', arr', hes', htr'⟩ ⟨A', hAI, (hset.fields.sort A' i).mp hiA⟩ haS
        (by omega)
  obtain ⟨hroot, hbA, hhbA, hidx⟩ := hHD
  have hu := hset.fields.honestNode i hhon
  have hNu := hset.fields.nodeOk (nodeOf i) hu
  have hQu := hset.core (nodeOf i) hu att'.data.slot.toNat haS (by omega)
  have hinvA := hQu.slotInv hw hNu hcol
  have hbB : FcMap.lookup (run v s).store.blocks (run (nodeOf i) att'.data.slot.toNat).head.root
      = some b0 := hroot ▸ hb'
  have hbA' : hbA = b0 := SlotInv.block_eq hinvA hinvB hBlk hhbA hbB
  subst hbA'
  obtain ⟨sA, hrunA⟩ := hQu.headRun
  have hstatus := getHead_run_status _ _ _ _ hrunA
  have hmsg : attMessage att' =
      { slot := att'.data.slot, root := (run (nodeOf i) att'.data.slot.toNat).head.root,
        payloadPresent := honestAttestationIndex (run (nodeOf i) att'.data.slot.toNat).head
          hbA.slot att'.data.slot == 1 } := by
    unfold attMessage
    rw [hroot, hidx]
  refine ⟨haS, hlt', fun u0 u0' m hm => ⟨fun hwin => ?_, fun hpre => ?_⟩⟩
  · -- In the window: the head of the voter lies below `empty r`.
    simp only [attMessage] at hwin
    rw [hmsg] at hm
    have hQu' := hset.held (nodeOf i) hu att'.data.slot.toNat hwin (by omega)
    rcases (hV i hhon att'.data ⟨v, hv, s, hlo, hs, .inl ⟨att', mid', rfl, ⟨es1', es2', fb', arr',
        hes', htr'⟩, hW⟩⟩ hwin hlt').symm with hpend | hbelowA
    · -- A head at `pending r` supports `empty r`: the head block `rb` is before the vote.
      have hmeq := getSupportedNode_honest _ _ hbA hbB _ hm
      rw [hmeq, hpend]
      have hbr : hbA = rb := by
        rw [hpend, show (ForkChoiceNode.pending r).root = r from rfl, hQu'.block] at hhbA
        cases hhbA
        rfl
      subst hbr
      have hlt : hbA.slot.toNat < att'.data.slot.toNat := by unfold raceLo at hwin; omega
      unfold honestSupported
      rw [ite_eq_left hlt, ite_eq_right (fun h => payloadStatus_full_ne_pending h.symm)]
      exact .refl
    have hbelowB : NodeBelow (run v s).store (.empty r)
        (run (nodeOf i) att'.data.slot.toNat).head :=
      NodeBelow.transfer _ _ hinvA.slots r rb hQu'.block (node v).anchor
        (fun k x y hx hy => SlotInv.block_eq hinvA hinvB hBlk hx hy)
        (fun k x hx => hinvB.parentIn k x hx) hN.anchorSlot _ hbelowA (Or.inr ⟨hbA, hbB⟩)
    refine honest_supported_below_any _ (.empty r) att'.data.slot ?_ _ hbelowB hstatus hbA hbB
      hb0slot hm
    intro _ yb hyb
    rw [show (ForkChoiceNode.empty r).root = r from rfl, hQ.block] at hyb
    cases hyb
    rw [UInt64.lt_iff_toNat_lt]
    unfold raceLo at hwin
    omega
  · -- Before the window: `pathBefore` in the store of the run.
    simp only [attMessage] at hpre ⊢
    rw [hmsg] at hm
    have hmeq := getSupportedNode_honest _ _ hbA hbB _ hm
    subst hmeq
    exact (hset.pathBefore (nodeOf i) hu att'.data.slot.toNat haS hpre hbA hhbA v hv s hlo hs).2

/-- An index whose message supports a node below `d`, with a successful `supports` run at `d`,
is supported at `d`. `isAncestor_run_below_any` answers `true`. -/
theorem supportsVal_of_below (store : Store map) (hslots : SlotsIncrease store)
    (d : ForkChoiceNode) (db : BeaconBlock) (hdb : FcMap.lookup store.blocks d.root = some db)
    (i : ValidatorIndex) (lm : LatestMessage)
    (hlm : FcMap.lookup store.latestMessages i = some lm)
    (heq : store.equivocatingIndices.contains i = false)
    (hsup : ∀ (u u' : Store map) (n : ForkChoiceNode),
      (getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map)) store lm).run u
        = .ok (n, u') → NodeBelow store d n)
    (hok : ∃ (b : Bool) (u : Store map), (supports store d i).run store = .ok (b, u)) :
    supportsVal store d i = true := by
  obtain ⟨b, u, hb⟩ := hok
  have hb' := hb
  unfold supports at hb
  rw [hlm] at hb
  simp only [heq, Bool.false_eq_true, ite_false] at hb
  obtain ⟨n, w, hn, ha⟩ := run_bind_eq_ok _ _ _ _ hb
  have := isAncestor_run_below_any store hslots d db hdb n (hsup _ _ _ hn) ha
  subst this
  simp [supportsVal, hb']

/-- A node never lies above its own parent: the walk potential falls along an edge
(`NodeEdge.walkPot_lt`) and does not rise along a path (`NodeBelow.walkPot_le`). -/
theorem NodeEdge.not_below_parent (store : Store map) (hslots : SlotsIncrease store)
    {x z : ForkChoiceNode} (hxz : NodeEdge store x z)
    (hx : (FcMap.lookup store.blocks x.root).isSome) (hzx : NodeBelow store z x) : False := by
  obtain ⟨hz, hlt⟩ := NodeEdge.walkPot_lt store hslots hxz hx
  have hle := (NodeBelow.walkPot_le store hslots hzx hz).2
  omega

/-- Every run of `isPreviousSlotPayloadDecision` at a pending node answers `false`: the test
asks for a payload status. -/
theorem isPreviousSlotPayloadDecision_run_pending (store : Store map) (k : Root)
    {t t' : Store map} {b : Bool}
    (h : (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
      store (.pending k)).run t = .ok (b, t')) :
    b = false := by
  unfold isPreviousSlotPayloadDecision at h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  rw [run_pure_eq_ok _ _ _ _ h]
  simp [ForkChoiceNode.pending, EthCLSpecs.Heze.Const.payloadStatusPending,
    EthCLSpecs.Heze.Const.payloadStatusEmpty, EthCLSpecs.Heze.Const.payloadStatusFull]

/-- A child `c` of a node `x` whose block `xb` is two or more slots before the current slot is
off the decision slot. A payload child has the block of `x`
(`isPreviousSlotPayloadDecision_run_false`). A pending child is never a payload decision. -/
theorem NodeEdge.offDecision (store : Store map) {x c : ForkChoiceNode} (hxc : NodeEdge store x c)
    {xb : BeaconBlock} (hxb : FcMap.lookup store.blocks x.root = some xb) (cs : Slot)
    (hcur : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
      = .ok (cs, store))
    (hlt : xb.slot.toNat + 1 < cs.toNat) :
    ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store c).run t = .ok (b, t') → b = false := by
  rcases NodeEdge.cases_on_child store x c hxc with ⟨hp, -⟩ | ⟨k, -, -, -, hck, -⟩
  · have hcb : FcMap.lookup store.blocks c.root = some xb := by
      rw [show c.root = x.root by rw [hp]; rfl]
      exact hxb
    exact isPreviousSlotPayloadDecision_run_false store c xb cs hcb hcur hlt
  · subst hck
    intro t t' b h
    exact isPreviousSlotPayloadDecision_run_pending store k h

include hw in
/-- **An honest validator that votes at `supSlot y` or later supports the path child `y`.** Take
a node `y` of the path at or above `pending r`, or `empty r`. Take an honest validator in a
committee of a slot `t`, with `supSlot y ≤ t < s`. Its vote reaches the node (`deliver`, or
`preDuties.deliver` before the window). So its latest message has a slot of `t` or later
(`onAttestation_delivers`, `NodeTrace.latest_mono`). The supported node of that message lies
below `y` (`FinalitySetting.honest_latest`). The premise is a successful `supports` run at
`y`. -/
theorem FinalitySetting.honest_supports
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    {y : ForkChoiceNode} (hy : NodeBelow (run v s).store y (.pending r) ∨ y = .empty r)
    {yb : BeaconBlock} (hyb : FcMap.lookup (run v s).store.blocks y.root = some yb)
    (i : ValidatorIndex) (hhon : honestOf i = true) (t : Nat)
    (hty : supSlot (run v s).store y ≤ t) (htA : a.slot.toNat ≤ t) (hts : t < s)
    (hvote : committeeVotes committees i t = true)
    (hok : ∃ (b : Bool) (u : Store map),
      (supports (run v s).store y i).run (run v s).store = .ok (b, u)) :
    supportsVal (run v s).store y i = true := by
  have hN := hset.fields.nodeOk v hv
  have hQ := hset.held v hv s hlo hs
  have hinvB := hQ.slotInv hw hN hcol
  have hsigner : HonestSigner (node v).seed ((run v s).events.map Prod.fst) i := by
    by_cases hs1 : raceLo rb < s
    · exact hset.fields.signer v hv s hs1 hs i hhon
    · have : s = raceLo rb := by omega
      subst this
      exact hset.preDuties.signer v hv i hhon
  -- The vote of slot `t` reaches the node, so the latest message has at least slot `t`.
  obtain ⟨es1, es2, att, fb, hes, hslot, hatt⟩ :
      ∃ (es1 es2 : List TraceEvent) (att : Attestation) (fb : Bool),
        (run v s).events.map Prod.fst = es1 ++ TraceEvent.handler (.attestation att fb) :: es2 ∧
        att.data.slot.toNat = t ∧
        ∀ arr mid, NodeTrace (node v).seed es1 arr mid → ∀ A, AttIndices mid att A → i ∈ A := by
    by_cases htw : raceLo rb ≤ t
    · exact hset.fields.deliver v hv s (by omega) hs i hhon t htw hts hvote
    · exact hset.preDuties.deliver v hv s hlo hs i hhon t htA (by omega) hts hvote
  obtain ⟨mid, arr1, arr2, h1, h2, -⟩ := hQ.trace.split hes
  obtain ⟨post, a1, a2, hsingle, hrest, -⟩ :=
    h2.split (es1 := [TraceEvent.handler (.attestation att fb)]) (es2 := es2) rfl
  have hneMid : mid.equivocatingIndices.contains i = false := by
    have := honest_not_equivocating hN.anchorStore h1 i
      (by rw [hes] at hsigner; exact hsigner.prefix)
    simpa using this
  obtain ⟨q0, hq0, hle0⟩ := onAttestation_delivers hset.fields.sort att fb mid post
    (hN.storePure h1) hsingle.single_handler i (hatt arr1 mid h1) hneMid
  obtain ⟨q, hq, hle1⟩ := hrest.latest_mono i q0 hq0
  have hqt : t ≤ q.slot.toNat := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans hle0 hle1)
    omega
  obtain ⟨-, -, hm⟩ := hset.honest_latest hw hcol hv hlo hs hV i hhon q hq
  refine supportsVal_of_below _ hinvB.slots y yb hyb i q hq ?_ ?_ hok
  · have := honest_not_equivocating hN.anchorStore hQ.trace i hsigner
    simpa using this
  · intro u u' m hsup
    obtain ⟨hwin, hpre⟩ := hm u u' m hsup
    by_cases hqw : raceLo rb ≤ q.slot.toNat
    · -- In the window: below `empty r`, and `y` lies above `empty r`.
      have hE := hwin hqw
      rcases hy with hy | rfl
      · exact NodeBelow.trans _ _ _ _ (NodeBelow.step _ _ hy (NodeEdge.empty r)) hE
      · exact hE
    · -- Before the window: `y` is not `empty r`, whose support starts in the window.
      rcases hy with hy | rfl
      · exact (hpre (by omega)).2 y hy (by omega)
      · exfalso
        have : supSlot (run v s).store (.empty r) = rb.slot.toNat + 1 := by
          simp [supSlot, hQ.block, ForkChoiceNode.empty, payloadStatus_empty_ne_pending]
        unfold raceLo at hqw
        omega

include hw in
/-- **A validator that supports another child of the fork is adversarial, with a vote after the
fork block.** Take a node `x` with the path child `y` (at or above `pending r`, or `empty r`) and
another child `z`. A message that supports `z` is from a slot after the block of `x`
(`sibling_supporters_late`). An honest message supports a node below `empty r` or on the path
(`FinalitySetting.honest_latest`). Neither node lies below `z`. Two children of one node share
no node below them (`NodeEdge.siblings_disjoint`), and a node never lies above its parent. The
validator is in a committee of the vote slot (`committee`, or `preDuties.committee`). -/
theorem FinalitySetting.sibling_adversarial
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    {x y z : ForkChoiceNode} (hxy : NodeEdge (run v s).store x y)
    (hxz : NodeEdge (run v s).store x z) (hne : y ≠ z)
    (hy : NodeBelow (run v s).store y (.pending r) ∨ y = .empty r)
    {xb : BeaconBlock} (hxb : FcMap.lookup (run v s).store.blocks x.root = some xb)
    (i : ValidatorIndex) (hz : supportsVal (run v s).store z i = true) :
    honestOf i = false ∧ votedIn (committeeVotes committees i) (xb.slot.toNat + 1) s = true := by
  have hN := hset.fields.nodeOk v hv
  have hQ := hset.held v hv s hlo hs
  have hinvB := hQ.slotInv hw hN hcol
  have hslots := hinvB.slots
  have hx : (FcMap.lookup (run v s).store.blocks x.root).isSome := by rw [hxb]; rfl
  obtain ⟨lm, m, u, u', hlm, hm, hzm⟩ := supportsVal_below _ z i hz
  obtain ⟨es1', es2', att', fb', mid', arr', b0, hes', htr', hW, hq, hlt', hb', hb0slot⟩ :=
    hset.latest_src hw hcol hv hlo hs i lm hlm
  subst hq
  have hmsg : ∀ b, FcMap.lookup (run v s).store.blocks (attMessage att').root = some b →
      b.slot ≤ (attMessage att').slot := by
    intro b hb
    have hb'' : FcMap.lookup (run v s).store.blocks att'.data.beaconBlockRoot = some b := hb
    rw [hb'] at hb''
    cases hb''
    exact hb0slot
  have hgt := sibling_supporters_late _ hslots hxz hxb _ hmsg hm hzm
  have hgt' : xb.slot.toNat + 1 ≤ att'.data.slot.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp hgt
    simp only [attMessage] at this
    omega
  refine ⟨?_, ?_⟩
  · -- An honest message does not support `z`.
    cases hh : honestOf i
    · rfl
    · exfalso
      obtain ⟨-, -, hfacts⟩ := hset.honest_latest hw hcol hv hlo hs hV i hh _ hlm
      obtain ⟨hwin, hpre⟩ := hfacts u u' m hm
      by_cases hqw : raceLo rb ≤ (attMessage att').slot.toNat
      · have hE := hwin hqw
        have hym : NodeBelow (run v s).store y m := by
          rcases hy with hy | rfl
          · exact NodeBelow.trans _ _ _ _ (NodeBelow.step _ _ hy (NodeEdge.empty r)) hE
          · exact hE
        exact NodeEdge.siblings_disjoint _ hslots hxy hxz hne hx hym hzm
      · have hzr : NodeBelow (run v s).store z (.pending r) :=
          NodeBelow.trans _ _ _ _ hzm (hpre (by omega)).1
        rcases hy with hy | rfl
        · exact NodeEdge.siblings_disjoint _ hslots hxy hxz hne hx hy hzr
        · -- `x` is `pending r`, the one parent of `empty r`.
          have hxr : x = .pending r :=
            NodeEdge.parent_unique _ x (.pending r) (.empty r) hxy (NodeEdge.empty r)
          subst hxr
          exact NodeEdge.not_below_parent _ hslots hxz hx hzr
  · -- The validator is in a committee of the vote slot.
    have ha0 : a.slot ≤ b0.slot := by
      have := hinvB.anchor_le_slot _ _ hb'
      rwa [hset.anchorBlock v hv] at this
    have haS : a.slot.toNat ≤ att'.data.slot.toNat :=
      UInt64.le_iff_toNat_le.mp (UInt64.le_trans ha0 hb0slot)
    obtain ⟨A', ⟨cps, s2, ts, hmid, hts, hA⟩, hiA⟩ := hW.indices
    obtain ⟨ci, c, hciIn, hc, hic⟩ :=
      getAttestingIndices_mem ts att' A' hA i ((hset.fields.sort A' i).mp hiA)
    have hcomm : (∀ ci ∈ getCommitteeIndices att'.committeeBits,
          ci < committeeCountOf (pureState ts) (computeEpochAtSlot att'.data.slot)) ∧
        ∀ ci, if ci < committeeCountOf (pureState ts) (computeEpochAtSlot att'.data.slot)
          then getBeaconCommittee (pureState ts) att'.data.slot ci
            = .ok (committees att'.data.slot.toNat ci)
          else committees att'.data.slot.toNat ci = #[] := by
      by_cases hw' : raceLo rb ≤ att'.data.slot.toNat
      · exact hset.fields.committee v hv s (by omega) hs att' mid'
          ⟨es1', es2', fb', arr', hes', htr'⟩ hw' (by omega) cps s2 ts hmid hts
      · exact hset.preDuties.committee v hv s hlo hs att' mid'
          ⟨es1', es2', fb', arr', hes', htr'⟩ haS (by omega) cps s2 ts hmid hts
    obtain ⟨hrange, hcomm⟩ := hcomm
    have hcomm' := hcomm ci
    rw [ite_eq_left (hrange ci hciIn)] at hcomm'
    have hceq : c = committees att'.data.slot.toNat ci := by
      have h2 := hc.symm.trans hcomm'
      injection h2
    refine (votedIn_iff _ _ _).mpr ⟨att'.data.slot.toNat, hgt', hlt', ?_⟩
    simp only [committeeVotes, decide_eq_true_eq]
    exact ⟨ci, hceq ▸ hic⟩

include hw in
/-- **The path child is ahead of every other child on weight.** Take a head run of slot `s` of
the window, after the honest votes before `s` are on the EMPTY side. Take a fork `x` of the path
with the path child `y` and another child `z`. The block `xb` of `x` is two or more slots before
`s`. The count `ForkCount` holds, with the honest window from `supSlot y` and the adversarial
window from the slot after `xb`. Then every pair of weight runs puts `y` strictly ahead of `z`
(`weightAhead_pair`). -/
theorem FinalitySetting.forkAhead
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf s)
    {jst : BeaconState}
    (hjst : FcMap.lookup (run v s).store.checkpointStates (run v s).store.justifiedCheckpoint
      = some (pureState jst))
    {x y z : ForkChoiceNode} (hxy : NodeEdge (run v s).store x y)
    (hxz : NodeEdge (run v s).store x z) (hne : y ≠ z)
    (hy : NodeBelow (run v s).store y (.pending r) ∨ y = .empty r)
    {yb : BeaconBlock} (hyb : FcMap.lookup (run v s).store.blocks y.root = some yb)
    {xb : BeaconBlock} (hxb : FcMap.lookup (run v s).store.blocks x.root = some xb)
    (hoff : xb.slot.toNat + 1 < s) (hyA : a.slot.toNat ≤ supSlot (run v s).store y)
    (hcount : ForkCount jst honestOf committees (supSlot (run v s).store y)
      (xb.slot.toNat + 1) s) :
    ∀ (s₁ s₁' s₂ s₂' : Store map) (wY wZ : Gwei),
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) (run v s).store y).run s₁
        = .ok (wY, s₁') →
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) (run v s).store z).run s₂
        = .ok (wZ, s₂') →
      wZ < wY := by
  have hN := hset.fields.nodeOk v hv
  have hQ := hset.held v hv s hlo hs
  have hinvB := hQ.slotInv hw hN hcol
  have hx : (FcMap.lookup (run v s).store.blocks x.root).isSome := by rw [hxb]; rfl
  obtain ⟨cs, hcsn, hcur⟩ := hQ.slot
  have hlt : xb.slot.toNat + 1 < cs.toNat := by omega
  refine weightAhead_pair _ hinvB.slots hxy hxz hne hx (hN.storePure hQ.trace) honestOf
    (committeeVotes committees) (supSlot (run v s).store y) (xb.slot.toNat + 1) s
    (proposerScoreOf (pureState jst)) jst hjst (NodeEdge.offDecision _ hxy hxb cs hcur hlt)
    (NodeEdge.offDecision _ hxz hxb cs hcur hlt)
    (fun _ _ _ hps => Nat.le_of_eq (getProposerScore_run_eq _ jst hjst hps)) ?_ ?_ hcount
  · intro i _ _ hh hvoted hok
    obtain ⟨t, htlo, hts, hvote⟩ := (votedIn_iff _ _ _).mp hvoted
    exact hset.honest_supports hw hcol hv hlo hs hV hy hyb i hh t htlo (by omega) hts hvote hok
  · intro i hz
    exact hset.sibling_adversarial hw hcol hv hlo hs hV hxy hxz hne hy hxb i hz

include hw in
/-- **The race weight at `r`.** `FinalitySetting.forkAhead` at `x = pending r`, with the path
child `empty r` and the other child `full r`. Both windows start at `raceLo rb`, so the count is
`RaceCount`. -/
theorem FinalitySetting.raceAhead
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees) :
    RaceAhead honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁) := by
  intro hcol s hlos hs hV _ v hv hjust
  obtain ⟨jb, hjb, hjle⟩ := hjust
  have hlo : raceLo rb ≤ s := Nat.le_of_lt hlos
  have hQ := hset.held v hv s hlo hs
  rcases hset.cases v hv s hlo hs with ⟨jst, -, hjst, hcount, -⟩ | ⟨jb', hjb', hjlt⟩
  · have hsup : supSlot (run v s).store (.empty r) = raceLo rb := by
      simp [supSlot, hQ.block, ForkChoiceNode.empty, payloadStatus_empty_ne_pending, raceLo]
    have hc := hcount hlos
    refine hset.forkAhead hw hcol hv hlo hs hV hjst (NodeEdge.empty r) (NodeEdge.full r)
      (fun h => payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h))
      (.inr rfl) hQ.block hQ.block (by unfold raceLo at hlos; omega)
      (by rw [hsup]; exact Nat.le_of_lt (hset.anchor_lt hv)) ?_
    rw [hsup]
    exact hc
  · rw [hjb] at hjb'
    cases hjb'
    exact absurd hjle (UInt64.not_le.mpr hjlt)

end Sides

end EthCLSpecs.Proofs.Heze
