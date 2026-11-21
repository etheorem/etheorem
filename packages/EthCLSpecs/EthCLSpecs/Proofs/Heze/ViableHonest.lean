import EthCLSpecs.Proofs.Heze.FinalizationLiveness
import EthCLSpecs.Proofs.Heze.ViableWindow
import EthCLSpecs.Proofs.Heze.KeyPrefix

/-!
# `EthCLSpecs.Proofs.Heze.ViableHonest`: EMPTY `r` stays viable at the honest heads

`ViableStep` asks, at each honest head run of the window whose justified block is no later than
`rb`, that EMPTY `r` is in the filtered tree whenever FULL `r` is. This module proves it at one
head run, in two cases by the epoch `E` of the run.

- `E` is the epoch of `rb`. Every node below `pending r` reads the voting source of `r`, and the
  finalized epoch starts before `rb` (`viable_same_epoch`).
- `E` is later. The carrier chain holds a block `T` of epoch `E - 1` below EMPTY `r`, and the
  node holds it. Every leaf below `T` passes the leaf check (`viable_store_core`).

Two theorems use it. `censored_payload_avoided` takes the carrier chain alone
(`CarrierWindow`): FULL `r` stays off every honest head of the window.
`censored_payload_final_carrier` adds a block of the carrier chain after `rb` by the first slot
of `E₁` and the delivery of its last block of `E₁ + 3` (`LastDelivered`), for the finality lock.
Neither theorem asks the honest heads to follow the carrier chain.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState pureState_inj runPure LawfulFcMap)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Checkpoint ForkChoiceNode
  ValidatorIndex SignedBeaconBlock ExecutionPayload Transaction ExecutionRequests getCheckpointBlock
  Epoch Slot isPayloadVerified AttestationData)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

/-! ## The store of an honest head run -/

section Store
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- **The invariants of the store of an honest head run.** Each holds at the anchor store and
each handler keeps it, unless a root collision exists. -/
theorem HeadRun.Core.viableInvs (hcol : ¬ RootCollision) {n : NodeRun map} {q : HeadRun map}
    {rb : BeaconBlock} {t : Nat} (hn : n.Honest rb) (hq : q.Core n t)
    (hord : StateCkptOrd n.anchorState)
    (hsr : ∀ (sb : SignedBeaconBlock) (w : Nat), (TraceEvent.handler (.block sb), w) ∈ n.events →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) :
    CkptInv n.anchorState n.anchor q.store ∧ UnrealInv (htr n.anchor) q.store ∧
      UnrealKeys q.store ∧ StateLink (htr n.anchor) q.store ∧ FullVerified q.store := by
  have hev : ∀ e, TraceEvent.handler e ∈ q.events.map Prod.fst → e.NotAtAnchorParent n.anchor :=
    fun e he => by
      obtain ⟨w, hw'⟩ := hq.mem_events e he
      exact hn.noAnchorParent e w hw'
  have hinv : CkptInv n.anchorState n.anchor q.store := by
    rcases NodeTrace.ckptInv hw hq.trace
        (CkptInv.anchor _ _ _ hn.anchorStore hn.anchorSelf) hord hev
        (fun sb he => by
          obtain ⟨w, hw'⟩ := hq.mem_events _ he
          exact hsr sb w hw') with hi | hc
    · exact hi
    · exact absurd hc hcol
  have hunr : UnrealInv (htr n.anchor) q.store :=
    hq.trace.unrealInv (UnrealInv.anchor _ _ _ hn.anchorStore)
  have hkeys : UnrealKeys q.store :=
    hq.trace.unrealKeys (BlockStatesPure.anchor _ _ _ hn.anchorStore)
      (UnrealKeys.anchor _ _ _ hn.anchorStore)
  have hlink : StateLink (htr n.anchor) q.store := by
    rcases NodeTrace.stateLink hw hq.trace
        (SlotInv.anchor _ _ _ hn.anchorStore hn.anchorSelf)
        (StateLink.anchor _ _ _ hn.anchorStore) hev with ⟨-, hl⟩ | hc
    · exact hl
    · exact absurd hc hcol
  have hfv : FullVerified q.store := by
    rcases NodeTrace.fullVerified hw hq.trace
        (SlotInv.anchor _ _ _ hn.anchorStore hn.anchorSelf)
        (FullVerified.anchor _ _ _ hn.anchorStore hn.anchorSelf) hev with ⟨-, hf⟩ | hc
    · exact hf
    · exact absurd hc hcol
  exact ⟨hinv, hunr, hkeys, hlink, hfv⟩

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] [CryptoBackend]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- The last block of an ancestor path is the block at its root, and an empty path ends at the
anchor root. -/
theorem AncestorPath.last {a : BeaconBlock} {store : Store map} {k : Root} {L : List BeaconBlock}
    (h : AncestorPath a store k L) :
    (L = [] → k = htr a) ∧ ∀ L' x, L = L' ++ [x] → FcMap.lookup store.blocks k = some x := by
  cases h with
  | anchor => exact ⟨fun _ => rfl, fun L' x he => absurd he.symm (by simp)⟩
  | cons hk _ _ =>
    refine ⟨fun he => absurd he (by simp), fun L' x he => ?_⟩
    have := (List.append_inj' he rfl).2
    rw [List.singleton_inj] at this
    rw [← this]
    exact hk

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] in
/-- **A stored block other than the anchor has a nonzero state root.** Its stored state ends a
validated store run along its ancestor path (`CkptInv.chains`). The run ends at that block, and
a validated block step has a nonzero state root. -/
theorem CkptInv.stateRoot_ne {A : BeaconState} {a : BeaconBlock} {store : Store map}
    (hinv : CkptInv A a store) (hlink : StateLink (htr a) store) :
    ∀ k b, FcMap.lookup store.blocks k = some b → k ≠ htr a →
      b.stateRoot ≠ EthCLSpecs.Heze.zeroRoot := by
  intro k b hk hne
  obtain ⟨-, -, w, -, -, hw, -⟩ := hlink k b hk hne
  obtain ⟨steps, -, hpath, hval, hend⟩ := hinv.chains k w hw
  obtain ⟨h0, h1⟩ := hpath.last
  rcases hend with rfl | ⟨p, sb, v, rfl⟩
  · exact absurd (h0 rfl) hne
  · rw [blocksOf_append_block] at h1
    have hb := h1 _ _ rfl
    rw [hk] at hb
    cases hb
    exact (hval sb v (List.mem_append_right _ (List.mem_singleton_self _))).2

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] in
/-- **The path from the justified root to EMPTY `r`, when the filtered tree holds FULL `r`.** The
walk keeps only nodes below the justified root (`go_result_below`). The only edge into FULL `r`
comes from `pending r`, which has EMPTY `r` as a child too. A FULL node above EMPTY `r` is above
`pending r`, so its payload is verified (`FullVerified.path`). -/
theorem justified_path_of_full (store : Store map) (hfv : FullVerified store) (r : Root)
    {nodes : Array ForkChoiceNode} {t t' : Store map}
    (hrun : (EthCLSpecs.Heze.getFilteredNodeTree (StoreTransition := ForkChoiceStoreRun (Store map))
      store).run t = .ok (nodes, t'))
    (hfull : nodes.contains (.full r) = true) :
    NodeBelow store (.pending store.justifiedCheckpoint.root) (.empty r) ∧
      ∀ z, NodeBelow store (.pending store.justifiedCheckpoint.root) (.full z) →
        NodeBelow store (.full z) (.empty r) → isPayloadVerified store z = true := by
  have hrun' : (EthCLSpecs.Heze.filterNodeTree.go (StoreTransition := ForkChoiceStoreRun (Store map))
      store (2 * (FcMap.keys store.blocks).length + 2)
      (.pending store.justifiedCheckpoint.root)).run t = .ok (nodes, t') := hrun
  obtain ⟨ht, -⟩ := (filterNodeTree_go_stateFree store _ _).run_eq hrun'
  subst t'
  have hJF := go_result_below store _ _ t nodes hrun' (.full r) (Array.contains_iff_mem.mp hfull)
  have hJP : NodeBelow store (.pending store.justifiedCheckpoint.root) (.pending r) :=
    below_decided_pending hJF payloadStatus_full_ne_pending
      (fun h => payloadStatus_full_ne_pending (congrArg ForkChoiceNode.payloadStatus h).symm)
  refine ⟨.step _ _ hJP (NodeEdge.empty r), fun z _ hz => ?_⟩
  exact hfv.path z r (below_decided_pending hz payloadStatus_empty_ne_pending
    (fun h => payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h).symm))

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] [CryptoBackend]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- **No node below a block at or after the anchor has the anchor root, but the block's own.** A
node below `pending x` with another root holds a block later than `x`'s (`below_slot_gt`). The
block at the anchor root is the anchor, which is no later than `x`'s block. -/
theorem below_not_anchor {store : Store map} {a : BeaconBlock} (hslot : SlotInv a store)
    (hcb : ¬ HtrCollision BeaconBlock) {x : Root} {xb : BeaconBlock}
    (hx : FcMap.lookup store.blocks x = some xb) (hax : a.slot ≤ xb.slot) :
    ∀ y, NodeBelow store (.pending x) y → y.root = htr a → y.root = x := by
  intro y hy hya
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨yb, hyb, hlt⟩ := below_slot_gt store hslot.slots hx hy hne
  rw [hya] at hyb
  have hat := hslot.atRoot _ _ hyb
  have hyba : yb = a := Classical.byContradiction fun h => hcb ⟨yb, a, h, hat⟩
  subst hyba
  exact absurd (UInt64.lt_of_le_of_lt hax hlt) (UInt64.lt_irrefl _)

/-- The current store epoch of a head run of slot `t`, read at any runner state. -/
theorem HeadRun.Core.storeEpoch {n : NodeRun map} {q : HeadRun map} {t : Nat}
    (hq : q.Core n t) :
    ∃ E : Epoch, E.toNat = t / slotsPerEpoch ∧
      ∀ u, (EthCLSpecs.Heze.getCurrentStoreEpoch (StoreTransition := ForkChoiceStoreRun (Store map))
        q.store).run u = .ok (E, u) := by
  obtain ⟨cs, hcsn, hcs0⟩ := hq.slot
  have hcs : ∀ u, (EthCLSpecs.Heze.getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
      q.store).run u = .ok (cs, u) := ((getCurrentSlot_stateFree q.store).run_eq hcs0).2
  refine ⟨EthCLSpecs.Heze.computeEpochAtSlot cs, by rw [computeEpochAtSlot_toNat, hcsn], fun u => ?_⟩
  unfold EthCLSpecs.Heze.getCurrentStoreEpoch
  rw [EthCLLib.Proofs.run_bind, hcs u, EthCLLib.Proofs.except_bind_ok]
  rfl

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] in
/-- **The start slot of the finalized epoch.** The finalized epoch is the anchor epoch or before
the epoch of the run (`finalized_epoch_le`), so its start slot fits in a slot. It is before the
block `rb` once `rb` is past the anchor epoch, and `rb` is in the epoch of the run or later than
the first slot of the finalized epoch's successor. -/
theorem HeadRun.Core.finalizedStart {n : NodeRun map} {q : HeadRun map}
    {rb : BeaconBlock} {t : Nat} (hn : n.Honest rb) (hq : q.Core n t)
    (hinv : CkptInv n.anchorState n.anchor q.store) (hord : StateCkptOrd n.anchorState)
    (hlo : rb.slot.toNat < t) (ht : t < 2 ^ 64)
    (hA : n.anchorState.slot.toNat / slotsPerEpoch ≤ t / slotsPerEpoch) :
    ∃ S : Slot, (EthCLSpecs.Heze.computeStartSlotAtEpoch q.store.finalizedCheckpoint.epoch :
        Except StateTransitionError Slot) = .ok S ∧
      S.toNat = q.store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch ∧
      (q.store.finalizedCheckpoint.epoch.toNat = n.anchorState.slot.toNat / slotsPerEpoch ∨
        q.store.finalizedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch - 1) := by
  have hp := slotsPerEpochPos
  have hblocks : ∀ k b, FcMap.lookup q.store.blocks k = some b → b.slot.toNat ≤ t :=
    fun k b hk => hq.block_slot_le hn (hn.anchor_le_of_lt hlo) hk
  have hF : q.store.finalizedCheckpoint.epoch.toNat = n.anchorState.slot.toNat / slotsPerEpoch ∨
      q.store.finalizedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch - 1 := by
    rcases finalized_epoch_le hinv hord hA hblocks with h | h
    · left
      rw [h]
      exact currentEpochOf_toNat n.anchorState
    · exact .inr h
  have hle : q.store.finalizedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch := by
    rcases hF with h | h
    · rw [h]
      exact hA
    · exact Nat.le_trans h (Nat.sub_le _ _)
  have hfit : q.store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch < 2 ^ 64 := by
    have := Nat.mul_le_mul_right slotsPerEpoch hle
    have := Nat.div_mul_le_self t slotsPerEpoch
    omega
  refine ⟨_, computeStartSlotAtEpoch_ok_of_lt hfit, ?_, hF⟩
  have hn : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
  rw [UInt64.toNat_mul, hn, Nat.mod_eq_of_lt hfit]

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] [CryptoBackend]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- **The checkpoint block of a node below `pending r`, at an epoch that starts at or after
`rb`.** The walk stops at the first block on the way up that is no later than the start slot
`S`. The block `rb` is no later than `S`, so the walk stops at `r` or at a block of the path
from `r`. A block edge to a block after `S` keeps the checkpoint block of the parent
(`getCheckpointBlock_child_eq`). A block edge to a block no later than `S` stops the walk
there (`getCheckpointBlock_run_stop`). -/
theorem cb_on_path (store : Store map) (hslots : SlotsIncrease store) {r : Root}
    {rb : BeaconBlock} (hrb : FcMap.lookup store.blocks r = some rb) (e : Epoch) (S : Slot)
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch e : Except StateTransitionError Slot) = .ok S)
    (hrS : ¬ rb.slot > S) {x : ForkChoiceNode} (hx : NodeBelow store (.pending r) x) :
    ∃ y, (y = r ∨ (y ≠ r ∧ NodeBelow store (.pending r) (.pending y) ∧
        NodeBelow store (.pending y) x ∧
        ∃ yb, FcMap.lookup store.blocks y = some yb ∧ ¬ yb.slot > S)) ∧
      ∀ u, (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store x.root
        e).run u = .ok (y, u) := by
  induction hx with
  | refl => exact ⟨r, .inl rfl, getCheckpointBlock_run_stop store r rb hrb e S hS hrS⟩
  | step p c hpd hedge ih =>
    obtain ⟨y, hy, hcb⟩ := ih
    -- An EMPTY or FULL edge keeps the root.
    have keep : ∀ c', c'.root = p.root → NodeEdge store p c' →
        ∃ y, (y = r ∨ (y ≠ r ∧ NodeBelow store (.pending r) (.pending y) ∧
          NodeBelow store (.pending y) c' ∧
          ∃ yb, FcMap.lookup store.blocks y = some yb ∧ ¬ yb.slot > S)) ∧
        ∀ u, (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store
          c'.root e).run u = .ok (y, u) := fun c' hc' he => by
      refine ⟨y, ?_, by rw [hc']; exact hcb⟩
      rcases hy with h | ⟨h1, h2, h3, h4⟩
      · exact .inl h
      · exact .inr ⟨h1, h2, .step _ _ h3 he, h4⟩
    cases hedge with
    | empty root => exact keep _ rfl (NodeEdge.empty root)
    | full root => exact keep _ rfl (NodeEdge.full root)
    | block _ root b s s' hb hpar hps =>
      have hedge := NodeEdge.block p root b s s' hb hpar hps
      obtain ⟨pb, hpb⟩ := below_stored hpd hrb
      have hlt : pb.slot < b.slot := hslots root b pb hb (hpar ▸ hpb)
      -- The parent's block is `rb` or later, so the child is later than `rb`.
      have hpr : ¬ rb.slot > pb.slot := by
        by_cases hpr : p.root = r
        · rw [hpr, hrb] at hpb
          cases hpb
          exact UInt64.lt_irrefl _
        · obtain ⟨yb, hyb, hgt⟩ := below_slot_gt store hslots hrb hpd hpr
          rw [hpb] at hyb
          cases hyb
          exact UInt64.not_lt.mpr (UInt64.le_of_lt hgt)
      by_cases hsl : S < b.slot
      · refine ⟨y, ?_, fun u => (getCheckpointBlock_child_eq store hslots hpb hb hpar e S hS hsl u).trans
          (hcb u)⟩
        rcases hy with h | ⟨h1, h2, h3, h4⟩
        · exact .inl h
        · exact .inr ⟨h1, h2, .step _ _ h3 hedge, h4⟩
      · have hne : root ≠ r := fun h => by
          rw [h, hrb] at hb
          cases hb
          exact hpr hlt
        exact ⟨root, .inr ⟨hne, .step _ _ hpd hedge, .refl, b, hb, hsl⟩,
          getCheckpointBlock_run_stop store root b hb e S hS hsl⟩

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] [CryptoBackend]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- **The finalized root read by a passing leaf below FULL `r`.** The finalized epoch is not
genesis and starts at `S`, at or after `rb`. The leaf `dF` passes the finalized test, so the
finalized root is its checkpoint block (`cb_on_path`). That block is `r`, or a block after `rb`
and no later than `S` on the FULL side of `r`: it is above `dF`, and a block above FULL `r` is
no later than `rb` (`NodeBelow.comparable`, `NodeBelow.slot_le`). -/
theorem finRoot_of_full (store : Store map) (hslots : SlotsIncrease store) {r : Root}
    {rb : BeaconBlock} (hrb : FcMap.lookup store.blocks r = some rb) {S : Slot}
    (hS : (EthCLSpecs.Heze.computeStartSlotAtEpoch store.finalizedCheckpoint.epoch :
      Except StateTransitionError Slot) = .ok S)
    (hrS : ¬ S < rb.slot)
    (hg : store.finalizedCheckpoint.epoch ≠ EthCLSpecs.Heze.Const.genesisEpoch)
    {dF : ForkChoiceNode} (hdF : NodeBelow store (.full r) dF)
    (hfF : ∀ u, (finRead store dF.root).run u = .ok (true, u)) :
    store.finalizedCheckpoint.root = r ∨
      (NodeBelow store (.full r) (.pending store.finalizedCheckpoint.root) ∧
        ∃ fb, FcMap.lookup store.blocks store.finalizedCheckpoint.root = some fb ∧
          rb.slot < fb.slot ∧ ¬ fb.slot > S) := by
  have hdFr : NodeBelow store (.pending r) dF :=
    NodeBelow.trans store _ _ _ (.step _ _ .refl (NodeEdge.full r)) hdF
  obtain ⟨y, hy, hcb⟩ := cb_on_path store hslots hrb _ S hS hrS hdFr
  -- The finalized test reads `y`.
  have hF : store.finalizedCheckpoint.root = y := by
    have h := hfF store
    unfold finRead at h
    rw [StateT.run_map, hcb store] at h
    simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq, and_true] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact absurd h hg
    · exact h
  rw [hF]
  rcases hy with rfl | ⟨hne, hry, hyd, yb, hyb, hyS⟩
  · exact .inl rfl
  · right
    obtain ⟨yb', hyb', hgt⟩ := below_slot_gt store hslots hrb hry hne
    change FcMap.lookup store.blocks y = some yb' at hyb'
    rw [hyb] at hyb'
    cases hyb'
    refine ⟨?_, yb, hyb, hgt, hyS⟩
    rcases NodeBelow.comparable store _ _ _ hdF hyd with h | h
    · exact h
    · obtain ⟨mb, hmb, hle⟩ := NodeBelow.slot_le store hslots _ _ h rb hrb
      change FcMap.lookup store.blocks y = some mb at hmb
      rw [hyb] at hmb
      cases hmb
      exact absurd hle (UInt64.not_le.mpr hgt)

omit [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint] [CryptoBackend]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability] in
/-- **An ancestor path from a block `x` down to `k` is a path of pending nodes.** Each block of
the path after `x` hangs below the pending node of its parent (`child_below`), and its parent is
the block before it. -/
theorem AncestorPath.pendingBelow {a : BeaconBlock} {store : Store map} (hslot : SlotInv a store)
    {x : BeaconBlock} {k : Root} {L : List BeaconBlock} (h : AncestorPath a store k L) :
    ∀ L₁ L₂, L = L₁ ++ x :: L₂ → NodeBelow store (.pending (htr x)) (.pending k) := by
  induction h with
  | anchor => intro L₁ L₂ he; simp at he
  | @cons k b bs hk _ hpath ih =>
    intro L₁ L₂ he
    rcases List.eq_nil_or_concat L₂ with rfl | ⟨L₂', y, rfl⟩
    · obtain ⟨-, hbx⟩ := List.append_inj' he rfl
      rw [List.singleton_inj] at hbx
      rw [← hbx, hslot.atRoot k b hk]
      exact .refl
    · have he' : bs ++ [b] = (L₁ ++ x :: L₂') ++ [y] := by rw [he]; simp
      obtain ⟨hbs, hby⟩ := List.append_inj' he' rfl
      rw [List.singleton_inj] at hby
      subst hby
      have hup := ih L₁ L₂' hbs
      -- The parent of `b` is the last block of `bs`, which is stored.
      obtain ⟨-, hlast⟩ := hpath.last
      obtain ⟨pb, hpb⟩ : ∃ pb, FcMap.lookup store.blocks b.parentRoot = some pb := by
        rcases List.eq_nil_or_concat L₂' with rfl | ⟨L₃, z, rfl⟩
        · exact ⟨x, hlast L₁ x (by simp [hbs])⟩
        · exact ⟨z, hlast (L₁ ++ x :: L₃) z (by simp [hbs])⟩
      exact NodeBelow.trans store _ _ _ hup (child_below hk hpb)

include hw in
/-- **Case I: the head run is in the epoch of `rb`.** The finalized epoch starts before `rb`: it
is the anchor epoch, which ends before `rb`, or an epoch before the epoch of the run. So EMPTY
`r` passes with FULL `r` (`viable_same_epoch`). -/
theorem HeadRun.Held.viable_sameEpoch (hcol : ¬ RootCollision) {n : NodeRun map}
    {q : HeadRun map} {r : Root} {rb : BeaconBlock} {t : Nat} (hn : n.Honest rb)
    (hq : q.Held n r rb t) (hord : StateCkptOrd n.anchorState)
    (hsr : ∀ (sb : SignedBeaconBlock) (w : Nat), (TraceEvent.handler (.block sb), w) ∈ n.events →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hr0 : r ≠ htr n.anchor) (hlo : rb.slot.toNat < t) (ht : t < 2 ^ 64)
    (hA : (n.anchorState.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤ rb.slot.toNat)
    (hE : t / slotsPerEpoch = rb.slot.toNat / slotsPerEpoch) {jb : BeaconBlock}
    (hj : FcMap.lookup q.store.blocks q.store.justifiedCheckpoint.root = some jb) :
    EmptyViableWithFull q.store r := by
  have hp := slotsPerEpochPos
  obtain ⟨hinv, -, -, hlink, hfv⟩ := hq.viableInvs hw hcol hn hord hsr
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  intro nodes t0 t' hrun hfull
  obtain ⟨hJr, hJfull⟩ := justified_path_of_full q.store hfv r hrun hfull
  obtain ⟨E, hEn, hEr⟩ := hq.storeEpoch
  have hAt : n.anchorState.slot.toNat / slotsPerEpoch ≤ t / slotsPerEpoch := by
    have : (n.anchorState.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤ t := by omega
    have := (Nat.le_div_iff_mul_le hp).mpr this
    omega
  obtain ⟨S, hS, hSv, hF⟩ := hq.finalizedStart hn hinv hord hlo ht hAt
  have hrE : EthCLSpecs.Heze.computeEpochAtSlot rb.slot = E :=
    UInt64.toNat_inj.mp (by rw [computeEpochAtSlot_toNat, hEn, hE])
  have hclock : ∀ k b, FcMap.lookup q.store.blocks k = some b →
      (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat ≤ E.toNat := fun k b hk => by
    rw [computeEpochAtSlot_toNat, hEn]
    exact Nat.div_le_div_right (hq.block_slot_le hn (hn.anchor_le_of_lt hlo) hk)
  -- The finalized epoch starts before `rb`.
  have hSr : S < rb.slot := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hSv]
    have hrd := Nat.div_mul_le_self rb.slot.toNat slotsPerEpoch
    rcases hF with h | h
    · rw [h]
      have := Nat.add_one_mul (n.anchorState.slot.toNat / slotsPerEpoch) slotsPerEpoch
      omega
    · rw [hE] at h
      have h1 : 1 ≤ rb.slot.toNat / slotsPerEpoch := by
        have : slotsPerEpoch ≤ rb.slot.toNat :=
          Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) hA
        exact (Nat.le_div_iff_mul_le hp).mpr (by omega)
      have h2 := Nat.mul_le_mul_right slotsPerEpoch h
      rw [Nat.sub_one_mul] at h2
      have h3 : slotsPerEpoch ≤ rb.slot.toNat / slotsPerEpoch * slotsPerEpoch :=
        Nat.le_mul_of_pos_left _ h1
      omega
  exact viable_same_epoch q.store hinv.slot.slots hlink hq.block hr0
    (below_not_anchor hinv.slot hcb hq.block hn.anchorSlot) hj hJr hJfull hEr hrE hclock hS hSr
    nodes t0 t' hrun hfull

end Store

/-! ## The honest chain -/

section Chain
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The blocks of a run below the bound come in strictly increasing slot order. A block step
sets the header slot to the block slot, and every later block is past the header slot
(`ChainRun.blocks_gt_header`). -/
theorem ChainRun.blocks_strict {hi : Nat} {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    (blocksOf q).Pairwise (fun x y => x.slot.toNat < y.slot.toNat) := by
  induction h with
  | nil => exact .nil
  | slot _ _ _ ih => exact ih
  | @block _ st st1 _ sb v hstep hrest ih =>
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih⟩
    obtain ⟨-, -, hhd, -, -⟩ := hstep.hdr
    have hh : st1.latestBlockHeader.slot = sb.message.slot := by rw [hhd]; rfl
    have := hrest.blocks_gt_header.2 b hb
    rw [hh] at this
    exact this

omit [HasherTag] [Config] [CryptoBackend] in
/-- A run with a block splits at its last block: the steps after it are slot steps. -/
theorem split_last_block :
    ∀ l : List ChainStep, blocksOf l ≠ [] →
      ∃ p sb vb q, l = p ++ .block sb vb :: q ∧ blocksOf q = []
  | [], h => absurd rfl h
  | x :: t, h => by
    by_cases ht : blocksOf t = []
    · cases x with
      | slot => exact absurd (show blocksOf (.slot :: t) = [] from ht) h
      | block sb vb => exact ⟨[], sb, vb, t, rfl, ht⟩
    · obtain ⟨p, sb, vb, q, rfl, hq⟩ := split_last_block t ht
      exact ⟨x :: p, sb, vb, q, rfl, hq⟩

end Chain

/-! ## Ancestors of a block lie on its ancestor path -/

section Path
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map] [LawfulFcMap map Root]

/-- An ancestor path that ends at a block ends with the block at its root, after the path of
the block's parent. -/
theorem AncestorPath.inv {a : BeaconBlock} {store : Store map} {k : Root} {L : List BeaconBlock}
    (h : AncestorPath a store k L) :
    L = [] ∨ ∃ bs b, L = bs ++ [b] ∧ FcMap.lookup store.blocks k = some b ∧
      AncestorPath a store b.parentRoot bs := by
  cases h with
  | anchor => exact .inl rfl
  | cons hk _ hpath => exact .inr ⟨_, _, rfl, hk, hpath⟩

/-- **A pending ancestor of a node has its block on the ancestor path of the node's root.** An
EMPTY or FULL edge keeps the root. A block edge goes from the parent root, and the ancestor path
of the child is the path of its parent followed by the child's block. At the top, the root is
the last block of its path, or the anchor root when the path is empty. -/
theorem NodeBelow.mem_path {a : BeaconBlock} {store : Store map} {x : Root} {z : ForkChoiceNode}
    (h : NodeBelow store (.pending x) z)
    (hxa : ∀ y, NodeBelow store (.pending x) y → y.root = htr a → y.root = x) :
    ∀ {L : List BeaconBlock}, AncestorPath a store z.root L →
      x = htr a ∨ ∃ xb, FcMap.lookup store.blocks x = some xb ∧ xb ∈ L := by
  induction h with
  | refl =>
    intro L hL
    obtain ⟨h0, h1⟩ := hL.last
    rcases List.eq_nil_or_concat L with rfl | ⟨L', y, rfl⟩
    · exact .inl (h0 rfl)
    · exact .inr ⟨y, h1 L' y (List.concat_eq_append ..), by simp⟩
  | step p c _ hedge ih =>
    intro L hL
    cases hedge with
    | empty root => exact ih hL
    | full root => exact ih hL
    | block _ root b s s' hb hpar _ =>
      rcases hL.inv with rfl | ⟨bs, b', rfl, hk, hpath⟩
      · -- An empty path ends at the anchor root, which is `x` itself.
        obtain ⟨h0, -⟩ := hL.last
        exact .inl ((hxa _ (.step _ _ ‹_› (.block _ root b s s' hb hpar ‹_›)) (h0 rfl)).symm.trans
          (h0 rfl))
      · change FcMap.lookup store.blocks root = some b' at hk
        rw [hb] at hk
        cases hk
        rw [hpar] at hpath
        rcases ih hpath with h | ⟨xb, hxb, hm⟩
        · exact .inl h
        · exact .inr ⟨xb, hxb, List.mem_append_left _ hm⟩

/-- A node below a pending node lies at or below the pending node of its own root. -/
theorem NodeBelow.pending_root {store : Store map} {n y : ForkChoiceNode} (h : NodeBelow store n y)
    (hn : n.payloadStatus = EthCLSpecs.Heze.Const.payloadStatusPending) :
    NodeBelow store (.pending y.root) y := by
  cases h with
  | refl =>
    have e := node_eq_of_root_status n (.pending n.root) rfl hn
    rw [e]
    exact .refl
  | step p c _ hedge =>
    cases hedge with
    | empty root => exact .step _ _ .refl (NodeEdge.empty root)
    | full root => exact .step _ _ .refl (NodeEdge.full root)
    | block _ root b s s' _ _ _ => exact .refl

end Path

/-! ## Runs and their blocks -/

section Runs
variable [Preset] [HasherTag]

omit [HasherTag] in
/-- A block of a run is the block of one of its block steps. -/
theorem split_of_mem_blocksOf {b : BeaconBlock} :
    ∀ steps : List ChainStep, b ∈ blocksOf steps →
      ∃ p sb vb q, steps = p ++ .block sb vb :: q ∧ sb.message = b
  | [], h => absurd h List.not_mem_nil
  | .slot :: t, h => by
    obtain ⟨p, sb, vb, q, rfl, hm⟩ := split_of_mem_blocksOf t h
    exact ⟨.slot :: p, sb, vb, q, rfl, hm⟩
  | .block sb vb :: t, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], sb, vb, t, rfl, rfl⟩
    · obtain ⟨p, sb', vb', q, rfl, hm⟩ := split_of_mem_blocksOf t h
      exact ⟨.block sb vb :: p, sb', vb', q, rfl, hm⟩

omit [HasherTag] in
/-- A run with a block splits at its first block: the steps before it are slot steps. -/
theorem split_first_block :
    ∀ l : List ChainStep, blocksOf l ≠ [] →
      ∃ x₁ sb vb x₂, l = x₁ ++ .block sb vb :: x₂ ∧ blocksOf x₁ = []
  | [], h => absurd rfl h
  | .slot :: t, h => by
    obtain ⟨x₁, sb, vb, x₂, rfl, hx⟩ := split_first_block t h
    exact ⟨.slot :: x₁, sb, vb, x₂, rfl, hx⟩
  | .block sb vb :: t, _ => ⟨[], sb, vb, t, rfl, rfl⟩

/-- The slot of the anchor block is the header slot of the anchor state. -/
theorem anchor_slot_eq {A : BeaconState} {a : BeaconBlock} (hanc : filledHeader A = headerOf a) :
    a.slot = A.latestBlockHeader.slot := by
  have e := congrArg EthCLSpecs.Heze.BeaconBlockHeader.slot hanc
  unfold filledHeader at e
  split at e <;> exact e.symm

/-- The chain root of an epoch is the anchor root or the root of a block of the run. -/
theorem chainRoot_mem {A : BeaconState} {a : BeaconBlock} (hanc : htr (filledHeader A) = htr a)
    (hal : A.latestBlockHeader.slot.toNat ≤ epochOf A * slotsPerEpoch) (steps : List ChainStep)
    {e : Nat} (he1 : 1 ≤ e) (he : epochOf A ≤ e) :
    chainRoot A steps e = htr a ∨ ∃ b ∈ blocksOf steps, htr b = chainRoot A steps e := by
  have hT : A.latestBlockHeader.slot.toNat ≤ e * slotsPerEpoch :=
    Nat.le_trans hal (Nat.mul_le_mul_right _ he)
  rw [chainRoot_pos _ _ he1, rootAtSlot_eq_lastRootOf hanc steps hT]
  unfold lastRootOf
  cases hl : ((blocksOf steps).filter (fun b => b.slot.toNat ≤ e * slotsPerEpoch)).getLast? with
  | none => exact .inl rfl
  | some b => exact .inr ⟨b, (List.mem_filter.mp (List.mem_of_getLast? hl)).1, rfl⟩

/-- A finalized checkpoint of the chain, or one of its base, is justified. -/
theorem justified_of_fin {V R : Type} [DecidableEq V] [DecidableEq R] {c : EthCLLib.Proofs.FFG.Chain V R}
    {x : EthCLLib.Proofs.FFG.Checkpoint R}
    (h : EthCLLib.Proofs.FFG.Finalized c x ∨ x ∈ c.base) : EthCLLib.Proofs.FFG.Justified c x := by
  rcases h with h | h
  · cases h with
    | one hb _ _ _ => exact hb
    | two hb _ _ _ _ _ => exact hb
  · exact .base h

end Runs

/-! ## The premises on the honest chain -/

section Setting
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

/-- **The vote carrier chain of the window.** `H` is a validated run from the anchor state `A`
through `rb` (the block step `sbR`) to a state in epoch `E₁ + 4` (`ends`, `endsHi`). Its blocks
after `rb` are on the EMPTY side, and it carries the honest votes of each epoch. The honest
heads need not follow it: a block of `H` that a later block re-orgs still counts, because the
store keeps it and the viability filter reads its leaves.

- `emptyEdge`: the first block of `H` after `rb` builds on EMPTY `rb`. Its bid names a parent
  block hash other than the hash of `rb`'s bid.
- `live`: `H` has a block in each epoch from the epoch before the epoch of `rb`, up to `E₁ + 3`.
- `included`: from the epoch before the epoch of `rb`, each weigh state of `H` holds a placed
  vote of every honest validator of the target test. These validators hold two thirds of the
  total. The weigh state at the end of the epoch before `rb` places the votes of two epochs
  before `rb`. So `H` enters the epoch of `rb` with that epoch justified, and the leaves below
  EMPTY `r` pass `correct_justified` there. Without these votes, a side branch can justify a
  later checkpoint and then lose it to a slashing. Then no leaf is viable in the epoch of `rb`,
  the honest votes of that epoch sit above `r`, and an honest node with no validators reaches
  FULL `r`.
- `holds`: an honest node holds every block of `H` from a slot before the slot of its head
  run.
- `unslashedH`, `unslashed`: no state on `H`, or on a store run of an honest store of the
  window, has an honest validator slashed.
- `single`: an honest validator signs at most one vote for each target epoch
  (`phase0/validator.md`, the slashing protection rule against a double vote). An honest vote
  of the window is one that an honest node receives, or a placed vote on a store run of an
  honest store (`HonestVoteOf`). Such a vote and a vote on `H` with the same target epoch are
  one vote.
- `active`: every honest validator is a registry index, active at each epoch from two epochs
  before the epoch of `rb` to `E₁ + 4`, at every state of `H`. Its exit needs its own signature
  or its withdrawal credentials, and no slashing marks it (`unslashedH`).
- `seed`, `room`: the preset facts and the epoch arithmetic that the committee lookups need. -/
structure CarrierWindow {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map)
    (rb : BeaconBlock) (A : BeaconState) (a : BeaconBlock) (E₁ : Nat)
    (honestOf : ValidatorIndex → Bool) (hi : Nat) (stepsH : List ChainStep) (sH : BeaconState)
    (aR : List ChainStep) (sbR : SignedBeaconBlock) (vbR : Bool) (bR : List ChainStep) : Prop
    where
  hhi : hi ≤ 2 ^ 64 - 1
  chainRun : ChainRun hi stepsH A sH
  val : ValidatedSteps stepsH
  tot : ∀ p q u, stepsH = p ++ q → ChainRun hi p A u → RunTotals u
  ends : (E₁ + 4) * slotsPerEpoch ≤ sH.slot.toNat
  endsHi : sH.slot.toNat < (E₁ + 5) * slotsPerEpoch
  split : stepsH = aR ++ .block sbR vbR :: bR
  isRb : sbR.message = rb
  emptyEdge : ∀ p sb vb q, stepsH = p ++ .block sb vb :: q → rb.slot < sb.message.slot →
    (∀ b ∈ blocksOf p, b.slot ≤ rb.slot) →
    (sb.message.body.signedExecutionPayloadBid.message.parentBlockHash ==
      rb.body.signedExecutionPayloadBid.message.blockHash) = false
  live : ∀ e, rb.slot.toNat / slotsPerEpoch ≤ e + 1 → e ≤ E₁ + 3 →
    ∃ b ∈ blocksOf stepsH, b.slot.toNat / slotsPerEpoch = e
  included : ∀ e, rb.slot.toNat / slotsPerEpoch ≤ e + 1 → e ≤ E₁ + 3 → ∀ W,
    WeighAt hi stepsH A e W →
    (∀ x ∈ honestList W honestOf (EthCLSpecs.Heze.previousEpochOf (pureState W)),
      PlacedVote hi A stepsH x (EthCLSpecs.Heze.previousEpochOf (pureState W))) ∧
    3 * honestStake W honestOf (EthCLSpecs.Heze.previousEpochOf (pureState W)) ≥
      2 * (totBal W).toNat
  holds : ∀ v, honest v → ∀ t, raceLo rb < t → t ≤ finSlot E₁ → ∀ b ∈ blocksOf stepsH,
    rb.slot < b.slot → b.slot.toNat < t → FcMap.lookup (run v t).store.blocks (htr b) = some b
  unslashedH : ∀ p q u, stepsH = p ++ q → ChainRun hi p A u →
    ∀ j < u.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (u.validators.val[j]!).slashed = false
  unslashed : ∀ v, honest v → ∀ t, raceLo rb ≤ t → t ≤ finSlot E₁ → ∀ p q z,
    StoreRun A a (run v t).store (p ++ q) → ChainRun (2 ^ 64 - 1) p A z →
    ∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (z.validators.val[j]!).slashed = false
  single : ∀ i, honestOf i = true → ∀ d, HonestVoteOf honest node run rb A a E₁ i d →
    ∀ (q s₂ : List ChainStep) (d₂ : AttestationData), stepsH = q ++ s₂ →
      RunVote hi A q i d₂ → d₂.target.epoch = d.target.epoch → d₂ = d
  active : ∀ p q z, stepsH = p ++ q → ChainRun hi p A z → ∀ i, honestOf i = true →
    ∀ e : EthCLSpecs.Heze.Epoch, rb.slot.toNat / slotsPerEpoch ≤ e.toNat + 2 → e.toNat ≤ E₁ + 4 →
      i.toNat < z.validators.val.size ∧
        EthCLSpecs.Heze.isActiveValidator z.validators.val[i.toNat]! e = true
  seed : EthCLSpecs.Heze.Const.minSeedLookahead.toNat + 2 <
    EthCLSpecs.Heze.Const.epochsPerHistoricalVector
  room : E₁ + 6 + 2 * EthCLSpecs.Heze.Const.maxSeedLookahead.toNat +
    EthCLSpecs.Heze.Const.epochsPerHistoricalVector < 2 ^ 64

/-- **The last block of `E₁ + 3` reaches every honest node in time.** `H` has a block at the
last slot of epoch `E₁ + 3`. Each honest node receives it before the first slot of `E₁ + 4`, at
an event whose store does not hold it yet. `on_block` returns early on a known block, so this
names the first receipt. The store finalizes only through the blocks it receives. -/
def LastDelivered {Node : Type} (honest : Node → Prop) (node : Node → NodeRun map)
    (run : Node → Nat → HeadRun map) (A : BeaconState) (E₁ : Nat) (hi : Nat)
    (stepsH : List ChainStep) : Prop :=
  ∃ (p q : List ChainStep) (sb : SignedBeaconBlock) (vb : Bool) (u w : BeaconState),
    stepsH = p ++ .block sb vb :: .slot :: q ∧ ChainRun hi p A u ∧ BlockStep sb vb u w ∧
    (u.slot.toNat + 1) % slotsPerEpoch = 0 ∧ u.slot.toNat / slotsPerEpoch = E₁ + 3 ∧
    ∀ v, honest v → ∃ (es1 es2 : List TraceEvent),
      (run v (finSlot E₁)).events.map Prod.fst = es1 ++ TraceEvent.handler (.block sb) :: es2 ∧
      ∀ arr mid, NodeTrace (node v).seed es1 arr mid →
        storeSlot mid < finSlot E₁ ∧ FcMap.contains mid.blocks (htr sb.message) = false

end Setting

/-! ## No honest block before the finalized epoch of `r` -/

section NoBlock
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)
  {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
  {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
  {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
  {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
  {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
  {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}

include hw in
/-- **An honest target other than `r` of an epoch from `E₁` is past `rb`.** The head is below
EMPTY `r`, so below the pending node of `r`. The checkpoint walk of an epoch `e` from `E₁` stops
at `r` or at a block below `r` (`cb_on_path`), since `rb` is before the first slot of `E₁`. A
block below `r` other than `r` is later than `rb` (`below_slot_gt`). The first slot of `e` fits
in a `Slot`, because the head run of `finSlot E₁` has that slot. -/
theorem FinalitySetting.early
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) : EarlyTargets honest run r rb E₁ := by
  intro v hv t ht1 ht2 hbelow e c u u' he1 he2 hcr hck
  have hp := slotsPerEpochPos
  have hbefore := hset.before
  have hlo : raceLo rb ≤ t := by unfold raceLo; omega
  have hq := hset.held v hv t hlo (Nat.le_of_lt ht2)
  have hslots := (hq.slotInv hw (hset.fields.nodeOk v hv) hcol).slots
  have hlk := hq.block
  have hbelow : NodeBelow (run v t).store (.pending r) (run v t).head :=
    NodeBelow.trans _ _ _ _ (.step _ _ .refl (.empty r)) hbelow
  -- The first slot of `e`.
  have hfit : e.toNat * slotsPerEpoch < 2 ^ 64 := by
    obtain ⟨cs, hcsn, -⟩ := (hset.held v hv (finSlot E₁) (by
      unfold raceLo finSlot
      have : E₁ * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
      omega) (Nat.le_refl _)).slot
    have h1 : e.toNat * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ he2
    have h3 := cs.toNat_lt
    unfold finSlot at hcsn
    omega
  have hS := computeStartSlotAtEpoch_ok_of_lt hfit
  have hn : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
  have hSn : (e * UInt64.ofNat slotsPerEpoch).toNat = e.toNat * slotsPerEpoch := by
    rw [UInt64.toNat_mul, hn, Nat.mod_eq_of_lt hfit]
  have hbS : ¬ rb.slot > e * UInt64.ofNat slotsPerEpoch := by
    intro h
    have h1 := UInt64.lt_iff_toNat_lt.mp h
    have h2 : E₁ * slotsPerEpoch ≤ e.toNat * slotsPerEpoch := Nat.mul_le_mul_right _ he1
    omega
  obtain ⟨y, hy, hcb⟩ := cb_on_path _ hslots hlk e _ hS hbS hbelow
  have hyc : c = y := by
    have h := (hcb u).symm.trans hck
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  subst hyc
  rcases hy with rfl | ⟨hne, hry, -, -⟩
  · exact absurd rfl hcr
  · exact below_slot_gt _ hslots hlk hry hne

include hw in
/-- **The finality chain is the carrier chain of the window.** `H` meets `HonestChain` over
`regVals`: the anchor facts of `FinalitySetting` and the totals of `H` give the refinement
premises, and `included` gives the votes and the stake of the epochs `E₁` to `E₁ + 2`. `late` and
`before` put the anchor epoch before `E₁`. `LastDelivered` gives the last block of `E₁ + 3`. -/
theorem CarrierWindow.chain
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hlast : LastDelivered honest node run A E₁ hi stepsH) :
    FinalityChain honest node run A honestOf E₁ := by
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have hrbE : rb.slot.toNat / slotsPerEpoch < E₁ := (Nat.div_lt_iff_lt_mul hp).mpr hbefore
  have hAE : epochOf A + 2 < E₁ := Nat.lt_of_mul_lt_mul_right (a := slotsPerEpoch) (by
    have := Nat.mul_le_mul_right slotsPerEpoch (Nat.le_max_left (epochOf A + 2) 3)
    omega)
  have h3E : 3 < E₁ := Nat.lt_of_mul_lt_mul_right (a := slotsPerEpoch) (by
    have := Nat.mul_le_mul_right slotsPerEpoch (Nat.le_max_right (epochOf A + 2) 3)
    omega)
  have hends : epochOf sH = E₁ + 4 := by
    unfold epochOf
    have h1 := hH.ends
    have h2 := hH.endsHi
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp).mpr h2))
      ((Nat.le_div_iff_mul_le hp).mpr h1)
  refine ⟨hi, stepsH, sH, regVals,
    { ref := ⟨hw, hH.hhi, hH.chainRun, hH.val, hset.roots, hset.cps, hset.ord, hset.sphr, hH.tot,
        regVals_nodup, fun _ _ _ _ _ i _ => mem_regVals i⟩
      low := by omega
      start := by omega
      ends := hends
      included := fun k hk W hW =>
        (hH.included (E₁ + k + 1) (by omega) (by omega) W hW).1
      stake := fun k hk W hW =>
        (hH.included (E₁ + k + 1) (by omega) (by omega) W hW).2 }, hlast⟩

/-- **The tip of the honest chain for epoch `E`.** Take the weigh state `W` of `H` at the last
slot of `E - 1`, for `E` from the epoch of `rb` on. The last block `T` of `H` up to `W` is in
epoch `E - 1`, because `H` has a block there (`live`). After the epoch of `rb`, `T` is `rb` or
later. The post-state `wT` of `T` reaches `W` by slot steps inside one epoch. These steps write
no flag (`ChainRun.targetFlag_back`), and they keep the activity and the balances
(`ChainRun.views_of_epoch`). So the votes that `W` holds (`included`) are flags of `wT`, with
the stake of `W`. -/
theorem CarrierWindow.tipChain
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat) {E : Nat}
    (hE1 : rb.slot.toNat / slotsPerEpoch ≤ E) (hE2 : E ≤ E₁ + 4) :
    ∃ p sbT vbT q s₂ wT W, stepsH = p ++ .block sbT vbT :: (q ++ .slot :: s₂) ∧
      ChainRun hi (p ++ [.block sbT vbT]) A wT ∧ ChainRun hi q wT W ∧ blocksOf q = [] ∧
      (∃ u, ChainRun hi p A u ∧ BlockStep sbT vbT u wT) ∧ ValidatedSteps p ∧
      wT.slot.toNat = sbT.message.slot.toNat ∧
      (E - 1) * slotsPerEpoch ≤ sbT.message.slot.toNat ∧
      sbT.message.slot.toNat < E * slotsPerEpoch ∧
      (rb.slot.toNat / slotsPerEpoch < E → rb ∈ blocksOf p ∨ sbT.message = rb) ∧
      (∀ x ∈ blocksOf p, x.slot.toNat < sbT.message.slot.toNat) ∧
      (∀ j < wT.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (wT.validators.val[j]!).slashed = false) ∧
      CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState wT)) (pureState wT) ∧
      CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState wT)) (pureState wT) ∧
      (∀ x ∈ honestList wT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState wT)),
        TargetFlagSet wT x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState wT))) ∧
      3 * honestStake wT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState wT)) ≥
        2 * (totBal wT).toNat := by
  have hp := slotsPerEpochPos
  have hhi := hH.hhi
  have hrA : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
  have hAs : A.slot.toNat < (epochOf A + 1) * slotsPerEpoch := by
    unfold epochOf
    have := Nat.lt_div_mul_add (a := A.slot.toNat) hp
    rw [Nat.add_one_mul]
    omega
  have hEE : E - 1 + 1 = E := by omega
  obtain ⟨W, hW⟩ := hH.chainRun.weighAt_of_cross hhi (E - 1)
    (by
      have : (epochOf A + 1) * slotsPerEpoch ≤ (E - 1 + 1) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
    (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hH.ends)
  obtain ⟨s₁, s₂, hs, hr1, hbW, heW⟩ := id hW
  -- The weigh state is the last slot of `E - 1`.
  have hW1 : W.slot.toNat + 1 = E * slotsPerEpoch := by
    have := Nat.div_add_mod (W.slot.toNat + 1) slotsPerEpoch
    rw [hbW, succ_div_of_mod_eq hbW, heW, hEE] at this
    rw [Nat.mul_comm]
    omega
  -- The blocks after `W` are from epoch `E` on.
  have hafter : ∀ b ∈ blocksOf s₂, E * slotsPerEpoch ≤ b.slot.toNat := by
    have hrun := hH.chainRun
    rw [hs] at hrun
    obtain ⟨m, hm1, hm2⟩ := hrun.split
    rw [← hr1.det hm1] at hm2
    cases hm2 with
    | slot hlt hstep hrest =>
      intro b hb
      have hlt' : W.slot.toNat < hi := hlt
      have := hstep.slot (by omega)
      have := hrest.blocks_slot_ge hhi b hb
      omega
  have hin : ∀ b ∈ blocksOf stepsH, b.slot.toNat < E * slotsPerEpoch → b ∈ blocksOf s₁ := by
    intro b hb hlt
    rw [hs, blocksOf_append] at hb
    rcases List.mem_append.mp hb with h | h
    · exact h
    · exact absurd (hafter b h) (by omega)
  have hrbH : rb ∈ blocksOf stepsH := by
    rw [hH.split, ← hH.isRb]
    exact mem_blocksOf_block _ _ _ _
  -- `H` has a block in `E - 1`, before the slot after `W`.
  obtain ⟨b₁, hb₁, hb₁e⟩ := hH.live (E - 1) (by omega) (by omega)
  have hb₁E : b₁.slot.toNat < E * slotsPerEpoch := by
    rw [← hEE]
    exact (Nat.div_lt_iff_lt_mul hp).mp (by omega)
  have hb₁s := hin b₁ hb₁ hb₁E
  obtain ⟨p, sbT, vbT, q, hs1, hq⟩ := split_last_block s₁ (List.ne_nil_of_mem hb₁s)
  have hbl : blocksOf s₁ = blocksOf p ++ [sbT.message] := by
    rw [hs1, blocksOf_append]
    show _ ++ sbT.message :: blocksOf q = _
    rw [hq]
  have hstrict := hr1.blocks_strict
  rw [hbl, List.pairwise_append] at hstrict
  have hlast : ∀ x ∈ blocksOf p, x.slot.toNat < sbT.message.slot.toNat :=
    fun x hx => hstrict.2.2 x hx _ (List.mem_singleton_self _)
  have hle1 : ∀ b ∈ blocksOf s₁, b.slot.toNat ≤ sbT.message.slot.toNat := by
    intro b hb
    rw [hbl] at hb
    rcases List.mem_append.mp hb with h | h
    · exact Nat.le_of_lt (hlast b h)
    · exact (List.mem_singleton.mp h) ▸ Nat.le_refl _
  -- The runs to `wT` and from `wT` to `W`.
  have hr1' := hr1
  rw [hs1, show p ++ ChainStep.block sbT vbT :: q = (p ++ [.block sbT vbT]) ++ q by simp] at hr1'
  obtain ⟨wT, hX, hY⟩ := hr1'.split
  obtain ⟨u, hpu, hblk⟩ := hX.split
  obtain ⟨hbs, hwT⟩ : BlockStep sbT vbT u wT ∧ wT.slot.toNat = sbT.message.slot.toNat := by
    cases hblk with
    | block _ _ hb hrest =>
      cases hrest
      obtain ⟨e1, e2⟩ := hb.slot
      exact ⟨hb, by omega⟩
  have hTW : sbT.message.slot.toNat ≤ W.slot.toNat :=
    ((hr1.slot_le hhi).2 sbT.message (by rw [hbl]; simp)).2
  have hTlo : (E - 1) * slotsPerEpoch ≤ sbT.message.slot.toNat := by
    rw [← hb₁e]
    exact Nat.le_trans (Nat.div_mul_le_self _ _) (hle1 b₁ hb₁s)
  have hsH : stepsH = p ++ .block sbT vbT :: (q ++ .slot :: s₂) := by rw [hs, hs1]; simp
  have hvalp : ValidatedSteps p := fun sb v hm => hH.val sb v (by rw [hsH]; simp [hm])
  have hrbp : rb.slot.toNat / slotsPerEpoch < E → rb ∈ blocksOf p ∨ sbT.message = rb := by
    intro hlt
    have hrb1 := hin rb hrbH ((Nat.div_lt_iff_lt_mul hp).mp hlt)
    rw [hbl] at hrb1
    rcases List.mem_append.mp hrb1 with h | h
    · exact .inl h
    · exact .inr (List.mem_singleton.mp h).symm
  -- The facts at `wT`, from the weigh state `W`.
  have hsame : wT.slot.toNat / slotsPerEpoch = W.slot.toNat / slotsPerEpoch := by
    rw [hwT, heW]
    have h1 : E - 1 ≤ sbT.message.slot.toNat / slotsPerEpoch :=
      (Nat.le_div_iff_mul_le hp).mpr hTlo
    have h2 : sbT.message.slot.toNat / slotsPerEpoch < E :=
      (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    omega
  have hus : ∀ j < wT.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (wT.validators.val[j]!).slashed = false :=
    hH.unslashedH (p ++ [.block sbT vbT]) (q ++ .slot :: s₂) wT (by rw [hsH]; simp) hX
  have huW : ∀ j < W.validators.val.size, honestOf (UInt64.ofNat j) = true →
      (W.validators.val[j]!).slashed = false := hH.unslashedH s₁ (.slot :: s₂) W hs hr1
  have h64 : wT.validators.val.size < 2 ^ 64 :=
    (hH.tot (p ++ [.block sbT vbT]) (q ++ .slot :: s₂) wT (by rw [hsH]; simp) hX).2.2
  have hcT : (EthCLSpecs.Heze.currentEpochOf (pureState wT)).toNat = E - 1 := by
    rw [currentEpochOf_toNat]
    show wT.slot.toNat / slotsPerEpoch = _
    rw [hsame, heW]
  have hpT : (EthCLSpecs.Heze.previousEpochOf (pureState wT)).toNat = E - 2 := by
    rw [previousEpochOf_toNat_sub]
    show wT.slot.toNat / slotsPerEpoch - 1 = _
    rw [hsame, heW]
    omega
  have hroom := hH.room
  have hseed := hH.seed
  have hw₀ : CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState wT)) (pureState wT) := by
    unfold CommitteeWindow
    refine ⟨by omega, by omega, by omega, hseed, by omega, h64⟩
  have hw₁ : CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState wT)) (pureState wT) := by
    unfold CommitteeWindow
    refine ⟨by omega, by omega, by omega, hseed, by omega, h64⟩
  have hc₀ : comView (EthCLSpecs.Heze.previousEpochOf (pureState wT)) (pureState wT) =
      (true, (comView (EthCLSpecs.Heze.previousEpochOf (pureState wT)) (pureState wT)).2) := by
    show ((comView _ (pureState wT)).1, (comView _ (pureState wT)).2) = _
    have : (comView (EthCLSpecs.Heze.previousEpochOf (pureState wT)) (pureState wT)).1 = true := by
      simpa [comView] using hw₀
    rw [this]
  have hc₁ : comView (EthCLSpecs.Heze.currentEpochOf (pureState wT)) (pureState wT) =
      (true, (comView (EthCLSpecs.Heze.currentEpochOf (pureState wT)) (pureState wT)).2) := by
    show ((comView _ (pureState wT)).1, (comView _ (pureState wT)).2) = _
    have : (comView (EthCLSpecs.Heze.currentEpochOf (pureState wT)) (pureState wT)).1 = true := by
      simpa [comView] using hw₁
    rw [this]
  obtain ⟨heb, hz₀⟩ := hY.views_of_epoch hhi hsame hc₀
  obtain ⟨-, hz₁⟩ := hY.views_of_epoch hhi hsame hc₁
  obtain ⟨hcur, hprev⟩ := epochs_eq_of_toNat (a := W) (b := wT) hsame.symm
  have hm₀ := act_of_comView hc₀ hz₀
  have hl := honestList_eq_of_views hm₀ hus huW
  have hsk := honestStake_eq_of_views hm₀ heb h64 hus huW
  have htb := totBal_eq_of_views hcur (act_of_comView hc₁ hz₁) heb h64
  obtain ⟨hinc, hstk⟩ := hH.included (E - 1) (by omega) (by omega) W hW
  rw [hprev] at hinc hstk
  refine ⟨p, sbT, vbT, q, s₂, wT, W, hsH, hX, hY, hq, ⟨u, hpu, hbs⟩, hvalp, hwT, hTlo,
    by omega, hrbp, hlast, hus, hw₀, hw₁, fun x hx => ?_, by rw [← hsk, ← htb]; exact hstk⟩
  rw [← hl] at hx
  have hW' : WeighAt hi stepsH A
      ((EthCLSpecs.Heze.previousEpochOf (pureState wT)).toNat + 1) W := by
    rw [hpT]
    have : E - 2 + 1 = E - 1 := by omega
    rw [this]
    exact hW
  exact hY.targetFlag_back hhi hq hsame ((hinc x hx).flag_at_weigh hhi hW')

include hw in
/-- **The stored state of a held block of `H`.** Take a block `T` of `H`, not the anchor, that an
honest store of the window holds, with `wT` the state of `H` after it. The stored state of `T`
is `wT`: the store run to it (`CkptInv.chains`) and the prefix of `H` to it have one list of
blocks (`Linked.eq_of_last`) and one end slot (`ChainRun.det_blocks`). -/
theorem CarrierWindow.tipState
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hle : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) {p rest : List ChainStep} {sbT : SignedBeaconBlock} {vbT : Bool}
    {wT : BeaconState} (hsH : stepsH = p ++ .block sbT vbT :: rest)
    (hX : ChainRun hi (p ++ [.block sbT vbT]) A wT)
    (hwT : wT.slot.toNat = sbT.message.slot.toNat)
    (hTk : FcMap.lookup (run v s).store.blocks (htr sbT.message) = some sbT.message)
    (hTa : htr sbT.message ≠ htr a) :
    ∃ preT, FcMap.lookup (run v s).store.blockStates (htr sbT.message) = some (pureState wT) ∧
      ChainRun (2 ^ 64 - 1) preT A wT ∧
      AncestorPath a (run v s).store (htr sbT.message) (blocksOf preT) ∧
      ValidatedSteps preT ∧ EndsAtBlock preT ∧ blocksOf preT = blocksOf p ++ [sbT.message] := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hq := hset.held v hv s hle hs
  have hn := hset.fields.nodeOk v hv
  obtain ⟨hI, -, -, -, -⟩ := hset.storeFacts hw hcol hv hle hs
  have hslot := hI.slot
  obtain ⟨-, -, -, hlink, -⟩ := hq.viableInvs hw hcol hn (hset.anchorState v hv ▸ hset.ord)
    (hset.stateRoots v hv)
  rw [hset.anchorBlock v hv] at hlink
  obtain ⟨sb', _, w', hsb', -, hw', ht'⟩ := hlink _ _ hTk hTa
  obtain ⟨preT, hrunT, hpathT, hvalT, hendT⟩ := hI.chains _ w' hw'
  obtain ⟨hL1, hk1⟩ := hpathT.linked hslot
  have hhi := hH.hhi
  have hvX : ValidatedSteps (p ++ [.block sbT vbT]) := fun sb vb hm => hH.val sb vb (by
    rw [hsH]
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ hm
    · rw [List.mem_singleton.mp hm]
      exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨hL2, -⟩ := hX.linked hw hhi hset.anchorHeader (p := []) hvX hset.roots.rootsInv
    hset.anchorFilled .nil
  rw [List.nil_append, blocksOf_append_block] at hL2
  have hbl : blocksOf preT = blocksOf p ++ [sbT.message] :=
    hL1.eq_of_last hcb hL2 (by rw [← hk1, lastRootOf_snoc])
  have hw'T : w' = wT := by
    have e1 : w'.slot.toNat = sbT.message.slot.toNat := by rw [transition_slot ht', hsb']
    exact ChainRun.det_blocks (Nat.le_refl _) hhi hrunT hX (by rw [hbl, blocksOf_append_block])
      (by rw [e1, hwT])
  subst hw'T
  exact ⟨preT, hw', hrunT, hpathT, hvalT, hendT, hbl⟩

include hw in
/-- **The tip `T` in the store of an honest head run of epoch `E`, after the epoch of `rb`.**
`T` is the block of `CarrierWindow.tipChain`. The node holds it: it is `rb`, or a block of `H`
after `rb` from an earlier slot (`holds`). Its stored state is `wT`: the store run to it
(`CkptInv.chains`) and the prefix of `H` to it have one list of blocks (`Linked.eq_of_last`)
and one end slot (`ChainRun.det_blocks`). Unless `T` is `rb`, the first block of `H` after
`rb` builds on EMPTY `rb` (`emptyEdge`, `child_edge`), and the ancestor path from it reaches
`T` (`AncestorPath.pendingBelow`). -/
theorem CarrierWindow.tipStore
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {s : Nat} (hlo : raceLo rb ≤ s)
    (hs : s ≤ finSlot E₁) (hE1 : rb.slot.toNat / slotsPerEpoch < s / slotsPerEpoch) :
    ∃ (T : Root) (tb : BeaconBlock) (sT : BeaconState) (preT : List ChainStep),
      FcMap.lookup (run v s).store.blocks T = some tb ∧ T ≠ htr a ∧
      FcMap.lookup (run v s).store.blockStates T = some (pureState sT) ∧
      ChainRun (2 ^ 64 - 1) preT A sT ∧ AncestorPath a (run v s).store T (blocksOf preT) ∧
      ValidatedSteps preT ∧ EndsAtBlock preT ∧
      sT.slot.toNat = tb.slot.toNat ∧ rb.slot.toNat ≤ tb.slot.toNat ∧
      sT.slot.toNat / slotsPerEpoch + 1 = s / slotsPerEpoch ∧
      (∀ y ∈ blocksOf preT, y ∈ blocksOf stepsH) ∧
      (∃ pT rest, stepsH = pT ++ rest ∧ blocksOf preT = blocksOf pT) ∧
      (T = r ∨ (rb.slot.toNat < tb.slot.toNat ∧
        NodeBelow (run v s).store (.empty r) (.pending T))) ∧
      (∀ j < sT.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (sT.validators.val[j]!).slashed = false) ∧
      CommitteeWindow (EthCLSpecs.Heze.previousEpochOf (pureState sT)) (pureState sT) ∧
      CommitteeWindow (EthCLSpecs.Heze.currentEpochOf (pureState sT)) (pureState sT) ∧
      (∀ x ∈ honestList sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)),
        TargetFlagSet sT x.toNat (EthCLSpecs.Heze.previousEpochOf (pureState sT))) ∧
      3 * honestStake sT honestOf (EthCLSpecs.Heze.previousEpochOf (pureState sT)) ≥
        2 * (totBal sT).toNat := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hle : raceLo rb ≤ s := hlo
  have hq := hset.held v hv s hle hs
  have hn := hset.fields.nodeOk v hv
  obtain ⟨hI, -, ha, -, -⟩ := hset.storeFacts hw hcol hv hle hs
  have hslot := hI.slot
  obtain ⟨-, -, -, hlink, -⟩ := hq.viableInvs hw hcol hn (hset.anchorState v hv ▸ hset.ord)
    (hset.stateRoots v hv)
  rw [hset.anchorBlock v hv] at hlink
  have hlate := hset.late
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have hE2 : s / slotsPerEpoch ≤ E₁ + 4 := by
    have : s / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right hs
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    exact this
  obtain ⟨p, sbT, vbT, q, s₂, wT, W, hsH, hX, hY, hq0, ⟨u, hpu, hbs⟩, hvalp, hwT, hTlo, hThi,
    hrbp, hlast, hus, hw₀, hw₁, hflags, hstake⟩ := hH.tipChain hlA (Nat.le_of_lt hE1) hE2
  replace hrbp := hrbp hE1
  have hsE : s / slotsPerEpoch * slotsPerEpoch ≤ s := Nat.div_mul_le_self _ _
  have hTs : sbT.message.slot.toNat < s := by omega
  have hrbr : htr rb = r := hslot.atRoot r rb hq.block
  -- `T` is `rb`, or a later block of `H`.
  have hrbT : rb.slot.toNat ≤ sbT.message.slot.toNat := by
    rcases hrbp with h | h
    · exact Nat.le_of_lt (hlast rb h)
    · exact Nat.le_of_eq (by rw [h])
  have hTk : FcMap.lookup (run v s).store.blocks (htr sbT.message) = some sbT.message := by
    rcases hrbp with h | h
    · -- A block of `H` after `rb` and before `s`: `s` is past the first slot of the window.
      have hTr := hlast rb h
      have hlo' : raceLo rb < s := by unfold raceLo at hle ⊢; omega
      exact hH.holds v hv s hlo' hs sbT.message (by rw [hsH]; exact mem_blocksOf_block _ _ _ _)
        (UInt64.lt_iff_toNat_lt.mpr hTr) hTs
    · rw [h, hrbr]
      exact hq.block
  -- `T` is not the anchor: the anchor block is before `rb`.
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have hTa : htr sbT.message ≠ htr a := fun h => by
    rw [h, ha] at hTk
    cases hTk
    have : epochOf A * slotsPerEpoch < (epochOf A + 2) * slotsPerEpoch :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    omega
  -- The stored state of `T` and its store run.
  obtain ⟨preT, hw', hrunT, hpathT, hvalT, hendT, hbl⟩ :=
    hH.tipState hw hset hcol hv hle hs hsH hX hwT hTk hTa
  have hsub : ∀ y ∈ blocksOf preT, y ∈ blocksOf stepsH := by
    intro y hy
    rw [hbl] at hy
    rw [hsH, blocksOf_append]
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append_left _ h
    · rw [List.mem_singleton.mp h]
      exact List.mem_append_right _ List.mem_cons_self
  have hpre : ∃ pT rest, stepsH = pT ++ rest ∧ blocksOf preT = blocksOf pT :=
    ⟨p ++ [.block sbT vbT], q ++ .slot :: s₂, by rw [hsH]; simp,
      by rw [hbl, blocksOf_append_block]⟩
  refine ⟨htr sbT.message, sbT.message, wT, preT, hTk, hTa, hw', hrunT, hpathT, hvalT, hendT,
    hwT, hrbT, ?_, hsub, hpre, ?_, hus, hw₀, hw₁, hflags, hstake⟩
  · rw [hwT]
    have h1 : s / slotsPerEpoch - 1 ≤ sbT.message.slot.toNat / slotsPerEpoch :=
      (Nat.le_div_iff_mul_le hp).mpr hTlo
    have h2 : sbT.message.slot.toNat / slotsPerEpoch < s / slotsPerEpoch :=
      (Nat.div_lt_iff_lt_mul hp).mpr hThi
    omega
  -- Below EMPTY `r`: through the first block of `H` after `rb`.
  rcases hrbp with hrbin | h
  · right
    refine ⟨hlast rb hrbin, ?_⟩
    obtain ⟨p₁, sbr, vr, p₂, hp, hsbr⟩ := split_of_mem_blocksOf p hrbin
    obtain ⟨x₁, sbc, vbc, x₂, hx, hx1⟩ := split_first_block (p₂ ++ [.block sbT vbT])
      (by rw [blocksOf_append_block]; simp)
    have hsplit : stepsH = (p₁ ++ .block sbr vr :: x₁) ++
        .block sbc vbc :: (x₂ ++ (q ++ .slot :: s₂)) := by
      have e : p ++ .block sbT vbT :: (q ++ .slot :: s₂) =
          p₁ ++ .block sbr vr :: ((p₂ ++ [.block sbT vbT]) ++ (q ++ .slot :: s₂)) := by
        rw [hp]; simp
      rw [hsH, e, hx]
      simp
    have hstr := hH.chainRun.blocks_strict
    rw [hsplit, blocksOf_append] at hstr
    have hb1 : blocksOf (p₁ ++ .block sbr vr :: x₁) = blocksOf p₁ ++ [rb] := by
      rw [blocksOf_append]
      show _ ++ sbr.message :: blocksOf x₁ = _
      rw [hx1, hsbr]
    rw [hb1] at hstr
    have hstr' := (List.pairwise_append.mp hstr).2.2
    have hrbc : rb.slot < sbc.message.slot := UInt64.lt_iff_toNat_lt.mpr
      (hstr' rb (by simp) sbc.message (by simp [blocksOf]))
    have hbefore : ∀ b ∈ blocksOf (p₁ ++ .block sbr vr :: x₁), b.slot ≤ rb.slot := by
      intro b hb
      rw [hb1] at hb
      rcases List.mem_append.mp hb with h | h
      · have hs1 := (List.pairwise_append.mp (List.pairwise_append.mp hstr).1).2.2 b h rb
          (List.mem_singleton_self _)
        exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hs1)
      · rw [List.mem_singleton.mp h]
        exact UInt64.le_refl _
    have hne := hH.emptyEdge _ sbc vbc _ hsplit hrbc hbefore
    -- The blocks of the path to `T`: `rb`, then `sbc`.
    have hLH : blocksOf preT = (blocksOf p₁ ++ [rb]) ++ sbc.message :: blocksOf x₂ := by
      rw [hbl, hp]
      have e : blocksOf (p₁ ++ .block sbr vr :: p₂) ++ [sbT.message] =
          blocksOf p₁ ++ sbr.message :: blocksOf (p₂ ++ [.block sbT vbT]) := by
        simp [blocksOf, blocksOf_append]
      rw [e, hx, blocksOf_append, hx1, hsbr]
      simp [blocksOf]
    have hpre := hpathT.prefix hslot ((blocksOf p₁ ++ [rb]) ++ [sbc.message]) (blocksOf x₂)
      (by rw [hLH]; simp)
    rw [lastRootOf_snoc] at hpre
    rcases hpre.inv with h0 | ⟨bs, b, hbs', hkc, hpp⟩
    · simp at h0
    · obtain ⟨hbs1, hbb⟩ := List.append_inj' hbs' rfl
      rw [List.singleton_inj] at hbb
      subst hbb
      obtain ⟨-, hlst⟩ := hpp.last
      have hpr : FcMap.lookup (run v s).store.blocks sbc.message.parentRoot = some rb :=
        hlst (blocksOf p₁) rb hbs1.symm
      have hpar : sbc.message.parentRoot = r := (hslot.atRoot _ _ hpr).symm.trans hrbr
      have hedge := (child_edge hkc hpr).1 (by rw [← hne])
      rw [hpar] at hedge
      have hdown := hpathT.pendingBelow hslot (x := sbc.message) (blocksOf p₁ ++ [rb]) (blocksOf x₂) hLH
      exact NodeBelow.trans _ _ _ _ (.step _ _ .refl hedge) hdown
  · left
    rw [h, hrbr]

include hw in
/-- **The finalized root of an honest store is not a FULL-side block after `rb`.** A
finalized checkpoint past the anchor is justified on a store run (`finalized_source`). Its
block is after `rb` and no later than the first slot of its epoch, so it is on the EMPTY side
(`FinalitySetting.target_empty`), which is not the FULL side (`NodeBelow.empty_not_full`). -/
theorem FinalitySetting.fin_not_full
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb < t)
    (ht' : t ≤ finSlot E₁)
    (hV : VotesEmpty honest node run r rb A a E₁ nodeOf honestOf t)
    {fb : BeaconBlock}
    (hfb : FcMap.lookup (run v t).store.blocks (run v t).store.finalizedCheckpoint.root = some fb)
    (hgt : rb.slot < fb.slot)
    (hle : fb.slot.toNat ≤ (run v t).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch)
    (hfull : NodeBelow (run v t).store (.full r)
      (.pending (run v t).store.finalizedCheckpoint.root)) : False := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hle' : raceLo rb ≤ t := Nat.le_of_lt ht
  obtain ⟨hI, -, -, -, hft⟩ := hset.storeFacts hw hcol hv hle' ht'
  have hq := hset.held v hv t hle' ht'
  have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
  have hlate := hset.late
  generalize hF : (run v t).store.finalizedCheckpoint = F at hfb hle hfull hft
  have hFe : max (epochOf A + 2) 3 < F.epoch.toNat :=
    Nat.lt_of_mul_lt_mul_right (a := slotsPerEpoch) (by omega)
  have hfA : (EthCLSpecs.Heze.currentEpochOf (pureState A)).toNat < F.epoch.toNat := by
    rw [currentEpochOf_epochOf]
    omega
  obtain ⟨k, steps, v', hrun, hpath, -, -, hfin, hsr⟩ := finalized_source hw (hF ▸ hI.fSource) hfA
    hset.roots hset.cps hset.ord hset.sphr (hset.totals v hv t hle' ht')
  have hFt : F.epoch.toNat ≤ E₁ + 4 := by
    have : t / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right ht'
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    omega
  have hE := hset.target_empty hw hcol hv hle' ht' hrun hpath hsr (x := toCp F)
    (justified_of_fin hfin) (by unfold anchorK; simp only [toCp]; omega)
    (by simp only [toCp]; omega) (by simp only [toCp]; omega) ⟨fb, hfb⟩
    (fun he => by
      simp only [toCp] at he
      rw [he, hq.block] at hfb
      cases hfb
      exact UInt64.lt_irrefl _ hgt) hV
    (fun u hu t' hlo' hlt' _ _ e uu uu' _ _ cb hcb' => by
      have hqu := hset.held u hu t' hlo' (by omega)
      have hinvu : SlotInv a (run u t').store :=
        hset.anchorBlock _ hu ▸ hqu.slotInv hw (hset.fields.nodeOk _ hu) hcol
      have : cb = fb := SlotInv.block_eq hinvu hI.slot hcb hcb' hfb
      rw [this]
      exact hgt)
  exact NodeBelow.empty_not_full _ hI.slot.slots r rb hq.block _ hE hfull

end NoBlock

/-! ## EMPTY `r` stays viable at each honest head of the window -/

section Main
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root] [LawfulFcMap map ValidatorIndex] [LawfulFcMap map Checkpoint]
  [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

/-- **An honest index names one key on every run from the anchor.** It is an index of the
anchor registry (`honestReg`), so each run from `A` keeps it, with the anchor's public key
(`ChainRun.pubkey_eq`). The premises that read `honestOf` on store runs and on `H`
(`allChains`, `honestVotes`, `CarrierWindow.unslashed`, `CarrierWindow.included`) speak of the same
keys on every run. -/
theorem FinalitySetting.honest_key {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    {i : ValidatorIndex} (hi : honestOf i = true) {hi₁ hi₂ : Nat} {q₁ q₂ : List ChainStep}
    {z₁ z₂ : BeaconState} (h₁ : ChainRun hi₁ q₁ A z₁) (h₂ : ChainRun hi₂ q₂ A z₂) :
    i.toNat < z₁.validators.val.size ∧ i.toNat < z₂.validators.val.size ∧
      (z₁.validators.val[i.toNat]!).pubkey = (z₂.validators.val[i.toNat]!).pubkey := by
  have hA := hset.honestReg i hi
  obtain ⟨s1, k1⟩ := h₁.pubkey_eq hA
  obtain ⟨s2, k2⟩ := h₂.pubkey_eq hA
  exact ⟨s1, s2, k1.trans k2.symm⟩

include hw in
/-- **`ViableStep` from the honest chain.** Take an honest head run of slot `s` in the window,
with a justified block no later than `rb`, after the honest votes before `s` are on the EMPTY
side (`VotesEmpty`). Suppose that the filtered tree holds FULL `r`.

- `s` in the epoch of `rb`: `HeadRun.Base.viable_sameEpoch`.
- `s` later: the tip `T` (`CarrierWindow.tipStore`) is `rb` or below EMPTY `r`, and its state
  passes the target test of the epoch before. Every leaf below the tip has a recent voting
  source. For the finalized test (`viable_store_core`'s `hlate`), the finalized epoch starts
  at or after `rb`, so it is not genesis. Its root is `r` (`finRoot_of_full`), because
  `FinalitySetting.fin_not_full` excludes a FULL-side root. Then no block of `H` lies after `rb`
  up to its first slot (`CarrierWindow.no_block_before`). The blocks from `r` down to `T` are
  blocks of `H` (`NodeBelow.mem_path`), and the blocks below `T` are later still. -/
theorem viableStep_core {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
    {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
    {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {hv' : Nat} (hhv : hv' ≤ finSlot E₁)
    (hnb : ∀ v, honest v → ∀ t, raceLo rb < t → t ≤ hv' →
      (run v t).store.finalizedCheckpoint.epoch.toNat ≤ t / slotsPerEpoch - 1 →
      (run v t).store.finalizedCheckpoint.root = r →
      ∀ b ∈ blocksOf stepsH, rb.slot.toNat < b.slot.toNat →
      b.slot.toNat ≤ (run v t).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch → False) :
    ViableStep honest node run r rb A a E₁ nodeOf honestOf hv' := by
  intro s hlo hs' hIH _ v hv hjust
  have hs : s ≤ finSlot E₁ := Nat.le_trans hs' hhv
  obtain ⟨jb, hjb, -⟩ := hjust
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hle : raceLo rb ≤ s := Nat.le_of_lt hlo
  have hq := hset.held v hv s hle hs
  have hn := hset.fields.nodeOk v hv
  have hA0 := hset.anchorState v hv
  have hA1 := hset.anchorBlock v hv
  obtain ⟨hI, -, ha, -, -⟩ := hset.storeFacts hw hcol hv hle hs
  have hslot := hI.slot
  have hslots := hslot.slots
  have hord : StateCkptOrd (node v).anchorState := by rw [hA0]; exact hset.ord
  obtain ⟨-, hunr, hkeys, hlink, hfv⟩ := hq.viableInvs hw hcol hn hord (hset.stateRoots v hv)
  rw [hA1] at hunr hlink
  have hlate := hset.late
  have hlA : (epochOf A + 2) * slotsPerEpoch ≤ rb.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)) hlate
  have hrA : epochOf A + 2 ≤ rb.slot.toNat / slotsPerEpoch := (Nat.le_div_iff_mul_le hp).mpr hlA
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [anchor_slot_eq hset.anchorHeader]
    exact hset.aligned
  have haS' : epochOf A * slotsPerEpoch < rb.slot.toNat := by
    have : epochOf A * slotsPerEpoch < (epochOf A + 2) * slotsPerEpoch :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    omega
  have hrb := hq.block
  have hr0 : r ≠ htr a := fun h => by
    rw [h, ha] at hrb
    cases hrb
    omega
  have hlt : rb.slot.toNat < s := by unfold raceLo at hlo; omega
  obtain ⟨cs, hcsn, -⟩ := hq.slot
  have hs64 : s < 2 ^ 64 := hcsn ▸ cs.toNat_lt
  have hAt : A.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch := by
    have : rb.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch := Nat.div_le_div_right (by omega)
    unfold epochOf at hrA
    omega
  by_cases hE : s / slotsPerEpoch = rb.slot.toNat / slotsPerEpoch
  · -- Case I: the epoch of `rb`.
    have hA' : ((node v).anchorState.slot.toNat / slotsPerEpoch + 1) * slotsPerEpoch ≤
        rb.slot.toNat := by
      rw [hA0]
      unfold epochOf at hlA
      exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlA
    exact hq.viable_sameEpoch hw hcol hn hord (hset.stateRoots v hv) (by rw [hA1]; exact hr0)
      hlt hs64 hA' hE hjb
  -- Case II: a later epoch.
  have hE1 : rb.slot.toNat / slotsPerEpoch < s / slotsPerEpoch := by
    have : rb.slot.toNat / slotsPerEpoch ≤ s / slotsPerEpoch := Nat.div_le_div_right (by omega)
    omega
  obtain ⟨T, tb, sT, preT, hTk, hTa, hsT, hrunT, hpathT, hvalT, hendT, hsTb, hrbT, hsTE, hsub,
    -, hTm, hus, hw₀, hw₁, hflags, hstake⟩ := hH.tipStore hw hset hcol hv hle hs hE1
  intro nodes t0 t' hrun hfull
  obtain ⟨hJr, hJfull⟩ := justified_path_of_full _ hfv r hrun hfull
  obtain ⟨E, hEn, hEr⟩ := hq.storeEpoch
  obtain ⟨S, hS, hSv, hF⟩ := hq.finalizedStart hn (by rw [hA0, hA1]; exact hI) hord hlt hs64
    (by rw [hA0]; exact hAt)
  rw [hA0] at hF
  have hclock : ∀ k b, FcMap.lookup (run v s).store.blocks k = some b →
      (EthCLSpecs.Heze.computeEpochAtSlot b.slot).toNat ≤ E.toNat := fun k b hk => by
    rw [computeEpochAtSlot_toNat, hEn]
    exact Nat.div_le_div_right (hq.block_slot_le hn (hn.anchor_le_of_lt hlt) hk)
  have hzr := CkptInv.stateRoot_ne hI hlink
  have hna := below_not_anchor hslot hcb hTk (by
    apply UInt64.le_iff_toNat_le.mpr
    omega)
  have hET : E.toNat = sT.slot.toNat / slotsPerEpoch + 1 := by rw [hEn]; omega
  have hE2 : s / slotsPerEpoch ≤ E₁ + 4 := by
    have : s / slotsPerEpoch ≤ finSlot E₁ / slotsPerEpoch := Nat.div_le_div_right hs
    rw [finSlot, Nat.mul_div_cancel _ hp] at this
    exact this
  have hroom : E.toNat + 2 < 2 ^ 64 := by have := hH.room; omega
  have h2 : 2 ≤ sT.slot.toNat / slotsPerEpoch := by omega
  have hall : ∀ p q z, StoreRun A a (run v s).store (p ++ q) → ChainRun (2 ^ 64 - 1) p A z →
      (∀ j < z.validators.val.size, honestOf (UInt64.ofNat j) = true →
        (z.validators.val[j]!).slashed = false) ∧ RunTotals z := fun p q z hsr hz =>
    ⟨hH.unslashed v hv s hle hs p q z hsr hz, hset.totals v hv s hle hs p q z hsr hz⟩
  -- The finalized checkpoint, when its epoch starts at or after `rb`.
  have hfinr : ∀ dF, NodeBelow (run v s).store (.full r) dF →
      (∀ u, (finRead (run v s).store dF.root).run u = .ok (true, u)) → ¬ S < rb.slot →
      (run v s).store.finalizedCheckpoint.epoch.toNat ≤ s / slotsPerEpoch - 1 ∧
      (run v s).store.finalizedCheckpoint.root = r := by
    intro dF hdF hfF hSr
    have hSr' : rb.slot.toNat ≤ S.toNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hSr)
    have hFs : (run v s).store.finalizedCheckpoint.epoch.toNat ≤ s / slotsPerEpoch - 1 := by
      rcases hF with h | h
      · exfalso
        unfold epochOf at haS'
        rw [h] at hSv
        omega
      · exact h
    have hg : (run v s).store.finalizedCheckpoint.epoch ≠ EthCLSpecs.Heze.Const.genesisEpoch :=
      fun h => by
        rw [h] at hSv
        simp [EthCLSpecs.Heze.Const.genesisEpoch] at hSv
        omega
    refine ⟨hFs, ?_⟩
    rcases finRoot_of_full _ hslots hrb hS hSr hg hdF hfF with h | ⟨hfullF, fb, hfb, hgt, hfS⟩
    · exact h
    · exfalso
      have hfS' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hfS)
      exact hset.fin_not_full hw hcol hv hlo hs hIH hfb hgt (by omega) hfullF
  rcases hTm with hTr | ⟨hrbtb, hTbelow⟩
  · -- `T` is `rb`: the tip node is EMPTY `r`, and the finalized epoch starts no later than `rb`.
    subst T
    rw [hrb] at hTk
    cases hTk
    have hTm' : NodeBelow (run v s).store (.pending r) (.empty r) := .step _ _ .refl (NodeEdge.empty r)
    refine viable_store_core _ hslot hlink hzr hunr hkeys hrb hjb hJr hJfull (.empty r) .refl
      (fun z hz _ => hfv.path z r (below_decided_pending hz payloadStatus_empty_ne_pending
        (fun h => payloadStatus_empty_ne_full (congrArg ForkChoiceNode.payloadStatus h).symm)))
      hTm' hTa hrb hsT hrunT hpathT hvalT hendT hna hEr hET hclock hroom h2 hw₀ hw₁ hus hflags
      hstake hall hS ?_ nodes t0 t' hrun hfull
    intro dF hdF hfF d hd hSr
    obtain ⟨hFs, hFr⟩ := hfinr dF hdF hfF hSr
    refine ⟨.inr hFr, fun y hy _ hne => ?_⟩
    obtain ⟨yb, hyb, hgt⟩ := below_slot_gt _ hslots hrb hy hne
    refine ⟨yb, hyb, UInt64.lt_iff_toNat_lt.mpr ?_⟩
    have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
    have hsr : sT.slot.toNat / slotsPerEpoch = rb.slot.toNat / slotsPerEpoch := by rw [hsTb]
    have h1 : (run v s).store.finalizedCheckpoint.epoch.toNat ≤ rb.slot.toNat / slotsPerEpoch := by
      omega
    have h2' := Nat.mul_le_mul_right slotsPerEpoch h1
    have h3 := Nat.div_mul_le_self rb.slot.toNat slotsPerEpoch
    omega
  · -- `T` is a block of `H` below EMPTY `r`.
    refine viable_store_core _ hslot hlink hzr hunr hkeys hrb hjb hJr hJfull (.pending T) hTbelow
      (fun z h1 _ => hfv.path z T h1) .refl hTa hTk hsT hrunT hpathT hvalT hendT hna hEr hET
      hclock hroom h2 hw₀ hw₁ hus hflags hstake hall hS ?_ nodes t0 t' hrun hfull
    intro dF hdF hfF d hd hSr
    obtain ⟨hFs, hFr⟩ := hfinr dF hdF hfF hSr
    -- A block of `H` after `rb` starts after `S`.
    have hHS : ∀ b ∈ blocksOf stepsH, rb.slot.toNat < b.slot.toNat → S < b.slot := fun b hb hb1 =>
      UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_not_le fun hb2 =>
        hnb v hv s hlo hs' hFs hFr b hb hb1 (by omega))
    -- `T`'s block is the last block of its path, a block of `H`.
    have htbS : S < tb.slot := by
      obtain ⟨h0, h1⟩ := hpathT.last
      rcases List.eq_nil_or_concat (blocksOf preT) with he | ⟨L', x, he⟩
      · exact absurd (h0 he) hTa
      · have hx := h1 L' x (he.trans (List.concat_eq_append ..))
        rw [hTk] at hx
        cases hx
        exact hHS tb (hsub tb (by rw [he]; simp)) hrbtb
    refine ⟨.inr hFr, fun y hy hyd hne => ?_⟩
    obtain ⟨yb, hyb, hgt⟩ := below_slot_gt _ hslots hrb hy hne
    refine ⟨yb, hyb, ?_⟩
    rcases NodeBelow.comparable _ _ _ _ hyd hd with hyT | hTy
    · -- `y` is above `T`: its block is on the path of `T`, a block of `H` after `rb`.
      have hpy := (hy.pending_root rfl).trans _ _ _ _ hyT
      have hyax := below_not_anchor hslot hcb hyb (by
        apply UInt64.le_iff_toNat_le.mpr
        have := UInt64.lt_iff_toNat_lt.mp hgt
        omega)
      rcases hpy.mem_path hyax hpathT with h | ⟨yb', hyb', hm⟩
      · exfalso
        rw [h, ha] at hyb
        cases hyb
        have := UInt64.lt_iff_toNat_lt.mp hgt
        omega
      · rw [hyb] at hyb'
        cases hyb'
        exact hHS yb (hsub yb hm) (UInt64.lt_iff_toNat_lt.mp hgt)
    · -- `y` is at or below `T`.
      by_cases hyT : y.root = T
      · rw [hyT, hTk] at hyb
        cases hyb
        exact htbS
      · obtain ⟨yb', hyb', hgt'⟩ := below_slot_gt _ hslots hTk hTy hyT
        rw [hyb] at hyb'
        cases hyb'
        exact UInt64.lt_trans htbS hgt'

include hw in
/-- **No block of the carrier chain after `rb` up to the first slot of the finalized epoch,
when the finalized root is `r`.** The finalized checkpoint `(r, e)` is justified on a store run `C`, with an honest voter `i`
(`justified_honest_voter`). `H` places `i`'s vote of `e`, `i` being active on `H` (`active`),
and an honest validator signs one vote per target epoch (`single`). The vote on `H` names the
checkpoint root of `H` at `e`, which is a block after `rb`, not `r` (`fcase_core_active`). The
finalized epoch is at most `E₁ + 2`, so `H` weighs the epoch after it. -/
theorem CarrierWindow.no_block_before {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) {v : Node} (hv : honest v) {t : Nat} (ht : raceLo rb < t)
    (ht' : t ≤ finSlot E₁)
    (hFe : (run v t).store.finalizedCheckpoint.epoch.toNat ≤ E₁ + 2)
    (hFr : (run v t).store.finalizedCheckpoint.root = r)
    {b : BeaconBlock} (hb : b ∈ blocksOf stepsH) (hb1 : rb.slot.toNat < b.slot.toNat)
    (hb2 : b.slot.toNat ≤ (run v t).store.finalizedCheckpoint.epoch.toNat * slotsPerEpoch) :
    False := by
  have hcb : ¬ HtrCollision BeaconBlock := fun h => hcol (.inr h)
  have hp := slotsPerEpochPos
  have hle : raceLo rb ≤ t := Nat.le_of_lt ht
  obtain ⟨hI, -, ha, -, hft⟩ := hset.storeFacts hw hcol hv hle ht'
  have hq := hset.held v hv t hle ht'
  have hn := hset.fields.nodeOk v hv
  have hrb := hq.block
  have hlt : rb.slot.toNat < t := by unfold raceLo at ht; omega
  generalize hF : (run v t).store.finalizedCheckpoint = F at hFr hb2 hft hFe
  have hlate := hset.late
  have hFe' : max (epochOf A + 2) 3 < F.epoch.toNat :=
    Nat.lt_of_mul_lt_mul_right (a := slotsPerEpoch) (by omega)
  have hfA : (EthCLSpecs.Heze.currentEpochOf (pureState A)).toNat < F.epoch.toNat := by
    rw [currentEpochOf_epochOf]
    omega
  obtain ⟨k, steps, v', hrun, hpath, -, -, hfin, hsr⟩ := finalized_source hw (hF ▸ hI.fSource) hfA
    hset.roots hset.cps hset.ord hset.sphr (hset.totals v hv t hle ht')
  have hj := justified_of_fin hfin
  obtain ⟨i, d, hhon, hvote, htg⟩ := justified_honest_voter hrun hset.cps hset.ord honestOf
    (fun p q u he hu hB => hset.allChains v hv t hle ht' p q u (he ▸ hsr) hu hB) hj
    (by unfold anchorK; simp only [toCp]; omega) (by simp only [toCp]; omega)
  have he' : d.target.epoch.toNat = F.epoch.toNat :=
    congrArg EthCLLib.Proofs.FFG.Checkpoint.epoch htg
  have hroot : d.target.root = r := (congrArg EthCLLib.Proofs.FFG.Checkpoint.root htg).trans hFr
  -- `C` holds `rb`: its chain root at the finalized epoch is `r`.
  have hm := ffgChain_matches (hi := 2 ^ 64 - 1) (vals := regVals) hset.cps hset.ord
    (hrun.blocks_slot_ge (Nat.le_refl _))
  have hon : chainRoot A steps F.epoch.toNat = F.root :=
    Option.some.inj (hj.onChain fun x hx => (hm.base x hx).2)
  have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
    rw [← hset.anchorBlock v hv, anchor_slot_eq (hset.anchorBlock v hv ▸ hset.anchorHeader)]
    exact hset.aligned
  have hrbC : rb ∈ blocksOf steps := by
    rcases chainRoot_mem hset.anchorRoot hset.aligned steps (e := F.epoch.toNat) (by omega)
        (by omega) with h | ⟨bb, hbb, hbr⟩
    · -- The anchor root is not `r`: the anchor block is before `rb`.
      exfalso
      rw [hon, hFr] at h
      rw [h, ha] at hrb
      cases hrb
      have : epochOf A * slotsPerEpoch < max (epochOf A + 2) 3 * slotsPerEpoch :=
        Nat.mul_lt_mul_of_pos_right (by omega) hp
      omega
    · rw [hon, hFr] at hbr
      obtain ⟨k'', hk''⟩ := hpath.mem_lookup hbb
      rw [← hI.slot.atRoot _ _ hk'', hbr, hrb] at hk''
      cases hk''
      exact hbb
  obtain ⟨aC, sbC, vbC, bC, hC, hrbC'⟩ := split_of_mem_blocksOf steps hrbC
  obtain ⟨_, _, -, -, hvalC, -⟩ := id hsr
  -- The weigh state of `e + 1` on `H`.
  have hends := hH.ends
  have hAs : A.slot.toNat < (epochOf A + 1) * slotsPerEpoch := by
    unfold epochOf
    have := Nat.lt_div_mul_add (a := A.slot.toNat) hp
    rw [Nat.add_one_mul]
    omega
  obtain ⟨W, hW⟩ := hH.chainRun.weighAt_of_cross hH.hhi (F.epoch.toNat + 1)
    (by
      have : (epochOf A + 1) * slotsPerEpoch ≤ (F.epoch.toNat + 1 + 1) * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      have : slotsPerEpoch ≤ (epochOf A + 1) * slotsPerEpoch :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega)
    (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hends)
  have hrbe : rb.slot.toNat / slotsPerEpoch < F.epoch.toNat :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  obtain ⟨hinc, -⟩ := hH.included (F.epoch.toNat + 1) (by omega) (by omega) W hW
  obtain ⟨w₁, w₂, hws, hrW, -, -⟩ := id hW
  rw [← he'] at hW hb2 hrbe
  exact fcase_core_active hw hcol hset.roots hset.anchorFilled hset.anchorHeader hset.anchorRoot
    hset.aligned hrun hvalC hC hrbC' (hroot.trans (hI.slot.atRoot r rb hrb).symm)
    hH.hhi hH.chainRun hH.val hH.split hH.isRb hW hinc hhon
    (fun hlt' => by
      have := hH.unslashedH w₁ (.slot :: w₂) W hws hrW i.toNat hlt'
        (by rw [UInt64.ofNat_toNat]; exact hhon)
      exact this)
    (fun p q z hpq hz => hH.active p q z hpq hz i hhon d.target.epoch (by omega)
      (by omega))
    hb hb1 hb2 (by omega) (by omega)
    (fun _ _ s₂ d₂ _ _ _ hst hv₂ he => hH.single i hhon d
      ⟨v, hv, t, Nat.le_of_lt ht, ht', .inr ⟨steps, hsr, hvote⟩⟩ _ s₂ d₂ hst hv₂ he)

include hw in
/-- **`ViableStep` from the carrier chain**, over the whole window: `viableStep_core` with
`CarrierWindow.no_block_before`. The finalized epoch of an honest store lags its slot by two
epochs (`FinalitySetting.finLag`), so it is at most `E₁ + 2` up to `finSlot E₁`, inside the
range of `included`. -/
theorem viableStep_of_carrier {Node : Type} {honest : Node → Prop} {node : Node → NodeRun map}
    {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock} {A : BeaconState}
    {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision) :
    ViableStep honest node run r rb A a E₁ nodeOf honestOf (finSlot E₁) := by
  have hp := slotsPerEpochPos
  refine viableStep_core hw hset hH hcol (Nat.le_refl _)
    fun _ hv t hlo hs _ hFr b hb hb1 hb2 =>
      hH.no_block_before hw hset hcol hv hlo hs ?_ hFr hb hb1 hb2
  have hlate := hset.late
  have hbefore := hset.before
  have ht4 : t / slotsPerEpoch ≤ E₁ + 4 :=
    Nat.div_le_of_le_mul (by unfold finSlot at hs; rw [Nat.mul_comm]; exact hs)
  -- The anchor epoch is before `E₁`: `rb` is at least two epochs after it and before `E₁`.
  have hAE : epochOf A ≤ E₁ + 2 := by
    have : epochOf A * slotsPerEpoch < E₁ * slotsPerEpoch := by
      have : epochOf A * slotsPerEpoch ≤ max (epochOf A + 2) 3 * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  rcases hset.finLag hw hcol hv (Nat.le_of_lt hlo) hs with h | h <;> omega

/-- **A carrier block after `rb` by the first slot of `E₁`, when `E₁` is two epochs past `rb`.**
`live` gives a block of `H` in the epoch after `rb`, which ends by the first slot of `E₁`. -/
theorem CarrierWindow.early_block {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {honestOf : ValidatorIndex → Bool}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hE : rb.slot.toNat / slotsPerEpoch + 2 ≤ E₁) :
    ∃ b ∈ blocksOf stepsH, rb.slot.toNat < b.slot.toNat ∧ b.slot.toNat ≤ E₁ * slotsPerEpoch := by
  have hp := slotsPerEpochPos
  obtain ⟨b, hb, he⟩ := hH.live (rb.slot.toNat / slotsPerEpoch + 1) (by omega) (by omega)
  refine ⟨b, hb, Nat.lt_of_div_lt_div (c := slotsPerEpoch) (by omega), ?_⟩
  have hlt : b.slot.toNat < (rb.slot.toNat / slotsPerEpoch + 2) * slotsPerEpoch :=
    (Nat.div_lt_iff_lt_mul hp).mp (by omega)
  exact Nat.le_of_lt (Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ hE))

include hw in
/-- **The finalized root at the end of the window is not `r`.** Take a block `b` of `H` after
`rb`, no later than the first slot of `E₁`. A finalized checkpoint at `r` of epoch `E₁` or later
puts no block of `H` after `rb` up to the first slot of its epoch
(`CarrierWindow.no_block_before`), but `b` is one. The finalized epoch is at most `E₁ + 2`
(`FinalitySetting.finLag`). -/
theorem CarrierWindow.finRoot_ne {Node : Type} {honest : Node → Prop}
    {node : Node → NodeRun map} {run : Node → Nat → HeadRun map} {r : Root} {rb : BeaconBlock}
    {A : BeaconState} {a : BeaconBlock} {E₁ : Nat} {nodeOf : ValidatorIndex → Node}
    {honestOf : ValidatorIndex → Bool} {committees : Nat → Nat → Array ValidatorIndex}
    {hi : Nat} {stepsH : List ChainStep} {sH : BeaconState} {aR : List ChainStep}
    {sbR : SignedBeaconBlock} {vbR : Bool} {bR : List ChainStep}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hH : CarrierWindow honest node run rb A a E₁ honestOf hi stepsH sH aR sbR vbR bR)
    (hcol : ¬ RootCollision)
    (hb0 : ∃ b ∈ blocksOf stepsH, rb.slot.toNat < b.slot.toNat ∧
      b.slot.toNat ≤ E₁ * slotsPerEpoch) :
    FinRootNe honest run r E₁ := by
  intro v hv hE hFr
  obtain ⟨b, hb, hb1, hb2⟩ := hb0
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have h4 : E₁ * slotsPerEpoch < (E₁ + 4) * slotsPerEpoch :=
    Nat.mul_lt_mul_of_pos_right (by omega) hp
  have ht : raceLo rb < finSlot E₁ := by unfold raceLo finSlot; omega
  refine hH.no_block_before hw hset hcol hv ht (Nat.le_refl _) ?_ hFr hb hb1
    (Nat.le_trans hb2 (Nat.mul_le_mul_right _ hE))
  have hAE : epochOf A ≤ E₁ + 2 := by
    have : epochOf A * slotsPerEpoch < E₁ * slotsPerEpoch := by
      have : epochOf A * slotsPerEpoch ≤ max (epochOf A + 2) 3 * slotsPerEpoch :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have ht4 : finSlot E₁ / slotsPerEpoch = E₁ + 4 := by
    unfold finSlot
    exact Nat.mul_div_cancel _ hp
  rcases hset.finLag hw hcol hv (Nat.le_of_lt ht) (Nat.le_refl _) with h | h <;> omega

include hw in
/-- **The censored payload stays off the honest heads of the first slot.** Take an honest head
run of slot `N + 1`.

- Its justified block is no later than `rb`. EMPTY `r` is viable beside FULL `r` there
  (`HeadRun.Base.emptyViable_raceLo`). The honest inclusion list and the envelopes that omit its
  transaction put the head off FULL `r` (`DecisionSetting.head_avoids_full`).
- Its justified block is past `rb`. It is on the EMPTY side (`FinalitySetting.justified_empty`),
  and the head is below it. -/
theorem FinalitySetting.first_of_decision [LawfulFcMap map (Slot × Root)] {Node : Type}
    {honest : Node → Prop} {node : Node → NodeRun map} {run : Node → Nat → HeadRun map}
    {r : Root} {rb : BeaconBlock} {A : BeaconState} {a : BeaconBlock} {E₁ : Nat}
    {nodeOf : ValidatorIndex → Node} {honestOf : ValidatorIndex → Bool}
    {committees : Nat → Nat → Array ValidatorIndex}
    {g : UInt64} {dr : Root} {il : EthCLSpecs.Heze.InclusionList} {tSend Δ : Nat} {due : UInt64}
    {txs : ExecutionPayload → Array Transaction}
    {isValidOmission : ExecutionPayload → Transaction → Prop} {tx : Transaction}
    (hset : FinalitySetting honest node run r rb A a E₁ nodeOf honestOf committees)
    (hdec : DecisionSetting honest node run r rb g dr il tSend Δ due txs isValidOmission tx) :
    RootCollision ∨ FirstSlotAvoids honest run r rb := by
  by_cases hcol : RootCollision
  · exact .inl hcol
  refine .inr fun v hv => ?_
  have hp := slotsPerEpochPos
  have hlate := hset.late
  have hbefore := hset.before
  have hlo : raceLo rb ≤ raceLo rb := Nat.le_refl _
  have hhi : raceLo rb ≤ finSlot E₁ := by
    unfold raceLo finSlot
    have : E₁ * slotsPerEpoch ≤ (E₁ + 4) * slotsPerEpoch := Nat.mul_le_mul_right _ (by omega)
    omega
  have hn := hset.fields.nodeOk v hv
  have hQ := hset.held v hv _ hlo hhi
  have hinv := hQ.slotInv hw hn hcol
  obtain ⟨s', hrun⟩ := hQ.headRun
  rcases hset.cases v hv _ hlo hhi with ⟨jst, ⟨jb, hj, hjle⟩, -, -, -⟩ | ⟨jb, hjb, hjlt⟩
  · have hA' : (node v).anchorState.slot.toNat / slotsPerEpoch ≤
        (rb.slot.toNat + 1) / slotsPerEpoch := by
      rw [hset.anchorState v hv]
      exact hset.anchor_le hlo
    have hr0 : r ≠ htr (node v).anchor := by
      rw [hset.anchorBlock v hv]
      intro he
      obtain ⟨-, -, ha, -, -⟩ := hset.storeFacts hw hcol hv hlo hhi
      have hrb := hQ.block
      rw [he, ha] at hrb
      have hab : a = rb := Option.some.inj hrb
      have haS : a.slot.toNat ≤ epochOf A * slotsPerEpoch := by
        rw [anchor_slot_eq hset.anchorHeader]
        exact hset.aligned
      rw [hab] at haS
      have : epochOf A * slotsPerEpoch < max (epochOf A + 2) 3 * slotsPerEpoch :=
        Nat.mul_lt_mul_of_pos_right (by omega) hp
      omega
    have hord : StateCkptOrd (node v).anchorState := by
      rw [hset.anchorState v hv]
      exact hset.ord
    have hv0 := hQ.emptyViable_raceLo hw hset.sphr hcol hn hord (hset.stateRoots v hv) hA' hr0 hj
    exact (hdec.head_avoids_full hw hv hn hQ.toCore hj hjle hv0).resolve_left hcol
  · have hj := hset.justified_empty hw hcol hv hlo hhi hjb hjlt
      (fun _ _ _ _ h1 h2 => absurd h2 (Nat.not_lt.mpr h1))
    exact below_emptySide_not_full _ hinv.slots r rb hQ.block _ _ hj
      (getHead_run_below_justified _ _ _ _ hrun)

end Main

end EthCLSpecs.Proofs.Heze
