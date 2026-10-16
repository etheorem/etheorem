import EthCLSpecs.Proofs.Heze.RootFrames
import EthCLSpecs.Proofs.Heze.BlockRoot
import EthCLSpecs.Proofs.Heze.StorePure

/-!
# `EthCLSpecs.Proofs.Heze.SlotsIncrease`: block slots increase along parent links

`getHead_run_avoids_full` (`HeadAvoidsFull.lean`) assumes that the justified root is not
below the FULL node of the block at `r`. `not_nodeBelow_full_of_slot_le` gives that from
`SlotsIncrease`: each stored block has a greater slot than its stored parent. This module
proves `SlotsIncrease` at the end of a node trace from the anchor store, or it exhibits a
root collision.

## The header argument

`onBlock` runs the state transition on the block `b`. Inside it, `processBlockHeader`
checks `b` against the header `H` in the state: `H.slot < b.slot`, and
`b.parentRoot = htr H` (`stateTransition_run_header`). The parent block `pb` sits at
`b.parentRoot`, and a stored block sits at its own root. A block root is the root of its
header (`htr_eq_htr_headerOf`, `BlockRoot.lean`). So `htr H = htr (headerOf pb)`. Either
`H` is the header of `pb`, and then `pb.slot < b.slot`, or two distinct headers share a
root. The argument reads nothing else from the state, so it needs no frame over the
state transition.

The parent state is the uncached box of a plain value, and the state transition keeps
that box uncached (`keepsUncached_stateTransition`). So the header lemmas take plain
values.

## The invariant

`SlotInv a s` holds for the anchor block `a` and the store `s`. It has six parts: each
stored block sits at its own root, and each key of `blockStates` is a key of `blocks`.
Each stored block other than `a` has its parent in `blocks`. No block sits at the parent
root of `a`. Block slots increase along parent links (`SlotsIncrease s`). The last part is
`BlockStatesPure s`: every state in `blockStates` is the uncached box of a plain value.

- `SlotInv.anchor`: the anchor store of `getForkchoiceStore` from `pureState v` meets
  it, when the parent root of `a` is not the root of `a`.
- `SlotInv.onBlock`: `onBlock` keeps it, or exhibits a `RootCollision`. The run
  inversion `onBlock_run_ok` (`StorePure.lean`) gives the parent state, the state
  transition, and the two inserts. An old block at the new root that differs from `b` is
  a block collision.
- The envelope handler stores back, at the envelope root, the state it read there
  (`onExecutionPayloadEnvelope_run_ok`). The other handlers keep both maps.
- `NodeTrace.slotInv` lifts the steps to a trace with no block at the parent root of `a`.

`SlotInv.justified_not_below` turns the invariant into the justified-root hypothesis of
`getHead_run_avoids_full`, given a justified block with a slot no greater than the block
at `r`. `inclusionList_missing_tx_anchored` composes this with
`inclusionList_missing_tx_trace` (`RootFrames.lean`) on a trace from the anchor store.

The block-root lemma needs the combine-width law, so the theorems that use it take the
law as the hypothesis `hw`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt run_get_bind_eq_ok run_assert_bind_eq_ok
  run_bind_eq_ok_pure LawfulFcMap pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Store Root BeaconBlock)

section
variable [Preset] [HasherTag]

/-- A successful `processBlockHeader` run checked the header of the state `v` it read: the
block has a greater slot, and the block's parent root is the root of that header. -/
theorem processBlockHeader_run_ok (b : BeaconBlock) (v w : BeaconState)
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState v)
      = .ok ((), pureState w)) :
    v.latestBlockHeader.slot < b.slot ∧ b.parentRoot = htr v.latestBlockHeader := by
  unfold EthCLSpecs.Heze.processBlockHeader at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hslot, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hparent, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact ⟨hslot, beq_iff_eq.mp hparent⟩

variable [Config] [CryptoBackend]

/-- A successful `stateTransition` run from the uncached box of `v` passes through
`processBlockHeader`. So some state `t` on the way has a header with a smaller slot than
the block, and the block's parent root is the root of that header. Every step before the
header step keeps the uncached box, so `t` is a plain value. -/
theorem stateTransition_run_header (sb : EthCLSpecs.Heze.SignedBeaconBlock) (v w : BeaconState)
    (h : (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb).run (pureState v)
      = .ok ((), pureState w)) :
    ∃ t : BeaconState, t.latestBlockHeader.slot < sb.message.slot ∧
      sb.message.parentRoot = htr t.latestBlockHeader := by
  unfold EthCLSpecs.Heze.stateTransition at h
  -- `processSlots`, then the read, the `Except` result, and the assert of the signature
  -- check.
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok_pure (keepsUncached_processSlots _) h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok_pure (by keeps_uncached) h
  -- `processBlock`: the parent payload step, then the header step.
  obtain ⟨_, _, hblock, -⟩ := run_bind_eq_ok_pure (keepsUncached_processBlock _) h
  unfold EthCLSpecs.Heze.processBlock at hblock
  obtain ⟨_, t, -, hblock⟩ :=
    run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) hblock
  obtain ⟨⟨⟩, _, hheader, -⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) hblock
  exact ⟨t, processBlockHeader_run_ok _ _ _ hheader⟩

end

section Invariant
variable [Preset] [HasherTag] {map : MapKind} [FcMap map]

/-- Two distinct values of `T` with one root. -/
def HtrCollision (T : Type) [SizzLean.SSZRepr T] : Prop :=
  ∃ x y : T, x ≠ y ∧ htr x = htr y

/-- The store invariant behind `SlotsIncrease`, for the anchor block `a`:

- every stored block sits at its own root;
- every key of `blockStates` is a key of `blocks`;
- every stored block other than the anchor has its parent in `blocks`;
- no block sits at the parent root of the anchor;
- block slots increase along parent links;
- every state in `blockStates` is the uncached box of a plain value. -/
structure SlotInv (a : BeaconBlock) (s : Store map) : Prop where
  atRoot : ∀ k b, FcMap.lookup s.blocks k = some b → htr b = k
  stateKeys : ∀ k, (FcMap.lookup s.blockStates k).isSome →
    ∃ b, FcMap.lookup s.blocks k = some b
  parentIn : ∀ k b, FcMap.lookup s.blocks k = some b →
    b = a ∨ ∃ pb, FcMap.lookup s.blocks b.parentRoot = some pb
  anchorParent : FcMap.lookup s.blocks a.parentRoot = none
  slots : SlotsIncrease s
  statesPure : BlockStatesPure s

variable [LawfulFcMap map Root]

omit [Preset] [HasherTag] in
/-- A lookup after an insert: the inserted key with the inserted value, or another key
with its old value. -/
theorem lookup_insert_cases {V : Type} (m : map Root V) (k c : Root) (x v : V)
    (h : FcMap.lookup (FcMap.insert m k x) c = some v) :
    (c = k ∧ v = x) ∨ (c ≠ k ∧ FcMap.lookup m c = some v) := by
  by_cases hc : k = c
  · subst hc
    rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne m k c x hc] at h
    exact Or.inr ⟨fun h' => hc h'.symm, h⟩

omit [Preset] [HasherTag] in
/-- A lookup after an insert at another key is the old lookup. -/
theorem lookup_insert_of_ne {V : Type} (m : map Root V) (k c : Root) (x : V) (hc : c ≠ k) :
    FcMap.lookup (FcMap.insert m k x) c = FcMap.lookup m c :=
  EthCLLib.Proofs.LawfulFcMap.lookup_insert_ne m k c x (fun h => hc h.symm)

/-- The block step of the invariant. The store `post` has the block `b` inserted at its
root `k`, and the uncached box of a state `st` inserted at the same key. The parent of `b`
is in `pre` with a smaller slot. The old block at `k` is `b` or absent, and `k` is not the
parent root of the anchor. Then `post` meets the invariant. -/
theorem SlotInv.insert_block {a : BeaconBlock} {pre post : Store map} (hpre : SlotInv a pre)
    (b pb : BeaconBlock) (st : BeaconState)
    (hblocks : post.blocks = FcMap.insert pre.blocks (htr b) b)
    (hstates : post.blockStates = FcMap.insert pre.blockStates (htr b) (pureState st))
    (hpb : FcMap.lookup pre.blocks b.parentRoot = some pb) (hslot : pb.slot < b.slot)
    (hold : FcMap.lookup pre.blocks (htr b) = none ∨ FcMap.lookup pre.blocks (htr b) = some b)
    (hka : htr b ≠ a.parentRoot) :
    SlotInv a post := by
  -- The old block at the parent root of a stored block is `b`, when that root is `htr b`.
  have hparentOld : ∀ px, FcMap.lookup pre.blocks (htr b) = some px → px = b := by
    intro px hpx
    rcases hold with hnone | hsome
    · rw [hnone] at hpx
      cases hpx
    · rw [hsome] at hpx
      exact (Option.some.inj hpx).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, hpre.statesPure.insert _ st hstates⟩
  · -- Every stored block sits at its own root.
    intro k x hx
    rw [hblocks] at hx
    rcases lookup_insert_cases _ _ _ _ _ hx with ⟨rfl, rfl⟩ | ⟨_, hx⟩
    · rfl
    · exact hpre.atRoot k x hx
  · -- Every key of `blockStates` is a key of `blocks`.
    intro k hs
    rw [hstates] at hs
    rw [hblocks]
    by_cases hk : k = htr b
    · subst hk
      exact ⟨b, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self _ _ _⟩
    · rw [lookup_insert_of_ne _ _ _ _ hk] at hs
      obtain ⟨x, hx⟩ := hpre.stateKeys k hs
      exact ⟨x, (lookup_insert_of_ne _ _ _ _ hk).trans hx⟩
  · -- Every stored block other than the anchor has its parent in `blocks`.
    intro k x hx
    rw [hblocks] at hx ⊢
    have hparentIn : ∀ r, (∃ pr, FcMap.lookup pre.blocks r = some pr) →
        ∃ pr, FcMap.lookup (FcMap.insert pre.blocks (htr b) b) r = some pr := by
      intro r ⟨pr, hr⟩
      by_cases hrk : r = htr b
      · subst hrk
        exact ⟨b, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self _ _ _⟩
      · exact ⟨pr, (lookup_insert_of_ne _ _ _ _ hrk).trans hr⟩
    rcases lookup_insert_cases _ _ _ _ _ hx with ⟨-, rfl⟩ | ⟨_, hx⟩
    · exact Or.inr (hparentIn _ ⟨pb, hpb⟩)
    · rcases hpre.parentIn k x hx with hxa | hpx
      · exact Or.inl hxa
      · exact Or.inr (hparentIn _ hpx)
  · -- No block sits at the parent root of the anchor.
    rw [hblocks, lookup_insert_of_ne _ _ _ _ (fun h => hka h.symm)]
    exact hpre.anchorParent
  · -- Block slots increase along parent links.
    intro k x px hx hpx
    rw [hblocks] at hx hpx
    rcases lookup_insert_cases _ _ _ _ _ hx with ⟨-, rfl⟩ | ⟨_, hx⟩
    · -- `x` is `b`. Its parent is `pb`, or `b` itself when `b.parentRoot = htr b`.
      rcases lookup_insert_cases _ _ _ _ _ hpx with ⟨hroot, rfl⟩ | ⟨_, hpx⟩
      · rw [hroot] at hpb
        rw [hparentOld pb hpb] at hslot
        exact absurd hslot (UInt64.lt_irrefl _)
      · rw [hpb] at hpx
        rw [← Option.some.inj hpx]
        exact hslot
    · rcases lookup_insert_cases _ _ _ _ _ hpx with ⟨hroot, hpxb⟩ | ⟨_, hpx⟩
      · -- The parent of `x` is the new block. `x` is not the anchor, so its old parent was
        -- the block at `htr b`, which is `b`.
        rw [hpxb]
        rcases hpre.parentIn k x hx with hxa | ⟨p0, hp0⟩
        · rw [hxa] at hroot
          exact absurd hroot.symm hka
        · have hp0' := hp0
          rw [hroot] at hp0'
          have hb : p0 = b := hparentOld p0 hp0'
          rw [hb] at hp0
          exact hpre.slots k x b hx hp0
      · exact hpre.slots k x px hx hpx

omit [LawfulFcMap map Root] in
/-- A step that keeps the block map, adds no key to `blockStates`, and keeps the states
there uncached keeps the invariant. -/
theorem SlotInv.of_blocks_eq {a : BeaconBlock} {pre post : Store map} (hpre : SlotInv a pre)
    (hblocks : post.blocks = pre.blocks)
    (hstates : ∀ k, (FcMap.lookup post.blockStates k).isSome →
      (FcMap.lookup pre.blockStates k).isSome)
    (hpure : BlockStatesPure post) :
    SlotInv a post := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hpure⟩
  · rw [hblocks]
    exact hpre.atRoot
  · intro k hk
    rw [hblocks]
    exact hpre.stateKeys k (hstates k hk)
  · rw [hblocks]
    exact hpre.parentIn
  · rw [hblocks]
    exact hpre.anchorParent
  · intro k x px hx hpx
    rw [hblocks] at hx hpx
    exact hpre.slots k x px hx hpx

variable [Config] [CryptoBackend]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- `onBlock` keeps the invariant, or two distinct headers share a root, or two distinct
blocks share a root. The block root must not be the parent root of the anchor.

`processBlockHeader` checked a header `H` against the block: `H` has a smaller slot, and
the parent root of the block is `htr H`. The parent block `pb` sits at that root, and
`htr pb` is the root of its header (`htr_eq_htr_headerOf`). So `H` is the header of `pb`,
or the two headers collide. -/
theorem SlotInv.onBlock {a : BeaconBlock} {pre post : Store map} (hpre : SlotInv a pre)
    (sb : EthCLSpecs.Heze.SignedBeaconBlock)
    (h : (EthCLSpecs.Heze.onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      sb).run pre = .ok ((), post))
    (hka : htr sb.message ≠ a.parentRoot) :
    SlotInv a post ∨ HtrCollision EthCLSpecs.Heze.BeaconBlockHeader ∨
      HtrCollision BeaconBlock := by
  obtain ⟨pv, postState, hps, htrans, hblocks, hstates⟩ :=
    onBlock_run_ok sb pre post hpre.statesPure h
  obtain ⟨t, hslotH, hparentH⟩ := stateTransition_run_header sb pv postState htrans
  obtain ⟨pb, hpb⟩ := hpre.stateKeys _ (by rw [hps]; rfl)
  have hpbRoot : htr pb = sb.message.parentRoot := hpre.atRoot _ _ hpb
  by_cases hH : t.latestBlockHeader = headerOf pb
  · -- The checked header is the header of the parent block.
    have hslot : pb.slot < sb.message.slot := by
      rw [hH] at hslotH
      exact hslotH
    cases hold : FcMap.lookup pre.blocks (htr sb.message) with
    | none =>
      exact Or.inl (hpre.insert_block sb.message pb postState hblocks hstates hpb hslot
        (Or.inl hold) hka)
    | some b0 =>
      by_cases hb0 : b0 = sb.message
      · rw [hb0] at hold
        exact Or.inl (hpre.insert_block sb.message pb postState hblocks hstates hpb hslot
          (Or.inr hold) hka)
      · exact Or.inr (Or.inr ⟨b0, sb.message, hb0, hpre.atRoot _ _ hold⟩)
  · -- Two distinct headers with the root of the parent block.
    refine Or.inr (Or.inl ⟨t.latestBlockHeader, headerOf pb, hH, ?_⟩)
    rw [← hparentH, ← hpbRoot]
    exact htr_eq_htr_headerOf hw pb

omit [CryptoBackend] in
/-- The anchor store of `getForkchoiceStore` from the uncached box of `anchorState` meets
the invariant, when the parent root of the anchor block is not its own root. -/
theorem SlotInv.anchor (anchorState : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : EthCLSpecs.Heze.getForkchoiceStore (pureState anchorState) a = .ok s0)
    (hparent : a.parentRoot ≠ htr a) :
    SlotInv a s0 := by
  have hpure := BlockStatesPure.anchor anchorState a s0 h
  simp only [EthCLSpecs.Heze.getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  -- The only block is the anchor, at its own root.
  have honly : ∀ k b, FcMap.lookup (FcMap.insert (FcMap.empty : map Root BeaconBlock) (htr a) a)
      k = some b → k = htr a ∧ b = a := by
    intro k b hk
    rcases lookup_insert_cases _ _ _ _ _ hk with hk | ⟨_, hk⟩
    · exact hk
    · rw [EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hk
      cases hk
  have hnoParent : FcMap.lookup (FcMap.insert (FcMap.empty : map Root BeaconBlock) (htr a) a)
      a.parentRoot = none := by
    rw [lookup_insert_of_ne _ _ _ _ hparent, EthCLLib.Proofs.LawfulFcMap.lookup_empty]
  refine ⟨?_, ?_, ?_, hnoParent, ?_, hpure⟩
  · intro k b hk
    obtain ⟨rfl, rfl⟩ := honly k b hk
    rfl
  · intro k hk
    by_cases hka : k = htr a
    · subst hka
      exact ⟨a, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self _ _ _⟩
    · rw [lookup_insert_of_ne _ _ _ _ hka, EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hk
      cases hk
  · intro k b hk
    exact Or.inl (honly k b hk).2
  · intro k b pb hk hpb
    obtain ⟨-, rfl⟩ := honly k b hk
    rw [hnoParent] at hpb
    cases hpb

end Invariant

section Events
variable [Preset] [HasherTag]

/-- One of the two root collisions: two distinct headers, or two distinct blocks, with one
root. -/
def RootCollision : Prop :=
  HtrCollision EthCLSpecs.Heze.BeaconBlockHeader ∨ HtrCollision BeaconBlock

/-- The event is not a block at the parent root of the anchor `a`. -/
def HandlerEvent.NotAtAnchorParent (a : BeaconBlock) : HandlerEvent → Prop
  | .block sb => htr sb.message ≠ a.parentRoot
  | _ => True

/-- `NotAtAnchorParent` compares two roots, so it is decidable. -/
instance HandlerEvent.NotAtAnchorParent.decidable (a : BeaconBlock) (e : HandlerEvent) :
    Decidable (e.NotAtAnchorParent a) := by
  unfold HandlerEvent.NotAtAnchorParent
  split <;> infer_instance

variable [Config] [CryptoBackend] {map : MapKind} [FcMap map]

omit [Config] [CryptoBackend] in
/-- A handler run that keeps both block maps keeps the invariant. -/
theorem SlotInv.of_keeps_blockMaps {a : BeaconBlock} {pre post : Store map}
    (hpre : SlotInv a pre) (x : ForkChoiceStoreRun (Store map) Unit)
    (hx : KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
      (pre.blocks, pre.blockStates) x)
    (h : x.run pre = .ok ((), post)) : SlotInv a post := by
  have hmaps := hx pre () post rfl h
  injection hmaps with hblocks hstates
  refine hpre.of_blocks_eq hblocks (fun k hk => by rwa [hstates] at hk) ?_
  intro k
  rw [hstates]
  exact hpre.statesPure k

variable [LawfulFcMap map Root]
  [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
    EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- A handler event keeps the invariant, or exhibits a root collision. The event must not be
a block at the parent root of the anchor. -/
theorem SlotInv.handler {a : BeaconBlock} {pre post : Store map} (hpre : SlotInv a pre)
    (e : HandlerEvent) (he : e.NotAtAnchorParent a)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) :
    SlotInv a post ∨ RootCollision := by
  cases e with
  | tick time =>
    exact Or.inl (hpre.of_keeps_blockMaps _ (onTick_keeps_blockMaps _ time) h)
  | block sb => exact hpre.onBlock hw sb h he
  | attestation att isFromBlock =>
    exact Or.inl (hpre.of_keeps_blockMaps _ (onAttestation_keeps_blockMaps _ att isFromBlock) h)
  | attesterSlashing asl =>
    exact Or.inl (hpre.of_keeps_blockMaps _ (onAttesterSlashing_keeps_blockMaps _ asl) h)
  | payloadAttestation msg isFromBlock =>
    exact Or.inl (hpre.of_keeps_blockMaps _
      (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock) h)
  | envelope signedEnv =>
    obtain ⟨hblocks, v, hst, hstates⟩ :=
      onExecutionPayloadEnvelope_run_ok signedEnv pre post hpre.statesPure h
    refine Or.inl (hpre.of_blocks_eq hblocks (fun k hk => ?_)
      (hpre.statesPure.insert _ v hstates))
    rw [hstates] at hk
    by_cases hkr : k = signedEnv.message.beaconBlockRoot
    · subst hkr
      rw [hst]
      rfl
    · rwa [lookup_insert_of_ne _ _ _ _ hkr] at hk

include hw in
/-- The invariant along a trace. From a store that meets it, every trace with no block at
the parent root of the anchor ends in a store that meets it, or a root collision exists. -/
theorem NodeTrace.slotInv {a : BeaconBlock} {s0 s : Store map} {events : List TraceEvent}
    {arrivals : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (h0 : SlotInv a s0)
    (hev : ∀ e, TraceEvent.handler e ∈ events → e.NotAtAnchorParent a) :
    SlotInv a s ∨ RootCollision := by
  revert hev
  induction h with
  | nil => intro _; exact Or.inl h0
  | handler e _ hrun ih =>
    intro hev
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he')) with hinv | hc
    · exact hinv.handler hw e (hev e (List.mem_append_right _ (List.mem_singleton_self _))) hrun
    · exact Or.inr hc
  | inclusionList signed t _ hclock hrun ih =>
    intro hev
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he')) with hinv | hc
    · rw [onInclusionList_run_eq _ signed t hclock
        (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
      injection hrun with hrun
      injection hrun with _ hrun
      subst hrun
      exact Or.inl (hinv.of_blocks_eq rfl (fun _ hk => hk) hinv.statesPure)
    · exact Or.inr hc

end Events

section Head
variable [Preset] [HasherTag] {map : MapKind} [FcMap map]

/-- Under the invariant, the justified root is not below the FULL node of `r` when the
justified block has a slot no greater than the block at `r`. This is the justified-root
hypothesis of `getHead_run_avoids_full`. -/
theorem SlotInv.justified_not_below {a : BeaconBlock} {s : Store map} (hinv : SlotInv a s)
    {r : Root} {rootBlock jb : BeaconBlock} (hr : FcMap.lookup s.blocks r = some rootBlock)
    (hj : FcMap.lookup s.blocks s.justifiedCheckpoint.root = some jb)
    (hle : jb.slot ≤ rootBlock.slot) :
    ¬ NodeBelow s (.full r) (.pending s.justifiedCheckpoint.root) :=
  not_nodeBelow_full_of_slot_le s hinv.slots r rootBlock hr _ jb hj hle fun h =>
    payloadStatus_full_ne_pending (congrArg EthCLSpecs.Heze.ForkChoiceNode.payloadStatus h).symm

variable [Config] [CryptoBackend] [LawfulFcMap map Root]
  [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
    EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]
  (hw : ∀ a b : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) a b).size = 32)

include hw in
/-- The missing-transaction result on a node trace from the anchor store.

The node starts at the anchor store of `getForkchoiceStore` and runs a trace to `pre`.
`DichotomyHypotheses` holds at `pre`, `pre` holds the block at `r`, and `tx` is missing
with no valid omission. Then the envelope handler succeeds. Take any trace after it, with
no second envelope for `r` and no other block at `r`. At its end, in the slot after the
block, take a justified block with a slot no greater than the block at `r`. Then
`UnsatisfiedPayload` holds and the head avoids the FULL node of `r`, or a root collision
exists.

No trace event may be a block at the parent root of the anchor, and that root is not the
root of the anchor itself. The combine-width law `hw` gives the block-root lemma. -/
theorem inclusionList_missing_tx_anchored {anchorState : BeaconState} {a : BeaconBlock}
    {s0 : Store map}
    (hanchor : EthCLSpecs.Heze.getForkchoiceStore (pureState anchorState) a = .ok s0)
    (hself : a.parentRoot ≠ htr a) {es1 : List TraceEvent}
    {arr1 : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)} {pre : Store map}
    (htrace : NodeTrace s0 es1 arr1 pre)
    (hev1 : ∀ e, TraceEvent.handler e ∈ es1 → e.NotAtAnchorParent a)
    {isValidOmission : EthCLSpecs.Heze.ExecutionPayload → EthCLSpecs.Heze.Transaction → Prop}
    {signedEnv : EthCLSpecs.Heze.SignedExecutionPayloadEnvelope} {state : BeaconState}
    {committee : Vector EthCLSpecs.Heze.ValidatorIndex
      EthCLSpecs.Heze.Const.inclusionListCommitteeSize}
    {before after : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)}
    {signed : EthCLSpecs.Heze.SignedInclusionList} {t : UInt64}
    {il : EthCLSpecs.Heze.InclusionList} (rootBlock : BeaconBlock)
    (h : DichotomyHypotheses isValidOmission pre signedEnv state committee before after
      signed t il)
    (hpre : FcMap.lookup pre.blocks signedEnv.message.beaconBlockRoot = some rootBlock)
    {tx : EthCLSpecs.Heze.Transaction} (htx : tx ∈ il.transactions.toArray)
    (hmissing : tx ∉ signedEnv.message.payload.transactions.toArray)
    (hinvalid : ¬ isValidOmission signedEnv.message.payload tx) :
    ∃ post : Store map,
      (EthCLSpecs.Heze.onExecutionPayloadEnvelope (map := map)
          (StoreTransition := ForkChoiceStoreRun (Store map)) signedEnv).run pre
        = .ok ((), post) ∧
      ∀ (events : List TraceEvent)
        (arrivals : List (EthCLSpecs.Heze.SignedInclusionList × UInt64)) (s : Store map),
        NodeTrace post events arrivals s →
        (∀ e, TraceEvent.handler e ∈ events →
          e.KeepsBlockAt signedEnv.message.beaconBlockRoot (some rootBlock)) →
        (∀ e, TraceEvent.handler e ∈ events → e.NotEnvelopeAt signedEnv.message.beaconBlockRoot) →
        (∀ e, TraceEvent.handler e ∈ events → e.NotAtAnchorParent a) →
        (EthCLSpecs.Heze.getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
            s).run s = .ok (rootBlock.slot + 1, s) →
        ¬ (rootBlock.slot + 1 < rootBlock.slot) →
        ∀ jb : BeaconBlock, FcMap.lookup s.blocks s.justifiedCheckpoint.root = some jb →
        jb.slot ≤ rootBlock.slot →
        (UnsatisfiedPayload s signedEnv.message.beaconBlockRoot rootBlock ∧
          ∀ (runnerStore s' : Store map) (head : EthCLSpecs.Heze.ForkChoiceNode),
            (EthCLSpecs.Heze.getHead (StoreTransition := ForkChoiceStoreRun (Store map)) s).run
                runnerStore = .ok (head, s') →
            ¬ NodeBelow s (.full signedEnv.message.beaconBlockRoot) head) ∨
        RootCollision := by
  obtain ⟨post, hrun, hrest⟩ := inclusionList_missing_tx_trace rootBlock h hpre htx hmissing hinvalid
  refine ⟨post, hrun, fun events arrivals s htrace2 hblock henv hanc hslot hno jb hj hle => ?_⟩
  obtain ⟨hunsat, hhead⟩ := hrest events arrivals s htrace2 hblock henv hslot hno
  -- The whole trace: to `pre`, the envelope, then to `s`.
  have henvTrace : NodeTrace pre [TraceEvent.handler (.envelope signedEnv)] [] post := by
    simpa using NodeTrace.handler (s0 := pre) (.envelope signedEnv) NodeTrace.nil hrun
  have hall := (htrace.append henvTrace).append htrace2
  have hevAll : ∀ e, TraceEvent.handler e ∈ es1 ++ [TraceEvent.handler (.envelope signedEnv)]
      ++ events → e.NotAtAnchorParent a := by
    intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | he
    · exact hev1 e he
    · cases he
      trivial
    · exact hanc e he
  rcases hall.slotInv hw (SlotInv.anchor anchorState a s0 hanchor hself) hevAll with hinv | hc
  · exact Or.inl ⟨hunsat, hhead (hinv.justified_not_below hunsat.block hj hle)⟩
  · exact Or.inr hc

end Head

end EthCLSpecs.Proofs.Heze
