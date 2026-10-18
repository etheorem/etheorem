import EthCLSpecs.Proofs.Heze.CheckpointInvariants
import EthCLSpecs.Proofs.Heze.SlotsIncrease

/-!
# `EthCLSpecs.Proofs.Heze.BlockChain`: the block states and the checkpoints trace to the anchor

A node starts at the anchor store of `getForkchoiceStore`, from the anchor state and the
anchor block `a`, and runs a trace of handler events. This module proves an invariant of
every store on the trace, `CkptInv`, or it exhibits a root collision (`NodeTrace.ckptInv`).

- `chains`: each stored state ends a chain run from the anchor state. The blocks of the run
  are the blocks on the parent links from the root of the state down to `a`
  (`AncestorPath`). Each block step validates the state root, and no block has a zero state
  root (`ValidatedSteps`). The trace theorem takes the second fact as a premise on the block
  events. The run is empty or ends with a block step (`EndsAtBlock`).
- The four store checkpoints come from block states (`CheckpointSource`). A checkpoint is
  the anchor checkpoint, or the checkpoint of a state on such a chain run, or the
  checkpoint that `process_justification_and_finalization` writes on that state.
- `ord`, `uord`: in each pair, the finalized epoch is at most the justified epoch.
- `slot`: the slot invariant `SlotInv` of `SlotsIncrease.lean`.

## The steps

`onBlock` runs the state transition from the parent state `pv` to `w`
(`onBlock_run_ckpt`). The parent root has a chain run to `pv`, and `stateTransition_chainRun`
extends it to `w`. The path of the new root is the path of the parent with the new block.
An insert at a root keeps every old path, when the old block at that root is the new block
or absent. Otherwise two distinct blocks share a root. The new block is not `a`, since no
block sits at the parent root of `a`.

The checkpoints that `onBlock` writes are the pairs of `w` and of the pull-up of `w`. Both
pairs are ordered, since `w` keeps the state order of the anchor state
(`ChainRun.stateCkptOrd`). `onTick` copies the unrealized pair into the realized pair
(`TickRel`). The envelope handler stores back the state it read. The other handlers keep the
block maps and the checkpoints.

The chain runs take the bound `2 ^ 64 - 1`, which every block slot meets. A slot step of
such a run does not wrap the slot, so the run keeps the state order.

`onBlock_run_ok_asserts` states the two acceptance asserts that a successful `onBlock` run
passed.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun KeepsAt LawfulFcMap pureState runPure
  run_bind_eq_ok run_get_bind_eq_ok run_assert_bind_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root Checkpoint BeaconBlock
  SignedBeaconBlock SignedInclusionList currentEpochOf processJustificationAndFinalization
  updateCheckpoints getForkchoiceStore onBlock isParentNodeFull isPayloadVerified
  getCheckpointBlock)

/-! ## Chain runs and ancestor paths -/

section Paths
variable [Preset]

/-- The blocks of the block steps of a chain run, in order. -/
def blocksOf : List ChainStep → List BeaconBlock
  | [] => []
  | .slot :: rest => blocksOf rest
  | .block sb _ :: rest => sb.message :: blocksOf rest

/-- `blocksOf` of two runs in a row. -/
theorem blocksOf_append (l1 l2 : List ChainStep) :
    blocksOf (l1 ++ l2) = blocksOf l1 ++ blocksOf l2 := by
  induction l1 with
  | nil => rfl
  | cons st rest ih =>
    cases st with
    | slot => exact ih
    | block sb v => exact congrArg (sb.message :: ·) ih

/-- Slot steps have no blocks. -/
theorem blocksOf_replicate_slot (n : Nat) : blocksOf (List.replicate n .slot) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Every block step of the run validates the state root, and no block has a zero state
root. -/
def ValidatedSteps (steps : List ChainStep) : Prop :=
  ∀ sb v, ChainStep.block sb v ∈ steps →
    v = true ∧ sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot

/-- A `stateTransition` run for a block with a nonzero state root gives validated steps: slot
steps, then the block step with `validateResult = true`. -/
theorem ValidatedSteps.append_transition {steps : List ChainStep} (h : ValidatedSteps steps)
    (n : Nat) (sb : SignedBeaconBlock) (hr : sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) :
    ValidatedSteps (steps ++ (List.replicate n .slot ++ [.block sb true])) := by
  intro sb' v hm
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
  rcases hm with hm | ⟨-, hm⟩ | hm
  · exact h sb' v hm
  · cases hm
  · cases hm
    exact ⟨rfl, hr⟩

variable [HasherTag] {map : MapKind} [FcMap map]

/-- `AncestorPath a s k bs`: the parent links of the store `s` lead from the root `k` down to
the anchor block `a`, through the blocks `bs`, oldest first. The anchor is not in `bs`. -/
inductive AncestorPath (a : BeaconBlock) (s : Store map) : Root → List BeaconBlock → Prop
  | anchor : AncestorPath a s (htr a) []
  | cons {k : Root} {b : BeaconBlock} {bs : List BeaconBlock} :
      FcMap.lookup s.blocks k = some b → b ≠ a → AncestorPath a s b.parentRoot bs →
      AncestorPath a s k (bs ++ [b])

/-- A path in `pre` is a path in `post` when each block of `pre` is in `post`. -/
theorem AncestorPath.mono {a : BeaconBlock} {pre post : Store map}
    (hb : ∀ k b, FcMap.lookup pre.blocks k = some b → FcMap.lookup post.blocks k = some b)
    {k : Root} {bs : List BeaconBlock} (h : AncestorPath a pre k bs) :
    AncestorPath a post k bs := by
  induction h with
  | anchor => exact .anchor
  | cons hk hne _ ih => exact .cons (hb _ _ hk) hne ih

variable [LawfulFcMap map Root]

/-- An insert of `b` at the root `r` keeps each block of `pre`, when the old block at `r` is
`b` or absent. -/
theorem lookup_mono_of_insert {pre post : Store map} {r : Root} {b : BeaconBlock}
    (hb : post.blocks = FcMap.insert pre.blocks r b)
    (hold : FcMap.lookup pre.blocks r = none ∨ FcMap.lookup pre.blocks r = some b) :
    ∀ k x, FcMap.lookup pre.blocks k = some x → FcMap.lookup post.blocks k = some x := by
  intro k x hx
  rw [hb]
  by_cases hk : k = r
  · subst hk
    rcases hold with h | h <;> rw [h] at hx
    · cases hx
    · rw [EthCLLib.Proofs.LawfulFcMap.lookup_insert_self, hx]
  · rw [lookup_insert_of_ne _ _ _ _ hk]
    exact hx

end Paths

/-! ## The invariant -/

section Invariant
variable [Preset] [HasherTag] [Config] [CryptoBackend] {map : MapKind} [FcMap map]

/-- Which checkpoint of a state: the current justified one or the finalized one. -/
inductive CkptKind where
  | justified
  | finalized

omit [HasherTag] [Config] [CryptoBackend] in
/-- The checkpoint of kind `k` of a state. -/
def CkptKind.of (v : BeaconState) : CkptKind → Checkpoint
  | .justified => v.currentJustifiedCheckpoint
  | .finalized => v.finalizedCheckpoint

omit [HasherTag] [Config] [CryptoBackend] in
/-- The run is empty or ends with a block step. A stored state is the state after its block,
before any later slot, so its run ends at the block. The end slot of such a run is the slot of
a block of the run. -/
def EndsAtBlock (steps : List ChainStep) : Prop :=
  steps = [] ∨ ∃ (p : List ChainStep) (sb : SignedBeaconBlock) (v : Bool),
    steps = p ++ [.block sb v]

/-- The checkpoint `c` comes from a block state. It is the anchor checkpoint, or the
checkpoint of kind `k` of a state `v` on a validated chain run from the anchor state along an
ancestor path of `s`, or of the pull-up of such a state. The run ends at its last block. -/
def CheckpointSource (anchorState : BeaconState) (a : BeaconBlock) (s : Store map)
    (k : CkptKind) (c : Checkpoint) : Prop :=
  c = { epoch := currentEpochOf (pureState anchorState), root := htr a } ∨
  ∃ (b : Root) (steps : List ChainStep) (v : BeaconState),
    ChainRun (2 ^ 64 - 1) steps anchorState v ∧ AncestorPath a s b (blocksOf steps) ∧
    ValidatedSteps steps ∧ EndsAtBlock steps ∧
    (c = k.of v ∨ ∃ w, runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v
      = .ok ((), w) ∧ c = k.of w)

/-- The checkpoint invariant of a store, for the anchor block `a` and the anchor state
`anchorState`. -/
structure CkptInv (anchorState : BeaconState) (a : BeaconBlock) (s : Store map) : Prop where
  slot : SlotInv a s
  chains : ∀ k v, FcMap.lookup s.blockStates k = some (pureState v) →
    ∃ steps, ChainRun (2 ^ 64 - 1) steps anchorState v ∧ AncestorPath a s k (blocksOf steps) ∧
      ValidatedSteps steps ∧ EndsAtBlock steps
  jSource : CheckpointSource anchorState a s .justified s.justifiedCheckpoint
  fSource : CheckpointSource anchorState a s .finalized s.finalizedCheckpoint
  ujSource : CheckpointSource anchorState a s .justified s.unrealizedJustifiedCheckpoint
  ufSource : CheckpointSource anchorState a s .finalized s.unrealizedFinalizedCheckpoint
  ord : s.finalizedCheckpoint.epoch ≤ s.justifiedCheckpoint.epoch
  uord : s.unrealizedFinalizedCheckpoint.epoch ≤ s.unrealizedJustifiedCheckpoint.epoch

/-- A source in `pre` is a source in `post` when each block of `pre` is in `post`. -/
theorem CheckpointSource.mono {anchorState : BeaconState} {a : BeaconBlock}
    {pre post : Store map} {k : CkptKind} {c : Checkpoint}
    (hb : ∀ r x, FcMap.lookup pre.blocks r = some x → FcMap.lookup post.blocks r = some x)
    (h : CheckpointSource anchorState a pre k c) : CheckpointSource anchorState a post k c := by
  rcases h with h | ⟨b, steps, v, hrun, hpath, hval, hend, hc⟩
  · exact .inl h
  · exact .inr ⟨b, steps, v, hrun, hpath.mono hb, hval, hend, hc⟩

/-- A step that keeps the slot invariant, the block map, the states of `blockStates`, and
the four checkpoints keeps the invariant. -/
theorem CkptInv.of_maps {anchorState : BeaconState} {a : BeaconBlock} {pre post : Store map}
    (hpre : CkptInv anchorState a pre) (hslot : SlotInv a post)
    (hblocks : post.blocks = pre.blocks)
    (hstates : ∀ k v, FcMap.lookup post.blockStates k = some (pureState v) →
      FcMap.lookup pre.blockStates k = some (pureState v))
    (hck : storeCkpts post = storeCkpts pre) : CkptInv anchorState a post := by
  have hb : ∀ r x, FcMap.lookup pre.blocks r = some x → FcMap.lookup post.blocks r = some x :=
    fun r x hx => by rw [hblocks]; exact hx
  simp only [storeCkpts, Prod.mk.injEq] at hck
  obtain ⟨ej, ef, euj, euf⟩ := hck
  refine ⟨hslot, fun k v hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨steps, hrun, hpath, hval⟩ := hpre.chains k v (hstates k v hk)
    exact ⟨steps, hrun, hpath.mono hb, hval⟩
  · rw [ej]; exact hpre.jSource.mono hb
  · rw [ef]; exact hpre.fSource.mono hb
  · rw [euj]; exact hpre.ujSource.mono hb
  · rw [euf]; exact hpre.ufSource.mono hb
  · rw [ej, ef]; exact hpre.ord
  · rw [euj, euf]; exact hpre.uord

variable [LawfulFcMap map Root]

/-- The anchor store meets the invariant: the only state is the anchor state at the anchor
root, with the empty run, and all four checkpoints are the anchor checkpoint. -/
theorem CkptInv.anchor (anchorState : BeaconState) (a : BeaconBlock) (s0 : Store map)
    (h : getForkchoiceStore (pureState anchorState) a = .ok s0)
    (hparent : a.parentRoot ≠ htr a) : CkptInv anchorState a s0 := by
  have hslot := SlotInv.anchor anchorState a s0 h hparent
  simp only [getForkchoiceStore] at h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_bind_eq_ok h
  obtain ⟨_, -, h⟩ := except_map_eq_ok h
  subst h
  refine ⟨hslot, fun k v hk => ?_, .inl rfl, .inl rfl, .inl rfl, .inl rfl,
    UInt64.le_refl _, UInt64.le_refl _⟩
  rcases lookup_insert_cases _ _ _ _ _ hk with ⟨rfl, hv⟩ | ⟨_, hk⟩
  · rw [pureState_inj hv]
    exact ⟨[], .nil _, .anchor, fun _ _ h => absurd h List.not_mem_nil, .inl rfl⟩
  · rw [EthCLLib.Proofs.LawfulFcMap.lookup_empty] at hk
    cases hk

omit [LawfulFcMap map Root] in
/-- `ckptPick` of two sources is a source. -/
theorem CheckpointSource.pick {anchorState : BeaconState} {a : BeaconBlock} {s : Store map}
    {k : CkptKind} {old c : Checkpoint} (ho : CheckpointSource anchorState a s k old)
    (hc : CheckpointSource anchorState a s k c) :
    CheckpointSource anchorState a s k (ckptPick old c) := by
  rcases ckptPick_cases old c with e | e <;> rw [e]
  · exact ho
  · exact hc

omit [LawfulFcMap map Root] in
/-- `onTick` keeps the invariant. It keeps the block maps and the unrealized pair, and each
realized checkpoint stays or takes the unrealized one of its kind (`TickRel`). -/
theorem CkptInv.onTick {anchorState : BeaconState} {a : BeaconBlock} {pre post : Store map}
    (hpre : CkptInv anchorState a pre) (time : UInt64)
    (h : (EthCLSpecs.Heze.onTick (map := map) (StoreTransition := ForkChoiceStoreRun (Store map))
      time).run pre = .ok ((), post)) :
    CkptInv anchorState a post := by
  obtain ⟨-, euj, euf, ej, ef, eo⟩ := onTick_growsAt time pre () post h
  have hm := onTick_keeps_blockMaps _ time pre () post rfl h
  injection hm with hb hbs
  have hmono : ∀ r x, FcMap.lookup pre.blocks r = some x → FcMap.lookup post.blocks r = some x :=
    fun r x hx => by rw [hb]; exact hx
  refine ⟨hpre.slot.of_keeps_blockMaps _ (onTick_keeps_blockMaps _ time) h, fun k v hk => ?_,
    ?_, ?_, ?_, ?_, eo hpre.ord hpre.uord, ?_⟩
  · rw [hbs] at hk
    obtain ⟨steps, hr, hp, hval⟩ := hpre.chains k v hk
    exact ⟨steps, hr, hp.mono hmono, hval⟩
  · rcases ej with e | e <;> rw [e]
    · exact hpre.jSource.mono hmono
    · exact hpre.ujSource.mono hmono
  · rcases ef with e | e <;> rw [e]
    · exact hpre.fSource.mono hmono
    · exact hpre.ufSource.mono hmono
  · rw [euj]; exact hpre.ujSource.mono hmono
  · rw [euf]; exact hpre.ufSource.mono hmono
  · rw [euj, euf]; exact hpre.uord

/-- `onBlock` keeps the invariant, or two distinct headers or blocks share a root. The block
root must not be the parent root of the anchor.

The post-state `w` ends the chain run of the parent state, extended by the state
transition. The new root has the path of the parent root with the new block. The written
checkpoints are those of `w` and of its pull-up, and both pairs are ordered because `w`
keeps the state order of the anchor state. -/
theorem CkptInv.onBlock
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {anchorState : BeaconState} {a : BeaconBlock} {pre post : Store map}
    (hpre : CkptInv anchorState a pre) (hord : StateCkptOrd anchorState)
    (sb : SignedBeaconBlock)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post))
    (hka : htr sb.message ≠ a.parentRoot)
    (hsr : sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) :
    CkptInv anchorState a post ∨ RootCollision := by
  rcases hpre.slot.onBlock hw sb h hka with hslot | hc | hc
  rotate_left
  · exact .inr (.inl hc)
  · exact .inr (.inr hc)
  obtain ⟨pv, w, u, hps, htrans, hbu, hbsu, hck, hpull⟩ :=
    onBlock_run_ckpt sb pre post hpre.slot.statesPure h
  obtain ⟨j1, f1, uj1, uf1, b1, bs1⟩ :=
    updateCheckpoints_ckpt u w.currentJustifiedCheckpoint w.finalizedCheckpoint
  have hl : FcMap.lookup (updateCheckpoints u w.currentJustifiedCheckpoint
      w.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w) := by
    rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
  obtain ⟨pulled, hjf, pb, pbs, puj, puf, hj⟩ := computePulledUpTip_run_ok _ w _ post hl hpull
  have hpb : post.blocks = FcMap.insert pre.blocks (htr sb.message) sb.message :=
    pb.trans (b1.trans hbu)
  have hpbs : post.blockStates = FcMap.insert pre.blockStates (htr sb.message) (pureState w) :=
    pbs.trans (bs1.trans hbsu)
  -- An old block at the new root other than the new block is a block collision.
  by_cases hold : FcMap.lookup pre.blocks (htr sb.message) = none ∨
      FcMap.lookup pre.blocks (htr sb.message) = some sb.message
  rotate_left
  · refine .inr (.inr ?_)
    cases hb0 : FcMap.lookup pre.blocks (htr sb.message) with
    | none => exact absurd (.inl hb0) hold
    | some b0 =>
      refine ⟨b0, sb.message, fun he => hold (.inr (by rw [hb0, he])), ?_⟩
      exact hpre.slot.atRoot _ _ hb0
  have hmono := lookup_mono_of_insert hpb hold
  -- The chain run to `w`, along the path of the new root.
  obtain ⟨steps0, hrun0, hpath0, hval0, -⟩ := hpre.chains _ pv hps
  obtain ⟨n, hrunT⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1)
    (by have := sb.message.slot.toNat_lt; omega) pv w htrans
  have hrunW := hrun0.append hrunT
  have hvalW := hval0.append_transition n sb hsr
  have hendW : EndsAtBlock (steps0 ++ (List.replicate n .slot ++ [.block sb true])) :=
    .inr ⟨steps0 ++ List.replicate n .slot, sb, true, by rw [List.append_assoc]⟩
  have hne : sb.message ≠ a := by
    intro he
    obtain ⟨b, hb⟩ := hpre.slot.stateKeys _ (by rw [hps]; rfl)
    rw [he, hpre.slot.anchorParent] at hb
    cases hb
  have hpathW : AncestorPath a post (htr sb.message)
      (blocksOf (steps0 ++ (List.replicate n .slot ++ [.block sb true]))) := by
    have e : blocksOf (steps0 ++ (List.replicate n .slot ++ [.block sb true]))
        = blocksOf steps0 ++ [sb.message] := by
      rw [blocksOf_append, blocksOf_append, blocksOf_replicate_slot]
      rfl
    rw [e]
    refine .cons ?_ hne (hpath0.mono hmono)
    rw [hpb]
    exact EthCLLib.Proofs.LawfulFcMap.lookup_insert_self _ _ _
  -- The two written pairs are ordered.
  have hordW : StateCkptOrd w := hrunW.stateCkptOrd (Nat.le_refl _) hord
  have hfinW : w.finalizedCheckpoint.epoch ≤ w.currentJustifiedCheckpoint.epoch :=
    UInt64.le_trans hordW.1 hordW.2.1
  have hfinP := processJustificationAndFinalization_run_fin_le w pulled hordW hjf
  have srcW : ∀ k, CheckpointSource anchorState a post k (k.of w) :=
    fun _ => .inr ⟨_, _, w, hrunW, hpathW, hvalW, hendW, .inl rfl⟩
  have srcP : ∀ k, CheckpointSource anchorState a post k (k.of pulled) :=
    fun _ => .inr ⟨_, _, w, hrunW, hpathW, hvalW, hendW, .inr ⟨pulled, hjf, rfl⟩⟩
  simp only [storeCkpts, Prod.mk.injEq] at hck
  obtain ⟨cj, cf, cuj, cuf⟩ := hck
  refine .inl ⟨hslot, fun k v hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `chains`: the new root has the run to `w`, and old roots keep theirs.
    rw [hpbs] at hk
    rcases lookup_insert_cases _ _ _ _ _ hk with ⟨rfl, hv⟩ | ⟨_, hk⟩
    · rw [pureState_inj hv]
      exact ⟨_, hrunW, hpathW, hvalW, hendW⟩
    · obtain ⟨steps, hr, hp, hval⟩ := hpre.chains k v hk
      exact ⟨steps, hr, hp.mono hmono, hval⟩
  · rcases hj with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e, j1, cj]
    · exact (hpre.jSource.mono hmono).pick (srcW .justified)
    · exact ((hpre.jSource.mono hmono).pick (srcW .justified)).pick (srcP .justified)
  · rcases hj with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e, f1, cf]
    · exact (hpre.fSource.mono hmono).pick (srcW .finalized)
    · exact ((hpre.fSource.mono hmono).pick (srcW .finalized)).pick (srcP .finalized)
  · rw [puj, uj1, cuj]
    exact (hpre.ujSource.mono hmono).pick (srcP .justified)
  · rw [puf, uf1, cuf]
    exact (hpre.ufSource.mono hmono).pick (srcP .finalized)
  · rcases hj with ⟨ej, ef⟩ | ⟨ej, ef⟩ <;> rw [ej, ef, j1, f1, cj, cf]
    · exact ckptPick_ord hpre.ord hfinW
    · exact ckptPick_ord (ckptPick_ord hpre.ord hfinW) hfinP
  · rw [puj, puf, uj1, uf1, cuj, cuf]
    exact ckptPick_ord hpre.uord hfinP

variable [ExecutionEngine EthCLSpecs.Heze.ExecutionPayload EthCLSpecs.Heze.Transaction
  EthCLSpecs.Heze.ExecutionRequests] [DataAvailability]
  (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)

include hw in
/-- A handler event keeps the invariant, or exhibits a root collision. The event must not be
a block at the parent root of the anchor, or a block with a zero state root. -/
theorem CkptInv.handler {anchorState : BeaconState} {a : BeaconBlock} {pre post : Store map}
    (hpre : CkptInv anchorState a pre) (hord : StateCkptOrd anchorState) (e : HandlerEvent)
    (he : e.NotAtAnchorParent a)
    (hsr : ∀ sb, e = .block sb → sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (h : (HandlerEvent.run (map := map) e).run pre = .ok ((), post)) :
    CkptInv anchorState a post ∨ RootCollision := by
  -- A handler that keeps the block maps and the checkpoints keeps the invariant.
  have hkeep : ∀ x : ForkChoiceStoreRun (Store map) Unit,
      KeepsAt (fun st : Store map => (st.blocks, st.blockStates))
        (pre.blocks, pre.blockStates) x →
      KeepsAt storeCkpts (storeCkpts pre) x → x.run pre = .ok ((), post) →
      SlotInv a post ∨ RootCollision → CkptInv anchorState a post ∨ RootCollision := by
    intro x hx hc hrun hs
    have hm := hx pre () post rfl hrun
    injection hm with hb hbs
    rcases hs with hslot | hcol
    · exact .inl (hpre.of_maps hslot hb (fun k v hk => by rw [← hbs]; exact hk)
        (hc pre () post rfl hrun))
    · exact .inr hcol
  have hs := hpre.slot.handler hw e he h
  cases e with
  | tick time => exact .inl (hpre.onTick time h)
  | block sb => exact hpre.onBlock hw hord sb h he (hsr sb rfl)
  | attestation att isFromBlock =>
    exact hkeep _ (onAttestation_keeps_blockMaps _ att isFromBlock)
      (onAttestation_keeps_ckpts _ att isFromBlock) h hs
  | attesterSlashing asl =>
    exact hkeep _ (onAttesterSlashing_keeps_blockMaps _ asl)
      (onAttesterSlashing_keeps_ckpts _ asl) h hs
  | payloadAttestation msg isFromBlock =>
    exact hkeep _ (onPayloadAttestationMessage_keeps_blockMaps _ msg isFromBlock)
      (onPayloadAttestationMessage_keeps_ckpts _ msg isFromBlock) h hs
  | envelope signedEnv =>
    -- The handler stores back, at the envelope root, the state it read there.
    obtain ⟨hblocks, v, hst, hstates⟩ :=
      onExecutionPayloadEnvelope_run_ok signedEnv pre post hpre.slot.statesPure h
    rcases hs with hslot | hcol
    · refine .inl (hpre.of_maps hslot hblocks (fun k v' hk => ?_)
        (onExecutionPayloadEnvelope_keeps_ckpts _ signedEnv pre () post rfl h))
      rw [hstates] at hk
      rcases lookup_insert_cases _ _ _ _ _ hk with ⟨rfl, hv⟩ | ⟨_, hk⟩
      · rw [hst, hv]
      · exact hk
    · exact .inr hcol

include hw in
/-- The invariant along a trace. A trace from a store that meets the invariant ends in a store
that meets it, or a root collision exists. The trace has no block at the parent root of the
anchor and no block with a zero state root. The anchor state must meet the state order. -/
theorem NodeTrace.ckptInv {anchorState : BeaconState} {a : BeaconBlock} {s0 s : Store map}
    {events : List TraceEvent} {arrivals : List (SignedInclusionList × UInt64)}
    (h : NodeTrace s0 events arrivals s) (h0 : CkptInv anchorState a s0)
    (hord : StateCkptOrd anchorState)
    (hev : ∀ e, TraceEvent.handler e ∈ events → e.NotAtAnchorParent a)
    (hsr : ∀ sb, TraceEvent.handler (.block sb) ∈ events →
      sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) :
    CkptInv anchorState a s ∨ RootCollision := by
  revert hev hsr
  induction h with
  | nil => intro _ _; exact .inl h0
  | handler e _ hrun ih =>
    intro hev hsr
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he'))
        (fun sb hm => hsr sb (List.mem_append_left _ hm)) with hinv | hc
    · exact hinv.handler hw hord e
        (hev e (List.mem_append_right _ (List.mem_singleton_self _)))
        (fun sb he => hsr sb (by rw [← he]; exact List.mem_append_right _ (List.mem_singleton_self _)))
        hrun
    · exact .inr hc
  | inclusionList signed t _ hclock hrun ih =>
    intro hev hsr
    rcases ih (fun e' he' => hev e' (List.mem_append_left _ he'))
        (fun sb hm => hsr sb (List.mem_append_left _ hm)) with hinv | hc
    · rw [onInclusionList_run_eq _ signed t hclock
        (getInclusionListDueMs_eq_of_run _ _ signed t hclock hrun)] at hrun
      injection hrun with hrun
      injection hrun with _ hrun
      subst hrun
      exact .inl (hinv.of_maps (hinv.slot.of_blocks_eq rfl (fun _ hk => hk) hinv.slot.statesPure)
        rfl (fun _ _ hk => hk) rfl)
    · exact .inr hc

end Invariant

/-! ## The acceptance asserts of `onBlock` -/

section Asserts
variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

omit [Config] in
/-- `isParentNodeFull` reads the store only. -/
theorem isParentNodeFull_keeps (store : Store map) (b : BeaconBlock) (v : Store map) :
    KeepsAt (fun s : Store map => s) v
      (isParentNodeFull (StoreTransition := ForkChoiceStoreRun (Store map)) store b) := by
  unfold isParentNodeFull
  keeps_solve

omit [FcMap map] in
/-- `getCurrentSlot` reads the store only. -/
theorem getCurrentSlot_keeps (store : Store map) (v : Store map) :
    KeepsAt (fun s : Store map => s) v
      (EthCLSpecs.Heze.getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map))
        store) := by
  keeps_solve

omit [Config] in
/-- `getCheckpointBlock` reads the store only. -/
theorem getCheckpointBlock_keeps (store : Store map) (r : Root) (e : EthCLSpecs.Heze.Epoch)
    (v : Store map) :
    KeepsAt (fun s : Store map => s) v
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store r e) := by
  keeps_solve

omit [Config] [FcMap map] in
/-- The checked start slot of an epoch reads no store. -/
theorem computeStartSlotAtEpoch_keeps (e : EthCLSpecs.Heze.Epoch) (v : Store map) :
    KeepsAt (fun s : Store map => s) v
      (liftErr (m := ForkChoiceStoreRun (Store map))
        (EthCLSpecs.Heze.computeStartSlotAtEpoch e)) := by
  keeps_solve

variable [CryptoBackend]

/-- A successful `onBlock` run passed the two acceptance asserts on the store `pre` it read.
When the parent node is full, the parent payload is verified. The checkpoint block of the
parent at the finalized epoch is the finalized root. Both reads run at `pre` and keep it. -/
theorem onBlock_run_ok_asserts (sb : SignedBeaconBlock) (pre post : Store map)
    (h : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run pre
      = .ok ((), post)) :
    ∃ (full : Bool) (fb : Root),
      (isParentNodeFull (StoreTransition := ForkChoiceStoreRun (Store map)) pre
        sb.message).run pre = .ok (full, pre) ∧
      (!full || isPayloadVerified pre sb.message.parentRoot) = true ∧
      (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) pre
        sb.message.parentRoot pre.finalizedCheckpoint.epoch).run pre = .ok (fb, pre) ∧
      pre.finalizedCheckpoint.root = fb := by
  unfold onBlock at h
  have h := run_get_bind_eq_ok _ _ _ h
  -- The parent state read keeps the store.
  obtain ⟨_, s1, hread, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, e1⟩ := getOrAssert_run_eq_ok _ _ _ _ _ _ hread
  subst e1
  -- The parent-payload assert.
  obtain ⟨full, s2, hfull, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e2 := isParentNodeFull_keeps _ _ _ _ _ _ rfl hfull
  subst e2
  obtain ⟨hc1, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The clock assert, the checked finalized slot, and the finalized-slot assert.
  obtain ⟨_, s3, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 := getCurrentSlot_keeps _ _ _ _ _ rfl hcs
  subst e3
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨_, s3', hfs, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3' := computeStartSlotAtEpoch_keeps _ _ _ _ _ rfl hfs
  subst e3'
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The finality assert.
  obtain ⟨fb, s4, hfb, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e4 := getCheckpointBlock_keeps _ _ _ _ _ _ _ rfl hfb
  subst e4
  obtain ⟨hc2, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact ⟨full, fb, hfull, hc1, hfb, beq_iff_eq.mp hc2⟩

end Asserts

end EthCLSpecs.Proofs.Heze
