import EthCLSpecs.Proofs.Heze.BlockRootsRun
import EthCLSpecs.Proofs.Heze.ChainAgree

/-!
# `EthCLSpecs.Proofs.Heze.StoreChainState`: a store holds the state of the chain

A node runs `onBlock` on a block of a chain run from the anchor state. This module proves
that the store then holds the state of the chain after that block, at the block root
(`onBlock_stores_chainState`).

## The parent links of a run

`process_block_header` checks that the parent root of the block is the root of the latest
header (`BlockStep.parent`). A slot step fills the state root of the header (`HdrFilled`). A block step needs a header slot below the state slot, so the header at a
block step is the filled header. `RootsInv` gives the root of the filled header: the root of
the last block of the run. So each block of a run names the block before it as its parent
(`ChainRun.linked`). The anchor state has the header of the anchor block, so the first block
names the anchor block. Each block has a slot greater than the anchor slot, so no block is
the anchor block.

## Runs with one list of blocks

A slot step adds one to the slot. A block step needs the block slot to be the state slot. So
the blocks of a run fix its slot steps, except the slot steps after the last block. Two runs
from one state, with one list of blocks and one end slot, end in one state
(`ChainRun.det_blocks`).

## The store

The store holds a chain run from the anchor state to the parent state (`CkptInv.chains`).
Its blocks lie on the ancestor path of the parent root, so they meet `Linked`. The blocks of
the honest chain before the block meet `Linked` too, with the same last root. Without a block
collision, the two lists are one list (`Linked.eq_of_last`). `onBlock` runs the state
transition from the parent state. So the store run and the honest run have one list of
blocks, and both end at the block slot.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState run_bind_eq_ok_pure run_get_bind_eq_ok
  run_assert_bind_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState BeaconBlock SignedBeaconBlock Store onBlock
  updateCheckpoints)

/-! ## The parent links of a run -/

section Links
variable [Preset] [HasherTag]

/-- `processBlockHeader` checks that the parent root of the block is the root of the latest
header. -/
theorem processBlockHeader_run_parent (b : BeaconBlock) (v w : BeaconState)
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState v)
      = .ok ((), pureState w)) :
    b.parentRoot = htr v.latestBlockHeader := by
  unfold EthCLSpecs.Heze.processBlockHeader at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hp, -⟩ := run_assert_bind_eq_ok _ _ _ _ h
  exact beq_iff_eq.mp hp

/-- The header of `u` has a filled state root when the header slot is below the state slot. -/
def HdrFilled (u : BeaconState) : Prop :=
  u.latestBlockHeader.slot.toNat < u.slot.toNat → u.latestBlockHeader = filledHeader u

/-- With the header of the anchor block in the anchor state, the last root of a run is the
root after its blocks. -/
theorem lastRoot_eq_lastRootOf (hw : ∀ x y : ByteArray,
      (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {st₀ : BeaconState} {a : BeaconBlock} (hanc : filledHeader st₀ = headerOf a)
    (steps : List ChainStep) : lastRoot st₀ steps = lastRootOf a (blocksOf steps) := by
  unfold lastRoot lastRootOf
  rw [hanc, ← htr_eq_htr_headerOf hw]

variable [Config] [CryptoBackend]

/-- A block step checks that the parent root of the block is the root of the latest header.
`processParentExecutionPayload` runs first, and it keeps the header. -/
theorem BlockStep.parent {sb : SignedBeaconBlock} {vr : Bool} {u u' : BeaconState}
    (h : BlockStep sb vr u u') : sb.message.parentRoot = htr u.latestBlockHeader := by
  have hb := h.2.1
  rw [processBlock_eq_tail] at hb
  obtain ⟨⟨⟩, mid, hp, hb⟩ :=
    run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) hb
  obtain ⟨⟨⟩, t, hh, -⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) hb
  have ep := processParentExecutionPayload_frame_hdr hp
  simp only [hdrView, Prod.mk.injEq] at ep
  change mid.latestBlockHeader = u.latestBlockHeader ∧ _ at ep
  rw [processBlockHeader_run_parent _ _ _ hh, ep.1]

/-- A slot step fills the header when the filled header of the start state has a nonzero
state root. -/
theorem SlotStep.hdrFilled {u u' : BeaconState} (h : SlotStep u u')
    (hf : (filledHeader u).stateRoot ≠ EthCLSpecs.Heze.zeroRoot) : HdrFilled u' := fun _ => by
  have eh := h.hdr.1
  exact (filledHeader_of_ne (by rw [eh]; exact hf)).symm

/-- After a block step, the header slot is the state slot. -/
theorem BlockStep.hdrFilled {sb : SignedBeaconBlock} {vr : Bool} {u u' : BeaconState}
    (h : BlockStep sb vr u u') : HdrFilled u' := fun hlt => by
  obtain ⟨hs, -, eh, -, es⟩ := h.hdr
  have hhs : u'.latestBlockHeader.slot = sb.message.slot := by rw [eh]; rfl
  rw [hhs, hs, ← es] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

/-- **A block names the last block of the run as its parent.** The header slot is below the
block slot, which is the state slot. So the header is the filled header, whose root is the
last root (`RootsInv.cached`). -/
theorem BlockStep.parent_eq_lastRoot {st₀ : BeaconState} {p : List ChainStep}
    {sb : SignedBeaconBlock} {vr : Bool} {u u' : BeaconState} (h : BlockStep sb vr u u')
    (hi : RootsInv st₀ p u) (hf : HdrFilled u) : sb.message.parentRoot = lastRoot st₀ p := by
  obtain ⟨hs, hlt, -⟩ := h.hdr
  have hlt' : u.latestBlockHeader.slot.toNat < u.slot.toNat := by
    rw [← hs]
    exact UInt64.lt_iff_toNat_lt.mp hlt
  rw [h.parent, hf hlt', hi.cached]

/-- **The blocks of a run are linked from the anchor block.** The anchor state has the
header of the anchor block `a`, so the last root of a run is the root after its blocks
(`lastRoot_eq_lastRootOf`). Each block names that root as its parent
(`BlockStep.parent_eq_lastRoot`). Each block has a slot greater than the header slot of the
anchor state. That slot is the slot of `a`, so no block is `a`. -/
theorem ChainRun.linked (hw : ∀ x y : ByteArray,
      (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {st₀ : BeaconState} {a : BeaconBlock}
    (hanc : filledHeader st₀ = headerOf a) {q : List ChainStep} {u w : BeaconState}
    (h : ChainRun hi q u w) :
    ∀ {p : List ChainStep}, ValidatedSteps q → RootsInv st₀ p u → HdrFilled u →
      Linked a (blocksOf p) → Linked a (blocksOf (p ++ q)) ∧ HdrFilled w := by
  -- The slot of `a` is the header slot of the anchor state.
  have ha : a.slot = st₀.latestBlockHeader.slot := by
    have e := congrArg EthCLSpecs.Heze.BeaconBlockHeader.slot hanc
    unfold filledHeader at e
    split at e <;> exact e.symm
  induction h with
  | nil =>
    intro p _ _ hf hl
    rw [List.append_nil]
    exact ⟨hl, hf⟩
  | @slot steps st _ _ hlt hstep _ ih =>
    intro p hv hinv _ hl
    have hlt' : st.slot.toNat < hi := hlt
    have := ih (p := p ++ [.slot]) (fun sb v hm => hv sb v (List.mem_cons_of_mem _ hm))
      (hstep.rootsInv (by omega) hinv) (hstep.hdrFilled hinv.filled)
      (by rw [blocksOf_append_slot]; exact hl)
    rwa [List.append_assoc, List.singleton_append] at this
  | block sb v hstep _ ih =>
    intro p hv hinv hf hl
    have hval := hv sb v (List.mem_cons_self ..)
    have hpar := hstep.parent_eq_lastRoot hinv hf
    rw [lastRoot_eq_lastRootOf hw hanc] at hpar
    -- The block slot is above the header slot of `u`, which is at least the anchor slot.
    have hne : sb.message ≠ a := by
      intro he
      obtain ⟨-, hlt, -⟩ := hstep.hdr
      have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      have hge := hinv.hdrGe
      rw [he, ha] at hlt'
      omega
    have hl' : Linked a (blocksOf (p ++ [.block sb v])) := by
      rw [blocksOf_append_block]
      exact .snoc hl hpar hne
    have := ih (p := p ++ [.block sb v]) (fun sb' v' hm => hv sb' v' (List.mem_cons_of_mem _ hm))
      (hstep.rootsInv hw hval hinv) hstep.hdrFilled hl'
    rwa [List.append_assoc, List.singleton_append] at this

end Links

/-! ## Runs with one list of blocks -/

section Det
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- **Two runs from one state with one list of blocks and one end slot end in one state.**
At each step the runs take the same kind of step. A slot step against a block step fails:
the block has the start slot, and every block after a slot step has a later slot. A slot step
against the end of the other run fails too: the slot increases and never decreases. -/
theorem ChainRun.det_blocks {hi₁ hi₂ : Nat} (h₁ : hi₁ ≤ 2 ^ 64 - 1) (h₂ : hi₂ ≤ 2 ^ 64 - 1)
    {p : List ChainStep} {u x : BeaconState} (hx : ChainRun hi₁ p u x) :
    ∀ {q : List ChainStep} {y : BeaconState}, ChainRun hi₂ q u y →
      blocksOf p = blocksOf q → x.slot.toNat = y.slot.toNat → x = y := by
  induction hx with
  | nil s =>
    intro q y hy hb hs
    cases hy with
    | nil => rfl
    | slot hlt hstep hrest =>
      have hlt' : s.slot.toNat < hi₂ := hlt
      have := hstep.slot (by omega)
      have := (hrest.slot_le h₂).1
      omega
    | block sb v _ _ => simp [blocksOf] at hb
  | @slot steps st st1 _ hlt hstep hrest ih =>
    intro q y hy hb hs
    have hlt' : st.slot.toNat < hi₁ := hlt
    have hs1 := hstep.slot (by omega)
    cases hy with
    | nil =>
      have := (hrest.slot_le h₁).1
      omega
    | slot _ hstep' hrest' =>
      rw [hstep.det hstep'] at ih
      exact ih hrest' hb hs
    | block sb v hstep' _ =>
      have hm : sb.message ∈ blocksOf steps := by
        change blocksOf steps = sb.message :: _ at hb
        rw [hb]
        exact List.mem_cons_self
      have := hrest.blocks_slot_ge h₁ _ hm
      have := hstep'.slot.2
      omega
  | @block steps st _ _ sb v hstep _ ih =>
    intro q y hy hb hs
    cases hy with
    | nil => simp [blocksOf] at hb
    | @slot q' _ st1' _ hlt' hstep' hrest' =>
      have hlt'' : st.slot.toNat < hi₂ := hlt'
      have hs1 := hstep'.slot (by omega)
      have hm : sb.message ∈ blocksOf q' := by
        change sb.message :: _ = blocksOf q' at hb
        rw [← hb]
        exact List.mem_cons_self
      have := hrest'.blocks_slot_ge h₂ _ hm
      have := hstep.slot.2
      omega
    | block sb' v' hstep' hrest' =>
      obtain ⟨hmsg, hb'⟩ := List.cons.inj hb
      rw [hstep.det_msg hstep' hmsg] at ih
      exact ih hrest' hb' hs

end Det

/-! ## The store -/

section Store
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [EthCLLib.Proofs.LawfulFcMap map EthCLSpecs.Heze.Root]

/-- **`onBlock` stores the state of the chain after the block.** The store `sA` traces to
the anchor state `st₀` and the anchor block `a` (`CkptInv`, from `NodeTrace.ckptInv`). The
anchor state has the header of `a`, with a filled state root when the header slot is below the
state slot. The block ends a validated chain run from `st₀`, whose prefix `p` ends in `u`.
Without a block collision, the store after `onBlock` holds `w` at the block root. -/
theorem onBlock_stores_chainState (hw : ∀ x y : ByteArray,
      (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    (hc : ¬ HtrCollision BeaconBlock) {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1)
    {st₀ : BeaconState} {a : BeaconBlock} (hroots : AnchorRoots st₀) (hfill₀ : HdrFilled st₀)
    (hanc : filledHeader st₀ = headerOf a) {p : List ChainStep} {sb : SignedBeaconBlock}
    {v : Bool} {u w : BeaconState} (hu : ChainRun hi p st₀ u) (hval : ValidatedSteps p)
    (hstep : BlockStep sb v u w) {sA sB : Store map} (hinv : CkptInv st₀ a sA)
    (hblk : (onBlock (map := map) (StoreTransition := ForkChoiceStoreRun (Store map)) sb).run sA
      = .ok ((), sB)) :
    FcMap.lookup sB.blockStates (htr sb.message) = some (pureState w) := by
  obtain ⟨pv, w', s', hps, htrans, -, hbsu, -, hpull⟩ :=
    onBlock_run_ckpt sb sA sB hinv.slot.statesPure hblk
  obtain ⟨-, -, -, -, -, bs1⟩ :=
    updateCheckpoints_ckpt s' w'.currentJustifiedCheckpoint w'.finalizedCheckpoint
  have hl : FcMap.lookup (updateCheckpoints s' w'.currentJustifiedCheckpoint
      w'.finalizedCheckpoint).blockStates (htr sb.message) = some (pureState w') := by
    rw [bs1, hbsu, EthCLLib.Proofs.LawfulFcMap.lookup_insert_self]
  obtain ⟨-, -, -, pbs, -⟩ := computePulledUpTip_run_ok _ w' _ sB hl hpull
  rw [pbs, hl]
  -- The store run to the parent state, and its blocks.
  obtain ⟨steps0, hrun0, hpath0, -⟩ := hinv.chains _ pv hps
  obtain ⟨hL0, hk0⟩ := hpath0.linked hinv.slot
  obtain ⟨n, hrunT⟩ := stateTransition_chainRun sb true (2 ^ 64 - 1)
    (by have := sb.message.slot.toNat_lt; omega) pv w' htrans
  -- The honest blocks before the block, and its parent.
  have hR : RootsInv st₀ p u := by
    have := hu.rootsInv hw hhi (p := []) hval hroots.rootsInv
    rwa [List.nil_append] at this
  obtain ⟨hL, hfu⟩ := hu.linked hw hhi hanc (p := []) hval hroots.rootsInv hfill₀ .nil
  rw [List.nil_append] at hL
  have hpar := hstep.parent_eq_lastRoot hR hfu
  rw [lastRoot_eq_lastRootOf hw hanc] at hpar
  have he : blocksOf steps0 = blocksOf p := hL0.eq_of_last hc hL (hk0.symm.trans hpar)
  -- The two runs have one list of blocks and end at the block slot.
  have hX : ChainRun hi (p ++ [.block sb v]) st₀ w := hu.append (.block sb v hstep (.nil _))
  have hY := hrun0.append hrunT
  have hblocks : blocksOf (p ++ [.block sb v]) =
      blocksOf (steps0 ++ (List.replicate n .slot ++ [.block sb true])) := by
    rw [blocksOf_append_block, blocksOf_append, blocksOf_append, blocksOf_replicate_slot, he]
    rfl
  obtain ⟨m, -, hm⟩ := hrunT.split
  have hsY : w'.slot.toNat = sb.message.slot.toNat := by
    cases hm with
    | block _ _ hb hrest =>
      cases hrest
      obtain ⟨e1, e2⟩ := hb.slot
      omega
  obtain ⟨e1, e2⟩ := hstep.slot
  rw [hX.det_blocks hhi (Nat.le_refl _) hY hblocks (by omega)]

end Store

end EthCLSpecs.Proofs.Heze
