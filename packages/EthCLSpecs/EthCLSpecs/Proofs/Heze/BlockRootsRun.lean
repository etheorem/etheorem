import EthCLSpecs.Proofs.Heze.BlockChain
import EthCLSpecs.Proofs.Heze.HeaderFrame

/-!
# `EthCLSpecs.Proofs.Heze.BlockRootsRun`: the block roots along a chain run

`get_block_root_at_slot` reads the ring buffer `blockRoots` of a state. This module proves
that the buffer holds the block roots of the run: at a slot `s`, the root of the last block
of the run at or before `s` (`rootAtSlot`). Before the first block of the run, the root is
the one that the anchor state records (`anchorRoot`): the root of its filled header from the
header slot on, and its own `blockRoots` entry before it.

## The writes

Two functions write the latest block header and `blockRoots` (`HeaderFrame.lean`):

- `processBlockHeader` writes the header of the new block, with a zero state root. The
  block slot is the state slot, and it is greater than the slot of the old header
  (`processBlockHeader_run_hdr`).
- `processSlot` fills a zero state root of the header with the root of the state
  (`filledHeader`). Then it writes the root of the filled header into `blockRoots`, at the
  state slot modulo `SLOTS_PER_HISTORICAL_ROOT` (`slotWrite`, `processSlot_run_eq`).

A validated block names the root of its post-state. So after the next `processSlot`, the
header is the header of the block, and its root is the block root (`htr_eq_htr_headerOf`).
The proof needs the state root of each block to be nonzero. A zero state root would make
the next `processSlot` fill the header again, with the root of a later state.

## The invariant

`RootsInv st₀ p u` holds at the end `u` of a run prefix `p` from the anchor state `st₀`:

- Each block of `p` has a slot no greater than the header slot of `u`. The header slot of
  `st₀` is at most that of `u`.
- The root of the filled header of `u` is the root of the last block of `p` (`lastRoot`).
- The filled header has a nonzero state root.
- The header slot is at most the state slot.
- For each slot `s` below the state slot and within `SLOTS_PER_HISTORICAL_ROOT` of it,
  `blockRoots` holds `rootAtSlot st₀ p s` at `s`.

`ChainRun.rootsInv` proves that a run of validated blocks keeps it, from an anchor state
that meets `AnchorRoots`. `RootsInv.read` reads `get_block_root_at_slot` on the end state of
a run. `RootsInv.read_slotWrite` reads it on the state after the next `processSlot`, where the
epoch step runs, when the slot is less than `SLOTS_PER_HISTORICAL_ROOT` behind.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState BeaconBlock BeaconBlockHeader Root Slot)
open EthCLSpecs.Heze.Const (slotsPerHistoricalRoot)

/-! ## The two writes -/

section Writes
variable [Preset] [HasherTag]

/-- The header of `u` with its state root filled, as `processSlot` fills it: a zero state
root becomes the root of `u`. -/
def filledHeader (u : BeaconState) : BeaconBlockHeader :=
  if u.latestBlockHeader.stateRoot == EthCLSpecs.Heze.zeroRoot then
    { u.latestBlockHeader with stateRoot := bytesToRoot (stateRoot (pureState u)).1 }
  else u.latestBlockHeader

/-- A header with a nonzero state root stays as it is. -/
theorem filledHeader_of_ne {u : BeaconState}
    (h : u.latestBlockHeader.stateRoot ≠ EthCLSpecs.Heze.zeroRoot) :
    filledHeader u = u.latestBlockHeader := by
  unfold filledHeader
  rw [if_neg (by simpa using h)]

/-- The state after `processSlot`: the state root and the root of the filled header at the
index of the slot, the filled header, and the next availability bit cleared. -/
def slotWrite (u : BeaconState) : BeaconState :=
  { u with
    latestBlockHeader := filledHeader u
    blockRoots := u.blockRoots.set! (umodIdx u.slot slotsPerHistoricalRoot)
      (htr (filledHeader u))
    stateRoots := u.stateRoots.set! (umodIdx u.slot slotsPerHistoricalRoot)
      (bytesToRoot (stateRoot (pureState u)).1)
    executionPayloadAvailability := bitSet u.executionPayloadAvailability
      (umodIdx (u.slot + 1) slotsPerHistoricalRoot) false }

/-- `processSlot` ends in `slotWrite`. -/
@[characterizes EthCLSpecs.Heze.processSlot]
theorem processSlot_run_eq {st st1 : BeaconState}
    (h : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState st)
      = .ok ((), pureState st1)) :
    st1 = slotWrite st := by
  unfold EthCLSpecs.Heze.processSlot at h
  have e := modifyState_run_eq h
  have ev := congrArg SizzLean.Cache.SSZ.Box.view e
  -- On an uncached box, `stateRoot` returns the root and the same box.
  simp only [EthCLLib.Spec.stateRoot, SizzLean.Proofs.hashTreeRoot_uncachedBox] at ev
  unfold slotWrite filledHeader
  change st1 = _ at ev
  exact ev

/-- `processBlockHeader` checks that the block slot is the state slot and is greater than
the header slot. It writes the header of the block, with a zero state root, and keeps the
block roots and the slot. -/
theorem processBlockHeader_run_hdr (b : BeaconBlock) (v w : BeaconState)
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState v)
      = .ok ((), pureState w)) :
    b.slot = v.slot ∧ v.latestBlockHeader.slot < b.slot ∧
    w.latestBlockHeader = { headerOf b with stateRoot := EthCLSpecs.Heze.zeroRoot } ∧
    w.blockRoots = v.blockRoots ∧ w.slot = v.slot := by
  unfold EthCLSpecs.Heze.processBlockHeader at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨hs, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨hlt, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  -- The proposer read keeps the state.
  simp only [sszGetIdx] at h
  obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  have e := congrArg SizzLean.Cache.SSZ.Box.view (modifyState_run_eq h)
  change w = _ at e
  subst e
  exact ⟨beq_iff_eq.mp hs, hlt, rfl, rfl, rfl⟩

variable [Config] [CryptoBackend]

/-- A slot step writes the filled header, and the root of the filled header at the index of
the old slot. It adds one to the slot. -/
theorem SlotStep.hdr {u u' : BeaconState} (h : SlotStep u u') :
    u'.latestBlockHeader = filledHeader u ∧
    u'.blockRoots = u.blockRoots.set! (umodIdx u.slot slotsPerHistoricalRoot)
      (htr (filledHeader u)) ∧
    u'.slot = u.slot + 1 := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 := processSlot_run_eq h1
  subst e1
  have e2 : hdrView (pureState st2) = hdrView (pureState (slotWrite u)) ∧
      st2.slot = (slotWrite u).slot := by
    split at h2
    · refine ⟨processEpoch_frame_hdr h2, ?_⟩
      exact congrArg Prod.fst (processEpoch_frame_spine h2)
    · rw [h2]
      exact ⟨rfl, rfl⟩
  obtain ⟨e2, s2⟩ := e2
  simp only [hdrView, Prod.mk.injEq] at e2
  obtain ⟨eh, er⟩ := e2
  change st2.latestBlockHeader = filledHeader u at eh
  change st2.blockRoots = _ at er
  have ev := congrArg SizzLean.Cache.SSZ.Box.view hst'
  change u' = _ at ev
  subst ev
  exact ⟨eh, er, by change st2.slot + 1 = _; rw [s2]; rfl⟩

/-- A block step checks that the block slot is the state slot and is greater than the
header slot. It writes the header of the block, with a zero state root, and keeps the block
roots and the slot. -/
theorem BlockStep.hdr {sb : EthCLSpecs.Heze.SignedBeaconBlock} {vr : Bool} {u u' : BeaconState}
    (h : BlockStep sb vr u u') :
    sb.message.slot = u.slot ∧ u.latestBlockHeader.slot < sb.message.slot ∧
    u'.latestBlockHeader = { headerOf sb.message with stateRoot := EthCLSpecs.Heze.zeroRoot } ∧
    u'.blockRoots = u.blockRoots ∧ u'.slot = u.slot := by
  have hb := h.2.1
  have hsl := processBlock_frame_ord hb
  simp only [ordView, Prod.mk.injEq] at hsl
  rw [processBlock_eq_tail] at hb
  obtain ⟨⟨⟩, mid, hp, hb⟩ :=
    run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) hb
  obtain ⟨⟨⟩, t, hh, hb⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) hb
  have ep := processParentExecutionPayload_frame_hdr hp
  have eo := processParentExecutionPayload_frame_ord hp
  have et := processBlockTail_frame_hdr hb
  simp only [hdrView, ordView, Prod.mk.injEq] at ep eo et
  obtain ⟨hs, hlt, hhd, hbr, -⟩ := processBlockHeader_run_hdr _ _ _ hh
  change mid.latestBlockHeader = u.latestBlockHeader ∧ mid.blockRoots = u.blockRoots at ep
  change _ ∧ mid.slot = u.slot at eo
  change u'.latestBlockHeader = t.latestBlockHeader ∧ u'.blockRoots = t.blockRoots at et
  refine ⟨hs.trans eo.2, by rw [← ep.1]; exact hlt, et.1.trans hhd, et.2.trans (hbr.trans ep.2),
    hsl.2⟩

end Writes

/-! ## The ring buffer -/

/-- Two slots less than `d` apart have distinct indices modulo `d`. -/
theorem mod_ne_of_lt {s t d : Nat} (hst : s < t) (hwin : t < s + d) : s % d ≠ t % d := by
  intro h
  have hz := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have hle := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hz)
  omega

/-- The ring-buffer read after a ring-buffer write: the written value at the written index,
else the old value. -/
theorem vmodGet_set! {α : Type} {n : Nat} (v : Vector α n) (t s : UInt64) (d : Nat)
    [vd : ValidModulus d] (hle : d ≤ n) (x : α) :
    vmodGet (v.set! (umodIdx t d) x) s d hle =
      if s.toNat % d = t.toNat % d then x else vmodGet v s d hle := by
  have hd : (UInt64.ofNat d).toNat = d := UInt64.toNat_ofNat_of_lt' vd.lt
  unfold vmodGet umodIdx
  simp only [UInt64.toNat_mod, hd]
  have hs := Nat.mod_lt s.toNat vd.pos
  have ht := Nat.mod_lt t.toNat vd.pos
  -- `Vector.set!` is `setIfInBounds` on the array.
  change (v.setIfInBounds (t.toNat % d) x)[s.toNat % d] = _
  rw [Vector.getElem_setIfInBounds (by omega)]
  by_cases h : s.toNat % d = t.toNat % d
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-! ## The roots of a run -/

section Roots
variable [Preset] [HasherTag]

/-- The root that the anchor state records for slot `s`: the root of its filled header from
the header slot on, else its `blockRoots` entry. -/
def anchorRoot (st₀ : BeaconState) (s : Nat) : Root :=
  if st₀.latestBlockHeader.slot.toNat ≤ s then htr (filledHeader st₀)
  else vmodGet st₀.blockRoots (UInt64.ofNat s) slotsPerHistoricalRoot

/-- The root of the last block at or before slot `s` on the run, or the root that the anchor
state records when the run has no such block. -/
def rootAtSlot (st₀ : BeaconState) (steps : List ChainStep) (s : Nat) : Root :=
  ((blocksOf steps).filter (fun b => b.slot.toNat ≤ s)).getLast?.elim (anchorRoot st₀ s) htr

/-- The root of the last block of the run, or the root of the filled header of the anchor
state. -/
def lastRoot (st₀ : BeaconState) (steps : List ChainStep) : Root :=
  (blocksOf steps).getLast?.elim (htr (filledHeader st₀)) htr

/-- At a slot no less than every block slot of the run and than the anchor header slot, the
root is the last root. -/
theorem rootAtSlot_of_le (st₀ : BeaconState) (steps : List ChainStep) (s : Nat)
    (h : ∀ b ∈ blocksOf steps, b.slot.toNat ≤ s) (h₀ : st₀.latestBlockHeader.slot.toNat ≤ s) :
    rootAtSlot st₀ steps s = lastRoot st₀ steps := by
  unfold rootAtSlot lastRoot
  rw [List.filter_eq_self.mpr (fun b hb => decide_eq_true (h b hb))]
  rcases (blocksOf steps).getLast? with _ | b
  · simp only [Option.elim]
    unfold anchorRoot
    rw [if_pos h₀]
  · simp only [Option.elim]

/-- Before every block of the run, the root is the anchor root. -/
theorem rootAtSlot_of_lt (st₀ : BeaconState) (steps : List ChainStep) (s : Nat)
    (h : ∀ b ∈ blocksOf steps, s < b.slot.toNat) :
    rootAtSlot st₀ steps s = anchorRoot st₀ s := by
  unfold rootAtSlot
  rw [List.filter_eq_nil_iff.mpr (fun b hb => by simpa using h b hb)]
  rfl

/-- Blocks after slot `s` leave the root at `s`. -/
theorem rootAtSlot_append_of_lt (st₀ : BeaconState) (p q : List ChainStep) (s : Nat)
    (hs : ∀ b ∈ blocksOf q, s < b.slot.toNat) :
    rootAtSlot st₀ (p ++ q) s = rootAtSlot st₀ p s := by
  have hq : (blocksOf q).filter (fun b => decide (b.slot.toNat ≤ s)) = [] :=
    List.filter_eq_nil_iff.mpr (fun b hb => by simpa using hs b hb)
  unfold rootAtSlot
  rw [blocksOf_append, List.filter_append, hq, List.append_nil]

omit [HasherTag] in
/-- A slot step adds no block. -/
theorem blocksOf_append_slot (p : List ChainStep) : blocksOf (p ++ [.slot]) = blocksOf p := by
  rw [blocksOf_append]
  exact List.append_nil _

omit [HasherTag] in
/-- A block step adds its block at the end. -/
theorem blocksOf_append_block (p : List ChainStep) (sb : EthCLSpecs.Heze.SignedBeaconBlock)
    (v : Bool) : blocksOf (p ++ [.block sb v]) = blocksOf p ++ [sb.message] := by
  rw [blocksOf_append]
  rfl

/-- A block after slot `s` leaves the root at `s`. -/
theorem rootAtSlot_append_block (st₀ : BeaconState) (p : List ChainStep)
    (sb : EthCLSpecs.Heze.SignedBeaconBlock) (v : Bool) (s : Nat)
    (hs : s < sb.message.slot.toNat) :
    rootAtSlot st₀ (p ++ [.block sb v]) s = rootAtSlot st₀ p s :=
  rootAtSlot_append_of_lt st₀ p _ s fun b hb => by
    change b ∈ [sb.message] at hb
    rw [List.mem_singleton.mp hb]
    exact hs

/-- The last root after a block step is the root of the block. -/
theorem lastRoot_append_block (st₀ : BeaconState) (p : List ChainStep)
    (sb : EthCLSpecs.Heze.SignedBeaconBlock) (v : Bool) :
    lastRoot st₀ (p ++ [.block sb v]) = htr sb.message := by
  unfold lastRoot
  rw [blocksOf_append_block, List.getLast?_concat]
  rfl

/-- A slot step leaves every root. -/
theorem rootAtSlot_append_slot (st₀ : BeaconState) (p : List ChainStep) (s : Nat) :
    rootAtSlot st₀ (p ++ [.slot]) s = rootAtSlot st₀ p s := by
  unfold rootAtSlot
  rw [blocksOf_append_slot]

/-- A slot step leaves the last root. -/
theorem lastRoot_append_slot (st₀ : BeaconState) (p : List ChainStep) :
    lastRoot st₀ (p ++ [.slot]) = lastRoot st₀ p := by
  unfold lastRoot
  rw [blocksOf_append_slot]

end Roots

/-! ## The invariant -/

section Inv
variable [Preset] [HasherTag]

/-- The block roots of the state `u` at the end of the run prefix `p` from the anchor state
`st₀`. Each block of `p`, and the anchor header, is at or before the header slot. The filled
header has the last root of `p` and a nonzero state root. The header slot is at most the
state slot. At each slot `s` below the state slot and within `SLOTS_PER_HISTORICAL_ROOT` of
it, `blockRoots` holds the root at `s`. -/
structure RootsInv (st₀ : BeaconState) (p : List ChainStep) (u : BeaconState) : Prop where
  blocks : ∀ b ∈ blocksOf p, b.slot.toNat ≤ u.latestBlockHeader.slot.toNat
  hdrGe : st₀.latestBlockHeader.slot.toNat ≤ u.latestBlockHeader.slot.toNat
  cached : htr (filledHeader u) = lastRoot st₀ p
  filled : (filledHeader u).stateRoot ≠ EthCLSpecs.Heze.zeroRoot
  hdrLe : u.latestBlockHeader.slot.toNat ≤ u.slot.toNat
  roots : ∀ s : Slot, s.toNat < u.slot.toNat →
    u.slot.toNat ≤ s.toNat + slotsPerHistoricalRoot →
    vmodGet u.blockRoots s slotsPerHistoricalRoot = rootAtSlot st₀ p s.toNat

/-- The anchor state records its own block roots: the filled header has a nonzero state root
and a slot at most the state slot, and from the header slot on, `blockRoots` holds the root
of the filled header. -/
structure AnchorRoots (st₀ : BeaconState) : Prop where
  filled : (filledHeader st₀).stateRoot ≠ EthCLSpecs.Heze.zeroRoot
  hdrLe : st₀.latestBlockHeader.slot.toNat ≤ st₀.slot.toNat
  roots : ∀ s : Slot, st₀.latestBlockHeader.slot.toNat ≤ s.toNat → s.toNat < st₀.slot.toNat →
    st₀.slot.toNat ≤ s.toNat + slotsPerHistoricalRoot →
    vmodGet st₀.blockRoots s slotsPerHistoricalRoot = htr (filledHeader st₀)

/-- An anchor state with its own block roots meets the invariant for the empty run. -/
theorem AnchorRoots.rootsInv {st₀ : BeaconState} (h : AnchorRoots st₀) : RootsInv st₀ [] st₀ := by
  refine ⟨fun b hb => absurd hb List.not_mem_nil, Nat.le_refl _, rfl, h.filled, h.hdrLe, fun s hs hw => ?_⟩
  unfold rootAtSlot anchorRoot
  simp only [blocksOf, List.filter_nil, List.getLast?_nil, Option.elim, UInt64.ofNat_toNat]
  split
  · exact h.roots s (by assumption) hs hw
  · rfl

/-- A run that keeps the invariant: at a slot from the header slot on, the root is the last
root. -/
theorem RootsInv.rootAtSlot_eq {st₀ : BeaconState} {p : List ChainStep} {u : BeaconState}
    (hi : RootsInv st₀ p u) (s : Nat) (hs : u.latestBlockHeader.slot.toNat ≤ s) :
    rootAtSlot st₀ p s = lastRoot st₀ p :=
  rootAtSlot_of_le st₀ p s (fun b hb => Nat.le_trans (hi.blocks b hb) hs)
    (Nat.le_trans hi.hdrGe hs)

variable [Config] [CryptoBackend]

/-- A slot step keeps the invariant, when the slot increment does not wrap. The step writes
the root of the filled header at the old slot. That root is the last root, and the last root
is the root at every slot from the header slot. -/
theorem SlotStep.rootsInv {st₀ : BeaconState} {p : List ChainStep} {u u' : BeaconState}
    (h : SlotStep u u') (hlt : u.slot.toNat + 1 < 2 ^ 64) (hi : RootsInv st₀ p u) :
    RootsInv st₀ (p ++ [.slot]) u' := by
  obtain ⟨eh, er, es⟩ := h.hdr
  have hsl : u'.slot.toNat = u.slot.toNat + 1 := by
    rw [es, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
  have hfill : filledHeader u' = filledHeader u := by
    rw [filledHeader_of_ne (by rw [eh]; exact hi.filled), eh]
  have hhs : u'.latestBlockHeader.slot = u.latestBlockHeader.slot := by
    rw [eh]
    unfold filledHeader
    split <;> rfl
  have hhl := hi.hdrLe
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun s hs hw => ?_⟩
  · rw [blocksOf_append_slot] at hb
    rw [hhs]
    exact hi.blocks b hb
  · rw [hhs]
    exact hi.hdrGe
  · rw [hfill, lastRoot_append_slot]
    exact hi.cached
  · rw [hfill]
    exact hi.filled
  · rw [hhs, hsl]
    omega
  · rw [rootAtSlot_append_slot, er, vmodGet_set!]
    rw [hsl] at hs hw
    by_cases hm : s.toNat % slotsPerHistoricalRoot = u.slot.toNat % slotsPerHistoricalRoot
    · rw [if_pos hm]
      -- The written index is the old slot: a slot before it is too close to share it.
      have he : s.toNat = u.slot.toNat := by
        rcases Nat.lt_or_ge s.toNat u.slot.toNat with hl | hl
        · exact absurd hm (mod_ne_of_lt hl (by omega))
        · omega
      rw [hi.cached, hi.rootAtSlot_eq s.toNat (by omega)]
    · rw [if_neg hm]
      have hne : s.toNat ≠ u.slot.toNat := fun he => hm (by rw [he])
      exact hi.roots s (by omega) (by omega)

/-- A block step of a validated block with a nonzero state root keeps the invariant, under
the combine-width law. The filled header after the step is the header of the block, whose
root is the block root (`htr_eq_htr_headerOf`). The block slot is the state slot, so the
block is after every slot that `blockRoots` covers. -/
theorem BlockStep.rootsInv
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {st₀ : BeaconState} {p : List ChainStep} {sb : EthCLSpecs.Heze.SignedBeaconBlock}
    {vr : Bool} {u u' : BeaconState} (h : BlockStep sb vr u u')
    (hval : vr = true ∧ sb.message.stateRoot ≠ EthCLSpecs.Heze.zeroRoot)
    (hi : RootsInv st₀ p u) : RootsInv st₀ (p ++ [.block sb vr]) u' := by
  obtain ⟨hs, hlt, eh, er, es⟩ := h.hdr
  have hroot := h.2.2 hval.1
  have hfill : filledHeader u' = headerOf sb.message := by
    unfold filledHeader
    rw [eh, if_pos (beq_self_eq_true _), ← hroot]
    rfl
  have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
  have hs' : sb.message.slot.toNat = u.slot.toNat := congrArg UInt64.toNat hs
  have hsl : u'.slot.toNat = u.slot.toNat := congrArg UInt64.toNat es
  have hhs : u'.latestBlockHeader.slot = sb.message.slot := by rw [eh]; rfl
  have hge := hi.hdrGe
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun s hs1 hw1 => ?_⟩
  · rw [blocksOf_append_block] at hb
    rw [hhs]
    rcases List.mem_append.mp hb with hb | hb
    · have := hi.blocks b hb
      omega
    · rw [List.mem_singleton.mp hb]
      exact Nat.le_refl _
  · rw [hhs]
    omega
  · rw [hfill, ← htr_eq_htr_headerOf hw, lastRoot_append_block]
  · rw [hfill]
    exact hval.2
  · rw [hhs, hsl, hs']
    exact Nat.le_refl _
  · rw [hsl] at hs1 hw1
    rw [er, rootAtSlot_append_block _ _ _ _ _ (by omega)]
    exact hi.roots s hs1 hw1

/-- A chain run of validated blocks keeps the invariant. Each slot step starts below slot
`hi`, and `hi` is below `2 ^ 64`, so no slot increment wraps. -/
theorem ChainRun.rootsInv
    (hw : ∀ x y : ByteArray, (SizzLean.Hasher.combine (H := HasherTag.H) x y).size = 32)
    {hi : Nat} (hhi : hi ≤ 2 ^ 64 - 1) {st₀ : BeaconState} {q : List ChainStep}
    {u w : BeaconState} (h : ChainRun hi q u w) :
    ∀ {p : List ChainStep}, ValidatedSteps q → RootsInv st₀ p u → RootsInv st₀ (p ++ q) w := by
  induction h with
  | nil =>
    intro p _ hinv
    rw [List.append_nil]
    exact hinv
  | @slot steps st _ _ hlt hstep _ ih =>
    intro p hv hinv
    have hlt' : st.slot.toNat < hi := hlt
    have := ih (p := p ++ [.slot]) (fun sb v hm => hv sb v (List.mem_cons_of_mem _ hm))
      (hstep.rootsInv (by omega) hinv)
    rwa [List.append_assoc, List.singleton_append] at this
  | block sb v hstep _ ih =>
    intro p hv hinv
    have := ih (p := p ++ [.block sb v]) (fun sb' v' hm => hv sb' v' (List.mem_cons_of_mem _ hm))
      (hstep.rootsInv hw (hv sb v (List.mem_cons_self ..)) hinv)
    rwa [List.append_assoc, List.singleton_append] at this

omit [Config] [CryptoBackend] in
/-- A successful `get_block_root_at_slot` passed its two asserts and read the ring buffer. -/
@[characterizes EthCLSpecs.Heze.getBlockRootAtSlot]
theorem getBlockRootAtSlot_run_ok {u u' : BeaconState} {s : Slot} {r : Root}
    (h : runPure (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun)
      (pureState u) s) u = .ok (r, u')) :
    s.toNat < u.slot.toNat ∧ u.slot.toNat ≤ s.toNat + slotsPerHistoricalRoot ∧
      r = vmodGet u.blockRoots s slotsPerHistoricalRoot ∧ u' = u := by
  rw [EthCLLib.Proofs.runPure_eq] at h
  cases hx : (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun)
      (pureState u) s).run (pureState u) with
  | error e =>
    rw [hx] at h
    cases h
  | ok p =>
    obtain ⟨r', b⟩ := p
    rw [hx] at h
    injection h with h
    injection h with hr hu
    unfold EthCLSpecs.Heze.getBlockRootAtSlot at hx
    obtain ⟨c1, hx⟩ := run_assert_bind_eq_ok _ _ _ _ hx
    obtain ⟨bound, s2, h2, hx⟩ := run_bind_eq_ok _ _ _ _ hx
    unfold checkedAdd at h2
    split at h2
    · cases h2
    rename_i c2
    have eb := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ h2
    have es := run_pure_state_eq _ _ _ _ h2
    subst eb es
    obtain ⟨c3, hx⟩ := run_assert_bind_eq_ok _ _ _ _ hx
    have er := EthCLLib.Proofs.run_pure_eq_ok _ _ _ _ hx
    have es' := run_pure_state_eq _ _ _ _ hx
    subst es'
    have hd : (UInt64.ofNat slotsPerHistoricalRoot).toNat = slotsPerHistoricalRoot :=
      UInt64.toNat_ofNat_of_lt' EthCLSpecs.Heze.Const.slotsPerHistoricalRootLt
    have c1' := UInt64.lt_iff_toNat_lt.mp c1
    have c2' : ¬ (s + UInt64.ofNat slotsPerHistoricalRoot).toNat < s.toNat :=
      fun h' => c2 (UInt64.lt_iff_toNat_lt.mpr h')
    have c3' := UInt64.le_iff_toNat_le.mp c3
    rw [UInt64.toNat_add, hd] at c2' c3'
    refine ⟨c1', ?_, hr.symm.trans er, hu.symm⟩
    have := s.toNat_lt
    by_cases hov : s.toNat + slotsPerHistoricalRoot < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hov] at c3'
      exact c3'
    · exfalso
      apply c2'
      have hlt := EthCLSpecs.Heze.Const.slotsPerHistoricalRootLt
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

omit [Config] [CryptoBackend] in
/-- `get_block_root_at_slot` on the end state of a run that keeps the invariant reads the root
at the slot. -/
theorem RootsInv.read {st₀ : BeaconState} {p : List ChainStep} {u u' : BeaconState}
    (hi : RootsInv st₀ p u) {s : Slot} {r : Root}
    (h : runPure (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun)
      (pureState u) s) u = .ok (r, u')) : r = rootAtSlot st₀ p s.toNat := by
  obtain ⟨h1, h2, h3, -⟩ := getBlockRootAtSlot_run_ok h
  rw [h3]
  exact hi.roots s h1 h2

omit [Config] [CryptoBackend] in
/-- `get_block_root_at_slot` on a state with the slot and the block roots of the end state of
a run reads the root at the slot. -/
theorem RootsInv.read_of {st₀ : BeaconState} {p : List ChainStep} {u w w' : BeaconState}
    (hi : RootsInv st₀ p u) (hs : w.slot = u.slot) (hb : w.blockRoots = u.blockRoots)
    {s : Slot} {r : Root}
    (h : runPure (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun)
      (pureState w) s) w = .ok (r, w')) : r = rootAtSlot st₀ p s.toNat := by
  obtain ⟨h1, h2, h3, -⟩ := getBlockRootAtSlot_run_ok h
  rw [h3, hb]
  rw [hs] at h1 h2
  exact hi.roots s h1 h2

omit [HasherTag] [Config] [CryptoBackend] in
/-- The first slot of an epoch, when it fits a `uint64`. -/
theorem epochStart_toNat (e : EthCLSpecs.Heze.Epoch)
    (h : e.toNat * EthCLSpecs.Heze.Const.slotsPerEpoch < 2 ^ 64) :
    (e * UInt64.ofNat EthCLSpecs.Heze.Const.slotsPerEpoch).toNat =
      e.toNat * EthCLSpecs.Heze.Const.slotsPerEpoch := by
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' EthCLSpecs.Heze.Const.slotsPerEpochLt,
    Nat.mod_eq_of_lt h]

omit [Config] [CryptoBackend] in
/-- `get_block_root_at_slot` on the state after the next `processSlot` reads the root at the
slot, when the slot is less than `SLOTS_PER_HISTORICAL_ROOT` behind. The write of
`processSlot` sits at the index of the state slot, and a slot that close has another
index. -/
theorem RootsInv.read_slotWrite {st₀ : BeaconState} {p : List ChainStep} {u u' : BeaconState}
    (hi : RootsInv st₀ p u) {s : Slot} {r : Root}
    (h : runPure (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun)
      (pureState (slotWrite u)) s) (slotWrite u) = .ok (r, u'))
    (hgap : u.slot.toNat < s.toNat + slotsPerHistoricalRoot) :
    r = rootAtSlot st₀ p s.toNat := by
  obtain ⟨h1, -, h3, -⟩ := getBlockRootAtSlot_run_ok h
  change s.toNat < u.slot.toNat at h1
  rw [h3]
  change vmodGet (u.blockRoots.set! (umodIdx u.slot slotsPerHistoricalRoot)
    (htr (filledHeader u))) s slotsPerHistoricalRoot = _
  rw [vmodGet_set!, if_neg (mod_ne_of_lt h1 hgap)]
  exact hi.roots s h1 (Nat.le_of_lt hgap)

end Inv

end EthCLSpecs.Proofs.Heze
