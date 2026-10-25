import EthCLSpecs.Proofs.Heze.PayloadRaceRefines
import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.StorePure.Basic

/-!
# `EthCLSpecs.Proofs.Heze.PayloadRaceWalk`: weight decides the walk at `pending r`

From slot `N + 2` on, the block `r` of slot `N` is not from the previous slot. So
`is_previous_slot_payload_decision` (`gloas/fork-choice.md:410`) is false at both children
of `pending r`. Then `get_weight` (`:516`) returns the attestation score plus the gated
proposer score. The two children have the same root, so the `max` key of `get_head`
(`:584-590`) compares the weights first. A tie goes to the tiebreaker. Off the decision slot
the tiebreaker is the raw status, and FULL wins it.

`WeightAhead store r` states that EMPTY is strictly ahead on weight. Under it, the loop body
of `getHead` at `pending r` steps to `empty r` (`headLoopBody_run_pending_of_ahead`).
`weightAhead_of_scores` derives `WeightAhead` from the two score runs: the EMPTY score beats
the FULL score plus a bound `boost` on every proposer score. `getWeight_run_bounds` gives
the shape of a weight run off the decision slot: the score, or the score plus one proposer
score.

`getHead_run_below_empty` lifts the step to the walk with
`headLoop_run_avoids_full_of_step` (`HeadAvoidsFull.lean`). The head avoids `full r`. A
head strictly below `pending r` is below `empty r`, because those two nodes are the only
children of `pending r` (`NodeBelow.pending_split`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok run_pure_eq_ok toNat_add_of_not_lt
  pureState)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd)
open EthCLSpecs.Heze (Preset Config Store State BeaconState Root ForkChoiceNode BeaconBlock Gwei
  getCurrentSlot isPreviousSlotPayloadDecision getWeight getNodeChildren getHead
  getAttestationScore getProposerScore getParentPayloadStatus)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- `getParentPayloadStatus` answers EMPTY or FULL, never PENDING. -/
theorem getParentPayloadStatus_run_ne_pending (store s s' : Store map) (b : BeaconBlock)
    (v : UInt8)
    (h : (getParentPayloadStatus (StoreTransition := ForkChoiceStoreRun (Store map))
      store b).run s = .ok (v, s')) :
    v ≠ EthCLSpecs.Heze.Const.payloadStatusPending := by
  rcases getParentPayloadStatus_run_decided store s s' b v h with rfl | rfl
  · exact payloadStatus_empty_ne_pending
  · exact payloadStatus_full_ne_pending

/-- A node strictly below `pending r` is below `empty r` or below `full r`. Those are the
only children of `pending r`. An edge out of a pending node goes to one of its two decided
nodes. A block edge never starts at a pending node, because a parent status is never
PENDING. -/
theorem NodeBelow.pending_split (store : Store map) (r : Root) (n : ForkChoiceNode)
    (h : NodeBelow store (ForkChoiceNode.pending r) n) (hne : n ≠ ForkChoiceNode.pending r) :
    NodeBelow store (ForkChoiceNode.empty r) n ∨ NodeBelow store (ForkChoiceNode.full r) n := by
  induction h with
  | refl => exact absurd rfl hne
  | step p c hp hpc ih =>
    by_cases hpr : p = ForkChoiceNode.pending r
    · subst hpr
      rcases NodeEdge.cases_on_child store _ c hpc with
        ⟨hp', hc | hc⟩ | ⟨root, b, s, s', -, -, -, hstatus⟩
      · have hroot : c.root = r := (congrArg ForkChoiceNode.root hp').symm
        rw [hc, hroot]
        exact Or.inl NodeBelow.refl
      · have hroot : c.root = r := (congrArg ForkChoiceNode.root hp').symm
        rw [hc, hroot]
        exact Or.inr NodeBelow.refl
      · exact absurd rfl (getParentPayloadStatus_run_ne_pending store s s' b _ hstatus)
    · rcases ih hpr with h' | h'
      · exact Or.inl (NodeBelow.step p c h' hpc)
      · exact Or.inr (NodeBelow.step p c h' hpc)

variable [Config]

/-- EMPTY is strictly ahead of FULL on weight at `r`. Every pair of successful weight runs,
at any runner states, puts EMPTY ahead. -/
def WeightAhead (store : Store map) (r : Root) : Prop :=
  ∀ (s₁ s₁' s₂ s₂' : Store map) (wE wF : Gwei),
    (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store
      (ForkChoiceNode.empty r)).run s₁ = .ok (wE, s₁') →
    (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store
      (ForkChoiceNode.full r)).run s₂ = .ok (wF, s₂') →
    wF < wE

/-- `betterOf a b` returns `a` when every pair of weight runs puts `a` strictly ahead. The
weight comparison comes first, so the root and the tiebreaker do not matter. -/
theorem betterOf_run_of_ahead (store : Store map) (a b x : ForkChoiceNode) (s s' : Store map)
    (hahead : ∀ (s₁ s₁' s₂ s₂' : Store map) (wA wB : Gwei),
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store a).run s₁
        = .ok (wA, s₁') →
      (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store b).run s₂
        = .ok (wB, s₂') →
      wB < wA)
    (h : (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store a b).run s
      = .ok (x, s')) :
    x = a := by
  unfold getHead.betterOf at h
  obtain ⟨wA, s1, hwA, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨wB, s2, hwB, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hlt := hahead _ _ _ _ _ _ hwA hwB
  split at h
  · exact run_pure_eq_ok _ _ _ _ h
  · rename_i hng
    exact absurd hlt hng

/-- At `pending r`, the loop body steps to `empty r` when EMPTY is ahead on weight. The fold
starts at `empty r`, the first child. Each `betterOf` step against `empty r` or `full r`
keeps `empty r`. -/
theorem headLoopBody_run_pending_of_ahead (store : Store map) (blocks : Array Root) (r : Root)
    (hahead : WeightAhead store r) (c : ForkChoiceNode) (s s' : Store map)
    (h : (headLoopBody store blocks (ForkChoiceNode.pending r)).run s = .ok (.next c, s')) :
    c = ForkChoiceNode.empty r := by
  unfold headLoopBody headFold at h
  obtain ⟨cs, s1, hcs, h⟩ := run_bind_eq_ok _ _ _ _ h
  split at h
  · cases run_pure_eq_ok _ _ _ _ h
  · obtain ⟨best, s2, hfold, h⟩ := run_bind_eq_ok _ _ _ _ h
    have hc : c = best := by
      have := run_pure_eq_ok _ _ _ _ h
      injection this
    subst hc
    have hself : ∀ (x : ForkChoiceNode) (t t' : Store map),
        (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store
          (ForkChoiceNode.empty r) (ForkChoiceNode.empty r)).run t = .ok (x, t') →
        x = ForkChoiceNode.empty r := fun x t t' hx => by
      rcases betterOf_run_mem store _ _ x t t' hx with hx | hx <;> exact hx
    have hEF : ∀ (x : ForkChoiceNode) (t t' : Store map),
        (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store
          (ForkChoiceNode.empty r) (ForkChoiceNode.full r)).run t = .ok (x, t') →
        x = ForkChoiceNode.empty r := fun x t t' hx =>
      betterOf_run_of_ahead store _ _ x t t' hahead hx
    -- Each `betterOf` step from `empty r` against a child of `pending r` stays at `empty r`.
    have hkeep : ∀ (l : List ForkChoiceNode),
        (∀ x ∈ l, x = ForkChoiceNode.empty r ∨ x = ForkChoiceNode.full r) →
        ∀ (y : ForkChoiceNode) (t t' : Store map),
          (l.foldlM (getHead.betterOf (StoreTransition := ForkChoiceStoreRun (Store map)) store)
            (ForkChoiceNode.empty r)).run t = .ok (y, t') →
          y = ForkChoiceNode.empty r := by
      intro l
      induction l with
      | nil => intro _ y t t' hy; exact run_pure_eq_ok _ _ _ _ hy
      | cons x xs ih =>
        intro hl y t t' hy
        rw [List.foldlM_cons] at hy
        obtain ⟨z, t1, hz, hy⟩ := run_bind_eq_ok _ _ _ _ hy
        have hz' : z = ForkChoiceNode.empty r := by
          rcases hl x List.mem_cons_self with hx | hx <;> subst hx
          · exact hself z _ _ hz
          · exact hEF z _ _ hz
        subst hz'
        exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) y t1 t' hy
    -- The children are `#[empty r, full r]`, or `#[empty r]` without a verified payload.
    -- `#[…][0]!` reduces to `empty r`, so `hkeep` applies to the fold without a change.
    simp only [getNodeChildren, ForkChoiceNode.pending] at hcs
    split at hcs
    · split at hcs
      · rw [run_pure_eq_ok _ _ _ _ hcs, ← Array.foldlM_toList] at hfold
        exact hkeep _ (by simp) _ _ _ hfold
      · rw [run_pure_eq_ok _ _ _ _ hcs, ← Array.foldlM_toList] at hfold
        exact hkeep _ (by simp) _ _ _ hfold
    · rename_i hnp
      exact absurd rfl hnp

/-- Off the decision slot, a successful weight run returns the score, or the score plus a
proposer score. The final add is `checkedAdd`, so the `toNat` sum is exact. Under
`StorePure`, the justified state is the uncached box of `st`. -/
theorem getWeight_run_bounds (store : Store map) (node : ForkChoiceNode)
    (hp : StorePure store)
    (hnd : ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store node).run t = .ok (b, t') → b = false)
    {t t' : Store map} {w : Gwei}
    (h : (getWeight (StoreTransition := ForkChoiceStoreRun (Store map)) store node).run t
      = .ok (w, t')) :
    ∃ (st : BeaconState) (sc : Gwei) (t1 t1' : Store map),
      FcMap.lookup store.checkpointStates store.justifiedCheckpoint = some (pureState st) ∧
      (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
        store node (pureState st)).run t1 = .ok (sc, t1') ∧
      (w = sc ∨ ∃ (ps : Gwei) (t2 t2' : Store map),
        (getProposerScore (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t2
          = .ok (ps, t2') ∧ w.toNat = sc.toNat + ps.toNat) := by
  unfold getWeight at h
  obtain ⟨b, u1, hb, h⟩ := run_bind_eq_ok _ _ _ _ h
  have hb' := hnd _ _ _ hb
  subst hb'
  simp only [Bool.false_eq_true, if_false, FcMap.getOrThrowKey] at h
  split at h
  · rename_i st0 hst
    -- The justified state is the uncached box of a value `st`.
    obtain ⟨st, hv⟩ := hp.checkpointStates_some _ (by rw [hst]; rfl)
    rw [hst] at hv
    injection hv with hv
    subst hv
    simp only [pure_bind] at h
    obtain ⟨sc, u2, hsc, h⟩ := run_bind_eq_ok _ _ _ _ h
    refine ⟨st, sc, u1, u2, hst, hsc, ?_⟩
    obtain ⟨ab, u3, -, h⟩ := run_bind_eq_ok _ _ _ _ h
    split at h
    · exact Or.inl (run_pure_eq_ok _ _ _ _ h)
    · obtain ⟨anc, u4, -, h⟩ := run_bind_eq_ok _ _ _ _ h
      split at h
      · obtain ⟨ps, u5, hps, h⟩ := run_bind_eq_ok _ _ _ _ h
        simp only [checkedAdd] at h
        split at h
        · simp [EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run] at h
        · rename_i hno
          refine Or.inr ⟨ps, u4, u5, hps, ?_⟩
          rw [run_pure_eq_ok _ _ _ _ h]
          exact toNat_add_of_not_lt _ _ hno
      · exact Or.inl (run_pure_eq_ok _ _ _ _ h)
  · simp [EthCLLib.Proofs.run_throw, EthCLLib.Proofs.except_bind_error] at h

/-- Off the decision slot, EMPTY is ahead on weight when its score beats the FULL score plus
`boost`, and `boost` bounds every proposer score. The boost reaches a child at most once.
So FULL's weight is at most its score plus `boost`. EMPTY's weight is at least its score. -/
theorem weightAhead_of_scores (store : Store map) (r : Root) (boost : Nat)
    (hp : StorePure store)
    (hndE : ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store (ForkChoiceNode.empty r)).run t = .ok (b, t') → b = false)
    (hndF : ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store (ForkChoiceNode.full r)).run t = .ok (b, t') → b = false)
    (hboost : ∀ (t t' : Store map) (ps : Gwei),
      (getProposerScore (StoreTransition := ForkChoiceStoreRun (Store map)) store).run t
        = .ok (ps, t') → ps.toNat ≤ boost)
    (hscore : ∀ (st : BeaconState) (sE sF : Gwei) (t₁ t₁' t₂ t₂' : Store map),
      FcMap.lookup store.checkpointStates store.justifiedCheckpoint = some (pureState st) →
      (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
        store (ForkChoiceNode.empty r) (pureState st)).run t₁ = .ok (sE, t₁') →
      (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
        store (ForkChoiceNode.full r) (pureState st)).run t₂ = .ok (sF, t₂') →
      sF.toNat + boost < sE.toNat) :
    WeightAhead store r := by
  intro s₁ s₁' s₂ s₂' wE wF hE hF
  obtain ⟨st, sE, t1, t1', hst, hsE, hwE⟩ := getWeight_run_bounds store _ hp hndE hE
  obtain ⟨st', sF, t2, t2', hst', hsF, hwF⟩ := getWeight_run_bounds store _ hp hndF hF
  rw [hst] at hst'
  injection hst' with hst'
  have e : st = st' := congrArg SizzLean.Cache.SSZ.Box.view hst'
  subst e
  have hlt := hscore st sE sF _ _ _ _ hst hsE hsF
  have hE' : sE.toNat ≤ wE.toNat := by
    rcases hwE with h | ⟨ps, _, _, _, h⟩
    · rw [h]; exact Nat.le_refl _
    · omega
  have hF' : wF.toNat ≤ sF.toNat + boost := by
    rcases hwF with h | ⟨ps, _, _, hps, h⟩
    · rw [h]; omega
    · have := hboost _ _ _ hps; omega
  rw [UInt64.lt_iff_toNat_lt]
  omega

/-- A node whose block is two or more slots before the current slot is off the decision
slot: every run of `isPreviousSlotPayloadDecision` answers `false`. -/
theorem isPreviousSlotPayloadDecision_run_false (store : Store map) (node : ForkChoiceNode)
    (nb : BeaconBlock) (cs : EthCLSpecs.Heze.Slot)
    (hblock : FcMap.lookup store.blocks node.root = some nb)
    (hcur : (getCurrentSlot (StoreTransition := ForkChoiceStoreRun (Store map)) store).run store
      = .ok (cs, store))
    (hlt : nb.slot.toNat + 1 < cs.toNat) :
    ∀ (t t' : Store map) (b : Bool),
      (isPreviousSlotPayloadDecision (StoreTransition := ForkChoiceStoreRun (Store map))
        store node).run t = .ok (b, t') → b = false := by
  intro t t' b h
  have hcur' := getCurrentSlot_run_state store store t cs hcur
  have hno : ¬ (nb.slot + 1 < nb.slot) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    have : cs.toNat < 2 ^ 64 := cs.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have hne : (nb.slot + 1 == cs) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have := congrArg UInt64.toNat heq
    rw [UInt64.toNat_add] at this
    have : cs.toNat < 2 ^ 64 := cs.toNat_lt
    simp only [UInt64.toNat_one] at *
    omega
  simp [isPreviousSlotPayloadDecision, FcMap.getOrThrow, FcMap.getOrThrowKey, hblock,
    checkedAdd, hno, hcur'] at h
  change Except.ok _ = Except.ok _ at h
  injection h with h
  injection h with h1 _
  rw [← h1, hne, Bool.false_and]

/-- EMPTY is ahead on weight at `r`. Then the head avoids `full r`, and a head strictly
below `pending r` is below `empty r`. -/
theorem getHead_run_below_empty (store : Store map) (r : Root) (hahead : WeightAhead store r)
    (hjustified : ¬ NodeBelow store (.full r) (.pending store.justifiedCheckpoint.root))
    (runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) store).run runnerStore
      = .ok (head, s')) :
    ¬ NodeBelow store (.full r) head ∧
      (NodeBelow store (.pending r) head → head ≠ .pending r →
        NodeBelow store (.empty r) head) := by
  rw [getHead_eq_fuelLoop_headLoopBody] at hrun
  obtain ⟨blocks, s1, -, hloop⟩ := run_bind_eq_ok _ _ _ _ hrun
  have havoid := headLoop_run_avoids_full_of_step store blocks r
    (fun c t t' h => headLoopBody_run_pending_of_ahead store blocks r hahead c t t' h)
    _ _ _ head s1 s' hjustified hjustified hloop
  refine ⟨havoid, fun hbelow hne => ?_⟩
  rcases NodeBelow.pending_split store r head hbelow hne with h | h
  · exact h
  · exact absurd h havoid

end

end EthCLSpecs.Proofs.Heze
