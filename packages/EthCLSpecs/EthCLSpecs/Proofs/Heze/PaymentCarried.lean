import EthCLSpecs.Proofs.Heze.PaymentWriters

/-!
# `EthCLSpecs.Proofs.Heze.PaymentCarried`: the payment of a bid reaches its judge

`BidPaymentCarried` (`BuilderPendingPayments.lean`) says that the entry for the slot of a
bid still carries the bid's withdrawal when `processBuilderPendingPayments` reads it. This
module derives it from the chain between the block `r` of the bid and that read.

## The run

`ChainRun hi steps st st'` runs `steps` from `st` to `st'`. A `slot` step is one iteration
of the `processSlots` loop (`SlotStep`). It needs a state slot below `hi`. A `block sb v`
step is the part of `stateTransition` after `processSlots` (`BlockStep`).
`processSlots_chainRun` and `stateTransition_chainRun` turn the spec functions into runs.

The states of a run are plain values. Each step runs from the uncached box of a value to
the uncached box of another, and every spec function on the way keeps the uncached box
(`KeepsUncached.lean`). So the proofs below split a run with `run_bind_eq_ok_pure`, and
each state on the way is `pureState` of a value.

Both steps are relations. A `def` of the loop body is not definitionally equal to the body
that the `do` notation builds, because the notation names a join point. A `def` of the
block half is not equal to the tail of `stateTransition` either: each `assert` raises an
error whose message holds the source text of its condition. `slotIteration` and
`blockStep` compute one step each, and `slotIteration_slotStep` and `blockStep_blockStep`
relate them to the relations.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok keepsUncached_bind
  keepsUncached_pure)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Slot ExecutionPayloadBid SignedBeaconBlock
  BeaconBlock builderPaymentIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

/-- Two uncached boxes are equal only when their values are. -/
theorem pureState_inj [Preset] [HasherTag] {a b : BeaconState}
    (h : pureState a = pureState b) : a = b :=
  congrArg SizzLean.Cache.SSZ.Box.view h

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The eight epoch substeps before `processBuilderPendingPayments` keep the uncached
box. -/
theorem keepsUncached_processEpochPrefix : KeepsUncached processEpochPrefix := by
  unfold processEpochPrefix
  refine keepsUncached_bind keepsUncached_processJustificationAndFinalization (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processInactivityUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processRewardsAndPenalties (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processRegistryUpdates (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processSlashings (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processEth1DataReset (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processPendingDeposits (fun _ => ?_)
  exact keepsUncached_processPendingConsolidations

/-- One iteration of the `processSlots` loop, as a relation: `processSlot`, then
`processEpoch` when the next slot starts an epoch, then the slot increment. -/
def SlotStep (st st' : BeaconState) : Prop :=
  ∃ st1 st2 : BeaconState,
    (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState st)
      = .ok ((), pureState st1) ∧
    (if ((sszGet (pureState st1) slot) + 1) % UInt64.ofNat slotsPerEpoch == 0 then
      (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run (pureState st1)
        = .ok ((), pureState st2)
    else st2 = st1) ∧
    pureState st' = (sszUpdate (pureState st2) with slot := (sszGet (pureState st2) slot) + 1)

/-- One iteration of the `processSlots` loop, as a function. -/
def slotIteration : HezeRun Unit := do
  EthCLSpecs.Heze.processSlot
  if ((sszGet (← get) slot) + 1) % UInt64.ofNat slotsPerEpoch == 0 then
    EthCLSpecs.Heze.processEpoch
  EthCLSpecs.Heze.modifyState fun state => sszUpdate state with slot := (sszGet state slot) + 1

/-- A successful `slotIteration` is a `SlotStep`. -/
theorem slotIteration_slotStep {st st' : BeaconState}
    (h : slotIteration.run (pureState st) = .ok ((), pureState st')) : SlotStep st st' := by
  unfold slotIteration at h
  obtain ⟨⟨⟩, st1, hslot, h⟩ := run_bind_eq_ok_pure keepsUncached_processSlot h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨hc, h⟩ | ⟨hc, h⟩
  · obtain ⟨⟨⟩, st2, hep, h⟩ := run_bind_eq_ok_pure keepsUncached_processEpoch h
    exact ⟨st1, st2, hslot, by rw [if_pos hc]; exact hep, modifyState_run_eq h⟩
  · exact ⟨st1, st1, hslot, by rw [if_neg hc], modifyState_run_eq h⟩

/-- `slotIteration` keeps the uncached box. -/
theorem keepsUncached_slotIteration : KeepsUncached slotIteration := by
  unfold slotIteration
  keeps_uncached_using [keepsUncached_processSlot, keepsUncached_processEpoch]

/-- The part of `stateTransition` after `processSlots`, as a relation. With
`validateResult`, the signature check passes on `st`. `processBlock` runs to `st'`. With
`validateResult`, the state root of `st'` matches the block. On an uncached box,
`stateRoot` returns the same box, so the run ends in the box that `processBlock`
returns. -/
def BlockStep (sb : SignedBeaconBlock) (validateResult : Bool) (st st' : BeaconState) :
    Prop :=
  (validateResult = true → EthCLSpecs.Heze.verifyBlockSignature (pureState st) sb = .ok true) ∧
  (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) sb.message).run (pureState st)
    = .ok ((), pureState st') ∧
  (validateResult = true → sb.message.stateRoot = bytesToRoot (stateRoot (pureState st')).1)

/-- The part of `stateTransition` after `processSlots`, as a function. -/
def blockStep (sb : SignedBeaconBlock) (validateResult : Bool) : HezeRun Unit := do
  let block := sb.message
  if validateResult then assert (← liftErr (EthCLSpecs.Heze.verifyBlockSignature (← get) sb))
  EthCLSpecs.Heze.processBlock block
  if validateResult then
    let root ← getStateRoot
    assert (block.stateRoot == bytesToRoot root)

/-- `blockStep` keeps the uncached box. -/
theorem keepsUncached_blockStep (sb : SignedBeaconBlock) (v : Bool) :
    KeepsUncached (blockStep sb v) := by
  unfold blockStep
  -- The `let` of the block and the join point after the first `if` both elaborate to
  -- local definitions. `extract_lets` names them, as in `keepsUncached_stateTransition`.
  extract_lets block jp
  have hjp : ∀ y, KeepsUncached (jp y) := fun _ => by
    refine keepsUncached_bind (keepsUncached_processBlock _) (fun _ => ?_)
    exact EthCLLib.Proofs.keepsUncached_ite
      (fun _ => keepsUncached_bind EthCLLib.Proofs.keepsUncached_getStateRoot
        (fun _ => EthCLLib.Proofs.keepsUncached_ite (fun _ => keepsUncached_pure _)
          (fun _ => EthCLLib.Proofs.keepsUncached_throw _)))
      (fun _ => keepsUncached_pure _)
  exact EthCLLib.Proofs.keepsUncached_ite
    (fun _ => keepsUncached_bind EthCLLib.Proofs.keepsUncached_get
      (fun _ => keepsUncached_bind (EthCLLib.Proofs.keepsUncached_liftErr _)
        (fun _ => keepsUncached_bind (EthCLLib.Proofs.keepsUncached_ite
          (fun _ => keepsUncached_pure _) (fun _ => EthCLLib.Proofs.keepsUncached_throw _)) hjp)))
    (fun _ => keepsUncached_bind (keepsUncached_pure _) hjp)

omit [Config] [CryptoBackend] in
/-- A run of `getStateRoot` on an uncached box returns the root and the same box. -/
theorem run_getStateRoot (s : BeaconState) :
    (getStateRoot : HezeRun ByteArray).run (pureState s)
      = .ok ((stateRoot (pureState s)).1, pureState s) := rfl

/-- The tail of a block step, after the signature check: `processBlock`, then the state
root check when `validateResult` holds. A successful run gives the last two facts of
`BlockStep`. The `assert` in the spec body and the one in `blockStep` raise errors with
different messages, so the statement takes the error `e` as an argument. -/
theorem blockStep_tail {sb : SignedBeaconBlock} {v : Bool} {st st' : BeaconState}
    {e : StateTransitionError}
    (h : ((EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) sb.message) >>= fun _ =>
      if v = true then (getStateRoot : HezeRun ByteArray) >>= fun root =>
        if (sb.message.stateRoot == bytesToRoot root) = true then pure PUnit.unit
        else throw e
      else pure PUnit.unit).run (pureState st) = .ok ((), pureState st')) :
    (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) sb.message).run (pureState st)
      = .ok ((), pureState st') ∧
    (v = true → sb.message.stateRoot = bytesToRoot (stateRoot (pureState st')).1) := by
  obtain ⟨⟨⟩, st1, hb, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlock _) h
  rcases run_ite_eq_ok h with ⟨hv, h⟩ | ⟨hv, h⟩
  · obtain ⟨root, s2, hr, h⟩ := run_bind_eq_ok _ _ _ _ h
    rw [run_getStateRoot] at hr
    injection hr with hr
    injection hr with hroot hs2
    subst hroot hs2
    rcases run_ite_eq_ok h with ⟨hc, h⟩ | ⟨-, h⟩
    · have e1 := pureState_inj (run_pure_state_eq _ _ _ _ h)
      subst e1
      exact ⟨hb, fun _ => beq_iff_eq.mp hc⟩
    · cases h
  · have e1 := pureState_inj (run_pure_state_eq _ _ _ _ h)
    subst e1
    exact ⟨hb, fun ht => absurd ht hv⟩

omit [Config] in
/-- The head of a block step: the signature check when `validateResult` holds, then the
tail on the same state. The check is an `Except` read, then its gate. The error `e` is an
argument, as in `blockStep_tail`. -/
theorem blockStep_head {sb : SignedBeaconBlock} {v : Bool} {st st' : BeaconState}
    {e : StateTransitionError} {tail : HezeRun Unit}
    (h : (if v = true then (get : HezeRun State) >>= fun s =>
        (liftErr (EthCLSpecs.Heze.verifyBlockSignature s sb) : HezeRun Bool) >>= fun b =>
        (if b = true then pure PUnit.unit else throw e) >>= fun _ => tail
      else (pure PUnit.unit : HezeRun PUnit) >>= fun _ => tail).run (pureState st)
        = .ok ((), pureState st')) :
    (v = true → EthCLSpecs.Heze.verifyBlockSignature (pureState st) sb = .ok true) ∧
      tail.run (pureState st) = .ok ((), pureState st') := by
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hv, h⟩
  · have h := run_get_bind_eq_ok _ _ _ h
    rw [EthCLLib.Proofs.run_bind] at h
    cases hx : EthCLSpecs.Heze.verifyBlockSignature (pureState st) sb with
    | error err =>
      rw [EthCLLib.Proofs.run_liftErr_of_error _ _ (by rw [hx]; rfl),
        EthCLLib.Proofs.except_bind_error] at h
      cases h
    | ok b =>
      rw [EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [hx]; rfl),
        EthCLLib.Proofs.except_bind_ok] at h
      obtain ⟨hs, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
      exact ⟨fun _ => congrArg Except.ok hs, h⟩
  · obtain ⟨⟨⟩, s1, hp, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e1 := run_pure_state_eq _ _ _ _ hp
    subst e1
    exact ⟨fun ht => absurd ht hv, h⟩

/-- A successful `blockStep` is a `BlockStep`. -/
theorem blockStep_blockStep {sb : SignedBeaconBlock} {v : Bool} {st st' : BeaconState}
    (h : (blockStep sb v).run (pureState st) = .ok ((), pureState st')) :
    BlockStep sb v st st' := by
  unfold blockStep at h
  dsimp only at h
  obtain ⟨hsig, h⟩ := blockStep_head h
  obtain ⟨hb, hroot⟩ := blockStep_tail h
  exact ⟨hsig, hb, hroot⟩

/-- A successful `stateTransition` is `processSlots` to the block's slot, then a
`BlockStep`. -/
theorem stateTransition_split {sb : SignedBeaconBlock} {v : Bool} {st st' : BeaconState}
    (h : (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb v).run (pureState st)
      = .ok ((), pureState st')) :
    ∃ mid : BeaconState,
      (EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) sb.message.slot).run
        (pureState st) = .ok ((), pureState mid) ∧ BlockStep sb v mid st' := by
  unfold EthCLSpecs.Heze.stateTransition at h
  dsimp only at h
  obtain ⟨⟨⟩, mid, hslots, h⟩ := run_bind_eq_ok_pure (keepsUncached_processSlots _) h
  obtain ⟨hsig, h⟩ := blockStep_head h
  obtain ⟨hb, hroot⟩ := blockStep_tail h
  exact ⟨mid, hslots, hsig, hb, hroot⟩

end

/-- A step of a chain run. -/
inductive ChainStep [Preset] where
  /-- One iteration of the `processSlots` loop. -/
  | slot
  /-- One block, with the `validateResult` flag of `stateTransition`. -/
  | block (sb : SignedBeaconBlock) (validateResult : Bool)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `ChainRun hi steps st st'`: `steps` run from `st` to `st'`, and each slot step starts
below slot `hi`. -/
inductive ChainRun (hi : Nat) : List ChainStep → BeaconState → BeaconState → Prop where
  | nil (st : BeaconState) : ChainRun hi [] st st
  | slot {steps : List ChainStep} {st st1 st2 : BeaconState}
      (hlt : (sszGet (pureState st) slot).toNat < hi)
      (hstep : SlotStep st st1)
      (hrest : ChainRun hi steps st1 st2) : ChainRun hi (.slot :: steps) st st2
  | block {steps : List ChainStep} {st st1 st2 : BeaconState} (sb : SignedBeaconBlock)
      (v : Bool) (hstep : BlockStep sb v st st1)
      (hrest : ChainRun hi steps st1 st2) : ChainRun hi (.block sb v :: steps) st st2

/-- Two runs in a row are a run. -/
theorem ChainRun.append {hi : Nat} {s1 s2 : List ChainStep} {a b c : BeaconState}
    (h1 : ChainRun hi s1 a b) (h2 : ChainRun hi s2 b c) : ChainRun hi (s1 ++ s2) a c := by
  induction h1 with
  | nil => exact h2
  | slot hlt hstep _ ih => exact .slot hlt hstep (ih h2)
  | block sb v hstep _ ih => exact .block sb v hstep (ih h2)

/-- `processEpoch` keeps the spine. -/
@[frame] theorem processEpoch_frame_spine {t t' : BeaconState} {a : Unit}
    (h : (EthCLSpecs.Heze.processEpoch (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    spineView (pureState t') = spineView (pureState t) := by
  rw [processEpoch_eq] at h
  frame_invert h

/-- A slot step adds one to the slot and keeps the header slot and the cached bid. -/
theorem SlotStep.spine {st st' : BeaconState} (h : SlotStep st st') :
    spineView (pureState st') = (sszGet (pureState st) slot + 1,
      (sszGet (pureState st) latestBlockHeader).slot,
      sszGet (pureState st) latestExecutionPayloadBid) := by
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  have e1 : spineView (pureState st1) = spineView (pureState st) :=
    spine_of_window (processSlot_frame h1)
  have e2 : spineView (pureState st2) = spineView (pureState st1) := by
    split at h2
    · exact processEpoch_frame_spine h2
    · rw [h2]
  have e := e2.trans e1
  simp only [spineView, Prod.mk.injEq] at e
  obtain ⟨es, eh, ec⟩ := e
  have hw : spineView (sszUpdate (pureState st2) with slot := (sszGet (pureState st2) slot) + 1)
      = (sszGet (pureState st2) slot + 1, (sszGet (pureState st2) latestBlockHeader).slot,
        sszGet (pureState st2) latestExecutionPayloadBid) := rfl
  rw [hst', hw, es, eh, ec]

/-- A run of slot steps from a body that makes one `SlotStep` per element: a `ChainRun` of
`k` slot steps. The slot goes up by one per step. Each run of the body keeps the uncached
box. -/
theorem slotLoop_chainRun (f : Nat → PUnit → HezeRun (ForInStep PUnit))
    (hk : ∀ a, KeepsUncached (f a PUnit.unit))
    (hf : ∀ a (st st3 : BeaconState) step,
      (f a PUnit.unit).run (pureState st) = .ok (step, pureState st3) →
      SlotStep st st3 ∧ step = .yield PUnit.unit)
    (hi : Nat) :
    ∀ (k s : Nat) (st st' : BeaconState), (sszGet (pureState st) slot).toNat + k ≤ hi →
      (sszGet (pureState st) slot).toNat + k < 2 ^ 64 →
      (forIn (List.range' s k) PUnit.unit f).run (pureState st)
        = .ok (PUnit.unit, pureState st') →
      ChainRun hi (List.replicate k .slot) st st' ∧
        (sszGet (pureState st') slot).toNat = (sszGet (pureState st) slot).toNat + k := by
  intro k
  induction k with
  | zero =>
    intro s st st' _ _ h
    rw [List.range'_zero, List.forIn_nil] at h
    have := pureState_inj (run_pure_state_eq _ _ _ _ h)
    subst this
    exact ⟨.nil _, rfl⟩
  | succ k ih =>
    intro s st st' hle hlt h
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨step, st3, hbody, hrest⟩ := run_bind_eq_ok_pure (hk s) h
    obtain ⟨hstep, rfl⟩ := hf s st st3 step hbody
    have hs3 : (sszGet (pureState st3) slot).toNat = (sszGet (pureState st) slot).toNat + 1 := by
      have := congrArg Prod.fst hstep.spine
      simp only [spineView] at this
      rw [this, UInt64.toNat_add, UInt64.toNat_one]
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨hrun, hslot⟩ := ih (s + 1) st3 st' (by omega) (by omega) hrest
    exact ⟨.slot (by omega) hstep hrun, by omega⟩

/-- A successful `processSlots` run to `target` is a run of slot steps, one per slot from
the start to `target`. Every step starts below `target`, so below any `hi ≥ target`. -/
theorem processSlots_chainRun (target : Slot) (hi : Nat) (hle : target.toNat ≤ hi)
    (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) target).run (pureState st)
      = .ok ((), pureState st')) :
    ChainRun hi (List.replicate (target.toNat - (sszGet (pureState st) slot).toNat) .slot)
        st st' ∧
      sszGet (pureState st') slot = target := by
  unfold EthCLSpecs.Heze.processSlots at h
  have h := run_get_bind_eq_ok _ _ _ h
  obtain ⟨hlt, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have hk : (target - sszGet (pureState st) slot).toNat
      = target.toNat - (sszGet (pureState st) slot).toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
  have hsize : ([:(target - sszGet (pureState st) slot).toNat] : Std.Legacy.Range).size
      = target.toNat - (sszGet (pureState st) slot).toNat := by
    simp [Std.Legacy.Range.size]
    exact hk
  rw [hsize] at h
  -- The loop, then `pure ()`.
  obtain ⟨⟨⟩, sL, h, hP⟩ := run_bind_eq_ok_pure
    (by keeps_uncached_using [keepsUncached_processSlot, keepsUncached_processEpoch]) h
  have hL := pureState_inj (run_pure_state_eq _ _ _ _ hP)
  subst sL
  have hlt' : (sszGet (pureState st) slot).toNat < target.toNat :=
    UInt64.lt_iff_toNat_lt.mp hlt
  have htgt : target.toNat < 2 ^ 64 := target.toNat_lt
  refine (fun hres => ⟨hres.1, UInt64.toNat_inj.mp (by have := hres.2; omega)⟩)
    (slotLoop_chainRun _
      (fun _ => by keeps_uncached_using [keepsUncached_processSlot, keepsUncached_processEpoch])
      ?_ hi (target.toNat - (sszGet (pureState st) slot).toNat) 0 st st'
      (by omega) (by omega) h)
  -- The loop body is one `SlotStep`, and it yields.
  intro a st0 st3 step hbody
  obtain ⟨⟨⟩, st1, hslot1, hbody⟩ := run_bind_eq_ok_pure keepsUncached_processSlot hbody
  have hbody := run_get_bind_eq_ok _ _ _ hbody
  rcases run_ite_eq_ok hbody with ⟨hc, hbody⟩ | ⟨hc, hbody⟩
  · obtain ⟨⟨⟩, st2, hep, hbody⟩ := run_bind_eq_ok_pure keepsUncached_processEpoch hbody
    obtain ⟨⟨⟩, st4, hmod, hbody⟩ :=
      run_bind_eq_ok_pure (EthCLLib.Proofs.keepsUncached_modify _ (fun _ => ⟨_, rfl⟩)) hbody
    have h4 := modifyState_run_eq hmod
    injection hbody with hbody
    injection hbody with hstep h3
    exact ⟨⟨st1, st2, hslot1, by rw [if_pos hc]; exact hep, h3 ▸ h4⟩, hstep.symm⟩
  · -- No epoch: `pure ()`, then the slot increment.
    obtain ⟨⟨⟩, st2, hp, hbody⟩ := run_bind_eq_ok_pure (keepsUncached_pure _) hbody
    have e2 := pureState_inj (run_pure_state_eq _ _ _ _ hp)
    subst st2
    obtain ⟨⟨⟩, st4, hmod, hbody⟩ :=
      run_bind_eq_ok_pure (EthCLLib.Proofs.keepsUncached_modify _ (fun _ => ⟨_, rfl⟩)) hbody
    have h4 := modifyState_run_eq hmod
    injection hbody with hbody
    injection hbody with hstep h3
    exact ⟨⟨st1, st1, hslot1, by rw [if_neg hc], h3 ▸ h4⟩, hstep.symm⟩

/-- A successful `stateTransition` is slot steps up to the block's slot, then the block. -/
theorem stateTransition_chainRun (sb : SignedBeaconBlock) (v : Bool) (hi : Nat)
    (hle : sb.message.slot.toNat ≤ hi) (st st' : BeaconState)
    (h : (EthCLSpecs.Heze.stateTransition (StateTransition := HezeRun) sb v).run (pureState st)
      = .ok ((), pureState st')) :
    ∃ k, ChainRun hi (List.replicate k .slot ++ [.block sb v]) st st' := by
  obtain ⟨mid, hslots, hblock⟩ := stateTransition_split h
  obtain ⟨hrun, -⟩ := processSlots_chainRun _ hi hle st mid hslots
  exact ⟨_, hrun.append (.block sb v hblock (.nil st'))⟩

end

end EthCLSpecs.Proofs.Heze
