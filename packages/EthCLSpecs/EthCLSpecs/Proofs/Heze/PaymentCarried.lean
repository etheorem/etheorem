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

## The invariant

Let `n` be the slot of the bid, in epoch `e`, and `windowEnd n` the last slot of epoch
`e + 1`. `PaymentTracked` holds between steps:

- The state slot is in `[n, windowEnd n]`, and the header slot is at least `n`.
- The entry of `n` carries the bid's withdrawal and the recorded proposer `p`, in the upper
  half while the state is in epoch `e` and in the lower half while it is in epoch `e + 1`
  (`trackedIndex`).
- The cached bid is the bid, or a bid for a slot in `(n, slot]`.

`processBlock_r_records` establishes it at the block of the bid. `SlotStep.tracked` and
`processBlock_later_tracked` keep it, under two assumptions about the blocks: the first
block after the bid takes the EMPTY edge, and no block carries a proposer slashing whose
first header has slot `n` and proposer `p`. A writer touches the tracked entry only at the
index of a slot `s` with a matching epoch test, and `eq_of_tracked_hit` then gives `s = n`.

`bidPaymentCarried_of_run` runs the last `processSlot` and the first eight epoch substeps,
and concludes `BidPaymentCarried`. The recorded proposer is the block's proposer, because
`processBlockHeader` checks it against the function that the bid step reads, and
`processWithdrawals` between the two keeps the proposer lookahead.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok keepsUncached_bind
  keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Slot ExecutionPayloadBid SignedBeaconBlock
  BeaconBlock builderPaymentIndex)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt)

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

end

/-! ## The proposer lookahead

`processExecutionPayloadBid` records `getBeaconProposerIndex` of the state it reads.
`processBlockHeader` checks the block's proposer against the same function, two steps
earlier. The function reads the slot and `proposerLookahead`, and `processWithdrawals`
runs between the two. The lemmas below prove that it keeps `proposerLookahead`, with the
walk of `PaymentFrame.lean` on the view `lookView`. -/

section
variable [Preset] [HasherTag]

/-- The proposer lookahead. -/
def lookView (st : State) := sszGet st proposerLookahead

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- `decreaseBalance` returns a state value with the lookahead of its argument. -/
@[frame] theorem decreaseBalance_ret_look {u t t' b : BeaconState}
    {i : EthCLSpecs.Heze.ValidatorIndex} {d : EthCLSpecs.Heze.Gwei}
    (h : (EthCLSpecs.Heze.decreaseBalance (StateTransition := HezeRun) (pureState u) i d).run
      (pureState t) = .ok (pureState b, pureState t')) :
    lookView (pureState b) = lookView (pureState u) := by
  frame_invert h

/-- `applyWithdrawals` writes the balances of validators and builders only. -/
@[frame] theorem applyWithdrawals_frame_look {t t' : BeaconState} {a : PUnit}
    {ws : Array EthCLSpecs.Heze.Withdrawal}
    (h : (EthCLSpecs.Heze.applyWithdrawals (StateTransition := HezeRun) ws).run (pureState t)
      = .ok (a, pureState t')) :
    lookView (pureState t') = lookView (pureState t) := by
  frame_invert h

/-- `processWithdrawals` keeps the lookahead. -/
@[frame] theorem processWithdrawals_frame_look {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processWithdrawals (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    lookView (pureState t') = lookView (pureState t) := by
  frame_invert h

omit [Config] [CryptoBackend] in
/-- `processBlockHeader` keeps the lookahead. -/
@[frame] theorem processBlockHeader_frame_look {t t' : BeaconState} {a : PUnit} {b : BeaconBlock}
    (h : (EthCLSpecs.Heze.processBlockHeader (StateTransition := HezeRun) b).run (pureState t)
      = .ok (a, pureState t')) :
    lookView (pureState t') = lookView (pureState t) := by
  frame_invert h

omit [Config] [CryptoBackend] in
/-- `getBeaconProposerIndex` reads the slot and the lookahead only. -/
theorem getBeaconProposerIndex_congr {a b : BeaconState}
    (hl : lookView (pureState a) = lookView (pureState b))
    (hs : sszGet (pureState a) slot = sszGet (pureState b) slot) :
    EthCLSpecs.Heze.getBeaconProposerIndex (pureState a)
      = EthCLSpecs.Heze.getBeaconProposerIndex (pureState b) := by
  unfold EthCLSpecs.Heze.getBeaconProposerIndex
  unfold lookView at hl
  rw [hl, hs]

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

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

/-! ## Epoch arithmetic

The window of the run is the epoch `e` of the bid's slot `n` and the epoch after it. The
lemmas below state the slot arithmetic for a symbolic `SLOTS_PER_EPOCH`. `omega` does not
reason about a quotient by a symbolic divisor, so each proof first names the quotients and
writes each product as a sum of the product `(n / S) * S` and multiples of `S`. -/

section
variable {S : Nat}

/-- `n < (n / S + 1) * S`: a slot is below the end of its epoch. -/
theorem lt_epoch_end (hS : 0 < S) (n : Nat) : n < (n / S + 1) * S := by
  have h := Nat.div_add_mod n S
  have hm := Nat.mod_lt n hS
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  omega

/-- A slot in `[n, (n / S + 2) * S)` is in the epoch of `n` or the next one. -/
theorem epoch_of_window (hS : 0 < S) {n x : Nat} (hge : n ≤ x) (hlt : x < (n / S + 2) * S) :
    x / S = n / S ∨ x / S = n / S + 1 := by
  have h1 : n / S ≤ x / S := Nat.div_le_div_right hge
  have h2 : x / S < n / S + 2 := (Nat.div_lt_iff_lt_mul hS).mpr hlt
  generalize x / S = q at *
  generalize n / S = e at *
  omega

/-- Inside an epoch, the next slot has the same epoch. -/
theorem succ_div_of_mod_ne {x : Nat} (h : (x + 1) % S ≠ 0) : (x + 1) / S = x / S := by
  rw [Nat.succ_div, if_neg (fun hd => h (Nat.mod_eq_zero_of_dvd hd)), Nat.add_zero]

/-- At the last slot of an epoch, the next slot starts the next epoch. -/
theorem succ_div_of_mod_eq {x : Nat} (h : (x + 1) % S = 0) : (x + 1) / S = x / S + 1 := by
  rw [Nat.succ_div, if_pos (Nat.dvd_of_mod_eq_zero h)]

/-- An epoch boundary below the end of the window is the boundary after the epoch of
`n`: the slot before it is in the epoch of `n`. -/
theorem epoch_at_boundary (hS : 0 < S) {n x : Nat} (hge : n ≤ x)
    (hlt : x + 1 < (n / S + 2) * S) (hb : (x + 1) % S = 0) : x / S = n / S := by
  rcases epoch_of_window hS hge (Nat.lt_of_succ_lt hlt) with h | h
  · exact h
  · exfalso
    have h3 := succ_div_of_mod_eq hb
    have h4 : (x + 1) / S < n / S + 2 := (Nat.div_lt_iff_lt_mul hS).mpr hlt
    rw [h3, h] at h4
    exact Nat.lt_irrefl _ h4

/-- The last slot of the epoch after the epoch of `n` is in that epoch. -/
theorem windowEnd_div (hS : 0 < S) (n : Nat) : ((n / S + 2) * S - 1) / S = n / S + 1 := by
  apply Nat.div_eq_of_lt_le
  · simp only [Nat.add_mul, Nat.one_mul]
    generalize n / S * S = a
    omega
  · simp only [Nat.add_mul, Nat.one_mul]
    generalize n / S * S = a
    omega

end

section
variable [Preset]

/-- The last slot of the epoch after the epoch of `n`. -/
def windowEnd (n : Slot) : Nat := (n.toNat / slotsPerEpoch + 2) * slotsPerEpoch - 1

/-- The slot of the bid is inside its window. -/
theorem le_windowEnd (n : Slot) : n.toNat ≤ windowEnd n := by
  have h := lt_epoch_end slotsPerEpochPos n.toNat
  have hS := slotsPerEpochPos
  unfold windowEnd
  simp only [Nat.add_mul, Nat.one_mul] at h ⊢
  generalize n.toNat / slotsPerEpoch * slotsPerEpoch = a at *
  omega

/-- `windowEnd n` is below `(n / S + 2) * S`, so a slot up to it is too. -/
theorem lt_of_le_windowEnd {n : Slot} {x : Nat} (hle : x ≤ windowEnd n) :
    x < (n.toNat / slotsPerEpoch + 2) * slotsPerEpoch := by
  have hpos : 0 < (n.toNat / slotsPerEpoch + 2) * slotsPerEpoch :=
    Nat.mul_pos (Nat.succ_pos _) slotsPerEpochPos
  unfold windowEnd at hle
  generalize (n.toNat / slotsPerEpoch + 2) * slotsPerEpoch = a at *
  omega

/-- A slot in `[n, windowEnd n]` is in the epoch of `n` or the next one. -/
theorem epoch_of_tracked {n : Slot} {x : Nat} (hge : n.toNat ≤ x) (hle : x ≤ windowEnd n) :
    x / slotsPerEpoch = n.toNat / slotsPerEpoch ∨
      x / slotsPerEpoch = n.toNat / slotsPerEpoch + 1 :=
  epoch_of_window slotsPerEpochPos hge (lt_of_le_windowEnd hle)

end

section
variable [Preset] [HasherTag]

/-- The index of the entry of the bid for slot `n` at `st`: the upper half while `st` is in
the epoch of `n`, the lower half after it. -/
def trackedIndex (n : Slot) (st : State) : Nat :=
  builderPaymentIndex n
    ((sszGet st slot).toNat / slotsPerEpoch == n.toNat / slotsPerEpoch)

/-- The current epoch as a `Nat` division. -/
theorem currentEpochOf_toNat (st : BeaconState) :
    (EthCLSpecs.Heze.currentEpochOf (pureState st)).toNat
      = (sszGet (pureState st) slot).toNat / slotsPerEpoch :=
  computeEpochAtSlot_toNat _

/-- The previous epoch as a `Nat`, when the current epoch is not the first. -/
theorem previousEpochOf_toNat (st : BeaconState)
    (h : 0 < (sszGet (pureState st) slot).toNat / slotsPerEpoch) :
    (EthCLSpecs.Heze.previousEpochOf (pureState st)).toNat
      = (sszGet (pureState st) slot).toNat / slotsPerEpoch - 1 := by
  -- `simp` reads `sszGet (pureState st) slot` as `st.slot`, so the proof states every fact
  -- in that form.
  have hc : (EthCLSpecs.Heze.currentEpochOf (pureState st)).toNat
      = st.slot.toNat / slotsPerEpoch := currentEpochOf_toNat st
  change 0 < st.slot.toNat / slotsPerEpoch at h
  show _ = st.slot.toNat / slotsPerEpoch - 1
  unfold EthCLSpecs.Heze.previousEpochOf
  have hne : (EthCLSpecs.Heze.currentEpochOf (pureState st)
      == EthCLSpecs.Heze.Const.genesisEpoch) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hc
    exact absurd hc (by simp [EthCLSpecs.Heze.Const.genesisEpoch]; omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [UInt64.toNat_sub_of_le _ _ (by
    rw [UInt64.le_iff_toNat_le, hc]; simp; omega), hc]
  simp

/-- A write that the spec makes at the index of slot `s`, after an epoch test on `s`,
hits the tracked entry of `n` only when `s = n`. The proposer slashing and the settlement
of `applyParentExecutionPayload` make such writes. -/
theorem eq_of_tracked_hit {n s : Slot} {st : BeaconState}
    (hge : n.toNat ≤ (sszGet (pureState st) slot).toNat)
    (hle : (sszGet (pureState st) slot).toNat ≤ windowEnd n)
    (h : (trackedIndex n (pureState st) = builderPaymentIndex s true ∧
          EthCLSpecs.Heze.computeEpochAtSlot s = EthCLSpecs.Heze.currentEpochOf (pureState st)) ∨
        (trackedIndex n (pureState st) = builderPaymentIndex s false ∧
          EthCLSpecs.Heze.computeEpochAtSlot s
            = EthCLSpecs.Heze.previousEpochOf (pureState st))) :
    s = n := by
  have hE := epoch_of_tracked hge hle
  unfold trackedIndex at h
  rcases h with ⟨hi, he⟩ | ⟨hi, he⟩
  · have he' := congrArg UInt64.toNat he
    rw [computeEpochAtSlot_toNat, currentEpochOf_toNat] at he'
    by_cases hc : (sszGet (pureState st) slot).toNat / slotsPerEpoch = n.toNat / slotsPerEpoch
    · rw [hc, beq_self_eq_true] at hi
      exact builderPaymentIndex_inj hi.symm (he'.trans hc)
    · rw [show ((sszGet (pureState st) slot).toNat / slotsPerEpoch
          == n.toNat / slotsPerEpoch) = false from beq_eq_false_iff_ne.mpr hc] at hi
      exact absurd hi.symm (builderPaymentIndex_true_ne_false s n)
  · have he' := congrArg UInt64.toNat he
    by_cases hc : (sszGet (pureState st) slot).toNat / slotsPerEpoch = n.toNat / slotsPerEpoch
    · rw [hc, beq_self_eq_true] at hi
      exact absurd hi (builderPaymentIndex_true_ne_false n s)
    · rw [show ((sszGet (pureState st) slot).toNat / slotsPerEpoch
          == n.toNat / slotsPerEpoch) = false from beq_eq_false_iff_ne.mpr hc] at hi
      have hnext : (sszGet (pureState st) slot).toNat / slotsPerEpoch
          = n.toNat / slotsPerEpoch + 1 :=
        hE.resolve_left hc
      have hpos : 0 < (sszGet (pureState st) slot).toNat / slotsPerEpoch := by
        rw [hnext]
        exact Nat.succ_pos _
      rw [computeEpochAtSlot_toNat, previousEpochOf_toNat st hpos, hnext,
        Nat.add_sub_cancel] at he'
      exact builderPaymentIndex_inj hi.symm he'

/-- The bid of a later block writes the upper index of the state slot. The tracked entry
is elsewhere: in the epoch of `n` the slots differ, and after it the halves differ. -/
theorem trackedIndex_ne_bid {n : Slot} {st : BeaconState}
    (hlt : n.toNat < (sszGet (pureState st) slot).toNat) :
    trackedIndex n (pureState st) ≠ builderPaymentIndex (sszGet (pureState st) slot) true := by
  intro hi
  unfold trackedIndex at hi
  by_cases hc : (sszGet (pureState st) slot).toNat / slotsPerEpoch = n.toNat / slotsPerEpoch
  · rw [hc, beq_self_eq_true] at hi
    have := builderPaymentIndex_inj hi.symm hc
    rw [this] at hlt
    omega
  · rw [show ((sszGet (pureState st) slot).toNat / slotsPerEpoch
        == n.toNat / slotsPerEpoch) = false from beq_eq_false_iff_ne.mpr hc] at hi
    exact builderPaymentIndex_true_ne_false _ n hi.symm

end

/-! ## The quorum of the substep

`processBuilderPendingPayments_run` (`BuilderPendingPayments.lean`) states the substep on
`pureState` of a value, so a chain step applies it at the plain state of the run. The
quorum that it reads is `builderPaymentQuorum`. -/

section
variable [Preset] [HasherTag]

open EthCLSpecs.Heze.Const (builderPaymentThresholdNumerator builderPaymentThresholdDenominator)

omit [HasherTag] in
/-- The quorum of the substep is the spec expression: the total active balance `total`,
over `SLOTS_PER_EPOCH`, times the threshold fraction. The substep reads `total` through
`getTotalActiveBalance`. -/
theorem builderPaymentQuorum_eq (total : EthCLSpecs.Heze.Gwei) :
    builderPaymentQuorum total =
      (total / UInt64.ofNat slotsPerEpoch) *
        builderPaymentThresholdNumerator / builderPaymentThresholdDenominator := rfl

end

/-! ## The invariant -/

section
variable [Preset]

/-- No proposer slashing of the block has a first header at slot `n` by proposer `p`. -/
def NoSlashingAt (n : Slot) (p : EthCLSpecs.Heze.ValidatorIndex) (sb : SignedBeaconBlock) :
    Prop :=
  ∀ ps ∈ sb.message.body.proposerSlashings.val,
    ps.signedHeader1.message.slot ≠ n ∨ ps.signedHeader1.message.proposerIndex ≠ p

/-- The slot form: no slashing at slot `n` at all. -/
theorem noSlashingAt_of_slot {n : Slot} {sb : SignedBeaconBlock}
    (h : ∀ ps ∈ sb.message.body.proposerSlashings.val, ps.signedHeader1.message.slot ≠ n)
    (p : EthCLSpecs.Heze.ValidatorIndex) : NoSlashingAt n p sb :=
  fun ps hm => .inl (h ps hm)

/-- The proposer form: no slashing of proposer `p` at all. -/
theorem noSlashingAt_of_proposer {p : EthCLSpecs.Heze.ValidatorIndex} {sb : SignedBeaconBlock}
    (h : ∀ ps ∈ sb.message.body.proposerSlashings.val,
      ps.signedHeader1.message.proposerIndex ≠ p) (n : Slot) : NoSlashingAt n p sb :=
  fun ps hm => .inr (h ps hm)

/-- The first block of a list of steps. -/
def firstBlock? : List ChainStep → Option SignedBeaconBlock
  | [] => none
  | .slot :: rest => firstBlock? rest
  | .block sb _ :: _ => some sb

/-- The first block of `steps` takes the EMPTY edge of the block with bid `bid`. -/
def EmptyChild (bid : ExecutionPayloadBid) (steps : List ChainStep) : Prop :=
  ∀ sb, firstBlock? steps = some sb →
    sb.message.body.signedExecutionPayloadBid.message.parentBlockHash ≠ bid.blockHash

/-- No block of `steps` has a proposer slashing at slot `n` by proposer `p`. -/
def NoSlashingSteps (n : Slot) (p : EthCLSpecs.Heze.ValidatorIndex) (steps : List ChainStep) :
    Prop :=
  ∀ sb v, ChainStep.block sb v ∈ steps → NoSlashingAt n p sb

end

section
variable [Preset] [HasherTag]

/-- The state of the chain between the block of `bid` and the judging substep. `p` is the
proposer that `processExecutionPayloadBid` recorded for the bid. -/
structure PaymentTracked (bid : ExecutionPayloadBid) (p : EthCLSpecs.Heze.ValidatorIndex)
    (st : BeaconState) : Prop where
  /-- The slot is at least the bid's slot. -/
  slot_ge : bid.slot.toNat ≤ (sszGet (pureState st) slot).toNat
  /-- The slot is at most the last slot of the epoch after the bid's epoch. -/
  slot_le : (sszGet (pureState st) slot).toNat ≤ windowEnd bid.slot
  /-- The latest block header is at the bid's slot or later. -/
  header_ge : bid.slot.toNat ≤ (sszGet (pureState st) latestBlockHeader).slot.toNat
  /-- The tracked entry carries the bid's withdrawal. -/
  entry : withdrawalAt (pureState st) (trackedIndex bid.slot (pureState st))
    = bidWithdrawal bid
  /-- The tracked entry records the proposer `p`. -/
  proposer : proposerAt (pureState st) (trackedIndex bid.slot (pureState st)) = p
  /-- The cached bid is the bid, or a bid for a slot in `(n, slot]`. -/
  cache : sszGet (pureState st) latestExecutionPayloadBid = bid ∨
    (bid.slot.toNat < (sszGet (pureState st) latestExecutionPayloadBid).slot.toNat ∧
      (sszGet (pureState st) latestExecutionPayloadBid).slot.toNat
        ≤ (sszGet (pureState st) slot).toNat)

/-- A step that keeps the spine and the tracked entry keeps the invariant. -/
theorem PaymentTracked.of_frame {bid : ExecutionPayloadBid} {p : EthCLSpecs.Heze.ValidatorIndex}
    {st st' : BeaconState} (ht : PaymentTracked bid p st)
    (hs : spineView (pureState st') = spineView (pureState st))
    (he : withdrawalAt (pureState st') (trackedIndex bid.slot (pureState st))
        = withdrawalAt (pureState st) (trackedIndex bid.slot (pureState st)) ∧
      proposerAt (pureState st') (trackedIndex bid.slot (pureState st))
        = proposerAt (pureState st) (trackedIndex bid.slot (pureState st))) :
    PaymentTracked bid p st' := by
  simp only [spineView, Prod.mk.injEq] at hs
  obtain ⟨hsl, hh, hc⟩ := hs
  have hj : trackedIndex bid.slot (pureState st') = trackedIndex bid.slot (pureState st) := by
    unfold trackedIndex
    rw [hsl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsl]; exact ht.slot_ge
  · rw [hsl]; exact ht.slot_le
  · rw [hh]; exact ht.header_ge
  · rw [hj, he.1]; exact ht.entry
  · rw [hj, he.2]; exact ht.proposer
  · rw [hc, hsl]; exact ht.cache

/-- A step that keeps `windowView` keeps the invariant. -/
theorem PaymentTracked.of_windowView {bid : ExecutionPayloadBid}
    {p : EthCLSpecs.Heze.ValidatorIndex} {st st' : BeaconState} (ht : PaymentTracked bid p st)
    (h : windowView (pureState st') = windowView (pureState st)) : PaymentTracked bid p st' :=
  ht.of_frame (congrArg Prod.fst h) (entry_of_payments (congrArg Prod.snd h) _)

/-- A run of `op` over the elements of a list keeps a predicate `P` on values when each
run of `op` on an element keeps it. Each `op` keeps the uncached box. -/
theorem forIn_list_ops_inv {δ : Type} (P : BeaconState → Prop) (op : δ → HezeRun PUnit)
    (hk : ∀ d, KeepsUncached (op d)) :
    ∀ (l : List δ), (∀ d ∈ l, ∀ s s' : BeaconState, P s →
        (op d).run (pureState s) = .ok ((), pureState s') → P s') →
      ∀ s s' : BeaconState, P s →
        (forIn l PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
          : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s') → P s' := by
  intro l
  induction l with
  | nil =>
    intro _ s s' hs h
    rw [List.forIn_nil] at h
    rw [pureState_inj (run_pure_state_eq _ _ _ _ h)]
    exact hs
  | cons d rest ih =>
    intro hop s s' hs h
    rw [List.forIn_cons] at h
    obtain ⟨step, s1, hb, hr⟩ :=
      run_bind_eq_ok_pure (keepsUncached_bind (hk d) (fun _ => keepsUncached_pure _)) h
    obtain ⟨⟨⟩, s0, hop1, hp⟩ := run_bind_eq_ok_pure (hk d) hb
    injection hp with hp
    injection hp with hstep hs1
    subst hstep
    rw [← pureState_inj hs1] at hr
    exact ih (fun d' hd' => hop d' (List.mem_cons_of_mem _ hd')) s0 s'
      (hop d List.mem_cons_self s s0 hs hop1) hr

/-- `forIn_list_ops_inv` for an array. -/
theorem forIn_array_ops_inv {δ : Type} (P : BeaconState → Prop) (op : δ → HezeRun PUnit)
    (hk : ∀ d, KeepsUncached (op d)) (xs : Array δ)
    (hop : ∀ d ∈ xs, ∀ s s' : BeaconState, P s →
      (op d).run (pureState s) = .ok ((), pureState s') → P s')
    (s s' : BeaconState) (hs : P s)
    (h : (forIn xs PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
      : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s')) : P s' := by
  rw [← Array.forIn_toList] at h
  exact forIn_list_ops_inv P op hk xs.toList (fun d hd => hop d (Array.mem_toList_iff.mp hd))
    s s' hs h

variable [Config] [CryptoBackend]

/-- A proposer slashing that is not at slot `n` by the recorded proposer keeps the
invariant. A clear needs the recorded proposer and the index of `n` with a matching epoch
(`eq_of_tracked_hit`). -/
theorem processProposerSlashing_tracked {bid : ExecutionPayloadBid}
    {p : EthCLSpecs.Heze.ValidatorIndex} (ps : EthCLSpecs.Heze.ProposerSlashing)
    {st st' : BeaconState} (ht : PaymentTracked bid p st)
    (hns : ps.signedHeader1.message.slot ≠ bid.slot ∨
      ps.signedHeader1.message.proposerIndex ≠ p)
    (h : (EthCLSpecs.Heze.processProposerSlashing (StateTransition := HezeRun) ps).run
      (pureState st) = .ok ((), pureState st')) : PaymentTracked bid p st' := by
  obtain ⟨hs, hi⟩ := processProposerSlashing_run_withdrawal ps st st' h
  refine ht.of_frame hs ?_
  rcases hi (trackedIndex bid.slot (pureState st)) with hk | ⟨hp, hidx⟩
  · exact hk
  · exfalso
    have heq := eq_of_tracked_hit ht.slot_ge ht.slot_le hidx
    rw [ht.proposer] at hp
    rcases hns with h1 | h2
    · exact h1 heq
    · exact h2 hp.symm

/-- The operations of a block keep the invariant and the spine, when no proposer slashing
is at slot `n` by the recorded proposer. -/
theorem processOperations_tracked {bid : ExecutionPayloadBid}
    {p : EthCLSpecs.Heze.ValidatorIndex} (body : EthCLSpecs.Heze.BeaconBlockBody)
    {st st' : BeaconState} (ht : PaymentTracked bid p st)
    (hns : ∀ ps ∈ body.proposerSlashings.val, ps.signedHeader1.message.slot ≠ bid.slot ∨
      ps.signedHeader1.message.proposerIndex ≠ p)
    (h : (EthCLSpecs.Heze.processOperations (StateTransition := HezeRun) body).run
      (pureState st) = .ok ((), pureState st')) :
    PaymentTracked bid p st' ∧ spineView (pureState st') = spineView (pureState st) := by
  -- The predicate: the invariant, and the spine of `st`.
  let P : BeaconState → Prop := fun s =>
    PaymentTracked bid p s ∧ spineView (pureState s) = spineView (pureState st)
  have keep : ∀ s s' : BeaconState, P s →
      windowView (pureState s') = windowView (pureState s) → P s' :=
    fun s s' hs hw => ⟨hs.1.of_windowView hw, (congrArg Prod.fst hw).trans hs.2⟩
  unfold EthCLSpecs.Heze.processOperations at h
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun ps _ =>
    keepsUncached_bind (keepsUncached_processProposerSlashing ps)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t1 : P s1 := forIn_array_ops_inv P _ keepsUncached_processProposerSlashing
    body.proposerSlashings.val
    (fun ps hm s s' hs hr => ⟨processProposerSlashing_tracked ps hs.1 (hns ps hm) hr,
      (processProposerSlashing_frame_spine hr).trans hs.2⟩)
    st s1 ⟨ht, rfl⟩ h1
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttesterSlashing a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t2 : P s2 := forIn_array_ops_inv P _ keepsUncached_processAttesterSlashing
    body.attesterSlashings.val
    (fun a _ s s' hs hr => keep s s' hs (processAttesterSlashing_frame hr))
    s1 s2 t1 h2
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t3 : P s3 := forIn_array_ops_inv P _ keepsUncached_processAttestation
    body.attestations.val
    (fun a _ s s' hs hr => by
      obtain ⟨hsp, he⟩ := processAttestation_run_withdrawal a s s' hr
      exact ⟨hs.1.of_frame hsp (he _), hsp.trans hs.2⟩)
    s2 s3 t2 h3
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processVoluntaryExit a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t4 : P s4 := forIn_array_ops_inv P _ keepsUncached_processVoluntaryExit
    body.voluntaryExits.val
    (fun a _ s s' hs hr => keep s s' hs (processVoluntaryExit_frame hr))
    s3 s4 t3 h4
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processBlsToExecutionChange a)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t5 : P s5 := forIn_array_ops_inv P _ keepsUncached_processBlsToExecutionChange
    body.blsToExecutionChanges.val
    (fun a _ s s' hs hr => keep s s' hs (processBlsToExecutionChange_frame hr))
    s4 s5 t4 h5
  -- The last loop, then `pure ()`.
  obtain ⟨⟨⟩, s6, h6, hp⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun a _ =>
    keepsUncached_bind (keepsUncached_processPayloadAttestation a)
      (fun _ => keepsUncached_pure _)) _ _) h
  rw [pureState_inj (run_pure_state_eq _ _ _ _ hp)]
  exact forIn_array_ops_inv P _ keepsUncached_processPayloadAttestation
    body.payloadAttestations.val
    (fun a _ s s' hs hr => keep s s' hs (frame_of_reads (processPayloadAttestation_frame hr)))
    s5 s6 t5 h6

omit [Config] [CryptoBackend] in
/-- At the slot of the bid, the tracked entry is in the upper half. -/
theorem trackedIndex_at_slot {n : Slot} {st : BeaconState} (h : sszGet (pureState st) slot = n) :
    trackedIndex n (pureState st) = builderPaymentIndex n true := by
  unfold trackedIndex
  rw [h, beq_self_eq_true]

/-- `processBlock` of a block after the bid keeps the invariant. The parent payload
settles the cached bid. When the cache holds the bid, the block takes the EMPTY edge and
the state stays. Otherwise the cached bid has a later slot, and the settlement misses the
tracked entry (`eq_of_tracked_hit`). The block's slot is above the header slot, so above
`n`, and the new bid writes another entry (`trackedIndex_ne_bid`). After the block, the
cache holds the new bid, which is not the bid of `n`. -/
theorem processBlock_later_tracked {bid : ExecutionPayloadBid}
    {p : EthCLSpecs.Heze.ValidatorIndex} (b : BeaconBlock) {st st' : BeaconState}
    (ht : PaymentTracked bid p st)
    (hempty : sszGet (pureState st) latestExecutionPayloadBid = bid →
      b.body.signedExecutionPayloadBid.message.parentBlockHash ≠ bid.blockHash)
    (hns : ∀ ps ∈ b.body.proposerSlashings.val, ps.signedHeader1.message.slot ≠ bid.slot ∨
      ps.signedHeader1.message.proposerIndex ≠ p)
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState st)
      = .ok ((), pureState st')) :
    PaymentTracked bid p st' ∧ sszGet (pureState st') latestExecutionPayloadBid ≠ bid := by
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  obtain ⟨⟨⟩, s7, h7, h8⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  -- The parent payload.
  obtain ⟨hsp1, hempty1, hent1⟩ := processParentExecutionPayload_run_withdrawal b st s1 h1
  have t1 : PaymentTracked bid p s1 := by
    by_cases hc : sszGet (pureState st) latestExecutionPayloadBid = bid
    · have e := hempty1 (by rw [hc]; exact hempty hc)
      rw [e]
      exact ht
    · refine ht.of_frame hsp1 ?_
      have hne : (sszGet (pureState st) latestExecutionPayloadBid).slot ≠ bid.slot := by
        intro heq
        rcases ht.cache with h' | ⟨hlt, -⟩
        · exact hc h'
        · rw [heq] at hlt
          exact Nat.lt_irrefl _ hlt
      rcases hent1 (trackedIndex bid.slot (pureState st)) with hk | hbad | hbad
      · exact hk
      · exact absurd (eq_of_tracked_hit ht.slot_ge ht.slot_le (.inl hbad)) hne
      · exact absurd (eq_of_tracked_hit ht.slot_ge ht.slot_le (.inr hbad)) hne
  -- The header.
  obtain ⟨hbs, hgt, -, hsp2, hpay2⟩ := processBlockHeader_run_spine b s1 s2 h2
  simp only [spineView, Prod.mk.injEq] at hsp2
  obtain ⟨hsl2, hh2, hc2⟩ := hsp2
  have hn_lt : bid.slot.toNat < (sszGet (pureState s1) slot).toNat := by
    rw [← hbs]
    exact Nat.lt_of_le_of_lt t1.header_ge (UInt64.lt_iff_toNat_lt.mp hgt)
  have t2 : PaymentTracked bid p s2 := by
    have hj : trackedIndex bid.slot (pureState s2) = trackedIndex bid.slot (pureState s1) := by
      unfold trackedIndex
      rw [hsl2]
    obtain ⟨hw, hpr⟩ := entry_of_payments hpay2 (trackedIndex bid.slot (pureState s1))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsl2]; exact t1.slot_ge
    · rw [hsl2]; exact t1.slot_le
    · rw [hh2, hbs]; exact Nat.le_of_lt hn_lt
    · rw [hj, hw]; exact t1.entry
    · rw [hj, hpr]; exact t1.proposer
    · rw [hc2, hsl2]; exact t1.cache
  -- The withdrawals.
  have w3 := processWithdrawals_frame h3
  have t3 := t2.of_windowView w3
  have hsl3 : sszGet (pureState s3) slot = sszGet (pureState s1) slot :=
    (congrArg (fun w => w.1.1) w3).trans hsl2
  -- The new bid.
  obtain ⟨hbslot, hsp4, hent4, -⟩ := processExecutionPayloadBid_run_payment _ s3 s4 h4
  have hlt3 : bid.slot.toNat < (sszGet (pureState s3) slot).toNat := by
    rw [hsl3]
    exact hn_lt
  have hc4 : sszGet (pureState s4) latestExecutionPayloadBid
      = b.body.signedExecutionPayloadBid.message :=
    congrArg (fun w => w.2.2) hsp4
  have t4 : PaymentTracked bid p s4 := by
    simp only [spineView, Prod.mk.injEq] at hsp4
    obtain ⟨hsl4, hh4, -⟩ := hsp4
    have hj : trackedIndex bid.slot (pureState s4) = trackedIndex bid.slot (pureState s3) := by
      unfold trackedIndex
      rw [hsl4]
    obtain ⟨hw, hpr⟩ := hent4 _ (by rw [hbslot]; exact trackedIndex_ne_bid hlt3)
    refine ⟨?_, ?_, ?_, ?_, ?_, .inr ⟨?_, ?_⟩⟩
    · rw [hsl4]; exact t3.slot_ge
    · rw [hsl4]; exact t3.slot_le
    · rw [hh4]; exact t3.header_ge
    · rw [hj, hw]; exact t3.entry
    · rw [hj, hpr]; exact t3.proposer
    · rw [hc4, hbslot]; exact hlt3
    · rw [hc4, hbslot, hsl4]; exact Nat.le_refl _
  -- The RANDAO mix, the eth1 data, the operations, and the sync aggregate.
  have w5 := processRandao_frame h5
  have w6 := processEth1Data_frame h6
  have t6 := (t4.of_windowView w5).of_windowView w6
  obtain ⟨t7, hsp7⟩ := processOperations_tracked _ t6 hns h7
  have w8 := processSyncAggregate_frame h8
  refine ⟨t7.of_windowView w8, fun heq => ?_⟩
  have hsp : spineView (pureState st') = spineView (pureState s4) :=
    (congrArg Prod.fst w8).trans (hsp7.trans ((congrArg Prod.fst w6).trans (congrArg Prod.fst w5)))
  have hc' : sszGet (pureState st') latestExecutionPayloadBid
      = sszGet (pureState s4) latestExecutionPayloadBid :=
    congrArg (fun w => w.2.2) hsp
  rw [hc', hc4] at heq
  have hs := congrArg (fun x : ExecutionPayloadBid => x.slot.toNat) heq
  simp only at hs
  rw [hbslot] at hs
  rw [hs] at hlt3
  exact Nat.lt_irrefl _ hlt3

/-- `processBlock` of the block of the bid records the payment. The header check makes the
block's proposer the proposer that the bid step reads. The operations after the bid keep
the entry, when no proposer slashing is at the bid's slot by that proposer. -/
theorem processBlock_r_records (b : BeaconBlock) {st st' : BeaconState}
    (hpos : 0 < b.body.signedExecutionPayloadBid.message.value)
    (hns : ∀ ps ∈ b.body.proposerSlashings.val,
      ps.signedHeader1.message.slot ≠ b.body.signedExecutionPayloadBid.message.slot ∨
      ps.signedHeader1.message.proposerIndex ≠ b.proposerIndex)
    (h : (EthCLSpecs.Heze.processBlock (StateTransition := HezeRun) b).run (pureState st)
      = .ok ((), pureState st')) :
    PaymentTracked b.body.signedExecutionPayloadBid.message b.proposerIndex st' := by
  unfold EthCLSpecs.Heze.processBlock at h
  obtain ⟨⟨⟩, s1, -, h⟩ := run_bind_eq_ok_pure (keepsUncached_processParentExecutionPayload _) h
  obtain ⟨⟨⟩, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_processBlockHeader _) h
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok_pure keepsUncached_processWithdrawals h
  obtain ⟨⟨⟩, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_processExecutionPayloadBid _) h
  obtain ⟨⟨⟩, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_processRandao _) h
  obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_processEth1Data _) h
  obtain ⟨⟨⟩, s7, h7, h8⟩ := run_bind_eq_ok_pure (keepsUncached_processOperations _) h
  -- The header fixes the block's slot and proposer.
  obtain ⟨hbs, -, hprop, hsp2, -⟩ := processBlockHeader_run_spine b s1 s2 h2
  have hl2 := processBlockHeader_frame_look h2
  simp only [spineView, Prod.mk.injEq] at hsp2
  obtain ⟨hsl2, hh2, -⟩ := hsp2
  -- The withdrawals keep the slot, the header, and the lookahead.
  have w3 := processWithdrawals_frame h3
  have hl3 := processWithdrawals_frame_look h3
  have hsl3 : sszGet (pureState s3) slot = sszGet (pureState s1) slot :=
    (congrArg (fun w => w.1.1) w3).trans hsl2
  have hh3 : (sszGet (pureState s3) latestBlockHeader).slot = b.slot :=
    (congrArg (fun w => w.1.2.1) w3).trans hh2
  have hprop3 : EthCLSpecs.Heze.getBeaconProposerIndex (pureState s3) = b.proposerIndex :=
    (getBeaconProposerIndex_congr (hl3.trans hl2) hsl3).trans hprop.symm
  -- The bid writes the entry.
  obtain ⟨hbslot, hsp4, -, hval⟩ := processExecutionPayloadBid_run_payment _ s3 s4 h4
  obtain ⟨hw4, hp4⟩ := hval hpos
  simp only [spineView, Prod.mk.injEq] at hsp4
  obtain ⟨hsl4, hh4, hc4⟩ := hsp4
  have hs4 : sszGet (pureState s4) slot = b.body.signedExecutionPayloadBid.message.slot :=
    hsl4.trans hbslot.symm
  have hj := trackedIndex_at_slot hs4
  have t4 : PaymentTracked b.body.signedExecutionPayloadBid.message b.proposerIndex s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, .inl hc4⟩
    · rw [hs4]; exact Nat.le_refl _
    · rw [hs4]; exact le_windowEnd _
    · rw [hh4, hh3, hbs, ← hsl3, ← hbslot]; exact Nat.le_refl _
    · rw [hj]; exact hw4
    · rw [hj, hp4, hprop3]
  have w5 := processRandao_frame h5
  have w6 := processEth1Data_frame h6
  have t6 := (t4.of_windowView w5).of_windowView w6
  obtain ⟨t7, -⟩ := processOperations_tracked _ t6 hns h7
  exact t7.of_windowView (processSyncAggregate_frame h8)

omit [HasherTag] [Config] [CryptoBackend] in
/-- The epoch test of the slot loop as a `Nat` fact, when the slot increment does not wrap. -/
theorem epochTest_iff (a : Slot) (ha : a.toNat + 1 < 2 ^ 64) :
    (((a + 1) % UInt64.ofNat slotsPerEpoch == 0) = true) ↔
      (a.toNat + 1) % slotsPerEpoch = 0 := by
  have hS : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
    UInt64.toNat_ofNat_of_lt slotsPerEpochLt
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_add, UInt64.toNat_one,
    hS, Nat.mod_eq_of_lt ha]
  simp

omit [Config] [CryptoBackend] in
/-- A step that adds one to the slot, keeps the header slot and the cached bid, and moves
the tracked entry with the tracked index keeps the invariant. -/
theorem PaymentTracked.of_slot_succ {bid : ExecutionPayloadBid}
    {p : EthCLSpecs.Heze.ValidatorIndex} {st st' : BeaconState} (ht : PaymentTracked bid p st)
    (hlt : (sszGet (pureState st) slot).toNat < windowEnd bid.slot)
    (hsl : (sszGet (pureState st') slot).toNat = (sszGet (pureState st) slot).toNat + 1)
    (hh : (sszGet (pureState st') latestBlockHeader).slot
      = (sszGet (pureState st) latestBlockHeader).slot)
    (hc : sszGet (pureState st') latestExecutionPayloadBid
      = sszGet (pureState st) latestExecutionPayloadBid)
    (he : withdrawalAt (pureState st') (trackedIndex bid.slot (pureState st'))
        = withdrawalAt (pureState st) (trackedIndex bid.slot (pureState st)) ∧
      proposerAt (pureState st') (trackedIndex bid.slot (pureState st'))
        = proposerAt (pureState st) (trackedIndex bid.slot (pureState st))) :
    PaymentTracked bid p st' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsl]; exact Nat.le_succ_of_le ht.slot_ge
  · rw [hsl]; exact hlt
  · rw [hh]; exact ht.header_ge
  · rw [he.1]; exact ht.entry
  · rw [he.2]; exact ht.proposer
  · rw [hc, hsl]
    rcases ht.cache with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, Nat.le_succ_of_le h2⟩

/-- A slot step below `windowEnd` keeps the invariant. At the last slot of the epoch of
`n`, the epoch transition moves the entry from the upper half to the lower half
(`expectedPaymentWindow_get_lt`), and the slot increment moves the tracked index with it. -/
theorem SlotStep.tracked {bid : ExecutionPayloadBid} {p : EthCLSpecs.Heze.ValidatorIndex}
    {st st' : BeaconState} (ht : PaymentTracked bid p st)
    (hlt : (sszGet (pureState st) slot).toNat < windowEnd bid.slot)
    (hwin : windowEnd bid.slot < 2 ^ 64)
    (h : SlotStep st st') : PaymentTracked bid p st' := by
  have hsp := h.spine
  obtain ⟨st1, st2, h1, h2, hst'⟩ := h
  simp only [spineView, Prod.mk.injEq] at hsp
  obtain ⟨hsl', hh', hc'⟩ := hsp
  have hx1 : (sszGet (pureState st) slot).toNat + 1 < 2 ^ 64 := by omega
  have hslN : (sszGet (pureState st') slot).toNat = (sszGet (pureState st) slot).toNat + 1 := by
    rw [hsl', UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hx1]
  have hpay' : sszGet (pureState st') builderPendingPayments
      = sszGet (pureState st2) builderPendingPayments := by
    rw [hst']
    rfl
  have w1 : windowView (pureState st1) = windowView (pureState st) :=
    processSlot_frame h1
  have hsl1 : sszGet (pureState st1) slot = sszGet (pureState st) slot :=
    congrArg (fun w => w.1.1) w1
  have hp1 : sszGet (pureState st1) builderPendingPayments
      = sszGet (pureState st) builderPendingPayments :=
    congrArg Prod.snd w1
  refine ht.of_slot_succ hlt hslN hh' hc' ?_
  split at h2
  · -- The epoch transition. The slot is the last slot of the epoch of `n`.
    rename_i hc
    rw [hsl1] at hc
    have hb : ((sszGet (pureState st) slot).toNat + 1) % slotsPerEpoch = 0 :=
      (epochTest_iff _ hx1).mp hc
    have hE : (sszGet (pureState st) slot).toNat / slotsPerEpoch
        = bid.slot.toNat / slotsPerEpoch :=
      epoch_at_boundary slotsPerEpochPos ht.slot_ge (lt_of_le_windowEnd hlt) hb
    have hE' : (sszGet (pureState st') slot).toNat / slotsPerEpoch
        = bid.slot.toNat / slotsPerEpoch + 1 := by
      rw [hslN, succ_div_of_mod_eq hb, hE]
    have hj : trackedIndex bid.slot (pureState st) = builderPaymentIndex bid.slot true := by
      unfold trackedIndex
      rw [hE, beq_self_eq_true]
    have hj' : trackedIndex bid.slot (pureState st') = builderPaymentIndex bid.slot false := by
      unfold trackedIndex
      rw [hE', show (bid.slot.toNat / slotsPerEpoch + 1 == bid.slot.toNat / slotsPerEpoch)
        = false from beq_eq_false_iff_ne.mpr (Nat.succ_ne_self _)]
    -- The three parts of `processEpoch`.
    rw [processEpoch_eq] at h2
    obtain ⟨⟨⟩, sa, ha, h2⟩ := run_bind_eq_ok_pure keepsUncached_processEpochPrefix h2
    obtain ⟨⟨⟩, sb, hb2, hc2⟩ :=
      run_bind_eq_ok_pure keepsUncached_processBuilderPendingPayments h2
    have wa : windowView (pureState sa) = windowView (pureState st1) :=
      processEpochPrefix_frame ha
    have wc : windowView (pureState st2) = windowView (pureState sb) :=
      processEpochSuffix_frame hc2
    -- The payment substep shifts the window (`processBuilderPendingPayments_run`).
    -- A fault of the total read would end the run, so the total is a value.
    have hpb : sszGet (pureState sb) builderPendingPayments = expectedPaymentWindow sa := by
      cases htot : EthCLSpecs.Heze.getTotalActiveBalance (pureState sa) with
      | error err =>
        rw [processBuilderPendingPayments_run_total_error sa err htot] at hb2
        cases hb2
      | ok total =>
        -- A fault of the quorum product would end the run too, so the product fits.
        by_cases hq : QuorumFits total
        · obtain ⟨hok, herr⟩ := processBuilderPendingPayments_run sa total htot hq
          by_cases hf : sa.builderPendingWithdrawals.val.size +
              (qualifyingBuilderWithdrawals sa total).length ≤
                EthCLSpecs.Heze.Const.builderPendingWithdrawalsLimit
          · rw [hok ⟨sa.builderPendingWithdrawals.val ++
                (qualifyingBuilderWithdrawals sa total).toArray,
              by simp only [Array.size_append, List.size_toArray]; omega⟩ rfl] at hb2
            injection hb2 with hb2
            injection hb2 with _ hb2
            rw [← pureState_inj hb2]
            rfl
          · rw [herr (Nat.lt_of_not_le hf)] at hb2
            cases hb2
        · rw [processBuilderPendingPayments_run_quorum_error sa total htot hq] at hb2
          cases hb2
    have hidxF : builderPaymentIndex bid.slot false = bid.slot.toNat % slotsPerEpoch := by
      rw [builderPaymentIndex_eq]
      simp
    have hidxT : builderPaymentIndex bid.slot true
        = bid.slot.toNat % slotsPerEpoch + slotsPerEpoch := by
      rw [builderPaymentIndex_eq]
      simp [Nat.add_comm]
    have hv : vget (sszGet (pureState st') builderPendingPayments)
          (builderPaymentIndex bid.slot false)
        = vget (sszGet (pureState st) builderPendingPayments)
          (builderPaymentIndex bid.slot true) := by
      have hp2 : sszGet (pureState st2) builderPendingPayments
          = sszGet (pureState sb) builderPendingPayments :=
        congrArg Prod.snd wc
      have hpa : sa.builderPendingPayments = sszGet (pureState st1) builderPendingPayments :=
        congrArg Prod.snd wa
      rw [hpay', hp2, hpb, hidxF,
        expectedPaymentWindow_get_lt sa _ (Nat.mod_lt _ slotsPerEpochPos), hpa, hp1, ← hidxT]
    rw [hj, hj']
    unfold withdrawalAt proposerAt
    rw [hv]
    exact ⟨rfl, rfl⟩
  · -- No epoch transition: the slot stays in its epoch, and the window stays.
    rename_i hc
    rw [hsl1] at hc
    have hb : ((sszGet (pureState st) slot).toNat + 1) % slotsPerEpoch ≠ 0 :=
      fun h0 => hc ((epochTest_iff _ hx1).mpr h0)
    have hj : trackedIndex bid.slot (pureState st') = trackedIndex bid.slot (pureState st) := by
      unfold trackedIndex
      rw [hslN, succ_div_of_mod_ne hb]
    rw [hj]
    subst h2
    exact entry_of_payments (hpay'.trans hp1) _

/-- The invariant holds at the end of a run that starts in it. The first block of the run
takes the EMPTY edge while the cache holds the bid. After that block, the cache holds a
later bid. -/
theorem ChainRun.paymentTracked (bid : ExecutionPayloadBid) (p : EthCLSpecs.Heze.ValidatorIndex)
    (hwin : windowEnd bid.slot < 2 ^ 64) {steps : List ChainStep} {st st' : BeaconState}
    (h : ChainRun (windowEnd bid.slot) steps st st') :
    PaymentTracked bid p st →
      (sszGet (pureState st) latestExecutionPayloadBid = bid → EmptyChild bid steps) →
      NoSlashingSteps bid.slot p steps → PaymentTracked bid p st' := by
  induction h with
  | nil => exact fun ht _ _ => ht
  | slot hlt hstep _ ih =>
    intro ht hempty hslash
    refine ih (SlotStep.tracked ht hlt hwin hstep) (fun hc => ?_)
      (fun sb v hm => hslash sb v (List.mem_cons_of_mem _ hm))
    -- A slot step keeps the cache, so the first block of the rest is the first block.
    have hcache := congrArg (fun w => w.2.2) hstep.spine
    simp only [spineView] at hcache
    exact hempty (hcache.symm.trans hc)
  | block sb v hstep _ ih =>
    intro ht hempty hslash
    obtain ⟨t, hcne⟩ := processBlock_later_tracked sb.message ht
      (fun hc => hempty hc sb rfl) (hslash sb v List.mem_cons_self) hstep.2.1
    exact ih t (fun hc => absurd hc hcne)
      (fun sb' v' hm => hslash sb' v' (List.mem_cons_of_mem _ hm))

/-- The payment of `r` reaches the substep that judges it. Run `r` from `st0`, then
`steps` to the last slot of the epoch after `r`'s, then `processSlot` and the first eight
epoch substeps. The first block of `steps` takes the EMPTY edge of `r`. No block, `r`
included, has a proposer slashing whose first header has the slot and the proposer of `r`.
Then the state that `processBuilderPendingPayments` reads carries the payment, and it has
the window of the end of the run. -/
theorem bidPaymentCarried_of_run (sbR : SignedBeaconBlock) (v : Bool)
    (steps : List ChainStep) (st0 st1 stEnd stA stJudge : BeaconState)
    (hpos : 0 < sbR.message.body.signedExecutionPayloadBid.message.value)
    (hwin : windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot < 2 ^ 64)
    (hr : BlockStep sbR v st0 st1)
    (hrun : ChainRun (windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot)
      steps st1 stEnd)
    (hend : (sszGet (pureState stEnd) slot).toNat
      = windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot)
    (hempty : EmptyChild sbR.message.body.signedExecutionPayloadBid.message steps)
    (hslashR : NoSlashingAt sbR.message.body.signedExecutionPayloadBid.message.slot
      sbR.message.proposerIndex sbR)
    (hslash : NoSlashingSteps sbR.message.body.signedExecutionPayloadBid.message.slot
      sbR.message.proposerIndex steps)
    (hslot : (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState stEnd)
      = .ok ((), pureState stA))
    (hprefix : processEpochPrefix.run (pureState stA) = .ok ((), pureState stJudge)) :
    BidPaymentCarried stJudge sbR.message.body.signedExecutionPayloadBid.message ∧
      sszGet (pureState stJudge) builderPendingPayments
        = sszGet (pureState stEnd) builderPendingPayments := by
  have t1 : PaymentTracked sbR.message.body.signedExecutionPayloadBid.message
      sbR.message.proposerIndex st1 :=
    processBlock_r_records sbR.message hpos hslashR hr.2.1
  have tEnd := hrun.paymentTracked _ _ hwin t1 (fun _ => hempty) hslash
  -- At the last slot of the window, the tracked entry is in the lower half.
  have hidx : trackedIndex sbR.message.body.signedExecutionPayloadBid.message.slot
        (pureState stEnd)
      = builderPaymentIndex sbR.message.body.signedExecutionPayloadBid.message.slot false := by
    unfold trackedIndex
    rw [hend]
    unfold windowEnd
    rw [windowEnd_div slotsPerEpochPos, show (_ + 1 == _) = false from
      beq_eq_false_iff_ne.mpr (Nat.succ_ne_self _)]
  have hentry := tEnd.entry
  rw [hidx] at hentry
  -- `processSlot` and the eight substeps keep the window.
  have wA : windowView (pureState stA) = windowView (pureState stEnd) :=
    processSlot_frame hslot
  have wJ : windowView (pureState stJudge) = windowView (pureState stA) :=
    processEpochPrefix_frame hprefix
  have hpay : sszGet (pureState stJudge) builderPendingPayments
      = sszGet (pureState stEnd) builderPendingPayments :=
    (congrArg Prod.snd wJ).trans (congrArg Prod.snd wA)
  refine ⟨?_, hpay⟩
  unfold BidPaymentCarried
  show withdrawalAt (pureState stJudge) _ = _
  unfold withdrawalAt
  rw [hpay]
  exact hentry

end

end EthCLSpecs.Proofs.Heze
