import EthCLSpecs.Proofs.Heze.KeepsUncached.Epoch
import EthCLSpecs.Proofs.Heze.PaymentFrame
import EthCLSpecs.Proofs.Heze.PaymentWriters

/-!
# `EthCLSpecs.Proofs.Heze.JustificationAndFinalization`: what the FFG step writes

`process_justification_and_finalization` (altair `beacon-chain.md:671-687`) skips the first
two epochs. After them it passes three balances to `weigh_justification_and_finalization`
(phase0 `beacon-chain.md:1509-1548`): the total active balance and the target balances of
the previous and the current epoch. Heze inherits both. The models are
`Fulu/EpochProcessing.lean:102-111` and `Fulu/EpochProcessing.lean:40-98`.

The weigh step writes four fields. The previous justified checkpoint takes the old current
one. The bits shift by one. A target balance of two thirds or more justifies its epoch: the
step sets its bit and writes the checkpoint of the epoch as the current justified one. Then
four tests on the new bits can finalize one of the two old justified checkpoints. The tests
run in program order, so the last test that passes wins. `finalizeRules` states the four
tests in the opposite order, with the first test that passes winning.

The pyspec forms its products and sums as `uint64` values, and an overflow raises. So the
model forms them through `checkedMul` and `checkedAdd`. On a successful run nothing
overflows, and each test is the same test on the `Nat` values (`quorum_iff`).

`weighJustificationAndFinalization_run_ok` states each of the four fields after a
successful run, and `weighJustificationAndFinalization_run_keeps` states that the step
keeps all other fields. The roots of the new checkpoints are the reads of `getBlockRoot`.
The step reads a root only when the test of its epoch passes, as the spec does. A failed
run fails in one of these reads or in an overflow
(`weighJustificationAndFinalization_run_error`).
`processJustificationAndFinalization_run_eq` reduces the outer step to its five reads and
the weigh step, and `processJustificationAndFinalization_run_ok` states the reads of a
successful run. `finalizeRules_cases` lists the four outcomes of the tests.

## The proof

The `do` blocks of the weigh step compile to join points: two in the run and six in the
pure update. A proof that inlines them copies each continuation into both branches of
its `if`, and the term grows by a factor of 64. So the proof states one fact for each join
point and passes it to the join point that calls it (`view_jp_ite_map`, `jp_map_level`).
The fact for the four fields is a map of the view `ckView`, and the fact for the other
fields is the identity on `restView`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure runPure_eq run_bind except_bind_ok except_bind_error
  run_get_bind_eq_ok run_ite_eq_ok run_bind_eq_ok_pure runPure_of_run_ok
  runPure_iff_run_of_keepsUncached run_liftErr_of_error toNat_mul_of_guard)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState Root Checkpoint Gwei Epoch
  previousEpochOf currentEpochOf weighJustificationAndFinalization
  processJustificationAndFinalization getBlockRoot getTotalActiveBalance getTotalBalance
  getUnslashedParticipatingIndices)
open EthCLSpecs.Heze.Const (justificationBitsLength)

section Rules
variable [Preset]

/-- The four fields that the weigh step writes: the previous justified, the current
justified, and the finalized checkpoint, and the justification bits. -/
abbrev CkView := Checkpoint × Checkpoint × Checkpoint × Bitvector justificationBitsLength

/-- The checkpoint that the four finalization tests write, or the old finalized checkpoint.
The program runs the tests in the opposite order, so the last test that passes there is the
first test that passes here. -/
def finalizeRules (bits : Bitvector justificationBitsLength)
    (oldPrev oldCurr oldFin : Checkpoint) (ce : UInt64) : Checkpoint :=
  if bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == ce then oldCurr
  else if bitGet bits 0 && bitGet bits 1 && bitGet bits 2 && oldCurr.epoch + 2 == ce then oldCurr
  else if bitGet bits 1 && bitGet bits 2 && oldPrev.epoch + 2 == ce then oldPrev
  else if bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && oldPrev.epoch + 3 == ce then oldPrev
  else oldFin

/-- The four outcomes of `finalizeRules`. The result is the old finalized checkpoint, or
one of the two old justified checkpoints with the bits and the epoch distance of its test. -/
theorem finalizeRules_cases (bits : Bitvector justificationBitsLength)
    (oldPrev oldCurr oldFin : Checkpoint) (ce : UInt64) :
    finalizeRules bits oldPrev oldCurr oldFin ce = oldFin ∨
    (finalizeRules bits oldPrev oldCurr oldFin ce = oldCurr ∧ bitGet bits 0 ∧ bitGet bits 1 ∧
      (oldCurr.epoch + 1 = ce ∨ (bitGet bits 2 ∧ oldCurr.epoch + 2 = ce))) ∨
    (finalizeRules bits oldPrev oldCurr oldFin ce = oldPrev ∧ bitGet bits 1 ∧ bitGet bits 2 ∧
      (oldPrev.epoch + 2 = ce ∨ (bitGet bits 3 ∧ oldPrev.epoch + 3 = ce))) := by
  unfold finalizeRules
  repeat' split
  all_goals simp_all

/-- `u x` when `c` holds, else `x`: the change that one `if` of the update makes to the
view. -/
def viewIf (c : Prop) [Decidable c] (u : CkView → CkView) (x : CkView) : CkView :=
  if c then u x else x

/-- The first write: the previous justified checkpoint takes `oc`, the old current one, and
the bits take `bits`, the new bits that the run computed before the update. -/
def firstView (oc : Checkpoint) (bits : Bitvector justificationBitsLength) (x : CkView) :
    CkView :=
  (oc, x.2.1, x.2.2.1, bits)

/-- A justification: the current justified checkpoint takes `ck`. -/
def justifyView (ck : Checkpoint) (x : CkView) : CkView :=
  (x.1, ck, x.2.2.1, x.2.2.2)

/-- A finalization: the finalized checkpoint takes `ck`. -/
def setFinalizedView (ck : Checkpoint) (x : CkView) : CkView :=
  (x.1, x.2.1, ck, x.2.2.2)

/-- The four tests in program order give `finalizeRules`. -/
theorem finalizeSteps_eq (bits : Bitvector justificationBitsLength) (op oc : Checkpoint)
    (ce : UInt64) (x : CkView) :
    viewIf (bitGet bits 0 && bitGet bits 1 && oc.epoch + 1 == ce) (setFinalizedView oc)
      (viewIf (bitGet bits 0 && bitGet bits 1 && bitGet bits 2 && oc.epoch + 2 == ce)
        (setFinalizedView oc)
        (viewIf (bitGet bits 1 && bitGet bits 2 && op.epoch + 2 == ce) (setFinalizedView op)
          (viewIf (bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && op.epoch + 3 == ce)
            (setFinalizedView op) x))) =
      setFinalizedView (finalizeRules bits op oc x.2.2.1 ce) x := by
  unfold finalizeRules
  by_cases hD : (bitGet bits 0 && bitGet bits 1 && oc.epoch + 1 == ce) = true <;>
  by_cases hC : (bitGet bits 0 && bitGet bits 1 && bitGet bits 2 && oc.epoch + 2 == ce) = true <;>
  by_cases hB : (bitGet bits 1 && bitGet bits 2 && op.epoch + 2 == ce) = true <;>
  by_cases hA : (bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && op.epoch + 3 == ce) = true <;>
  simp only [viewIf, setFinalizedView, hA, hB, hC, hD, if_true] <;> rfl

end Rules

section Views
variable [Preset] [HasherTag]

/-- The four fields that the weigh step writes. -/
def ckView (st : State) : CkView :=
  (sszGet st previousJustifiedCheckpoint, sszGet st currentJustifiedCheckpoint,
    sszGet st finalizedCheckpoint, sszGet st justificationBits)

/-- Every other field: the value with the four fields of `ckView` set to `default`. -/
def restView (st : State) : BeaconState :=
  { st.view with
    previousJustifiedCheckpoint := default, currentJustifiedCheckpoint := default,
    finalizedCheckpoint := default, justificationBits := default }

/-- The weigh step keeps `restView`. `weigh_frame` (`FrameInvert.lean`) names its join
points. -/
theorem weighJustificationAndFinalization_frame_rest [Config] [CryptoBackend]
    {t t' : BeaconState} {a : PUnit} {tot prev curr : Gwei}
    (h : (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr).run
      (pureState t) = .ok (a, pureState t')) :
    restView (pureState t') = restView (pureState t) := by
  weigh_frame restView h

/-- `processJustificationAndFinalization` on a plain value: the genesis guard, then the five
reads in `Except`, then the weigh step on the total active balance and the two target
balances. A read that fails ends the run with its error. -/
@[characterizes EthCLSpecs.Heze.processJustificationAndFinalization]
theorem processJustificationAndFinalization_run_eq (v : BeaconState) :
    runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v =
      if currentEpochOf (pureState v) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1 then .ok ((), v)
      else (do
        let prevIdx ← getUnslashedParticipatingIndices (pureState v)
          EthCLSpecs.Heze.Const.timelyTargetFlagIndex (previousEpochOf (pureState v))
        let currIdx ← getUnslashedParticipatingIndices (pureState v)
          EthCLSpecs.Heze.Const.timelyTargetFlagIndex (currentEpochOf (pureState v))
        let tot ← getTotalActiveBalance (pureState v)
        let prev ← getTotalBalance (pureState v) prevIdx
        let curr ← getTotalBalance (pureState v) currIdx
        runPure (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr)
          v) := by
  -- `runPure` runs on `pureState v`, so a leading `get` reads that box.
  have e : ∀ k : State → HezeRun Unit,
      runPure (get >>= k) v = runPure (k (pureState v)) v := fun _ => rfl
  -- A `liftErr` read keeps the box. Its error converts to itself, so the run is the
  -- `Except` bind of the read.
  have l : ∀ {α : Type} (x : Except StateTransitionError α) (k : α → HezeRun Unit),
      runPure (liftErr x >>= k) v = x >>= fun a => runPure (k a) v := by
    intro α x k
    cases x <;> rfl
  unfold processJustificationAndFinalization
  rw [e]
  by_cases hc : currentEpochOf (pureState v) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    simp only [l]

/-- A successful run after the first two epochs. The five reads succeed, and the weigh step
runs on the three balances that they return. -/
theorem processJustificationAndFinalization_run_ok {v w : BeaconState}
    (h : runPure (processJustificationAndFinalization (StateTransition := HezeRun)) v
      = .ok ((), w))
    (hc : ¬ currentEpochOf (pureState v) ≤ EthCLSpecs.Heze.Const.genesisEpoch + 1) :
    ∃ (prevIdx currIdx : Array EthCLSpecs.Heze.ValidatorIndex) (tot prev curr : Gwei),
      getUnslashedParticipatingIndices (pureState v)
        EthCLSpecs.Heze.Const.timelyTargetFlagIndex (previousEpochOf (pureState v))
        = .ok prevIdx ∧
      getUnslashedParticipatingIndices (pureState v)
        EthCLSpecs.Heze.Const.timelyTargetFlagIndex (currentEpochOf (pureState v))
        = .ok currIdx ∧
      getTotalActiveBalance (pureState v) = .ok tot ∧
      getTotalBalance (pureState v) prevIdx = .ok prev ∧
      getTotalBalance (pureState v) currIdx = .ok curr ∧
      runPure (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr) v
        = .ok ((), w) := by
  -- A successful `Except` bind: the first action succeeded, and the rest succeeded on its
  -- value.
  have bind_ok : ∀ {α β : Type} {x : Except StateTransitionError α}
      {f : α → Except StateTransitionError β} {b : β},
      x >>= f = .ok b → ∃ a, x = .ok a ∧ f a = .ok b := by
    intro α β x f b hb
    cases x with
    | error e => cases hb
    | ok a => exact ⟨a, rfl, hb⟩
  rw [processJustificationAndFinalization_run_eq, if_neg hc] at h
  obtain ⟨prevIdx, h1, h⟩ := bind_ok h
  obtain ⟨currIdx, h2, h⟩ := bind_ok h
  obtain ⟨tot, h3, h⟩ := bind_ok h
  obtain ⟨prev, h4, h⟩ := bind_ok h
  obtain ⟨curr, h5, h⟩ := bind_ok h
  exact ⟨prevIdx, currIdx, tot, prev, curr, h1, h2, h3, h4, h5, h⟩

end Views

section Weigh
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- A successful run of `checkedMul a b` and then `k`. The product does not overflow, and
`k` runs on it. -/
theorem run_checkedMul_bind_eq_ok {β : Type} {a b : UInt64} {d : String}
    {k : UInt64 → HezeRun β} {u : BeaconState} {r : β × State}
    (h : ((checkedMul a b d : HezeRun UInt64) >>= k).run (pureState u) = .ok r) :
    ¬ ((a != 0 && a * b / a != b) = true) ∧ (k (a * b)).run (pureState u) = .ok r := by
  unfold checkedMul at h
  split at h
  · unfold throwArithmetic at h
    rw [run_bind, run_liftErr_of_error _ _ rfl, except_bind_error] at h
    cases h
  · exact ⟨‹_›, h⟩

omit [Config] [CryptoBackend] in
/-- A failed run of `checkedMul a b` and then `k`. The product overflows, or `k` fails on it. -/
theorem run_checkedMul_bind_eq_error {β : Type} {a b : UInt64} {d : String}
    {k : UInt64 → HezeRun β} {u : BeaconState} {err : StateTransitionError}
    (h : ((checkedMul a b d : HezeRun UInt64) >>= k).run (pureState u) = .error err) :
    err = .arithmetic d ∨
      (¬ ((a != 0 && a * b / a != b) = true) ∧ (k (a * b)).run (pureState u) = .error err) := by
  unfold checkedMul at h
  split at h
  · unfold throwArithmetic at h
    rw [run_bind, run_liftErr_of_error _ _ rfl, except_bind_error] at h
    injection h with h
    exact .inl h.symm
  · exact .inr ⟨‹_›, h⟩

omit [Config] [CryptoBackend] in
/-- A successful run of `checkedAdd a b` and then `k`. The sum does not overflow, and `k`
runs on it. -/
theorem run_checkedAdd_bind_eq_ok {β : Type} {a b : UInt64} {d : String}
    {k : UInt64 → HezeRun β} {u : BeaconState} {r : β × State}
    (h : ((checkedAdd a b d : HezeRun UInt64) >>= k).run (pureState u) = .ok r) :
    ¬ (a + b < a) ∧ (k (a + b)).run (pureState u) = .ok r := by
  unfold checkedAdd at h
  split at h
  · unfold throwArithmetic at h
    rw [run_bind, run_liftErr_of_error _ _ rfl, except_bind_error] at h
    cases h
  · exact ⟨‹_›, h⟩

omit [Config] [CryptoBackend] in
/-- A failed run of `checkedAdd a b` and then `k`. The sum overflows, or `k` fails on it. -/
theorem run_checkedAdd_bind_eq_error {β : Type} {a b : UInt64} {d : String}
    {k : UInt64 → HezeRun β} {u : BeaconState} {err : StateTransitionError}
    (h : ((checkedAdd a b d : HezeRun UInt64) >>= k).run (pureState u) = .error err) :
    err = .arithmetic d ∨ (k (a + b)).run (pureState u) = .error err := by
  unfold checkedAdd at h
  split at h
  · unfold throwArithmetic at h
    rw [run_bind, run_liftErr_of_error _ _ rfl, except_bind_error] at h
    injection h with h
    exact .inl h.symm
  · exact .inr h

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- The quorum test of the weigh step in `Nat`. When neither checked product overflows,
`p * 3 ≥ t * 2` in `UInt64` is the same test on the `Nat` values. -/
theorem quorum_iff {p t : UInt64} (hp : ¬ ((p != 0 && p * 3 / p != 3) = true))
    (ht : ¬ ((t != 0 && t * 2 / t != 2) = true)) :
    p * 3 ≥ t * 2 ↔ p.toNat * 3 ≥ t.toNat * 2 := by
  rw [ge_iff_le, ge_iff_le, UInt64.le_iff_toNat_le, toNat_mul_of_guard _ _ hp,
    toNat_mul_of_guard _ _ ht]
  all_goals rfl

/-- A successful run of a join point that reads a root: `getBlockRoot` and then `J` when `c` holds,
else `J` on the default root. The read keeps the state. The run of `J` gets a root `rt`, and
`rt` is the result of the read when `c` holds. -/
theorem run_blockRoot_jp_eq_ok {β : Type} {c : Prop} [Decidable c] {v : BeaconState}
    {e : Epoch} {J : Root → HezeRun β} {r : β × State}
    (h : (if c then getBlockRoot (StateTransition := HezeRun) (pureState v) e >>= J
      else pure default >>= J).run (pureState v) = .ok r) :
    ∃ rt : Root, (c → runPure (getBlockRoot (StateTransition := HezeRun) (pureState v) e) v
      = .ok (rt, v)) ∧ (J rt).run (pureState v) = .ok r := by
  rcases run_ite_eq_ok h with ⟨_, h⟩ | ⟨hc, h⟩
  · obtain ⟨rt, w, h1, h2⟩ := run_bind_eq_ok_pure (keepsUncached_getBlockRoot _ _) h
    have e : (pureState w).view = (pureState v).view := by frame_invert h1
    change w = v at e
    subst e
    exact ⟨rt, fun _ => runPure_of_run_ok h1, h2⟩
  · exact ⟨default, fun h' => absurd h' hc, h⟩

/-- A failed run of a join point that reads a root. When `c` holds, the read fails with the
same error, or the read keeps the state and `J` fails on the root it read. When `c` does not
hold, `J` fails on the default root. -/
theorem run_blockRoot_jp_eq_error {β : Type} {c : Prop} [Decidable c] {v : BeaconState}
    {e : Epoch} {J : Root → HezeRun β} {err : StateTransitionError}
    (h : (if c then getBlockRoot (StateTransition := HezeRun) (pureState v) e >>= J
      else pure default >>= J).run (pureState v) = .error err) :
    (c ∧ runPure (getBlockRoot (StateTransition := HezeRun) (pureState v) e) v = .error err) ∨
      ∃ rt : Root, (J rt).run (pureState v) = .error err := by
  by_cases hc : c
  · rw [if_pos hc, run_bind] at h
    cases hx : (getBlockRoot (StateTransition := HezeRun) (pureState v) e).run (pureState v) with
    | error e' =>
      rw [hx] at h
      cases h
      exact .inl ⟨hc, by rw [runPure_eq, hx]; rfl⟩
    | ok p =>
      obtain ⟨a, s⟩ := p
      rw [hx, except_bind_ok] at h
      have hs := keepsUncached_getBlockRoot v e v a s hx
      rw [hs] at hx h
      have ev : (pureState s.view).view = (pureState v).view := by frame_invert hx
      change s.view = v at ev
      rw [ev] at h
      exact .inr ⟨a, h⟩
  · rw [if_neg hc] at h
    exact .inr ⟨default, h⟩

/-- The weigh step on a plain value. The previous justified checkpoint takes the old current
one. The current one takes the checkpoint of the current epoch when that test passes, else
the checkpoint of the previous epoch when that test passes, else it stays. The bits shift by
one and get the bit of each test that passes. The finalized checkpoint follows
`finalizeRules` on the new bits. `pr` and `cr` are the results of the two `getBlockRoot`
reads. -/
@[characterizes EthCLSpecs.Heze.weighJustificationAndFinalization]
theorem weighJustificationAndFinalization_run_ok (v w : BeaconState) (tot prev curr : Gwei)
    (h : runPure (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr) v
      = .ok ((), w)) :
    ∃ pr cr : Root,
      let jp := decide (prev.toNat * 3 ≥ tot.toNat * 2)
      let jc := decide (curr.toNat * 3 ≥ tot.toNat * 2)
      let bits1 : Bitvector justificationBitsLength :=
        { data := v.justificationBits.data <<< 1 }
      let bits2 := if jp then bitSet bits1 1 true else bits1
      let bits3 := if jc then bitSet bits2 0 true else bits2
      w.previousJustifiedCheckpoint = v.currentJustifiedCheckpoint ∧
      w.currentJustifiedCheckpoint =
        (if jc then { epoch := currentEpochOf (pureState v), root := cr }
         else if jp then { epoch := previousEpochOf (pureState v), root := pr }
         else v.currentJustifiedCheckpoint) ∧
      w.justificationBits = bits3 ∧
      w.finalizedCheckpoint = finalizeRules bits3 v.previousJustifiedCheckpoint
        v.currentJustifiedCheckpoint v.finalizedCheckpoint (currentEpochOf (pureState v)) ∧
      (jp = true → runPure (getBlockRoot (StateTransition := HezeRun)
        (pureState v) (previousEpochOf (pureState v))) v = .ok (pr, v)) ∧
      (jc = true → runPure (getBlockRoot (StateTransition := HezeRun)
        (pureState v) (currentEpochOf (pureState v))) v = .ok (cr, v)) := by
  rw [runPure_iff_run_of_keepsUncached (keepsUncached_weighJustificationAndFinalization _ _ _)]
    at h
  -- The run: the read of the state, the two checked products and the root read of each
  -- epoch, the four finalization tests, then the update.
  unfold weighJustificationAndFinalization at h
  have h := run_get_bind_eq_ok _ _ _ h
  extract_lets prevEpoch currEpoch oldPrev oldCurr shifted linkEpoch jpPure at h
  obtain ⟨hpw, h⟩ := run_checkedMul_bind_eq_ok h
  obtain ⟨hpq, h⟩ := run_checkedMul_bind_eq_ok h
  extract_lets justifyPrev afterPrev jp at h
  obtain ⟨pr, hpr, h⟩ := run_blockRoot_jp_eq_ok h
  simp -zeta only [jp] at h
  obtain ⟨hcw, h⟩ := run_checkedMul_bind_eq_ok h
  obtain ⟨hcq, h⟩ := run_checkedMul_bind_eq_ok h
  extract_lets justifyCurr bits jp2 at h
  obtain ⟨cr, hcr, h⟩ := run_blockRoot_jp_eq_ok h
  simp -zeta only [jp2] at h
  -- A test whose bits hold forms its epoch sum, and a successful run has no overflow there.
  -- So each test returns the `Bool` that `finalizeRules` reads.
  have hl : ∀ (b : Bool) (src k : UInt64) (d : String) (K : Bool → HezeRun Unit)
      (r : Unit × State), (linkEpoch b src k d >>= K).run (pureState v) = .ok r →
      (K (b && src + k == currEpoch)).run (pureState v) = .ok r := by
    intro b src k d K r hb
    cases b
    · exact hb
    · have hb' : (((checkedAdd src k d : HezeRun UInt64) >>= fun x => pure (x == currEpoch))
          >>= K).run (pureState v) = .ok r := hb
      rw [bind_assoc] at hb'
      exact (run_checkedAdd_bind_eq_ok hb').2
  have h := hl _ _ _ _ _ _ h
  have h := hl _ _ _ _ _ _ h
  have h := hl _ _ _ _ _ _ h
  have h := hl _ _ _ _ _ _ h
  have hw := modifyState_run_eq h
  clear h
  -- The update: `s1` writes the previous justified checkpoint and the bits, `s2` justifies
  -- the previous epoch, `jc` justifies the current one, and `j1` to `j4` run the four
  -- finalization writes.
  extract_lets _ _ s1 j4 j3 j2 j1 jc _ s2 at hw
  have hPure : ∀ s y, ckView (jpPure s y) = id (ckView s) := fun _ _ => rfl
  have h4 : ∀ s y, ckView (j4 s y) =
      viewIf (bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == currEpoch)
        (setFinalizedView oldCurr) (ckView s) := by
    jp_map_level j4 hPure id
  have h3 : ∀ s y, ckView (j3 s y) =
      viewIf (bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == currEpoch)
        (setFinalizedView oldCurr)
        (viewIf (bitGet bits 0 && bitGet bits 1 && bitGet bits 2 &&
            oldCurr.epoch + 2 == currEpoch)
          (setFinalizedView oldCurr) (ckView s)) := by
    jp_map_level j3 h4
      (viewIf (bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == currEpoch)
        (setFinalizedView oldCurr))
  -- `G3` is the change that `j3` makes after its own test.
  let G3 := fun x =>
    viewIf (bitGet bits 0 && bitGet bits 1 && oldCurr.epoch + 1 == currEpoch)
      (setFinalizedView oldCurr)
      (viewIf (bitGet bits 0 && bitGet bits 1 && bitGet bits 2 && oldCurr.epoch + 2 == currEpoch)
        (setFinalizedView oldCurr) x)
  have h2 : ∀ s y, ckView (j2 s y) =
      G3 (viewIf (bitGet bits 1 && bitGet bits 2 && oldPrev.epoch + 2 == currEpoch)
        (setFinalizedView oldPrev) (ckView s)) := by
    jp_map_level j2 h3 G3
  -- `G2` adds the test of `j2`, and `G1` adds the test of `j1`.
  let G2 := fun x => G3 (viewIf (bitGet bits 1 && bitGet bits 2 && oldPrev.epoch + 2 == currEpoch)
    (setFinalizedView oldPrev) x)
  have h1 : ∀ s y, ckView (j1 s y) =
      G2 (viewIf (bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && oldPrev.epoch + 3 == currEpoch)
        (setFinalizedView oldPrev) (ckView s)) := by
    jp_map_level j1 h2 G2
  let G1 := fun x => G2 (viewIf
    (bitGet bits 1 && bitGet bits 2 && bitGet bits 3 && oldPrev.epoch + 3 == currEpoch)
    (setFinalizedView oldPrev) x)
  have hG : ∀ x, G1 x = setFinalizedView (finalizeRules bits oldPrev oldCurr x.2.2.1 currEpoch) x :=
    fun x => finalizeSteps_eq bits oldPrev oldCurr currEpoch x
  have hc : ∀ s y, ckView (jc s y) =
      G1 (viewIf justifyCurr (justifyView { epoch := currEpoch, root := cr }) (ckView s)) := by
    jp_map_level jc h1 G1
  -- Without the named arguments, the unification of the outer `if` runs out of heartbeats.
  have hv : ckView (pureState w) = G1
      (viewIf justifyCurr (justifyView { epoch := currEpoch, root := cr })
        (if justifyPrev then ckView s2 else ckView s1)) := by
    rw [hw]
    dsimp only [Id.run]
    exact view_jp_ite_map (c := justifyPrev) (J := jc) (a := s2) (b := s1) ckView
      (fun x => G1 (viewIf justifyCurr (justifyView { epoch := currEpoch, root := cr }) x)) hc
  have e2 : ckView s2 = justifyView { epoch := prevEpoch, root := pr } (ckView s1) := by
    dsimp -zeta +zetaDelta only
    with_unfolding_all rfl
  have e1 : ckView s1 = firstView oldCurr bits (ckView (pureState v)) := by
    dsimp -zeta +zetaDelta only
    with_unfolding_all rfl
  rw [e2, e1, hG] at hv
  -- The fields: one case for each pair of test outcomes. The tests compare checked
  -- products that did not overflow, so they are the tests on the `Nat` values.
  refine ⟨pr, cr, ?_⟩
  dsimp only
  dsimp -zeta +zetaDelta only at hv hpr hcr
  simp only [quorum_iff hpw hpq, quorum_iff hcw hcq] at hv hpr hcr
  refine ⟨?_, ?_, ?_, ?_, fun hj => hpr (of_decide_eq_true hj),
    fun hj => hcr (of_decide_eq_true hj)⟩ <;>
  by_cases hjp : UInt64.toNat prev * 3 ≥ UInt64.toNat tot * 2 <;>
  by_cases hjc : UInt64.toNat curr * 3 ≥ UInt64.toNat tot * 2 <;>
  simp only [hjp, hjc, decide_true, decide_false, if_true, if_false, viewIf,
    setFinalizedView, justifyView, firstView, ckView, Prod.mk.injEq, Bool.false_eq_true]
    at hv ⊢ <;>
  first | exact hv.1 | exact hv.2.1 | exact hv.2.2.2 | exact hv.2.2.1

/-- The weigh step keeps every field other than the four of `ckView`. -/
theorem weighJustificationAndFinalization_run_keeps (v w : BeaconState) (tot prev curr : Gwei)
    (h : runPure (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr) v
      = .ok ((), w)) :
    { w with previousJustifiedCheckpoint := v.previousJustifiedCheckpoint,
             currentJustifiedCheckpoint := v.currentJustifiedCheckpoint,
             finalizedCheckpoint := v.finalizedCheckpoint,
             justificationBits := v.justificationBits } = v := by
  rw [runPure_iff_run_of_keepsUncached (keepsUncached_weighJustificationAndFinalization _ _ _)]
    at h
  have hr := weighJustificationAndFinalization_frame_rest h
  -- Put the four fields of `v` back on both sides of `restView w = restView v`.
  exact congrArg (fun x : BeaconState => { x with
    previousJustifiedCheckpoint := v.previousJustifiedCheckpoint,
    currentJustifiedCheckpoint := v.currentJustifiedCheckpoint,
    finalizedCheckpoint := v.finalizedCheckpoint,
    justificationBits := v.justificationBits }) hr

/-- A failed run of the weigh step fails in a `getBlockRoot` read or in checked arithmetic.
In the first case, the step read the root of an epoch whose target balance reaches two
thirds, and that read fails with the same error. In the second case, a product of a quorum
test or the epoch sum of a finalization test overflows. The update after the reads does not
fail. -/
theorem weighJustificationAndFinalization_run_error (v : BeaconState) (tot prev curr : Gwei)
    {err : StateTransitionError}
    (h : runPure (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr) v
      = .error err) :
    (prev.toNat * 3 ≥ tot.toNat * 2 ∧ runPure (getBlockRoot (StateTransition := HezeRun)
      (pureState v) (previousEpochOf (pureState v))) v = .error err) ∨
    (curr.toNat * 3 ≥ tot.toNat * 2 ∧ runPure (getBlockRoot (StateTransition := HezeRun)
      (pureState v) (currentEpochOf (pureState v))) v = .error err) ∨
    ∃ d, err = .arithmetic d := by
  -- `runPure` maps the result of the run, so the run fails with the same error.
  have hr : (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr).run
      (pureState v) = .error err := by
    rw [runPure_eq] at h
    cases hx : (weighJustificationAndFinalization (StateTransition := HezeRun) tot prev curr).run
      (pureState v) with
    | error e' =>
      rw [hx] at h
      cases h
      rfl
    | ok p =>
      rw [hx] at h
      cases h
  unfold weighJustificationAndFinalization at hr
  -- A leading `get` reads the start box, for a run that fails as for one that succeeds.
  have hg : ∀ (k : State → HezeRun Unit) (s : State),
      ((get : HezeRun State) >>= k).run s = .error err → (k s).run s = .error err :=
    fun _ _ h => h
  have hr := hg _ _ hr
  extract_lets prevEpoch currEpoch oldPrev oldCurr shifted linkEpoch jpPure at hr
  rcases run_checkedMul_bind_eq_error hr with he | ⟨hpw, hr⟩
  · exact .inr (.inr ⟨_, he⟩)
  rcases run_checkedMul_bind_eq_error hr with he | ⟨hpq, hr⟩
  · exact .inr (.inr ⟨_, he⟩)
  extract_lets justifyPrev afterPrev jp at hr
  rcases run_blockRoot_jp_eq_error hr with hp | ⟨pr, hr⟩
  · exact .inl ⟨(quorum_iff hpw hpq).mp hp.1, hp.2⟩
  simp -zeta only [jp] at hr
  rcases run_checkedMul_bind_eq_error hr with he | ⟨hcw, hr⟩
  · exact .inr (.inr ⟨_, he⟩)
  rcases run_checkedMul_bind_eq_error hr with he | ⟨hcq, hr⟩
  · exact .inr (.inr ⟨_, he⟩)
  extract_lets justifyCurr bits jp2 at hr
  rcases run_blockRoot_jp_eq_error hr with hc | ⟨cr, hr⟩
  · exact .inr (.inl ⟨(quorum_iff hcw hcq).mp hc.1, hc.2⟩)
  simp -zeta only [jp2] at hr
  -- A finalization test fails only when its epoch sum overflows.
  have hl : ∀ (b : Bool) (src k : UInt64) (d : String) (K : Bool → HezeRun Unit),
      (linkEpoch b src k d >>= K).run (pureState v) = .error err →
      (∃ d', err = .arithmetic d') ∨ (K (b && src + k == currEpoch)).run (pureState v) = .error err := by
    intro b src k d K hb
    cases b
    · exact .inr hb
    · have hb' : (((checkedAdd src k d : HezeRun UInt64) >>= fun x => pure (x == currEpoch))
          >>= K).run (pureState v) = .error err := hb
      rw [bind_assoc] at hb'
      rcases run_checkedAdd_bind_eq_error hb' with he | hb'
      · exact .inl ⟨_, he⟩
      · exact .inr hb'
  rcases hl _ _ _ _ _ hr with he | hr
  · exact .inr (.inr he)
  rcases hl _ _ _ _ _ hr with he | hr
  · exact .inr (.inr he)
  rcases hl _ _ _ _ _ hr with he | hr
  · exact .inr (.inr he)
  rcases hl _ _ _ _ _ hr with he | hr
  · exact .inr (.inr he)
  -- What is left is the `modifyState` of the update, which does not fail.
  cases hr

end Weigh

end EthCLSpecs.Proofs.Heze
