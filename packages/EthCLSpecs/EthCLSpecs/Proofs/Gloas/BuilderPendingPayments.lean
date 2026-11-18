import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.ProgressiveListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:357-374`)
modifies two fields sequentially within one state transition. This file characterizes the
whole transition as one value: the run on `pureState preState` returns `pureState` of
`preState` with `builderPendingWithdrawals` and `builderPendingPayments` written, and
nothing else. When
invoked by the epoch substep, it feeds every qualifying previous-epoch payment's
withdrawal, in slot order, through `ProgressiveList.push`, which always appends. It then
shifts the payment window down by `SLOTS_PER_EPOCH`, padding the vacated half with empties.

The withdrawals side rests on `progressiveListFoldlPush_val`
(`SizzLean.Proofs.ProgressiveListPush`): iterating `push` over a list of values ends at
the original list plus every value, in order. Alpha.12 dropped
`BUILDER_PENDING_WITHDRAWALS_LIMIT`, so there is no capacity clamp to assume.

The window side is a direct instance of `shiftWindow`'s general behavior:
`expectedPaymentWindow_get_lt` / `expectedPaymentWindow_get_upper` state the two
index-region facts (old upper half moves down; new upper half is empty).
`processBuilderPendingPayments` reads `builderPendingPayments` once, before the
withdrawals loop runs, and the loop never writes that field, so the window
transformation's input is unaffected by whatever the withdrawals loop did.

Statements bind plain `BeaconState` values and never bind a boxed `State`. The contract
`processBuilderPendingPayments_run` states the run at the box, in `.run` form, because
that is the shape the fork-choice bridge consumes; the readings state the `runPure` form,
which `runPure_of_run_ok` derives from the contract.

This file proves only the local before/after behavior of one call, for an arbitrary
input value. It does not prove protocol-wide exactly-once settlement, and says nothing
about how this substep's effect interacts with `settleBuilderPayment` or
`processProposerSlashing`, the other paths that clear a `BuilderPendingPayment` before
this substep ever runs.

See `EthCLSpecs/docs/PROOF_LEDGER.md`, Gloas "Safety and invariant preservation".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure runPure_eq runPure_of_run_ok run_bind run_pure
  except_bind_ok except_bind_error bind_ok_iff mul_eq_ok div_eq_ok runSum
  foldlM_add_ok_iff foldlM_add_value max_value)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas (Preset Gwei BeaconState)
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochDiv builderPaymentThresholdNumerator
  builderPaymentThresholdDenominator)
open SizzLean.Proofs (progressiveListFoldlPush_val view_uncachedBox)

/-- `do x` for a lone `for`-loop `x` elaborates as `x >>= fun _ => pure ()`, not as `x`
itself. Peels that wrapper so a fact about the bare loop run connects to a use site that
runs the bare `forIn` before more code: the wrapper succeeds with the same post-state, and
discards the loop's own value. -/
private theorem run_of_run_seq_pure {ε σ β : Type} (x : StateT σ (Except ε) β) (s0 s1 : σ)
    (h : (x >>= fun _ => (pure () : StateT σ (Except ε) Unit)).run s0 = .ok ((), s1)) :
    ∃ a : β, x.run s0 = .ok (a, s1) := by
  rw [run_bind] at h
  cases hx : x.run s0 with
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [hx] at h
    rw [except_bind_ok, run_pure] at h
    have h2 : s = s1 := congrArg Prod.snd (Except.ok.inj h)
    subst h2
    exact ⟨a, rfl⟩
  | error e =>
    rw [hx, except_bind_error] at h
    cases h

/-! ## The withdrawals loop

`builderPendingWithdrawalsLoop_run_eq` is the loop's whole-transition equation: the
conditional `appendState` loop always succeeds, and its effect reduces to a pure
`ProgressiveList.push` fold over the qualifying indices
(`progressiveListFoldlPush_val`). `builderPendingPayments` is untouched, which the
record-update form states by leaving it out. `cond` is a `Prop` with a `Decidable`
instance, matching the production `p.weight ≥ quorum` guard. -/

/-- The loop's whole-transition equation over an arbitrary index list. Stated at the box
level, on `pureState preState`, so the composite contract below rewrites with it directly. -/
private theorem builderPendingWithdrawalsList_run_eq [Preset] [HasherTag]
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (preState : BeaconState) (l : List Nat) :
    (do for i in l do
          if cond i then
            appendState builderPendingWithdrawals (val i)
        : GloasRun Unit).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals :=
            ((l.filter fun i => decide (cond i)).map val).foldl
              (fun l w => l.push w) preState.builderPendingWithdrawals }) := by
  induction l generalizing preState with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : cond i
    · have hstep : (appendState builderPendingWithdrawals (val i) : GloasRun Unit).run
            (pureState preState)
          = .ok ((), pureState { preState with builderPendingWithdrawals :=
            preState.builderPendingWithdrawals.push (val i) }) := rfl
      have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = i :: List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_pos]; simpa using h
      simp only [List.forIn_cons, run_bind, ite_eq_left h, hstep, except_bind_ok, run_pure]
      rw [hfilter, List.map_cons, List.foldl_cons]
      exact ih { preState with builderPendingWithdrawals :=
        preState.builderPendingWithdrawals.push (val i) }
    · have hfilter : (List.filter (fun i => decide (cond i)) (i :: rest))
          = List.filter (fun i => decide (cond i)) rest := by
        rw [List.filter_cons_of_neg]; simpa using h
      simp only [List.forIn_cons, run_bind, ite_eq_right h, run_pure, except_bind_ok]
      rw [hfilter]
      exact ih preState

/-- `processBuilderPendingPayments`'s withdrawals loop over `[0:n]`, the source's own
range: the list equation above at `List.range n`. -/
private theorem builderPendingWithdrawalsLoop_run_eq [Preset] [HasherTag] (n : Nat)
    (cond : Nat → Prop) [DecidablePred cond]
    (val : Nat → BuilderPendingWithdrawal) (preState : BeaconState) :
    (do for i in [0:n] do
          if cond i then
            appendState builderPendingWithdrawals (val i)
        : GloasRun Unit).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals :=
            (((List.range n).filter fun i => decide (cond i)).map val).foldl
              (fun l w => l.push w) preState.builderPendingWithdrawals }) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact builderPendingWithdrawalsList_run_eq cond val preState (List.range n)

/-! ## The named values the transition produces

`builderPaymentQuorum`, `qualifyingBuilderWithdrawals`, `expectedWithdrawals`, and
`expectedPaymentWindow` name the four values in `processBuilderPendingPayments_run`'s
conclusion, over plain `BeaconState` values. A spec accessor that takes the boxed `State`
reads `pureState state`, so the names stay free of any box of their own. -/

/-- `processBuilderPendingPayments`'s quorum threshold: the body's own
`getBuilderPaymentQuorumThreshold` at the plain state, named so the contract and
the two value definitions below share it. The chain is the checked `Gwei`
surface, so the threshold itself is a `Checked` value: at the migrated surface a
fault here rejects the substep exactly where the pyspec raises. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : BeaconState) : Checked Gwei :=
  getBuilderPaymentQuorumThreshold (pureState state)

/-- The effective balances `getTotalActiveBalance` folds, over plain state
values: the active set at the state's own slot, each member's
`effectiveBalance`. -/
def activeEffectiveBalances [Preset] [HasherTag] (state : BeaconState) : List Gwei :=
  (getActiveValidatorIndices (pureState state)
      (computeEpochAtSlot state.slot)).toList.map
    (fun i => state.validators[i.toNat]!.effectiveBalance)

/-- The plain `Nat` the quorum chain divides: the fold's final running sum,
floored at one increment (`get_total_balance`'s `max`). -/
def quorumTotal [Preset] [HasherTag] (state : BeaconState) : Nat :=
  max (runSum 0 (activeEffectiveBalances state)
      (activeEffectiveBalances state).length)
    Gloas.Const.effectiveBalanceIncrementG.toPlainNat

/-- `getTotalActiveBalance`'s fused reading: the accessor succeeds with `tab`
exactly when every running sum of `activeEffectiveBalances` stays in range
(the checked fold's own obligation), and then `tab` is the fold's final running
sum floored at one increment. This is the real arithmetic obligation the
quorum chain's first bind names. Laws: `bind_ok_iff` (the one bind),
`foldlM_add_ok_iff`, `foldlM_add_value`, `max_value`, over the `Array`-to-`List`
fold route and the mapped list. -/
theorem getTotalActiveBalance_eq_ok [Preset] [HasherTag] (state : BeaconState) (tab : Gwei) :
    getTotalActiveBalance (pureState state) = .ok tab ↔
      (∀ i ≤ (activeEffectiveBalances state).length,
          runSum 0 (activeEffectiveBalances state) i < UInt64.size) ∧
      tab.toPlainNat = max (runSum 0 (activeEffectiveBalances state)
          (activeEffectiveBalances state).length)
        Gloas.Const.effectiveBalanceIncrementG.toPlainNat := by
  unfold getTotalActiveBalance getTotalBalance activeEffectiveBalances
  simp only [view_uncachedBox]
  -- The fold runs over the active indices; route it through the mapped list
  -- the checked-fold laws are stated on.
  rw [← Array.foldlM_toList, ← List.foldlM_map]
  constructor
  · rw [bind_ok_iff]
    rintro ⟨c, hfold, hret⟩
    have hmaxc : max c Gloas.Const.effectiveBalanceIncrementG = tab :=
      Except.ok.inj hret
    have hval1 : tab.toPlainNat
        = max c.toPlainNat Gloas.Const.effectiveBalanceIncrementG.toPlainNat := by
      rw [← hmaxc, max_value]
    have hval2 : c.toPlainNat
        = runSum 0 (activeEffectiveBalances state)
            (activeEffectiveBalances state).length :=
      foldlM_add_value 0 _ _ hfold
    refine ⟨foldlM_add_ok_iff 0 _ |>.mp ⟨c, hfold⟩, ?_⟩
    rw [hval1]
    show max c.toPlainNat Gloas.Const.effectiveBalanceIncrementG.toPlainNat
      = max (runSum 0 (activeEffectiveBalances state)
          (activeEffectiveBalances state).length)
        Gloas.Const.effectiveBalanceIncrementG.toPlainNat
    rw [hval2]
  · rintro ⟨hbounds, hval⟩
    obtain ⟨c, hfold⟩ := foldlM_add_ok_iff 0 _ |>.mpr hbounds
    rw [bind_ok_iff]
    refine ⟨c, hfold, ?_⟩
    show (Except.ok (max c Gloas.Const.effectiveBalanceIncrementG) : Checked Gwei)
      = Except.ok tab
    refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
    show (max c Gloas.Const.effectiveBalanceIncrementG).toPlainNat = tab.toPlainNat
    rw [max_value, hval, ← foldlM_add_value 0 _ _ hfold]

/-- The quorum chain's fused reading: the threshold is the checked `Gwei` chain
`total // slotsPerEpoch * numerator // denominator`, with the per-slot division the
proved-total route, so the chain succeeds with `quorum` exactly when every
running sum of the active validators' effective balances stays in range, the
scaling product stays in range, and the denominator is nonzero; the value reads
back as that plain chain. This is the real arithmetic obligation the contract's
`.ok quorum` hypothesis names. The denominator is the literal `10`, so its zero
test discharges in the kernel. Laws: `getTotalActiveBalance_eq_ok` (hence
`foldlM_add_ok_iff`, `foldlM_add_value`, `max_value`), `bind_ok_iff` (twice, one
per bind), `mul_eq_ok`, `div_eq_ok`, and the proved-total route's
`divPos_toPlainNat`. -/
theorem builderPaymentQuorum_eq_ok [Preset] [HasherTag] (state : BeaconState) (quorum : Gwei) :
    builderPaymentQuorum state = .ok quorum ↔
      (∀ i ≤ (activeEffectiveBalances state).length,
          runSum 0 (activeEffectiveBalances state) i < UInt64.size) ∧
      ∃ scaled : Gwei,
        scaled.toPlainNat = quorumTotal state / slotsPerEpoch
            * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat ∧
        quorumTotal state / slotsPerEpoch
            * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat < UInt64.size ∧
        Gloas.Const.builderPaymentThresholdDenominator.toPlainNat ≠ 0 ∧
        quorum.toPlainNat = scaled.toPlainNat
            / Gloas.Const.builderPaymentThresholdDenominator.toPlainNat := by
  constructor
  · intro h
    rw [show builderPaymentQuorum state
        = (getBuilderPaymentQuorumThreshold (pureState state) : Checked Gwei) from rfl] at h
    simp only [getBuilderPaymentQuorumThreshold] at h
    -- Two binds, one per `←` in the body; `bind_ok_iff` exposes each, and the
    -- operator laws read the two checked steps on the plain values.
    rw [bind_ok_iff] at h
    obtain ⟨tab, hTAB, hrest⟩ := h
    rw [bind_ok_iff] at hrest
    obtain ⟨scaled, hmul, hdiv⟩ := hrest
    have hden := (div_eq_ok _ _ _ |>.mp hdiv).1
    have hval := (div_eq_ok _ _ _ |>.mp hdiv).2
    have hmulr := mul_eq_ok _ _ _ |>.mp hmul
    have htab := (getTotalActiveBalance_eq_ok state tab).mp hTAB
    -- `quorumTotal` is the floored running sum `htab.2` names, and the
    -- proved-total division reads back as the plain quotient, so the product's
    -- range fact and value land on the statement's plain terms.
    have hqt : quorumTotal state = tab.toPlainNat := by
      show max (runSum 0 (activeEffectiveBalances state)
          (activeEffectiveBalances state).length)
        Gloas.Const.effectiveBalanceIncrementG.toPlainNat = tab.toPlainNat
      rw [htab.2]
    have hps : (tab / Const.slotsPerEpochDiv).toPlainNat
        = quorumTotal state / slotsPerEpoch := by
      rw [show (tab / Const.slotsPerEpochDiv).toPlainNat
          = tab.toPlainNat / slotsPerEpoch from
            CLUint64.divPos_toPlainNat tab Const.slotsPerEpochDiv, hqt]
    have hrange'' : quorumTotal state / slotsPerEpoch
        * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat < UInt64.size := by
      rw [← hps]
      exact hmulr.1
    refine ⟨htab.1, scaled, ?_, hrange'', hden, hval⟩
    rw [hmulr.2, hps]
  · rintro ⟨hfold, scaled, hscaled, hrange, hden, hval⟩
    -- The total the laws name: the fold's final running sum, floored at one
    -- increment, is in range, so a bound `Gwei` carries it.
    have hinc : Gloas.Const.effectiveBalanceIncrementG.toPlainNat < UInt64.size :=
      UInt64.toNat_lt_size Gloas.Const.effectiveBalanceIncrementG.val
    have hrun : runSum 0 (activeEffectiveBalances state)
        (activeEffectiveBalances state).length < UInt64.size :=
      hfold _ (Nat.le_refl _)
    have htabrange : quorumTotal state < UInt64.size := by
      unfold quorumTotal
      omega
    -- The total the laws name is in range, so a bound `Gwei` carries it, and
    -- its value law reads it back as that plain `Nat`.
    have htabval : (CLUint64.ofNatLT (quorumTotal state) htabrange).toPlainNat
        = quorumTotal state := CLUint64.ofNatLT_toPlainNat _ _
    have hTAB : getTotalActiveBalance (pureState state)
        = .ok (CLUint64.ofNatLT (quorumTotal state) htabrange) :=
      (getTotalActiveBalance_eq_ok state _).mpr ⟨hfold, rfl⟩
    have hps : ((CLUint64.ofNatLT (quorumTotal state) htabrange)
        / Const.slotsPerEpochDiv).toPlainNat
        = quorumTotal state / slotsPerEpoch := by
      rw [show ((CLUint64.ofNatLT (quorumTotal state) htabrange)
          / Const.slotsPerEpochDiv).toPlainNat
          = (CLUint64.ofNatLT (quorumTotal state) htabrange).toPlainNat
            / slotsPerEpoch from CLUint64.divPos_toPlainNat _ _,
        htabval]
    have hrange' : ((CLUint64.ofNatLT (quorumTotal state) htabrange)
        / Const.slotsPerEpochDiv).toPlainNat
        * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat < UInt64.size := by
      rw [hps]
      exact hrange
    have hval' : scaled.toPlainNat
        = ((CLUint64.ofNatLT (quorumTotal state) htabrange)
          / Const.slotsPerEpochDiv).toPlainNat
          * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat := by
      rw [hps]
      exact hscaled
    rw [show builderPaymentQuorum state
        = (getBuilderPaymentQuorumThreshold (pureState state) : Checked Gwei) from rfl,
      show getBuilderPaymentQuorumThreshold (pureState state)
        = (getTotalActiveBalance (pureState state) >>= fun tab =>
            (tab / Const.slotsPerEpochDiv
              * Gloas.Const.builderPaymentThresholdNumerator : Checked Gwei)
            >>= fun scaled => scaled / Gloas.Const.builderPaymentThresholdDenominator)
          from rfl, hTAB, bind_ok_iff]
    refine ⟨CLUint64.ofNatLT (quorumTotal state) htabrange, rfl, ?_⟩
    rw [bind_ok_iff]
    exact ⟨scaled, mul_eq_ok _ _ _ |>.mpr ⟨hrange', hval'⟩,
      div_eq_ok _ _ _ |>.mpr ⟨hden, hval⟩⟩

/-- The previous-epoch payments whose weight clears `quorum`, mapped to their
withdrawals, in slot order. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (quorum : Gwei) (state : BeaconState) :
    List BuilderPendingWithdrawal :=
  let payments := state.builderPendingPayments
  ((List.range slotsPerEpoch).filter
      fun i => decide ((vget payments i).weight ≥ quorum)).map
    fun i => (vget payments i).withdrawal

/-- The `builderPendingWithdrawals` value `processBuilderPendingPayments` produces:
`qualifyingBuilderWithdrawals`, folded through `ProgressiveList.push` from the field's
current value. `progressiveListFoldlPush_val` says that fold appends every withdrawal. -/
def expectedWithdrawals [Preset] [HasherTag] (quorum : Gwei) (state : BeaconState) :
    ProgressiveList BuilderPendingWithdrawal :=
  (qualifyingBuilderWithdrawals quorum state).foldl (fun l w => l.push w)
    state.builderPendingWithdrawals

/-- The `builderPendingPayments` value `processBuilderPendingPayments` produces: the
field's current value shifted down by `SLOTS_PER_EPOCH` and padded with empties. -/
def expectedPaymentWindow [Preset] [HasherTag] (state : BeaconState) :
    Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  shiftWindow state.builderPendingPayments slotsPerEpoch slotsPerEpoch
    (fun _ => (default : BuilderPendingPayment))

/-- Lower half of `expectedPaymentWindow`: each index `i < slotsPerEpoch` copies the
old upper half at `i + slotsPerEpoch`. -/
theorem expectedPaymentWindow_get_lt [Preset] [HasherTag] (state : BeaconState)
    (i : Nat) (hi : i < slotsPerEpoch) :
    vget (expectedPaymentWindow state) i =
      vget state.builderPendingPayments (i + slotsPerEpoch) := by
  unfold expectedPaymentWindow shiftWindow vget
  have hsz : i < (Vector.ofFn (fun j : Fin (2 * slotsPerEpoch) =>
      if j.val < slotsPerEpoch then
        vget state.builderPendingPayments (j.val + slotsPerEpoch)
      else (default : BuilderPendingPayment))).toArray.size := by
    simp [Vector.toArray_ofFn, Array.size_ofFn]; omega
  rw [getElem!_pos _ i hsz]
  simp [Vector.toArray_ofFn, Array.getElem_ofFn, hi]

/-- Upper half of `expectedPaymentWindow`: each index in
`[slotsPerEpoch, 2 * slotsPerEpoch)` is the empty `BuilderPendingPayment`. -/
theorem expectedPaymentWindow_get_upper [Preset] [HasherTag] (state : BeaconState)
    (i : Nat) (hi : slotsPerEpoch ≤ i) (hi' : i < 2 * slotsPerEpoch) :
    vget (expectedPaymentWindow state) i = (default : BuilderPendingPayment) := by
  unfold expectedPaymentWindow shiftWindow vget
  have hsz : i < (Vector.ofFn (fun j : Fin (2 * slotsPerEpoch) =>
      if j.val < slotsPerEpoch then
        vget state.builderPendingPayments (j.val + slotsPerEpoch)
      else (default : BuilderPendingPayment))).toArray.size := by
    simp [Vector.toArray_ofFn, Array.size_ofFn]; omega
  rw [getElem!_pos _ i hsz]
  simp [Vector.toArray_ofFn, Array.getElem_ofFn, Nat.not_lt.mpr hi]

/-! ## The whole-transition contract

`processBuilderPendingPayments_run` is the contract: the run returns `preState` with only
`builderPendingWithdrawals` and `builderPendingPayments` written, as one value. The
withdrawals half comes from `builderPendingWithdrawalsLoop_run_eq`; the payment-window
half is the final `modifyState`, whose read of the field is unaffected by the loop. -/

/-- Exact whole-transition contract for `processBuilderPendingPayments`, at the box the
pure configuration runs: the step on `pureState preState` returns the uncached box of the original
value with only the two fields written through the source-level writes. Stated at the box
level so the fork-choice bridge consumes it by application; `runPure_of_run_ok` derives
the `runPure` form (`processBuilderPendingPayments_run_appended` reads it). -/
@[characterizes EthCLSpecs.Gloas.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState),
      (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
        = (match builderPaymentQuorum preState with
          | .error f => .error (StateTransitionError.ofArithFault f)
          | .ok quorum =>
            .ok ((), pureState { preState with
                builderPendingWithdrawals := expectedWithdrawals quorum preState,
                builderPendingPayments := expectedPaymentWindow preState })) := by
  intro preState
  have hloop (quorum : Gwei) := builderPendingWithdrawalsLoop_run_eq slotsPerEpoch
    (fun i => (vget preState.builderPendingPayments i).weight ≥ quorum)
    (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
  unfold processBuilderPendingPayments builderPaymentQuorum
  -- Re-elaborate the source shape here: the threshold call rides the monad lift,
  -- the loop term matches `hloop`'s left side, and the final `sszUpdate` reduces
  -- against the record-update form on the right.
  show (do
      let quorum ← liftM (getBuilderPaymentQuorumThreshold (pureState preState) : Checked Gwei)
      let payments := preState.builderPendingPayments
      for i in [0:slotsPerEpoch] do
        if (vget payments i).weight ≥ quorum then
          appendState builderPendingWithdrawals (vget payments i).withdrawal
      modifyState fun state =>
        sszUpdate state with builderPendingPayments :=
          shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment))
      : GloasRun Unit).run (pureState preState)
    = (match (getBuilderPaymentQuorumThreshold (pureState preState) : Checked Gwei) with
      | .error f => .error (StateTransitionError.ofArithFault f)
      | .ok quorum =>
        .ok ((), pureState { preState with
            builderPendingWithdrawals := expectedWithdrawals quorum preState,
            builderPendingPayments := expectedPaymentWindow preState }))
  -- The lift maps the threshold's fault through `ofArithFault`, whose range arm
  -- carries the faulting operator; on success the bind substitutes the threshold.
  have hlift : ∀ x : Checked Gwei, (liftM x : GloasRun Gwei)
      = MonadExcept.ofExcept (x.mapError StateTransitionError.ofArithFault) := by
    intro x
    cases x with
    | ok v => rfl
    | error e => rfl
  rw [hlift (getBuilderPaymentQuorumThreshold (pureState preState))]
  split
  · next f heq =>
    -- The threshold faults: the lift maps it through `ofArithFault`, whose range
    -- arm carries the faulting operator; the run rejects.
    rw [heq]
    simp
    rfl
  · next quorum heq =>
    -- The threshold computes: the bind substitutes it, and the rest is the loop
    -- equation plus the window shift.
    rw [heq]
    -- The successful threshold reduces away, putting the loop and the window
    -- shift where the loop equation names them.
    show (do
        let payments := preState.builderPendingPayments
        for i in [0:slotsPerEpoch] do
          if (vget payments i).weight ≥ quorum then
            appendState builderPendingWithdrawals (vget payments i).withdrawal
        modifyState fun state =>
          sszUpdate state with builderPendingPayments :=
            shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
              (fun _ => (default : BuilderPendingPayment))
        : GloasRun Unit).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals := expectedWithdrawals quorum preState,
          builderPendingPayments := expectedPaymentWindow preState })
    have hloop := builderPendingWithdrawalsLoop_run_eq slotsPerEpoch
      (fun i => (vget preState.builderPendingPayments i).weight ≥ quorum)
      (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
    obtain ⟨a, hbare⟩ := run_of_run_seq_pure _ _ _ hloop
    rw [run_bind, hbare, except_bind_ok]
    unfold expectedWithdrawals qualifyingBuilderWithdrawals expectedPaymentWindow
    rfl

/-- The contract on the threshold's success path, as a literal `.ok` value: the
form `runPure_of_run_ok` consumes. The `.ok` hypothesis names the quorum chain's
real arithmetic obligation through `builderPaymentQuorum_eq_ok`. -/
theorem processBuilderPendingPayments_run_ok [Preset] [HasherTag] (preState : BeaconState)
    (quorum : Gwei) (hq : builderPaymentQuorum preState = .ok quorum) :
    (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
      = .ok ((), pureState { preState with
          builderPendingWithdrawals := expectedWithdrawals quorum preState,
          builderPendingPayments := expectedPaymentWindow preState }) := by
  rw [processBuilderPendingPayments_run preState, hq]

/-- Value-level reading of `processBuilderPendingPayments_run` on the threshold's
success path: every qualifying withdrawal is appended in slot order. The
payment-window half is unchanged from the contract. On the fault path the run
rejects, so the reading states the success case through the threshold's own
`.ok` hypothesis. -/
theorem processBuilderPendingPayments_run_appended [Preset] [HasherTag] (preState : BeaconState)
    (quorum : Gwei) (hq : builderPaymentQuorum preState = .ok quorum) :
    runPure (processBuilderPendingPayments (StateTransition := GloasRun)) preState
      = .ok ((), { preState with
          builderPendingWithdrawals :=
            ⟨preState.builderPendingWithdrawals.val ++ (qualifyingBuilderWithdrawals quorum preState).toArray⟩,
          builderPendingPayments := expectedPaymentWindow preState }) := by
  rw [runPure_of_run_ok (processBuilderPendingPayments_run_ok preState quorum hq)]
  congr 1
  have hval : (expectedWithdrawals quorum preState).val =
      preState.builderPendingWithdrawals.val ++
        (qualifyingBuilderWithdrawals quorum preState).toArray := by
    unfold expectedWithdrawals
    rw [progressiveListFoldlPush_val]
  rw [show expectedWithdrawals quorum preState = ⟨(expectedWithdrawals quorum preState).val⟩ from by
    cases expectedWithdrawals quorum preState
    rfl]
  rw [hval]

end EthCLSpecs.Proofs.Gloas
