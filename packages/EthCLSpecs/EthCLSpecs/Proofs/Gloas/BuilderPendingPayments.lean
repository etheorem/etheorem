import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.IndexRead
import EthCLLib.Proofs.KeepsUncached
import SizzLean.Proofs.ProgressiveListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:376-393`)
computes the quorum threshold, then modifies two fields sequentially within one state
transition. This file characterizes the whole transition as one value. When
`builderPaymentQuorum preState` succeeds, the run on `pureState preState` returns
`pureState` of `preState` with `builderPendingWithdrawals` and `builderPendingPayments`
written, and nothing else. When the quorum computation fails, the run rejects with the
same error and returns no state. On the success path, the substep feeds every qualifying
previous-epoch payment's withdrawal, in slot order, through `ProgressiveList.push`, which
always appends. It then shifts the payment window down by `SLOTS_PER_EPOCH`, padding the
vacated half with empties.

The withdrawals side rests on `progressiveListFoldlPush_val`
(`SizzLean.Proofs.ProgressiveListPush`): iterating `push` over a list of values ends at
the original list plus every value, in order. The pinned spec types
`builder_pending_withdrawals` as a progressive list with no limit, so the append has no
capacity check to assume.

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
surface over the total active balance, whose registry reads raise `IndexError`,
so the threshold is an `Except StateTransitionError` value: a fault here rejects
the substep exactly where the pyspec raises. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : BeaconState) :
    Except StateTransitionError Gwei :=
  getBuilderPaymentQuorumThreshold (pureState state)

/-- The effective balances `getTotalBalance` folds over a given index set `active`: each
member read at its index. The readings below instantiate `active` with the cast active set
and restate the result over `activeBalances`. -/
def activeEffectiveBalances [Preset] (state : BeaconState) (active : Array ValidatorIndex) :
    List Gwei :=
  active.toList.map (fun i => state.validators.val[i.toPlainNat]!.effectiveBalance)

/-- The registry positions active at `epoch`, in registry order: the positions
`get_active_validator_indices` casts with `ValidatorIndex(index)`. -/
def activePositions [Preset] (state : BeaconState) (epoch : Epoch) : List Nat :=
  (List.range state.validators.val.size).filter
    fun i => isActiveValidator state.validators.val[i]! epoch

/-- The `ValidatorIndex(index)` casts of the current epoch's active set all fit `uint64`.
The Gloas registry is a `ProgressiveList`, which carries no length cap in its type, so this
is a real condition of the readings: it fails only for an active position at or past
`2^64`, where the pyspec's cast raises. -/
def activeCastsFit [Preset] (state : BeaconState) : Prop :=
  ∀ p ∈ activePositions state (computeEpochAtSlot state.slot), p < UInt64.size

/-- The effective balances of the current epoch's active validators, in registry order:
the list `get_total_active_balance` sums. -/
def activeBalances [Preset] (state : BeaconState) : List Gwei :=
  (activePositions state (computeEpochAtSlot state.slot)).map
    fun p => state.validators.val[p]!.effectiveBalance

/-- The plain `Nat` the quorum chain divides: the fold's final running sum over the
balance list `bals`, floored at one increment (`get_total_balance`'s `max`). -/
def quorumTotal [Preset] (bals : List Gwei) : Nat :=
  max (runSum 0 bals bals.length) Gloas.Const.effectiveBalanceIncrementG.toPlainNat

/-- The checked arithmetic of `get_total_balance` over a balance list: the `sum` fold,
then the one-increment floor. -/
def totalOf [Preset] (bals : List Gwei) : Checked Gwei :=
  bals.foldlM (fun acc b => acc + b) (0 : Gwei) >>= fun total =>
    pure (max total Gloas.Const.effectiveBalanceIncrementG)

/-- The checked arithmetic of the quorum chain over the balance list `bals`: the total,
the proved-total per-slot division, the scaling product, and the denominator division. -/
def quorumCore [Preset] (bals : List Gwei) : Checked Gwei :=
  totalOf bals >>= fun tab =>
    (tab / Const.slotsPerEpochDiv * Gloas.Const.builderPaymentThresholdNumerator : Checked Gwei)
      >>= fun scaled => scaled / Gloas.Const.builderPaymentThresholdDenominator

/-- `Except.mapM` over a list whose every step succeeds is the plain `map`. -/
private theorem list_mapM_except_ok {α β ε : Type} (f : α → Except ε β) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = .ok (g x)) → xs.mapM f = .ok (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, h x (List.mem_cons_self ..),
      list_mapM_except_ok f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- The total's registry reads succeed on an in-range active set, each returning the
member's effective balance. -/
private theorem activeReads_ok [Preset] (state : BeaconState) (active : Array ValidatorIndex)
    (hrange : ∀ i ∈ active, i.toPlainNat < state.validators.val.size) :
    active.mapM (fun i => (do
        let validator ← liftErr (getAt state.validators i)
        pure validator.effectiveBalance : Except StateTransitionError Gwei))
      = .ok (activeEffectiveBalances state active).toArray := by
  rw [Array.mapM_eq_mapM_toList]
  rw [list_mapM_except_ok _ (fun i => state.validators.val[i.toPlainNat]!.effectiveBalance)]
  · rfl
  · intro i hi
    have hlt := hrange i (Array.mem_toList_iff.mp hi)
    rw [EthCLLib.Proofs.getAt_progressiveList_clUint64,
      Array.getElem?_eq_getElem hlt, getElem!_pos state.validators.val _ hlt]
    rfl

/-- `getTotalActiveBalance` on an active set that casts and reads in range is the checked
total `totalOf` of the members' effective balances, its fault mapped to the state error. -/
private theorem getTotalActiveBalance_eq_of_active [Preset] [HasherTag] (state : BeaconState)
    (active : Array ValidatorIndex)
    (hact : getActiveValidatorIndices (pureState state) (computeEpochAtSlot state.slot)
      = .ok active)
    (hrange : ∀ i ∈ active, i.toPlainNat < state.validators.val.size) :
    getTotalActiveBalance (pureState state)
      = (totalOf (activeEffectiveBalances state active)).mapError
          StateTransitionError.ofArithFault := by
  unfold getTotalActiveBalance getTotalBalance
  simp only [view_uncachedBox]
  rw [hact]
  show (do
      let balances ← active.mapM (fun i => (do
        let validator ← liftErr (getAt state.validators i)
        pure validator.effectiveBalance : Except StateTransitionError Gwei))
      let total ← liftM (balances.foldlM (fun acc b => acc + b) (0 : Gwei) : Checked Gwei)
      pure (max total Gloas.Const.effectiveBalanceIncrementG) : Except StateTransitionError Gwei)
    = _
  rw [activeReads_ok state active hrange, except_bind_ok, List.foldlM_toArray]
  unfold totalOf
  cases (activeEffectiveBalances state active).foldlM (fun acc b => acc + b) (0 : Gwei) <;> rfl

/-! ### The active set

`getActiveValidatorIndices_eq` reads the registry loop as the checked casts of
`activePositions`. Each position indexes the registry by construction, so the reads of
`getTotalBalance` stay in range, and the casts succeed exactly under `activeCastsFit`. -/

/-- The loop shape of `get_active_validator_indices`: a `for` over a list that pushes the
checked image `g a` of each `a` passing `p`. Over `Except`, it runs as `mapM g` over the
filtered list, appended to the accumulator. The membership proof in `f` is unused, which
`hf` states. -/
private theorem forIn'_filter_push {ε β : Type} (p : Nat → Bool) (g : Nat → Except ε β) :
    ∀ (l : List Nat) (acc : Array β)
      (f : (a : Nat) → a ∈ l → Array β → Except ε (ForInStep (Array β))),
      (∀ a h r, f a h r = if p a then (g a >>= fun v => pure (ForInStep.yield (r.push v)))
        else pure (ForInStep.yield r)) →
      forIn' l acc f = ((l.filter p).mapM g).map (fun xs => acc ++ xs.toArray)
  | [], acc, f, _ => by simp; rfl
  | a :: rest, acc, f, hf => by
    rw [List.forIn'_cons, hf]
    by_cases hp : p a
    · simp only [hp, ↓reduceIte]
      rw [List.filter_cons_of_pos hp, List.mapM_cons]
      cases hg : g a with
      | error e => rfl
      | ok v =>
        show (forIn' rest (acc.push v) fun a' m b => f a' (List.mem_cons_of_mem a m) b) = _
        rw [forIn'_filter_push p g rest (acc.push v) _ (fun a' h r => hf a' _ r)]
        cases (rest.filter p).mapM g with
        | error e => rfl
        | ok xs =>
          show Except.ok (acc.push v ++ xs.toArray) = Except.ok (acc ++ (v :: xs).toArray)
          simp
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_cons_of_neg hp]
      exact forIn'_filter_push p g rest acc _ (fun a' h r => hf a' _ r)

/-- `getActiveValidatorIndices` is the checked `ValidatorIndex(index)` cast of every
active position, in registry order. -/
theorem getActiveValidatorIndices_eq [Preset] [HasherTag] (state : BeaconState)
    (epoch : Epoch) :
    getActiveValidatorIndices (pureState state) epoch
      = ((activePositions state epoch).mapM CLUint64.ofNat?).map List.toArray := by
  unfold getActiveValidatorIndices
  simp only [view_uncachedBox]
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [forIn'_filter_push (fun i => isActiveValidator state.validators.val[i]! epoch)
    CLUint64.ofNat?]
  · -- The range `[0 : n]` is `List.range n`, and the trailing `pure` drops out.
    have hsize : ([:state.validators.toArray.size] : Std.Legacy.Range).size
        = state.validators.val.size := by simp [Std.Legacy.Range.size]
    rw [hsize, show ([:state.validators.toArray.size] : Std.Legacy.Range).start = 0 from rfl,
      show ([:state.validators.toArray.size] : Std.Legacy.Range).step = 1 from rfl,
      ← List.range_eq_range', bind_pure]
    unfold activePositions
    cases List.mapM CLUint64.ofNat? _ <;> simp [Except.map]
  · -- The bound-carrying read `validators[i]` is the total read at an in-range `i`.
    intro a h r
    have hlt : a < state.validators.val.size := (Std.Legacy.Range.mem_of_mem_range' h).upper
    show (if isActiveValidator (state.validators.val[a]'hlt) epoch = true then _ else _) = _
    rw [getElem!_pos state.validators.val a hlt]

/-- Every active position indexes the registry. -/
theorem activePositions_lt [Preset] (state : BeaconState) (epoch : Epoch) :
    ∀ p ∈ activePositions state epoch, p < state.validators.val.size := by
  intro p hp
  unfold activePositions at hp
  exact List.mem_range.mp (List.mem_filter.mp hp).1

/-- The checked cast of an in-range `Nat` is its bound construction. -/
private theorem ofNat?_of_lt (p : Nat) (hp : p < UInt64.size) :
    CLUint64.ofNat? p = .ok (CLUint64.ofNatLT p hp) := by
  unfold CLUint64.ofNat?
  simp [hp]

/-- The checked cast of an out-of-range `Nat` faults. -/
private theorem ofNat?_of_not_lt (p : Nat) (hp : ¬ p < UInt64.size) :
    ∃ f, CLUint64.ofNat? p = .error f := by
  unfold CLUint64.ofNat?
  simp [hp]

/-- A successful run of the checked casts fits every position, and reads each back. -/
private theorem mapM_ofNat?_ok : ∀ (l : List Nat) (xs : List CLUint64),
    l.mapM CLUint64.ofNat? = .ok xs →
      (∀ p ∈ l, p < UInt64.size) ∧ xs.map CLUint64.toPlainNat = l
  | [], xs, h => by
    have hx : xs = [] := (Except.ok.inj h).symm
    subst hx
    exact ⟨fun _ hp => (nomatch hp), rfl⟩
  | p :: rest, xs, h => by
    rw [List.mapM_cons] at h
    by_cases hp : p < UInt64.size
    · rw [ofNat?_of_lt p hp] at h
      cases hm : rest.mapM CLUint64.ofNat? with
      | error e => rw [hm] at h; cases h
      | ok ys =>
        rw [hm] at h
        have hx : xs = CLUint64.ofNatLT p hp :: ys := (Except.ok.inj h).symm
        subst hx
        obtain ⟨hfit, hmap⟩ := mapM_ofNat?_ok rest ys hm
        refine ⟨fun q hq => ?_, ?_⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hp
          · exact hfit q hq
        · rw [List.map_cons, hmap, CLUint64.ofNatLT_toPlainNat]
    · obtain ⟨f, hf⟩ := ofNat?_of_not_lt p hp
      rw [hf] at h
      cases h

/-- The checked casts succeed when every position fits. -/
private theorem mapM_ofNat?_fit : ∀ (l : List Nat), (∀ p ∈ l, p < UInt64.size) →
    ∃ xs, l.mapM CLUint64.ofNat? = .ok xs
  | [], _ => ⟨[], rfl⟩
  | p :: rest, h => by
    obtain ⟨ys, hys⟩ := mapM_ofNat?_fit rest (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p (List.mem_cons_self ..)
    refine ⟨CLUint64.ofNatLT p hp :: ys, ?_⟩
    rw [List.mapM_cons, ofNat?_of_lt p hp, hys]
    rfl

/-- `getTotalActiveBalance` under `activeCastsFit` is the checked total `totalOf` of
`activeBalances`, its fault mapped to the state error. The registry reads cannot raise:
every active position indexes the registry (`activePositions_lt`). -/
theorem getTotalActiveBalance_eq [Preset] [HasherTag] (state : BeaconState)
    (hfit : activeCastsFit state) :
    getTotalActiveBalance (pureState state)
      = (totalOf (activeBalances state)).mapError StateTransitionError.ofArithFault := by
  obtain ⟨xs, hxs⟩ := mapM_ofNat?_fit _ hfit
  have hmap := (mapM_ofNat?_ok _ xs hxs).2
  have hact : getActiveValidatorIndices (pureState state) (computeEpochAtSlot state.slot)
      = .ok xs.toArray := by
    rw [getActiveValidatorIndices_eq, hxs]
    rfl
  have hrange : ∀ i ∈ xs.toArray, i.toPlainNat < state.validators.val.size := by
    intro i hi
    apply activePositions_lt state (computeEpochAtSlot state.slot)
    rw [← hmap]
    exact List.mem_map_of_mem (List.mem_toArray.mp hi)
  rw [getTotalActiveBalance_eq_of_active state xs.toArray hact hrange]
  have hbals : activeEffectiveBalances state xs.toArray = activeBalances state := by
    unfold activeEffectiveBalances activeBalances
    rw [← hmap, List.map_map, List.toList_toArray]
    rfl
  rw [hbals]

/-- When a cast of the active set does not fit, `getTotalActiveBalance` rejects: the
`ValidatorIndex(index)` cast raises before any registry read. -/
theorem getTotalActiveBalance_error [Preset] [HasherTag] (state : BeaconState)
    (hfit : ¬ activeCastsFit state) :
    ∃ e, getTotalActiveBalance (pureState state) = .error e := by
  cases hxs : (activePositions state (computeEpochAtSlot state.slot)).mapM CLUint64.ofNat? with
  | ok xs => exact absurd (mapM_ofNat?_ok _ xs hxs).1 hfit
  | error f =>
    refine ⟨StateTransitionError.ofArithFault f, ?_⟩
    unfold getTotalActiveBalance
    simp only [view_uncachedBox]
    rw [getActiveValidatorIndices_eq, hxs]
    rfl

/-- `Except.mapError` keeps a success unchanged and never produces one from a fault. -/
private theorem mapError_eq_ok {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

/-- The total's fused reading: `totalOf` succeeds with `tab` exactly when every running
sum of `bals` stays in range (the checked fold's own obligation), and then `tab` is the
fold's final running sum floored at one increment. `getTotalActiveBalance_eq_ok` reads the
accessor through it. Laws: `bind_ok_iff` (the one bind), `foldlM_add_ok_iff`, `foldlM_add_value`,
`max_value`. -/
theorem totalOf_eq_ok [Preset] (bals : List Gwei) (tab : Gwei) :
    totalOf bals = .ok tab ↔
      (∀ i ≤ bals.length, runSum 0 bals i < UInt64.size) ∧
      tab.toPlainNat = max (runSum 0 bals bals.length)
        Gloas.Const.effectiveBalanceIncrementG.toPlainNat := by
  unfold totalOf
  constructor
  · rw [bind_ok_iff]
    rintro ⟨c, hfold, hret⟩
    have hmaxc : max c Gloas.Const.effectiveBalanceIncrementG = tab :=
      Except.ok.inj hret
    have hval1 : tab.toPlainNat
        = max c.toPlainNat Gloas.Const.effectiveBalanceIncrementG.toPlainNat := by
      rw [← hmaxc, max_value]
    have hval2 : c.toPlainNat = runSum 0 bals bals.length :=
      foldlM_add_value 0 _ _ hfold
    refine ⟨foldlM_add_ok_iff 0 _ |>.mp ⟨c, hfold⟩, ?_⟩
    rw [hval1, hval2]
  · rintro ⟨hbounds, hval⟩
    obtain ⟨c, hfold⟩ := foldlM_add_ok_iff 0 _ |>.mpr hbounds
    rw [bind_ok_iff]
    refine ⟨c, hfold, ?_⟩
    show (Except.ok (max c Gloas.Const.effectiveBalanceIncrementG) : Checked Gwei)
      = Except.ok tab
    refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
    show (max c Gloas.Const.effectiveBalanceIncrementG).toPlainNat = tab.toPlainNat
    rw [max_value, hval, ← foldlM_add_value 0 _ _ hfold]

/-- The total's reading with no side hypothesis: `getTotalActiveBalance` succeeds with
`tab` exactly when the active set's casts fit, every running sum of `activeBalances` stays
in range, and `tab` is the fold's final running sum floored at one increment. -/
theorem getTotalActiveBalance_eq_ok [Preset] [HasherTag] (state : BeaconState) (tab : Gwei) :
    getTotalActiveBalance (pureState state) = .ok tab ↔
      activeCastsFit state ∧
      (∀ i ≤ (activeBalances state).length, runSum 0 (activeBalances state) i < UInt64.size) ∧
      tab.toPlainNat = max (runSum 0 (activeBalances state) (activeBalances state).length)
        Gloas.Const.effectiveBalanceIncrementG.toPlainNat := by
  by_cases hfit : activeCastsFit state
  · rw [getTotalActiveBalance_eq state hfit, mapError_eq_ok, totalOf_eq_ok]
    exact ⟨fun h => ⟨hfit, h⟩, fun h => h.2⟩
  · obtain ⟨e, he⟩ := getTotalActiveBalance_error state hfit
    rw [he]
    exact ⟨fun h => (nomatch h), fun h => absurd h.1 hfit⟩

/-- The quorum chain's fused reading: the threshold is the checked `Gwei` chain
`total // slotsPerEpoch * numerator // denominator`, with the per-slot division the
proved-total route, so the chain succeeds with `quorum` exactly when every
running sum of `bals` stays in range, the scaling product stays in range, and the
denominator is nonzero; the value reads back as that plain chain.
`builderPaymentQuorum_eq_ok` instantiates `bals` with `activeBalances`. The denominator is the literal `10`, so its zero
test discharges in the kernel. Laws: `totalOf_eq_ok` (hence
`foldlM_add_ok_iff`, `foldlM_add_value`, `max_value`), `bind_ok_iff` (twice, one
per bind), `mul_eq_ok`, `div_eq_ok`, and the proved-total route's
`divPos_toPlainNat`. `builderPaymentQuorum_eq` connects the core to the accessor. -/
theorem quorumCore_eq_ok [Preset] (bals : List Gwei) (quorum : Gwei) :
    quorumCore bals = .ok quorum ↔
      (∀ i ≤ bals.length, runSum 0 bals i < UInt64.size) ∧
      ∃ scaled : Gwei,
        scaled.toPlainNat = quorumTotal bals / slotsPerEpoch
            * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat ∧
        quorumTotal bals / slotsPerEpoch
            * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat < UInt64.size ∧
        Gloas.Const.builderPaymentThresholdDenominator.toPlainNat ≠ 0 ∧
        quorum.toPlainNat = scaled.toPlainNat
            / Gloas.Const.builderPaymentThresholdDenominator.toPlainNat := by
  constructor
  · intro h
    unfold quorumCore at h
    -- Two binds, one per `←` in the body; `bind_ok_iff` exposes each, and the
    -- operator laws read the two checked steps on the plain values.
    rw [bind_ok_iff] at h
    obtain ⟨tab, hTAB, hrest⟩ := h
    rw [bind_ok_iff] at hrest
    obtain ⟨scaled, hmul, hdiv⟩ := hrest
    have hden := (div_eq_ok _ _ _ |>.mp hdiv).1
    have hval := (div_eq_ok _ _ _ |>.mp hdiv).2
    have hmulr := mul_eq_ok _ _ _ |>.mp hmul
    have htab := (totalOf_eq_ok bals tab).mp hTAB
    -- `quorumTotal` is the floored running sum `htab.2` names, and the
    -- proved-total division reads back as the plain quotient, so the product's
    -- range fact and value land on the statement's plain terms.
    have hqt : quorumTotal bals = tab.toPlainNat := by
      show max (runSum 0 bals bals.length)
        Gloas.Const.effectiveBalanceIncrementG.toPlainNat = tab.toPlainNat
      rw [htab.2]
    have hps : (tab / Const.slotsPerEpochDiv).toPlainNat
        = quorumTotal bals / slotsPerEpoch := by
      rw [show (tab / Const.slotsPerEpochDiv).toPlainNat
          = tab.toPlainNat / slotsPerEpoch from
            CLUint64.divPos_toPlainNat tab Const.slotsPerEpochDiv, hqt]
    have hrange'' : quorumTotal bals / slotsPerEpoch
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
    have hrun : runSum 0 bals bals.length < UInt64.size :=
      hfold _ (Nat.le_refl _)
    have htabrange : quorumTotal bals < UInt64.size := by
      unfold quorumTotal
      omega
    -- The total the laws name is in range, so a bound `Gwei` carries it, and
    -- its value law reads it back as that plain `Nat`.
    have htabval : (CLUint64.ofNatLT (quorumTotal bals) htabrange).toPlainNat
        = quorumTotal bals := CLUint64.ofNatLT_toPlainNat _ _
    have hTAB : totalOf bals
        = .ok (CLUint64.ofNatLT (quorumTotal bals) htabrange) :=
      (totalOf_eq_ok bals _).mpr ⟨hfold, htabval⟩
    have hps : ((CLUint64.ofNatLT (quorumTotal bals) htabrange)
        / Const.slotsPerEpochDiv).toPlainNat
        = quorumTotal bals / slotsPerEpoch := by
      rw [show ((CLUint64.ofNatLT (quorumTotal bals) htabrange)
          / Const.slotsPerEpochDiv).toPlainNat
          = (CLUint64.ofNatLT (quorumTotal bals) htabrange).toPlainNat
            / slotsPerEpoch from CLUint64.divPos_toPlainNat _ _,
        htabval]
    have hrange' : ((CLUint64.ofNatLT (quorumTotal bals) htabrange)
        / Const.slotsPerEpochDiv).toPlainNat
        * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat < UInt64.size := by
      rw [hps]
      exact hrange
    have hval' : scaled.toPlainNat
        = ((CLUint64.ofNatLT (quorumTotal bals) htabrange)
          / Const.slotsPerEpochDiv).toPlainNat
          * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat := by
      rw [hps]
      exact hscaled
    unfold quorumCore
    rw [hTAB, bind_ok_iff]
    refine ⟨CLUint64.ofNatLT (quorumTotal bals) htabrange, rfl, ?_⟩
    rw [bind_ok_iff]
    exact ⟨scaled, mul_eq_ok _ _ _ |>.mpr ⟨hrange', hval'⟩,
      div_eq_ok _ _ _ |>.mpr ⟨hden, hval⟩⟩

/-- `builderPaymentQuorum` under `activeCastsFit` is the checked quorum chain `quorumCore`
over `activeBalances`, its fault mapped to the state error. -/
theorem builderPaymentQuorum_eq [Preset] [HasherTag] (state : BeaconState)
    (hfit : activeCastsFit state) :
    builderPaymentQuorum state
      = (quorumCore (activeBalances state)).mapError StateTransitionError.ofArithFault := by
  unfold builderPaymentQuorum getBuilderPaymentQuorumThreshold quorumCore
  rw [getTotalActiveBalance_eq state hfit]
  -- The lift of a checked step is its `mapError`, and `mapError` distributes over the
  -- binds.
  have hlift : ∀ (x : Checked Gwei),
      (liftM x : Except StateTransitionError Gwei) = x.mapError StateTransitionError.ofArithFault := by
    intro x
    cases x <;> rfl
  have hmap : ∀ (x : Checked Gwei) (f : Gwei → Checked Gwei),
      (x >>= f).mapError StateTransitionError.ofArithFault
        = x.mapError StateTransitionError.ofArithFault >>= fun a =>
            (f a).mapError StateTransitionError.ofArithFault := by
    intro x f
    cases x <;> rfl
  simp only [hlift, hmap]

/-- The quorum's reading with no side hypothesis: `builderPaymentQuorum` succeeds with
`quorum` exactly when the active set's `ValidatorIndex(index)` casts fit `uint64`, and the
quorum chain over `activeBalances` meets the arithmetic obligations of `quorumCore_eq_ok`. This is
the real obligation the contract's `.ok quorum` hypothesis names. The cast conjunct stays
because the Gloas registry is a `ProgressiveList`, whose type carries no `2^40` cap: an
active position at or past `2^64` makes the pyspec's cast raise, and the run rejects. -/
theorem builderPaymentQuorum_eq_ok [Preset] [HasherTag] (state : BeaconState)
    (quorum : Gwei) :
    builderPaymentQuorum state = .ok quorum ↔
      activeCastsFit state ∧
      (∀ i ≤ (activeBalances state).length, runSum 0 (activeBalances state) i < UInt64.size) ∧
      ∃ scaled : Gwei,
        scaled.toPlainNat = quorumTotal (activeBalances state) / slotsPerEpoch
            * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat ∧
        quorumTotal (activeBalances state) / slotsPerEpoch
            * Gloas.Const.builderPaymentThresholdNumerator.toPlainNat < UInt64.size ∧
        Gloas.Const.builderPaymentThresholdDenominator.toPlainNat ≠ 0 ∧
        quorum.toPlainNat = scaled.toPlainNat
            / Gloas.Const.builderPaymentThresholdDenominator.toPlainNat := by
  by_cases hfit : activeCastsFit state
  · rw [builderPaymentQuorum_eq state hfit, mapError_eq_ok, quorumCore_eq_ok]
    exact ⟨fun h => ⟨hfit, h⟩, fun h => h.2⟩
  · -- A cast fault rejects the total, and the threshold's first bind passes it on.
    obtain ⟨e, he⟩ := getTotalActiveBalance_error state hfit
    have hq : builderPaymentQuorum state = .error e := by
      unfold builderPaymentQuorum getBuilderPaymentQuorumThreshold
      rw [he]
      rfl
    rw [hq]
    exact ⟨fun h => (nomatch h), fun h => absurd h.1 hfit⟩

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

`processBuilderPendingPayments_run` is the contract. It matches on
`builderPaymentQuorum preState`. A quorum error propagates: the run rejects with that
error and writes nothing. After a successful quorum computation, the run returns
`preState` with only `builderPendingWithdrawals` and `builderPendingPayments` written, as
one value. The withdrawals half comes from `builderPendingWithdrawalsLoop_run_eq`. The
payment-window half is the final `modifyState`, whose read of the field is unaffected by
the loop. -/

/-- Exact whole-transition contract for `processBuilderPendingPayments`, at the box the
pure configuration runs. The step on `pureState preState` matches on
`builderPaymentQuorum preState`. On `.error e` the quorum error propagates: the run is
`.error e` and returns no state. On `.ok quorum` the run returns the uncached box of the
original value with only the two fields written through the source-level writes. Stated
at the box level so the fork-choice bridge consumes it by application. On the success
path, `runPure_of_run_ok` derives the `runPure` form
(`processBuilderPendingPayments_run_appended` reads it). -/
@[characterizes EthCLSpecs.Gloas.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState),
      (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
        = (match builderPaymentQuorum preState with
          | .error e => .error e
          | .ok quorum =>
            .ok ((), pureState { preState with
                builderPendingWithdrawals := expectedWithdrawals quorum preState,
                builderPendingPayments := expectedPaymentWindow preState })) := by
  intro preState
  have hloop (quorum : Gwei) := builderPendingWithdrawalsLoop_run_eq slotsPerEpoch
    (fun i => (vget preState.builderPendingPayments i).weight ≥ quorum)
    (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
  unfold processBuilderPendingPayments builderPaymentQuorum
  -- Re-elaborate the source shape here: the threshold call goes through `liftErr`,
  -- the loop term matches `hloop`'s left side, and the final `sszUpdate` reduces
  -- against the record-update form on the right.
  show (do
      let quorum ← liftErr (getBuilderPaymentQuorumThreshold (pureState preState))
      let payments := preState.builderPendingPayments
      for i in [0:slotsPerEpoch] do
        if (vget payments i).weight ≥ quorum then
          appendState builderPendingWithdrawals (vget payments i).withdrawal
      modifyState fun state =>
        sszUpdate state with builderPendingPayments :=
          shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment))
      : GloasRun Unit).run (pureState preState)
    = (match getBuilderPaymentQuorumThreshold (pureState preState) with
      | .error e => .error e
      | .ok quorum =>
        .ok ((), pureState { preState with
            builderPendingWithdrawals := expectedWithdrawals quorum preState,
            builderPendingPayments := expectedPaymentWindow preState }))
  -- `liftErr` through the identity conversion: the threshold's fault passes through
  -- unchanged; on success the bind substitutes the threshold.
  have hlift : ∀ x : Except StateTransitionError Gwei, (liftErr x : GloasRun Gwei)
      = MonadExcept.ofExcept x := by
    intro x
    cases x with
    | ok v => rfl
    | error e => rfl
  rw [hlift (getBuilderPaymentQuorumThreshold (pureState preState))]
  split
  · next f heq =>
    -- The threshold faults: the run rejects with the same error.
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
