import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.ProgressiveListPush
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.Gloas.BuilderPendingPayments`: the builder-payment epoch substep

`EthCLSpecs.Gloas.processBuilderPendingPayments` (`Gloas/EpochProcessing.lean:323-347`)
modifies two fields sequentially within one state transition. This file characterizes the
whole transition as one value: the run on `pureState preState` either rejects with the
`.arithmetic` fault of the quorum chain, or returns `pureState` of `preState` with
`builderPendingWithdrawals` and `builderPendingPayments` written, and nothing else. When
the quorum chain binds, the step feeds every qualifying previous-epoch payment's
withdrawal, in slot order, through `ProgressiveList.push`, which always appends. It then
shifts the payment window down by `SLOTS_PER_EPOCH`, padding the vacated half with empties.

The fault surface is the quorum computation. The Gwei port (Stage 2) made
`get_total_active_balance // SLOTS_PER_EPOCH * NUMERATOR // DENOMINATOR` a checked
`Gwei` chain, bound under one `←`: the total may fault in its own checked-add fold, a
zero or overflowing divisor step raises, and the lift surfaces the fault as
`.arithmetic` with the repr of the exact `ArithFault`. `builderPaymentQuorum` states
that chain as one `Checked Gwei` value, spelled exactly as the source writes it, and
the contract dispatches on it. The chain's `Nat`-route operands are the preset
`SLOTS_PER_EPOCH` and the two raw-`UInt64` constants read through `.toNat`, the route
the fork body itself takes. The loop and the window write cannot fault: the loop
appends to a progressive list, alpha.12 dropped
`BUILDER_PENDING_WITHDRAWALS_LIMIT`, so there is no capacity clamp.

The withdrawals side rests on `progressiveListFoldlPush_val`
(`SizzLean.Proofs.ProgressiveListPush`): iterating `push` over a list of values ends at
the original list plus every value, in order.

The window side is a direct instance of `shiftWindow`'s general behavior:
`expectedPaymentWindow_get_lt` / `expectedPaymentWindow_get_upper` state the two
index-region facts (old upper half moves down; new upper half is empty).
`processBuilderPendingPayments` reads `builderPendingPayments` once, before the
withdrawals loop runs, and the loop never writes that field, so the window
transformation's input is unaffected by whatever the withdrawals loop did.

Statements bind plain `BeaconState` values and never bind a boxed `State`. The contract
`processBuilderPendingPayments_run` states the run at the box, in `.run` form, because
that is the shape the fork-choice bridge consumes; the readings state the `runPure` form
under the chain's `.ok` equation, which `runPure_of_run_ok` derives from the contract.

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
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok run_bind run_pure
  except_bind_ok except_bind_error run_liftM_ok run_liftM_error)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas (Preset Gwei BeaconState)
open EthCLSpecs.Gloas.Const (slotsPerEpoch builderPaymentThresholdNumerator
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
reads `pureState state`, so the names stay free of any box of their own.

`builderPaymentQuorum` is the one fault surface: it states the checked chain the body
binds under its single `←`, as a `Checked Gwei` value. The chain's `Nat`-route operands
are the preset `slotsPerEpoch` and the two raw-`UInt64` threshold constants read through
`.toNat`, the route the fork body itself takes. The `Checked` shape is the value the
`do`-lift receives, so the contract can dispatch on it. The other three names parameter
on the quorum the body binds: the loop's guard compares the bound plain value, so the
names stay in `Gwei`, with the binding obligation carried by the `.ok` arm of the
contract. -/

/-- `processBuilderPendingPayments`'s quorum threshold, the checked chain
`get_total_active_balance // SLOTS_PER_EPOCH * NUMERATOR // DENOMINATOR`
(`gloas/beacon-chain.md:1433-1440`) exactly as the body binds it: the body lifts the
total's divisor step and the threshold's two `Nat`-route steps as two chained
`Checked` binds under one source `let ←`, and this value is those steps as one
`Checked Gwei`. Each `//` is a `Nat`-route divisor with the same zero-divisor raise,
each step tested in order. Faults surface as the `.arithmetic` of the repr of the
exact `ArithFault`. -/
def builderPaymentQuorum [Preset] [HasherTag] (state : BeaconState) : Checked Gwei :=
  (getTotalActiveBalance (pureState state) / slotsPerEpoch).bind
    fun tab =>
      (tab * builderPaymentThresholdNumerator.toNat / builderPaymentThresholdDenominator.toNat)

/-- `builderPaymentQuorum` is the two `Checked` steps the body binds, as one bind chain.
`rfl`: the def is that spelling. The contract's proof rewrites with this so the statement's
match scrutinee and the run's folded chain are one term. -/
private theorem builderPaymentQuorum_eq [Preset] [HasherTag] (state : BeaconState) :
    builderPaymentQuorum state
      = (getTotalActiveBalance (pureState state) / slotsPerEpoch).bind
          fun tab =>
            (tab * builderPaymentThresholdNumerator.toNat
              / builderPaymentThresholdDenominator.toNat) :=
  rfl

/-- The previous-epoch payments whose weight clears the quorum `quorum`, mapped to
their withdrawals, in slot order. `quorum` is the plain value the body compares
against, the one its own checked chain binds. -/
def qualifyingBuilderWithdrawals [Preset] [HasherTag] (state : BeaconState)
    (quorum : Gwei) : List BuilderPendingWithdrawal :=
  let payments := state.builderPendingPayments
  ((List.range slotsPerEpoch).filter
      fun i => decide ((vget payments i).weight ≥ quorum)).map
    fun i => (vget payments i).withdrawal

/-- The `builderPendingWithdrawals` value `processBuilderPendingPayments` produces when
its quorum chain binds: `qualifyingBuilderWithdrawals`, folded through
`ProgressiveList.push` from the field's current value. `progressiveListFoldlPush_val`
says that fold appends every withdrawal. -/
def expectedWithdrawals [Preset] [HasherTag] (state : BeaconState) (quorum : Gwei) :
    ProgressiveList BuilderPendingWithdrawal :=
  (qualifyingBuilderWithdrawals state quorum).foldl (fun l w => l.push w)
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

`processBuilderPendingPayments_run` is the contract: the run dispatches on the quorum
chain, and on `.ok` it returns `preState` with only `builderPendingWithdrawals` and
`builderPendingPayments` written, as one value. The fault half is the two chained
`liftM` leaves the body desugars its single `let quorum ← (← …) * … / …` to: each
`.ok` arm is `pure`, each `.error` arm raises as the `.arithmetic` fault carrying the
repr of the exact `ArithFault`, and neither arm writes the state. `run_liftChecked2`
folds the two leaves into one dispatch on `builderPaymentQuorum`, the same `Checked`
value the statement's match scrutinee names. The withdrawals half comes from
`builderPendingWithdrawalsLoop_run_eq`; the payment-window half is the final
`modifyState`, whose read of the field is unaffected by the loop. The `liftM` run leaves
come from `EthCLLib.Proofs.Run` (`run_liftM_ok` / `run_liftM_error`), the pair's one
canonical home; `KeepsUncached.lean` still carries its own private copies with the same
reason it documented: its tactic surface stays closed. -/

/-- The two chained `liftM` leaves the body binds its quorum chain with, folded into one
dispatch on the chain as a single `Checked` value: fault on the first step, fault on the
second, or bind the value and run the rest. The arms mirror `Except.bind`, so neither
write nor state crosses a fault. -/
private theorem run_liftChecked2 {σ α β : Type} (a₁ : Checked α) (k : α → Checked β)
    (f : β → StateT σ (Except StateTransitionError) Unit) (s : σ) :
    ((do
        let a ← a₁
        let b ← k a
        f b
      : StateT σ (Except StateTransitionError) Unit).run s)
      = match a₁.bind k with
        | .error e => .error (StateTransitionError.arithmetic (reprStr e))
        | .ok b => (f b).run s := by
  rw [run_bind]
  cases a₁ with
  | error e =>
    -- `ErrorConv` at the state machine is the identity, so the conv wrapper reduces.
    rw [run_liftM_error, except_bind_error, show (Except.error e).bind k = .error e from rfl]
    rfl
  | ok a =>
    rw [run_liftM_ok, except_bind_ok, show (Except.ok a).bind k = k a from rfl, run_bind]
    cases k a with
    | error e =>
      rw [run_liftM_error, except_bind_error]
      rfl
    | ok b => rw [run_liftM_ok, except_bind_ok]

/-- Exact whole-transition contract for `processBuilderPendingPayments`, at the box the
pure configuration runs: the step on `pureState preState` first runs the checked quorum
chain `builderPaymentQuorum`, and its fault is the run's fault. When the chain binds,
the run returns the uncached box of the original value with only the two fields written
through the source-level writes. Stated at the box level so the fork-choice bridge
consumes it by application; `runPure_of_run_ok` derives the `runPure` form
(`processBuilderPendingPayments_run_appended` reads it). -/
@[characterizes EthCLSpecs.Gloas.processBuilderPendingPayments]
theorem processBuilderPendingPayments_run [Preset] [HasherTag] :
    ∀ (preState : BeaconState),
      (processBuilderPendingPayments (StateTransition := GloasRun)).run (pureState preState)
        = match builderPaymentQuorum preState with
          | .error e => .error (StateTransitionError.arithmetic (reprStr e))
          | .ok quorum => .ok ((), pureState { preState with
              builderPendingWithdrawals := expectedWithdrawals preState quorum,
              builderPendingPayments := expectedPaymentWindow preState }) := by
  intro preState
  -- Re-elaborate the source shape here: the two chained quorum lifts, then the loop and
  -- the window write. The `get` peels by definitional reduction at `pureState preState`
  -- (its state and value are the same box), so the shown shape binds no box of its own,
  -- and the reads spell the plain fields the pure box reduces to.
  show (do
      let tab? ← (getTotalActiveBalance (pureState preState) / slotsPerEpoch)
      let quorum ← (tab? * builderPaymentThresholdNumerator.toNat
        / builderPaymentThresholdDenominator.toNat)
      for i in [0:slotsPerEpoch] do
        if (vget preState.builderPendingPayments i).weight ≥ quorum then
          appendState builderPendingWithdrawals (vget preState.builderPendingPayments i).withdrawal
      modifyState fun state =>
        sszUpdate state with builderPendingPayments :=
          shiftWindow (sszGet state builderPendingPayments) slotsPerEpoch slotsPerEpoch
            (fun _ => (default : BuilderPendingPayment))
      : GloasRun Unit).run (pureState preState)
    = match builderPaymentQuorum preState with
      | .error e => .error (StateTransitionError.arithmetic (reprStr e))
      | .ok quorum => .ok ((), pureState { preState with
          builderPendingWithdrawals := expectedWithdrawals preState quorum,
          builderPendingPayments := expectedPaymentWindow preState })
  rw [run_liftChecked2, builderPaymentQuorum_eq]
  generalize hq : ((getTotalActiveBalance (pureState preState) / slotsPerEpoch).bind
      fun tab => (tab * builderPaymentThresholdNumerator.toNat
        / builderPaymentThresholdDenominator.toNat)) = q
  cases q with
  | error e => rfl
  | ok quorum =>
    dsimp only
    have hloop := builderPendingWithdrawalsLoop_run_eq slotsPerEpoch
      (fun i => (vget preState.builderPendingPayments i).weight ≥ quorum)
      (fun i => (vget preState.builderPendingPayments i).withdrawal) preState
    obtain ⟨a, hbare⟩ := run_of_run_seq_pure _ _ _ hloop
    rw [run_bind, hbare, except_bind_ok]
    unfold expectedWithdrawals qualifyingBuilderWithdrawals expectedPaymentWindow
    rfl

/-- Value-level reading of `processBuilderPendingPayments_run`: when the quorum chain
binds at `quorum`, every withdrawal that weight clears is appended in slot order. The
payment-window half is unchanged from the contract. The chain's `.ok` equation is a
hypothesis, the same shape the contract's `.ok` arm commits to. -/
theorem processBuilderPendingPayments_run_appended [Preset] [HasherTag] (preState : BeaconState)
    (quorum : Gwei) (hq : builderPaymentQuorum preState = .ok quorum) :
    runPure (processBuilderPendingPayments (StateTransition := GloasRun)) preState
      = .ok ((), { preState with
          builderPendingWithdrawals :=
            ⟨preState.builderPendingWithdrawals.val ++
              (qualifyingBuilderWithdrawals preState quorum).toArray⟩,
          builderPendingPayments := expectedPaymentWindow preState }) := by
  have hrun := processBuilderPendingPayments_run preState
  simp only [hq] at hrun
  rw [runPure_of_run_ok hrun]
  congr 1
  have hval : (expectedWithdrawals preState quorum).val =
      preState.builderPendingWithdrawals.val ++
        (qualifyingBuilderWithdrawals preState quorum).toArray := by
    unfold expectedWithdrawals
    rw [progressiveListFoldlPush_val]
  rw [show expectedWithdrawals preState quorum
      = ⟨(expectedWithdrawals preState quorum).val⟩ from by
    cases expectedWithdrawals preState quorum
    rfl]
  rw [hval]

end EthCLSpecs.Proofs.Gloas
