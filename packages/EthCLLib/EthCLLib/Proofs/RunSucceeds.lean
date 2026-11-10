import EthCLLib.Proofs.Preserves

/-!
# `EthCLLib.Proofs.RunSucceeds`: a run that succeeds, with a postcondition

`RunEnsures v act Q` is partial correctness: it says what a successful run gives, and says
nothing when the run throws. `RunSucceeds v act Q` is total correctness. The run from the
uncached box of `v` returns `.ok`, ends on the uncached box of some `w`, and `Q a w` holds.
A theorem that a spec step cannot fail is a `RunSucceeds` fact.

## The rules

The rules have the weakest-precondition form of the `RunEnsures` rules, with one difference
at every check. A partial-correctness rule passes over a `throw`, because a throw has no
successful run to constrain. A total-correctness rule must rule the throw out:

* `throw` has no rule that proves a goal. `runSucceeds_throw` turns the goal into `False`, so
  the branch that throws needs a contradiction from its guard.
* `checkedAdd`, `checkedSucc` and `sszOfArrayM` take the no-overflow or fits-the-cap fact as a
  premise.
* `sszGetIdx` and `liftErr` take a premise that the read or the value is `some` / `.ok`.

`RunSucceeds.and_ensures` combines a `RunSucceeds` fact with a `RunEnsures` fact about the same
run. A frame fact proved once as partial correctness then joins a success proof as it is.

## The walk

`run_succeeds` walks a goal through straight-line code like `run_ensures`, with the same rule
order, the same reducible-transparency matching and the same guarded write rules. Each check
leaves its premise as a side goal next to the continuation, and each `throw` it reaches leaves
`False`. The author closes those, usually with `omega` or from a hypothesis the walk put in
context.

Like `RunEnsures.lean`, this module names no fork constant, so the plain-value check never
visits it.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (HasherTag ErrorConv liftErr getStateRoot sszGetIdx IdxRead
  StateTransitionError throwArithmetic throwListFull checkedAdd checkedSub checkedSucc sszOfArrayM
  Step fuelLoop)
open SizzLean (SSZRepr)
open SizzLean.Cache

/-- The run of `act` from the uncached box of `v` succeeds, ends on the uncached box of some
`w`, and its result and `w` satisfy `Q`. -/
def RunSucceeds {T ε α : Type} [SSZRepr T] [HasherTag] (v : T)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) (Q : α → T → Prop) : Prop :=
  ∃ a w, act.run (pureState v) = .ok (a, pureState w) ∧ Q a w

/-! ## Reading and weakening -/

section Reading

variable {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}
  {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}

/-- A weaker postcondition follows from a stronger one. -/
theorem RunSucceeds.weaken {P : α → T → Prop} (h : RunSucceeds v act P)
    (hPQ : ∀ a w, P a w → Q a w) : RunSucceeds v act Q :=
  let ⟨a, w, hr, hp⟩ := h
  ⟨a, w, hr, hPQ a w hp⟩

/-- A success fact and a partial-correctness fact about the same run combine: the run that
succeeds is a successful run, so the partial-correctness postcondition holds of it too. -/
theorem RunSucceeds.and_ensures {P : α → T → Prop} (hs : RunSucceeds v act P)
    (he : RunEnsures v act Q) : RunSucceeds v act (fun a w => P a w ∧ Q a w) := by
  obtain ⟨a, w, hr, hp⟩ := hs
  -- `RunEnsures` names the end state by the end box's view, which is `w` by `rfl`.
  exact ⟨a, w, hr, hp, (he a _ hr).2⟩

/-- The value-level reading: `runPure` returns `.ok` with a result and value that satisfy the
postcondition. The form a fork-body theorem states, over plain values. -/
theorem RunSucceeds.runPure_ok (h : RunSucceeds v act Q) :
    ∃ a w, runPure act v = .ok (a, w) ∧ Q a w := by
  obtain ⟨a, w, hr, hq⟩ := h
  exact ⟨a, w, by rw [runPure_eq, hr]; rfl, hq⟩

/-- Congruence: the triple transfers along an equality of actions. -/
theorem runSucceeds_congr {act' : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (heq : act = act') (h : RunSucceeds v act Q) : RunSucceeds v act' Q :=
  heq ▸ h

end Reading

/-! ## Leaves -/

section Leaves

variable {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}

/-- `pure a` succeeds with `a` and the start. -/
theorem runSucceeds_pure {a : α} {Q : α → T → Prop} (h : Q a v) :
    RunSucceeds v (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q :=
  ⟨a, v, rfl, h⟩

/-- `throw` never succeeds: the goal becomes `False`, which the branch's guard must refute. -/
theorem runSucceeds_throw (e : ε) {Q : α → T → Prop} (h : False) :
    RunSucceeds v (throw e : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q :=
  h.elim

/-- `get` succeeds with the start box and keeps it. -/
theorem runSucceeds_get {Q : SSZ.Box HasherTag.H T → T → Prop} (h : Q (pureState v) v) :
    RunSucceeds v (get : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)) Q :=
  ⟨_, v, rfl, h⟩

/-- `getThe`, the explicit-type `get`. -/
theorem runSucceeds_getThe {Q : SSZ.Box HasherTag.H T → T → Prop} (h : Q (pureState v) v) :
    RunSucceeds v (getThe (SSZ.Box HasherTag.H T) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)) Q :=
  ⟨_, v, rfl, h⟩

/-- `set` of a rebuilt box lands on that box. -/
theorem runSucceeds_set {w : T} {Q : PUnit → T → Prop} (h : Q ⟨⟩ w) :
    RunSucceeds v (set (pureState w) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q :=
  ⟨⟨⟩, w, rfl, h⟩

/-- `modifyThe` through a writer that maps the start box to the uncached box of some `w`. -/
theorem runSucceeds_modifyThe {f : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T}
    {Q : PUnit → T → Prop} (h : ∃ w, f (pureState v) = pureState w ∧ Q ⟨⟩ w) :
    RunSucceeds v (modifyThe (SSZ.Box HasherTag.H T) f :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q := by
  obtain ⟨w, hw, hq⟩ := h
  refine ⟨⟨⟩, w, ?_, hq⟩
  rw [show ((modifyThe (SSZ.Box HasherTag.H T) f : StateT (SSZ.Box HasherTag.H T)
      (Except ε) PUnit).run (pureState v)) = .ok (⟨⟩, f (pureState v)) from rfl, hw]

/-- A write of a box held in a variable. -/
theorem runSucceeds_modifyThe_const {b : SSZ.Box HasherTag.H T} {Q : PUnit → T → Prop}
    (h : ∃ w, b = pureState w ∧ Q ⟨⟩ w) :
    RunSucceeds v (modifyThe (SSZ.Box HasherTag.H T) (fun _ => b) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q :=
  runSucceeds_modifyThe h

/-- A write through `f`, naming the new state by the written box's view. -/
theorem runSucceeds_modifyThe_view {f : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T}
    {Q : PUnit → T → Prop} (hf : f (pureState v) = pureState (f (pureState v)).view)
    (h : Q ⟨⟩ (f (pureState v)).view) :
    RunSucceeds v (modifyThe (SSZ.Box HasherTag.H T) f :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q :=
  runSucceeds_modifyThe ⟨_, hf, h⟩

/-- `set b` of a box that is the uncached box of its own view. -/
theorem runSucceeds_set_view {b : SSZ.Box HasherTag.H T} {Q : PUnit → T → Prop}
    (hb : b = pureState b.view) (h : Q ⟨⟩ b.view) :
    RunSucceeds v (set b : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q := by
  rw [hb]
  exact runSucceeds_set h

/-- `getStateRoot` succeeds with the start value's root and keeps the uncached box. -/
theorem runSucceeds_getStateRoot {Q : ByteArray → T → Prop}
    (h : Q (SizzLean.SSZ.hashTreeRoot HasherTag.H v) v) :
    RunSucceeds v (getStateRoot (S := SSZ.Box HasherTag.H T) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) ByteArray) Q := by
  refine ⟨_, v, ?_, h⟩
  rw [show ((getStateRoot (S := SSZ.Box HasherTag.H T) : StateT (SSZ.Box HasherTag.H T)
      (Except ε) ByteArray).run (pureState v))
      = .ok (((pureState v).hashTreeRoot).1, ((pureState v).hashTreeRoot).2) from rfl,
    SizzLean.Proofs.hashTreeRoot_uncachedBox]

/-- `liftErr x` succeeds when `x` is `.ok`, with `x`'s value and the start. -/
theorem runSucceeds_liftErr {ε' : Type} [ErrorConv ε' ε] {x : Except ε' α} {Q : α → T → Prop}
    (hok : ∃ b, x = .ok b) (h : ∀ b, x = .ok b → Q b v) :
    RunSucceeds v (liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
      StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q := by
  obtain ⟨b, hb⟩ := hok
  exact ⟨b, v, run_liftErr_of_ok (a := b) _ _ (by rw [hb]; rfl), h b hb⟩

/-- `sszGetIdx xs i` succeeds when the read is `some`, with the element and the start. -/
theorem runSucceeds_sszGetIdx {ρ : Type} [IdxRead ρ α] [ErrorConv IndexError ε] (xs : ρ)
    (i : Nat) {Q : α → T → Prop} (hsome : ∃ y, IdxRead.get? xs i = some y)
    (h : ∀ y, IdxRead.get? xs i = some y → Q y v) :
    RunSucceeds v (sszGetIdx (E := ε) (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) xs i) Q := by
  obtain ⟨y, hy⟩ := hsome
  exact ⟨y, v, run_sszGetIdx_some xs i _ hy, h y hy⟩

end Leaves

/-! ## Combinators -/

section Combinators

variable {T ε α β : Type} [SSZRepr T] [HasherTag] {v : T}

/-- Bind, in weakest-precondition form: the first action succeeds into a state from which the
continuation succeeds into `Q`. -/
theorem runSucceeds_bind {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β} {Q : β → T → Prop}
    (h : RunSucceeds v x (fun a w => RunSucceeds w (f a) Q)) : RunSucceeds v (x >>= f) Q := by
  obtain ⟨a, u, hx, b, w, hf, hq⟩ := h
  refine ⟨b, w, ?_, hq⟩
  rw [run_bind, hx]
  exact hf

/-- `get` then a continuation on the read box. -/
theorem runSucceeds_get_bind
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}
    (h : RunSucceeds v (g (pureState v)) Q) : RunSucceeds v (get >>= g) Q :=
  runSucceeds_bind (runSucceeds_get h)

/-- `if`: each branch under its own guard. A branch that throws needs its guard refuted. -/
theorem runSucceeds_ite {c : Prop} [Decidable c] {x y : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {Q : α → T → Prop} (hx : c → RunSucceeds v x Q) (hy : ¬c → RunSucceeds v y Q) :
    RunSucceeds v (if c then x else y) Q := by
  split
  · exact hx (by assumption)
  · exact hy (by assumption)

/-- Dependent `if`: each branch under its own guard. -/
theorem runSucceeds_dite {c : Prop} [Decidable c]
    {t : c → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {e : ¬c → StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}
    (ht : ∀ hc : c, RunSucceeds v (t hc) Q) (he : ∀ hc : ¬c, RunSucceeds v (e hc) Q) :
    RunSucceeds v (dite c t e) Q := by
  split
  · exact ht (by assumption)
  · exact he (by assumption)

end Combinators

/-! ## Leaves for the spec helpers -/

/-- The sum of two `UInt64`s that fit does not wrap: the no-overflow premise of
`runSucceeds_checkedAdd` from a `Nat` bound. -/
theorem uint64_not_add_lt_of_toNat {a b : UInt64} (h : a.toNat + b.toNat < UInt64.size) :
    ¬ a + b < a := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega


section HelperLeaves

variable {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}

/-- `throwArithmetic` never succeeds. -/
theorem runSucceeds_throwArithmetic [ErrorConv StateTransitionError ε] (descr : String)
    {Q : α → T → Prop} (h : False) :
    RunSucceeds v (throwArithmetic descr : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q :=
  h.elim

/-- `throwListFull` never succeeds. -/
theorem runSucceeds_throwListFull [ErrorConv StateTransitionError ε] (field : String)
    {Q : α → T → Prop} (h : False) :
    RunSucceeds v (throwListFull field : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q :=
  h.elim

/-- `checkedAdd` succeeds when the sum does not wrap, with the sum and the start. -/
theorem runSucceeds_checkedAdd [ErrorConv StateTransitionError ε] (a b : UInt64) (descr : String)
    {Q : UInt64 → T → Prop} (hno : ¬ a + b < a) (h : Q (a + b) v) :
    RunSucceeds v (checkedAdd a b descr : StateT (SSZ.Box HasherTag.H T) (Except ε) UInt64) Q :=
  runSucceeds_ite (fun hc => absurd hc hno) (fun _ => runSucceeds_pure h)

/-- `checkedSub` succeeds when the difference does not underflow. -/
theorem runSucceeds_checkedSub [ErrorConv StateTransitionError ε] (a b : UInt64) (descr : String)
    {Q : UInt64 → T → Prop} (hno : ¬ b > a) (h : Q (a - b) v) :
    RunSucceeds v (checkedSub a b descr : StateT (SSZ.Box HasherTag.H T) (Except ε) UInt64) Q :=
  runSucceeds_ite (fun hc => absurd hc hno) (fun _ => runSucceeds_pure h)

/-- `checkedSucc` succeeds below `2 ^ 64 - 1`, with the successor. -/
theorem runSucceeds_checkedSucc [ErrorConv StateTransitionError ε] (i : Nat) (descr : String)
    {Q : { j : Nat // j = i + 1 ∧ j < UInt64.size } → T → Prop} (hi : i + 1 < UInt64.size)
    (h : Q ⟨i + 1, rfl, hi⟩ v) :
    RunSucceeds v (checkedSucc i descr :
      StateT (SSZ.Box HasherTag.H T) (Except ε) { j : Nat // j = i + 1 ∧ j < UInt64.size }) Q :=
  runSucceeds_dite (fun _ => runSucceeds_pure h) (fun hc => absurd hi hc)

/-- `sszOfArrayM` succeeds when the array fits under the cap, with a list whose elements are
the array's. -/
theorem runSucceeds_sszOfArrayM [ErrorConv StateTransitionError ε] {β : Type} {cap : Nat}
    (field : String) (a : Array β) {Q : SizzLean.Repr.SSZList β cap → T → Prop}
    (hfit : a.size ≤ cap) (h : ∀ l : SizzLean.Repr.SSZList β cap, l.val = a → Q l v) :
    RunSucceeds v (sszOfArrayM (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) (cap := cap)
      field a) Q := by
  unfold sszOfArrayM SizzLean.Repr.SSZList.ofArray?
  rw [dite_eq_left hfit]
  exact runSucceeds_pure (h _ rfl)

end HelperLeaves

/-! ## Loops -/

section Loops

variable {T ε α β : Type} [SSZRepr T] [HasherTag]

/-- `List.forIn` with an invariant on the list still to walk. -/
theorem runSucceeds_forIn_list {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : List α → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ x rest b w, I (x :: rest) b w → RunSucceeds w (f x b) (loopStepPost (I rest) Q))
    (hnil : ∀ b w, I [] b w → Q b w) :
    ∀ (l : List α) (init : β) (v : T), I l init v → RunSucceeds v (forIn l init f) Q := by
  intro l
  induction l with
  | nil =>
    intro init v hI
    rw [List.forIn_nil]
    exact runSucceeds_pure (hnil init v hI)
  | cons x rest ih =>
    intro init v hI
    rw [List.forIn_cons]
    refine runSucceeds_bind ((hstep x rest init v hI).weaken ?_)
    intro step w hw
    cases step with
    | done b => exact runSucceeds_pure hw
    | yield b => exact ih b w hw

/-- `List.forIn` with an invariant on the accumulator and state alone. -/
theorem runSucceeds_forIn_list_inv
    {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : β → T → Prop) (hstep : ∀ x b w, I b w → RunSucceeds w (f x b) (loopStepPost I I))
    (l : List α) (init : β) {v : T} (hinit : I init v) :
    RunSucceeds v (forIn l init f) I :=
  runSucceeds_forIn_list (fun _ => I) I (fun x _ b w hI => hstep x b w hI) (fun _ _ h => h)
    l init v hinit

/-- The walk of `List.range' s k`, with an invariant indexed by the next position. -/
private theorem runSucceeds_forIn_range'
    {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)} (n : Nat)
    (I : Nat → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ i b w, i < n → I i b w → RunSucceeds w (f i b) (loopStepPost (I (i + 1)) Q))
    (hend : ∀ b w, I n b w → Q b w) :
    ∀ (k s : Nat) (b : β) (w : T), s + k = n → I s b w →
      RunSucceeds w (forIn (List.range' s k) b f) Q := by
  intro k
  induction k with
  | zero =>
    intro s b w hs hI
    have hsn : s = n := by omega
    subst hsn
    rw [List.range'_zero, List.forIn_nil]
    exact runSucceeds_pure (hend b w hI)
  | succ k ih =>
    intro s b w hs hI
    rw [List.range'_succ, List.forIn_cons]
    refine runSucceeds_bind ((hstep s b w (by omega) hI).weaken ?_)
    intro step w' hw
    cases step with
    | done b' => exact runSucceeds_pure hw
    | yield b' => exact ih (s + 1) b' w' (by omega) hw

/-- `for i in [0:n]` with an invariant that sees the index. -/
theorem runSucceeds_forIn_range
    {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)} (n : Nat)
    (I : Nat → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ i b w, i < n → I i b w → RunSucceeds w (f i b) (loopStepPost (I (i + 1)) Q))
    (hend : ∀ b w, I n b w → Q b w) (init : β) {v : T} (hinit : I 0 init v) :
    RunSucceeds v (forIn [0:n] init f) Q := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl]
  exact runSucceeds_forIn_range' n I Q hstep hend n 0 init v (by omega) hinit

/-- `for i in [0:n]` with an invariant on the accumulator and state alone. -/
theorem runSucceeds_forIn_range_inv
    {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)} (n : Nat)
    (I : β → T → Prop) (hstep : ∀ i b w, i < n → I b w → RunSucceeds w (f i b) (loopStepPost I I))
    (init : β) {v : T} (hinit : I init v) :
    RunSucceeds v (forIn [0:n] init f) I :=
  runSucceeds_forIn_range n (fun _ => I) I hstep (fun _ _ h => h) init hinit

/-- `Array.forIn` with an invariant on the array still to walk, read through `toList`. -/
theorem runSucceeds_forIn_array
    {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : List α → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ x rest b w, I (x :: rest) b w → RunSucceeds w (f x b) (loopStepPost (I rest) Q))
    (hnil : ∀ b w, I [] b w → Q b w) (xs : Array α) (init : β) {v : T} (hinit : I xs.toList init v) :
    RunSucceeds v (forIn xs init f) Q := by
  rw [← Array.forIn_toList]
  exact runSucceeds_forIn_list I Q hstep hnil xs.toList init v hinit

/-- `Array.forIn` with an invariant on the accumulator and state alone. -/
theorem runSucceeds_forIn_array_inv
    {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : β → T → Prop) (hstep : ∀ x b w, I b w → RunSucceeds w (f x b) (loopStepPost I I))
    (xs : Array α) (init : β) {v : T} (hinit : I init v) :
    RunSucceeds v (forIn xs init f) I := by
  rw [← Array.forIn_toList]
  exact runSucceeds_forIn_list_inv I hstep xs.toList init hinit

/-- `fuelLoop` with an invariant that sees the fuel left. Each step from fuel `n + 1` must
re-establish the invariant at `n` or end in `Q`. The `exhausted` value must satisfy `Q` from
the invariant at fuel `0`; an invariant that bounds the work left by the fuel makes that case
impossible. -/
theorem runSucceeds_fuelLoop {step : β → StateT (SSZ.Box HasherTag.H T) (Except ε) (Step β α)}
    {exhausted : α} (I : Nat → β → T → Prop) (Q : α → T → Prop)
    (hstep : ∀ n b w, I (n + 1) b w → RunSucceeds w (step b) (fuelStepPost (I n) Q))
    (hex : ∀ b w, I 0 b w → Q exhausted w) :
    ∀ (fuel : Nat) (init : β) (v : T), I fuel init v →
      RunSucceeds v (fuelLoop fuel init exhausted step) Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro init v hI
    unfold fuelLoop
    exact runSucceeds_pure (hex init v hI)
  | succ fuel ih =>
    intro init v hI
    unfold fuelLoop
    refine runSucceeds_bind ((hstep fuel init v hI).weaken ?_)
    intro r w hw
    cases r with
    | done a => exact runSucceeds_pure hw
    | next b => exact ih b w hw

end Loops

/-! ## Loops that carry a box

The success counterparts of the `BoxInv` loops in `Preserves.lean`: a spec body threads a
local box through a loop, the threaded state stays the start, and the invariant lives on the
carried box. The invariant sees the index, because a loop over the registry writes entry `i`
at step `i`, and a bound on that entry holds before step `i` and changes after it. -/

section BoxLoops

variable {T ε : Type} [SSZRepr T] [HasherTag]

/-- `for i in [0:n]` with a box accumulator and an invariant on the carried value that sees the
index: step `i` takes a carried value in `I i` to one in `I (i + 1)`, and leaves the threaded
state alone. -/
theorem runSucceeds_forIn_range_box (I : Nat → T → Prop) (n : Nat)
    {f : Nat → SSZ.Box HasherTag.H T →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T))}
    (hstep : ∀ i s w, i < n → I i s →
      RunSucceeds w (f i (pureState s)) (loopStepPost (BoxInv (I (i + 1)) w) (BoxInv (I n) w)))
    (s v : T) (hs : I 0 s) :
    RunSucceeds v (forIn [0:n] (pureState s) f) (BoxInv (I n) v) :=
  runSucceeds_forIn_range n (fun i b w => BoxInv (I i) v b w) (BoxInv (I n) v)
    (fun i b w hi hI => by
      obtain ⟨hw, s', hb, hs'⟩ := hI
      subst hw hb
      exact hstep i s' w hi hs')
    (fun _ _ h => h) _ ⟨rfl, s, rfl, hs⟩

end BoxLoops

/-! ## The `Except` layer

Some spec helpers are pure functions into `Except`, called through `liftErr`. Their success is
an `.ok` value, and a `mapM` over a list or array of such calls succeeds when every call does. -/

section ExceptLayer

variable {ε α β : Type}

/-- A `List.mapM` in `Except` succeeds when every call does, with one result per element, and
every result satisfies `P` when every call's result does. -/
theorem except_list_mapM_ok {f : α → Except ε β} {P : β → Prop} :
    ∀ l : List α, (∀ x ∈ l, ∃ b, f x = .ok b ∧ P b) →
      ∃ r, l.mapM f = .ok r ∧ r.length = l.length ∧ ∀ y ∈ r, P y
  | [], _ => ⟨[], rfl, rfl, fun _ h => nomatch h⟩
  | x :: l, h => by
    obtain ⟨b, hb, hp⟩ := h x List.mem_cons_self
    obtain ⟨r, hr, hlen, hps⟩ :=
      except_list_mapM_ok l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨b :: r, ?_, by simp [hlen], ?_⟩
    · rw [List.mapM_cons, hb, hr]
      rfl
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hp
      · exact hps y hy

/-- An `Array.mapM` in `Except` succeeds when every call does: the array walk is the list walk
of its `toList`. -/
theorem except_array_mapM_ok {f : α → Except ε β} {P : β → Prop} (xs : Array α)
    (h : ∀ x ∈ xs, ∃ b, f x = .ok b ∧ P b) : ∃ r, xs.mapM f = .ok r ∧ ∀ y ∈ r, P y := by
  obtain ⟨r, hr, _, hps⟩ :=
    except_list_mapM_ok xs.toList (fun x hx => h x (Array.mem_toList_iff.mp hx))
  refine ⟨r.toArray, ?_, fun y hy => hps y (List.mem_toArray.mp hy)⟩
  rw [Array.mapM_eq_mapM_toList, hr]
  rfl

/-- A `List.forIn` in `Except` succeeds when every step does, from any accumulator that
satisfies the invariant `I`, and the result satisfies `I`. -/
theorem except_list_forIn_ok {f : α → β → Except ε (ForInStep β)} (I : β → Prop) :
    ∀ l : List α, (∀ x ∈ l, ∀ b, I b → ∃ r, f x b = .ok r ∧ I (ForInStep.value r)) →
      ∀ init, I init → ∃ b, forIn l init f = .ok b ∧ I b
  | [], _, init, hinit => ⟨init, rfl, hinit⟩
  | x :: l, h, init, hinit => by
    obtain ⟨r, hr, hI⟩ := h x List.mem_cons_self init hinit
    rw [List.forIn_cons, hr]
    cases r with
    | done b => exact ⟨b, rfl, hI⟩
    | yield b =>
      exact except_list_forIn_ok I l (fun y hy => h y (List.mem_cons_of_mem _ hy)) b hI

/-- An `Array.forIn` in `Except`, as the list walk of its `toList`. -/
theorem except_array_forIn_ok {f : α → β → Except ε (ForInStep β)} (I : β → Prop) (xs : Array α)
    (h : ∀ x ∈ xs, ∀ b, I b → ∃ r, f x b = .ok r ∧ I (ForInStep.value r)) (init : β)
    (hinit : I init) : ∃ b, forIn xs init f = .ok b ∧ I b := by
  rw [← Array.forIn_toList]
  exact except_list_forIn_ok I xs.toList (fun x hx => h x (Array.mem_toList_iff.mp hx)) init hinit

/-- An `Array.forIn` in `Except` followed by a continuation: the walk succeeds into an
accumulator in `I`, and the continuation succeeds from every such accumulator. The form that
matches a `do` block whose loop is followed by a `return`. -/
theorem except_array_forIn_bind_ok {γ : Type} {f : α → β → Except ε (ForInStep β)}
    {g : β → Except ε γ} {Q : γ → Prop} (I : β → Prop) {xs : Array α} {init : β}
    (h : ∀ x ∈ xs, ∀ b, I b → ∃ r, f x b = .ok r ∧ I (ForInStep.value r)) (hinit : I init)
    (hg : ∀ b, I b → ∃ c, g b = .ok c ∧ Q c) : ∃ c, (forIn xs init f >>= g) = .ok c ∧ Q c := by
  obtain ⟨b, hb, hI⟩ := except_array_forIn_ok I xs h init hinit
  rw [hb]
  exact hg b hI

end ExceptLayer

/-! ## The tactic -/

/-- One structural rule of the `run_succeeds` walk, as `run_ensures_step` is for
`run_ensures`. Each check leaves its premise as a side goal. -/
syntax "run_succeeds_step" : tactic

/-- The write rules of the `run_succeeds` walk, tried only when every structural rule fails. -/
syntax "run_succeeds_fallback" : tactic

macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_bind ?_)
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_dite (fun _ => ?_) (fun _ => ?_))
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| (with_reducible refine runSucceeds_ite (fun hc => ?_) (fun hc => ?_))
              <;> try (simp [box_reduce] at hc; done))
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_liftErr ?_ (fun _ _ => ?_))
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_sszGetIdx _ _ ?_ (fun _ _ => ?_))
macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_getStateRoot ?_)
macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_set ?_)
macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_get ?_)
macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_getThe ?_)
macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_pure ?_)
macro_rules
  | `(tactic| run_succeeds_step) => `(tactic| with_reducible refine runSucceeds_throw _ ?_)
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_sszOfArrayM _ _ ?_ (fun _ _ => ?_))
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_throwListFull _ ?_)
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_throwArithmetic _ ?_)
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_checkedSucc _ _ ?_ ?_)
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_checkedSub _ _ _ ?_ ?_)
macro_rules
  | `(tactic| run_succeeds_step) =>
    `(tactic| with_reducible refine runSucceeds_checkedAdd _ _ _ ?_ ?_)

macro_rules
  | `(tactic| run_succeeds_fallback) => `(tactic| refine runSucceeds_modifyThe_const ?_)
macro_rules
  | `(tactic| run_succeeds_fallback) => `(tactic| refine runSucceeds_set_view rfl ?_)
macro_rules
  | `(tactic| run_succeeds_fallback) => `(tactic| refine runSucceeds_modifyThe_view rfl ?_)

open Lean Elab Tactic Meta in
/-- Guard for the write rules, as `run_ensures_is_write`: the goal is a `RunSucceeds` triple
whose action is, at its head after `whnfCore`, a `modifyThe`, a fork's `modifyState`, or a
`set`. -/
elab "run_succeeds_is_write" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOf ``RunSucceeds do throwError "run_succeeds_is_write: not a RunSucceeds goal"
  let act ← whnfCore (t.getArg! 6)
  let isModifyState : Name → Bool
    | .str _ s => s == "modifyState"
    | _ => false
  let ok : Bool := match act.getAppFn.constName? with
    | some n => n == ``modifyThe || n == ``MonadStateOf.set || n == ``MonadState.set ||
        isModifyState n
    | none => false
  unless ok do throwError "run_succeeds_is_write: the action is not a write"

open Lean Elab Tactic Meta in
/-- Beta-reduce the head of the goal and of a triple's action, as `run_ensures_beta`. -/
elab "run_succeeds_beta" : tactic => liftMetaTactic fun g => do
  let t := (← instantiateMVars (← g.getType)).headBeta
  let t ← if t.isAppOfArity ``RunSucceeds 8 then do
      let act ← whnfCore (t.getArg! 6)
      pure (mkAppN t.getAppFn (t.getAppArgs.set! 6 act))
    else pure t
  return [← g.replaceTargetDefEq t]

open Lean Elab Tactic Meta in
/-- Tidy a postcondition leaf the walk left, as `run_ensures_tidy`. A goal that is still a
`RunSucceeds` triple is left alone. -/
elab "run_succeeds_tidy" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOf ``RunSucceeds do
    evalTactic (← `(tactic| try simp only [loopStepPost_yield, loopStepPost_done,
      fuelStepPost_next, fuelStepPost_done, SizzLean.Proofs.view_uncachedBox,
      uncachedSSZ_ofValue_view]))

/-- Walk a `RunSucceeds` goal through straight-line code, as `run_ensures` walks a `RunEnsures`
goal. The walk leaves three kinds of goal: postcondition leaves, the premises of the checks it
passed (`¬ a + b < a`, `∃ y, get? xs i = some y`, `∃ b, x = .ok b`, `a.size ≤ cap`,
`i + 1 < UInt64.size`), and `False` for each `throw` whose guard `simp` did not refute. It stops
at a call, a loop and a `match`, as `run_ensures` does. -/
macro "run_succeeds" : tactic => `(tactic|
  (repeat' (run_succeeds_beta; first | run_succeeds_step |
    (run_succeeds_is_write; run_succeeds_fallback)))
  <;> run_succeeds_tidy)

/-! ## Examples -/

/-- The `process_slots` shape, now with success: a counter that a loop advances through a
checked add reaches `start + n` without a fault, when the sum stays below `2 ^ 64`. -/
example [HasherTag] (n : Nat) (start : UInt64) (hn : start.toNat + n < 2 ^ 64) :
    RunSucceeds start
      (forIn [0:n] PUnit.unit (fun _ _ => do
        let s ← getThe (SSZ.Box HasherTag.H UInt64)
        let t ← checkedAdd s.view 1 "counter"
        modifyThe (SSZ.Box HasherTag.H UInt64) (fun _ => pureState t)
        pure (ForInStep.yield PUnit.unit)) :
        StateT (SSZ.Box HasherTag.H UInt64) (Except StateTransitionError) PUnit)
      (fun _ w => w.toNat = start.toNat + n) := by
  refine runSucceeds_forIn_range n
    (fun (i : Nat) (_ : PUnit) (w : UInt64) => w.toNat = start.toNat + i) _ ?_
    (fun _ _ h => h) _ (by simp)
  intro i b w hi hw
  run_succeeds
  · exact uint64_not_add_lt_of_toNat (by rw [UInt64.toNat_one]; unfold UInt64.size; omega)
  · rw [UInt64.toNat_add, hw, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    omega

end EthCLLib.Proofs
