import EthCLLib.Proofs.RunEnsures
import EthCLLib.Spec.Loop

/-!
# `EthCLLib.Proofs.Preserves`: invariants that every successful run keeps

`Preserves P act` says: from any start that satisfies `P`, every successful run of `act` ends
on an uncached box whose value satisfies `P` again. It is the `RunEnsures` triple
(`EthCLLib/Proofs/RunEnsures.lean`) with the same predicate before and after. A theorem that a
spec step keeps a state invariant, or keeps a set of fields at fixed values, is a `Preserves`
fact: the second kind takes `P w := proj w = c`, for every `c`.

The module holds three groups:

* `Preserves` and its rules: reading it at a call site (`Preserves.bind_run`), and the loop
  forms whose invariant is `P` itself.
* `RunEnsures` leaves for the spec helpers that are plain definitions, so the reducible-only
  `run_ensures` walk stops at them: `getThe`, the checked `uint64` operators,
  `throwArithmetic`, `throwListFull`, `sszOfArrayM`, and a write of a box held in a variable.
* Loop rules for `fuelLoop` and for `for h : i in [0:n]` (`forIn'`), and invariant lemmas for
  the pure `Id.run` loops a spec body runs inside `modifyState`.

Like the rest of the framework's proof toolkit, its statements name no fork constant.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (HasherTag ErrorConv liftErr StateTransitionError throwArithmetic
  throwListFull checkedAdd checkedSub checkedMul checkedSucc sszOfArrayM Step fuelLoop)
open SizzLean (SSZRepr)
open SizzLean.Cache

/-- Every successful run of `act` from a start that satisfies `P` ends on an uncached box whose
value satisfies `P`. -/
def Preserves {T ε α : Type} [SSZRepr T] [HasherTag] (P : T → Prop)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) : Prop :=
  ∀ v, P v → RunEnsures v act (fun _ w => P w)

section PreservesRules

variable {T ε α β : Type} [SSZRepr T] [HasherTag] {P : T → Prop} {v : T}

/-- Read a `Preserves` fact at a call site: the call keeps `P`, so the rest of the body runs
from a state that satisfies `P`. -/
theorem Preserves.run {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}
    (hx : Preserves P x) (hv : P v) (hq : ∀ a w, P w → Q a w) : RunEnsures v x Q :=
  (hx v hv).weaken hq

/-- Read a `Preserves` fact at a call site followed by more code: the weakest-precondition
bind with the first action's fact supplied. -/
theorem Preserves.bind_run {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β} {Q : β → T → Prop}
    (hx : Preserves P x) (hv : P v) (hk : ∀ a w, P w → RunEnsures w (f a) Q) :
    RunEnsures v (x >>= f) Q :=
  runEnsures_bind ((hx v hv).weaken hk)

/-- A weaker invariant follows when every `P'` state reaching the call is a `P` state and every
`P` state it leaves is a `P'` state. Used to read a fact about a stronger invariant. -/
theorem Preserves.of_imp {P' : T → Prop} {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hx : Preserves P x) (h : ∀ w, P' w → P w) (h' : ∀ w, P w → P' w) : Preserves P' x :=
  fun w hw => (hx w (h w hw)).weaken fun _ w' hw' => h' w' hw'

/-- A step body that keeps `P` meets the loop rules' step condition for the invariant `P`,
whichever way the step ends. -/
theorem Preserves.loopStep {x : StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (hx : Preserves P x) (hv : P v) :
    RunEnsures v x (loopStepPost (fun (_ : β) w => P w) (fun _ w => P w)) :=
  (hx v hv).weaken fun step w hw => by cases step <;> exact hw

/-- `for i in [0:n]` keeps `P` when every step does. -/
theorem Preserves.forIn_range {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (n : Nat) (init : β) (hf : ∀ i b, i < n → Preserves P (f i b)) :
    Preserves P (forIn [0:n] init f) :=
  fun _ hv => runEnsures_forIn_range_inv n (fun _ w => P w)
    (fun i b _ hi hw => (hf i b hi).loopStep hw) init hv

/-- `List.forIn` keeps `P` when every step does. -/
theorem Preserves.forIn_list {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (l : List α) (init : β) (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn l init f) :=
  fun _ hv => runEnsures_forIn_list_inv (fun _ w => P w)
    (fun x b _ hw => (hf x b).loopStep hw) l init hv

/-- `Array.forIn` keeps `P` when every step does. -/
theorem Preserves.forIn_array {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (xs : Array α) (init : β) (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
  fun _ hv => runEnsures_forIn_array_inv (fun _ w => P w)
    (fun x b _ hw => (hf x b).loopStep hw) xs init hv

/-- `ForM.forM` over an array keeps `P` when the handler does. -/
theorem Preserves.forM_array {handler : α → StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit}
    (xs : Array α) (hf : ∀ x, Preserves P (handler x)) : Preserves P (ForM.forM xs handler) :=
  fun _ hv => runEnsures_forM_array_inv P (fun x w hw => hf x w hw) xs hv

/-- `act` never writes the threaded state: every successful run ends on its start. An
accessor that reads the state and may reject, such as `get_block_root`, has this form. -/
def ReadsOnly (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) : Prop :=
  ∀ v, RunEnsures v act (fun _ w => w = v)

/-- A read-only step keeps every invariant. -/
theorem ReadsOnly.preserves {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α} (h : ReadsOnly x) :
    Preserves P x :=
  fun v hv => (h v).weaken fun _ _ hw => hw ▸ hv

end PreservesRules

/-! ## Leaves for the spec helpers -/

section HelperLeaves

variable {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}

/-- `getThe`, the explicit-type `get` that `appendState` and `setOrAppendState` read with. -/
theorem runEnsures_getThe {Q : SSZ.Box HasherTag.H T → T → Prop} (h : Q (pureState v) v) :
    RunEnsures v (getThe (SSZ.Box HasherTag.H T) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)) Q :=
  runEnsures_get h

/-- `throwArithmetic` never succeeds. -/
theorem runEnsures_throwArithmetic [ErrorConv StateTransitionError ε] (descr : String)
    {Q : α → T → Prop} :
    RunEnsures v (throwArithmetic descr : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q :=
  runEnsures_liftErr fun _ h => nomatch h

/-- `throwListFull` never succeeds. -/
theorem runEnsures_throwListFull [ErrorConv StateTransitionError ε] (field : String)
    {Q : α → T → Prop} :
    RunEnsures v (throwListFull field : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q :=
  runEnsures_liftErr fun _ h => nomatch h

/-- `checkedAdd`: on success it returns the sum, which did not wrap, and keeps the start. -/
theorem runEnsures_checkedAdd [ErrorConv StateTransitionError ε] (a b : UInt64) (descr : String)
    {Q : UInt64 → T → Prop} (h : ¬ a + b < a → Q (a + b) v) :
    RunEnsures v (checkedAdd a b descr : StateT (SSZ.Box HasherTag.H T) (Except ε) UInt64) Q :=
  runEnsures_ite (fun _ => runEnsures_throwArithmetic descr) (fun hc => runEnsures_pure (h hc))

/-- `checkedSub`: on success it returns the difference, which did not underflow. -/
theorem runEnsures_checkedSub [ErrorConv StateTransitionError ε] (a b : UInt64) (descr : String)
    {Q : UInt64 → T → Prop} (h : ¬ b > a → Q (a - b) v) :
    RunEnsures v (checkedSub a b descr : StateT (SSZ.Box HasherTag.H T) (Except ε) UInt64) Q :=
  runEnsures_ite (fun _ => runEnsures_throwArithmetic descr) (fun hc => runEnsures_pure (h hc))

/-- `checkedMul`: on success it returns the product, which did not overflow. -/
theorem runEnsures_checkedMul [ErrorConv StateTransitionError ε] (a b : UInt64) (descr : String)
    {Q : UInt64 → T → Prop} (h : ¬ (a != 0 && a * b / a != b) = true → Q (a * b) v) :
    RunEnsures v (checkedMul a b descr : StateT (SSZ.Box HasherTag.H T) (Except ε) UInt64) Q :=
  runEnsures_ite (fun _ => runEnsures_throwArithmetic descr) (fun hc => runEnsures_pure (h hc))

/-- `checkedSucc`: on success it returns the successor, still below `2 ^ 64`. -/
theorem runEnsures_checkedSucc [ErrorConv StateTransitionError ε] (i : Nat) (descr : String)
    {Q : { j : Nat // j = i + 1 ∧ j < UInt64.size } → T → Prop}
    (h : ∀ hi : i + 1 < UInt64.size, Q ⟨i + 1, rfl, hi⟩ v) :
    RunEnsures v (checkedSucc i descr :
      StateT (SSZ.Box HasherTag.H T) (Except ε) { j : Nat // j = i + 1 ∧ j < UInt64.size }) Q :=
  runEnsures_dite (fun hi => runEnsures_pure (h hi)) (fun _ => runEnsures_throwArithmetic descr)

/-- `sszOfArrayM`, the spec's `List[T, N](a)`: on success it returns a list whose elements are
`a`'s, and keeps the start. -/
theorem runEnsures_sszOfArrayM [ErrorConv StateTransitionError ε] {β : Type} {cap : Nat}
    (field : String) (a : Array β) {Q : SizzLean.Repr.SSZList β cap → T → Prop}
    (h : ∀ l : SizzLean.Repr.SSZList β cap, l.val = a → Q l v) :
    RunEnsures v (sszOfArrayM (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) (cap := cap)
      field a) Q := by
  unfold sszOfArrayM
  split
  · rename_i l hl
    refine runEnsures_pure (h l ?_)
    unfold SizzLean.Repr.SSZList.ofArray? at hl
    split at hl
    · cases hl; rfl
    · cases hl
  · exact runEnsures_throwListFull field

end HelperLeaves

/-- The helper leaves join the `run_ensures` walk. They match at reducible transparency like
the core leaves. -/
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_sszOfArrayM _ _ (fun _ _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible exact runEnsures_throwListFull _)
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible exact runEnsures_throwArithmetic _)
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_checkedSucc _ _ (fun _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_checkedMul _ _ _ (fun _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_checkedSub _ _ _ (fun _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_checkedAdd _ _ _ (fun _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible refine runEnsures_getThe ?_)

/-- Split the `match` that `appendState` expands to, on `sszAppend? s f v`. In the `some`
branch the written box is `sszUpdate s with f := l` for the longer list `l`, and the push fact
joins the context twice: as `l.val = (sszGet s f).val.push v`, and as the length fact
`l.val.size = (sszGet s f).val.size + 1` that `omega` reads. The `none` branch
throws. The walk continues with `run_ensures`. -/
macro "append_split" : tactic => `(tactic|
  split <;> try (rename_i _ heq
                 obtain ⟨_, hpush, hl⟩ := Option.map_eq_some_iff.mp heq
                 subst hl
                 first
                   | have hval := SizzLean.Proofs.sszListPush?_eq_some hpush
                     simp only [box_reduce] at hval
                     have hsize := congrArg Array.size hval
                     simp only [Array.size_push] at hsize
                   | have hval := SizzLean.Proofs.progressiveListPush?_eq_some hpush
                     simp only [box_reduce] at hval
                     have hsize := congrArg Array.size hval
                     simp only [Array.size_push] at hsize
                   | skip))

open Lean Elab Tactic Meta in
/-- Case on the first `if` guard in the goal and reduce every `if` on that guard. It is `split`
for the goals a spec `do` block leaves after its join points inline: the same guard then appears
at several places, and `split`'s clean-up step can fail to rewrite them all. This tactic runs
`by_cases` on the guard and rewrites with `simp only [h, ↓reduceIte]` in each case. -/
elab "split_ite" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let isCond (e : Expr) : Bool :=
    e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars
  let some e := t.find? isCond | throwError "split_ite: no `if` with a closed guard in the goal"
  let c ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| by_cases hsplit : $c <;>
    simp only [hsplit, ↓reduceIte, eq_self_iff_true, Bool.false_eq_true, not_false_eq_true,
      not_true_eq_false]))

/-! ## `fuelLoop` and `forIn'` -/

/-- What a `fuelLoop` step must establish: a `next` carries the loop on, so its accumulator
and state must satisfy the invariant `I`; a `done` ends it in `Q`. -/
def fuelStepPost {β α T : Type} (I : β → T → Prop) (Q : α → T → Prop) : Step β α → T → Prop
  | .next b, w => I b w
  | .done a, w => Q a w

@[simp] theorem fuelStepPost_next {β α T : Type} (I : β → T → Prop) (Q : α → T → Prop) (b : β)
    (w : T) : fuelStepPost I Q (.next b) w = I b w := rfl

@[simp] theorem fuelStepPost_done {β α T : Type} (I : β → T → Prop) (Q : α → T → Prop) (a : α)
    (w : T) : fuelStepPost I Q (.done a) w = Q a w := rfl

section Loops

variable {T ε α β : Type} [SSZRepr T] [HasherTag]

/-- `fuelLoop` with an invariant on the accumulator and state. Each step must re-establish
the invariant or end in `Q`, and the `exhausted` value must satisfy `Q` from any invariant
state, since the fuel can run out there. -/
theorem runEnsures_fuelLoop {step : β → StateT (SSZ.Box HasherTag.H T) (Except ε) (Step β α)}
    {exhausted : α} (I : β → T → Prop) (Q : α → T → Prop)
    (hstep : ∀ b w, I b w → RunEnsures w (step b) (fuelStepPost I Q))
    (hex : ∀ b w, I b w → Q exhausted w) :
    ∀ (fuel : Nat) (init : β) (v : T), I init v → RunEnsures v (fuelLoop fuel init exhausted step) Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro init v hI
    unfold fuelLoop
    exact runEnsures_pure (hex init v hI)
  | succ fuel ih =>
    intro init v hI
    unfold fuelLoop
    refine runEnsures_bind ((hstep init v hI).weaken ?_)
    intro r w hw
    cases r with
    | done a => exact runEnsures_pure hw
    | next b => exact ih b w hw

/-- `fuelLoop` keeps `P` when every step does. -/
theorem Preserves.fuelLoop {P : T → Prop} {step : β → StateT (SSZ.Box HasherTag.H T) (Except ε) (Step β α)}
    (fuel : Nat) (init : β) (exhausted : α) (hstep : ∀ b, Preserves P (step b)) :
    Preserves P (fuelLoop fuel init exhausted step) :=
  fun v hv => runEnsures_fuelLoop (fun _ w => P w) (fun _ w => P w)
    (fun b w hw => (hstep b w hw).weaken fun r w' h' => by cases r <;> exact h')
    (fun _ _ h => h) fuel init v hv

/-- `List.forIn'`, the loop that hands each step a membership proof, with an invariant on the
accumulator and state alone. The step function changes along the induction, because each
cons step re-wraps the membership proof, so the statement quantifies over it. -/
theorem runEnsures_forIn'_list_inv (I : β → T → Prop) :
    ∀ (l : List α) (f : (a : α) → a ∈ l → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)),
      (∀ x hx b w, I b w → RunEnsures w (f x hx b) (loopStepPost I I)) →
      ∀ (init : β) (v : T), I init v → RunEnsures v (forIn' l init f) I := by
  intro l
  induction l with
  | nil =>
    intro f _ init v hI
    rw [List.forIn'_nil]
    exact runEnsures_pure hI
  | cons x rest ih =>
    intro f hstep init v hI
    rw [List.forIn'_cons]
    refine runEnsures_bind ((hstep x List.mem_cons_self init v hI).weaken ?_)
    intro step w hw
    cases step with
    | done b => exact runEnsures_pure hw
    | yield b =>
      exact ih _ (fun x' hx' b' w' hI' => hstep x' (List.mem_cons_of_mem x hx') b' w' hI') b w hw

/-- `for h : i in [0:n]` with an invariant on the accumulator and state alone. Each step sees
its index's membership proof, from which `i < n` follows. -/
theorem runEnsures_forIn'_range_inv (n : Nat)
    {f : (i : Nat) → i ∈ [0:n] → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : β → T → Prop)
    (hstep : ∀ i (hi : i ∈ [0:n]) b w, I b w → RunEnsures w (f i hi b) (loopStepPost I I))
    (init : β) {v : T} (hinit : I init v) : RunEnsures v (forIn' [0:n] init f) I := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact runEnsures_forIn'_list_inv I _ _
    (fun x hx b w hI => hstep x (Std.Legacy.Range.mem_of_mem_range' hx) b w hI) init v hinit

/-- `for h : i in [0:n]` keeps `P` when every step does. -/
theorem Preserves.forIn'_range {P : T → Prop} (n : Nat)
    {f : (i : Nat) → i ∈ [0:n] → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (init : β) (hf : ∀ i hi b, Preserves P (f i hi b)) : Preserves P (forIn' [0:n] init f) :=
  fun _ hv => runEnsures_forIn'_range_inv n (fun _ w => P w)
    (fun i hi b _ hw => (hf i hi b).loopStep hw) init hv

end Loops

/-! ## Loops that carry a box

Some spec bodies read the state into a local box and thread that box through a loop, `let mut
state := state; for … do state ← increaseBalance state …`, before one `set state` at the end.
The threaded state stays fixed through the loop; the invariant lives on the carried box. -/

section BoxLoops

variable {T ε : Type} [SSZRepr T] [HasherTag]

/-- What a box-carrying loop keeps: the threaded state is still `v`, and the carried box is the
uncached box of a value that satisfies `P`. -/
def BoxInv (P : T → Prop) (v : T) (b : SSZ.Box HasherTag.H T) (w : T) : Prop :=
  w = v ∧ ∃ s, b = pureState s ∧ P s

/-- `for i in [0:n]` with a box accumulator: every step, from a carried box whose value
satisfies `P`, leaves the threaded state alone and carries a box whose value satisfies `P`. -/
theorem runEnsures_forIn_range_box (P : T → Prop) (n : Nat)
    {f : Nat → SSZ.Box HasherTag.H T →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T))}
    (hstep : ∀ i s w, i < n → P s →
      RunEnsures w (f i (pureState s)) (loopStepPost (BoxInv P w) (BoxInv P w)))
    (s v : T) (hs : P s) :
    RunEnsures v (forIn [0:n] (pureState s) f) (BoxInv P v) :=
  runEnsures_forIn_range_inv n (BoxInv P v)
    (fun i b w hi hI => by
      obtain ⟨hw, s', hb, hs'⟩ := hI
      subst hw hb
      exact hstep i s' w hi hs')
    _ ⟨rfl, s, rfl, hs⟩

/-- `Array.forIn` with a box accumulator, as `runEnsures_forIn_range_box`. -/
theorem runEnsures_forIn_array_box {α : Type} (P : T → Prop) (xs : Array α)
    {f : α → SSZ.Box HasherTag.H T →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T))}
    (hstep : ∀ x s w, P s →
      RunEnsures w (f x (pureState s)) (loopStepPost (BoxInv P w) (BoxInv P w)))
    (s v : T) (hs : P s) :
    RunEnsures v (forIn xs (pureState s) f) (BoxInv P v) :=
  runEnsures_forIn_array_inv (BoxInv P v)
    (fun x b w hI => by
      obtain ⟨hw, s', hb, hs'⟩ := hI
      subst hw hb
      exact hstep x s' w hs')
    xs _ ⟨rfl, s, rfl, hs⟩

/-- `BoxInv` on the first component of a pair accumulator: the shape of a loop with two
`let mut` variables, the box and a plain value. -/
def BoxInvFst {γ : Type} (P : T → Prop) (v : T) (acc : SSZ.Box HasherTag.H T × γ) (w : T) : Prop :=
  BoxInv P v acc.1 w

/-- `Array.forIn` with a `(box, value)` accumulator, the box carrying the invariant. -/
theorem runEnsures_forIn_array_boxFst {α γ : Type} (P : T → Prop) (xs : Array α)
    {f : α → SSZ.Box HasherTag.H T × γ →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T × γ))}
    (hstep : ∀ x s n w, P s →
      RunEnsures w (f x (pureState s, n)) (loopStepPost (BoxInvFst P w) (BoxInvFst P w)))
    (s v : T) (n : γ) (hs : P s) :
    RunEnsures v (forIn xs (pureState s, n) f) (BoxInvFst P v) :=
  runEnsures_forIn_array_inv (BoxInvFst P v)
    (fun x acc w hI => by
      obtain ⟨b, n'⟩ := acc
      obtain ⟨hw, s', hb, hs'⟩ := hI
      simp only at hb
      subst hw hb
      exact hstep x s' n' w hs')
    xs _ ⟨rfl, s, rfl, hs⟩

/-- `for i in [0:n]` with a `(box, value)` accumulator, the box carrying the invariant. -/
theorem runEnsures_forIn_range_boxFst {γ : Type} (P : T → Prop) (k : Nat)
    {f : Nat → SSZ.Box HasherTag.H T × γ →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T × γ))}
    (hstep : ∀ i s n w, i < k → P s →
      RunEnsures w (f i (pureState s, n)) (loopStepPost (BoxInvFst P w) (BoxInvFst P w)))
    (s v : T) (n : γ) (hs : P s) :
    RunEnsures v (forIn [0:k] (pureState s, n) f) (BoxInvFst P v) :=
  runEnsures_forIn_range_inv k (BoxInvFst P v)
    (fun i acc w hi hI => by
      obtain ⟨b, n'⟩ := acc
      obtain ⟨hw, s', hb, hs'⟩ := hI
      simp only at hb
      subst hw hb
      exact hstep i s' n' w hi hs')
    _ ⟨rfl, s, rfl, hs⟩

end BoxLoops

/-! ## Pure loops over the box

A spec body that rewrites many entries of one state often does it in one `modifyState`, with
an `Id.run` loop over the box inside: `modifyState fun state => Id.run do let mut state :=
state; for … do state := …; return state`. `runEnsures_modifyThe` needs the written box to be
the uncached box of some value that satisfies the postcondition. These lemmas supply it from a
per-step fact. -/

section PureLoops

variable {T α : Type} [SSZRepr T] [HasherTag]

/-- A pure `List.forIn` over the box maps the uncached box of a `P` value to the uncached box of
a `P` value, when every step does and none stops early. -/
theorem pureState_forIn_list_inv (P : T → Prop)
    {f : α → SSZ.Box HasherTag.H T → Id (ForInStep (SSZ.Box HasherTag.H T))}
    (hf : ∀ a (v : T), P v → ∃ w, f a (pureState v) = .yield (pureState w) ∧ P w) :
    ∀ (l : List α) (v : T), P v → ∃ w, (forIn l (pureState v) f : Id _) = pureState w ∧ P w := by
  intro l
  induction l with
  | nil => intro v hv; exact ⟨v, rfl, hv⟩
  | cons a rest ih =>
    intro v hv
    obtain ⟨w, hw, hpw⟩ := hf a v hv
    rw [List.forIn_cons, hw]
    exact ih w hpw

/-- The `Array` form: the array walk is the walk of its `toList`. -/
theorem pureState_forIn_array_inv (P : T → Prop)
    {f : α → SSZ.Box HasherTag.H T → Id (ForInStep (SSZ.Box HasherTag.H T))}
    (hf : ∀ a (v : T), P v → ∃ w, f a (pureState v) = .yield (pureState w) ∧ P w)
    (xs : Array α) (v : T) (hv : P v) :
    ∃ w, (forIn xs (pureState v) f : Id _) = pureState w ∧ P w := by
  rw [← Array.forIn_toList]
  exact pureState_forIn_list_inv P hf xs.toList v hv

/-- The `for i in [0:n]` form: the range walk is the walk of `List.range n`. -/
theorem pureState_forIn_range_inv (P : T → Prop)
    {f : Nat → SSZ.Box HasherTag.H T → Id (ForInStep (SSZ.Box HasherTag.H T))}
    (hf : ∀ i (v : T), P v → ∃ w, f i (pureState v) = .yield (pureState w) ∧ P w)
    (n : Nat) (v : T) (hv : P v) :
    ∃ w, (forIn [0:n] (pureState v) f : Id _) = pureState w ∧ P w := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact pureState_forIn_list_inv P hf _ v hv

end PureLoops

end EthCLLib.Proofs
