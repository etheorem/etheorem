import EthCLLib.Proofs.KeepsUncached
import EthCLLib.Proofs.BoxSimp

/-!
# `EthCLLib.Proofs.RunEnsures`: what a successful run guarantees

`RunEnsures v act Q` says: every successful run of `act` from the uncached box of `v` ends on
an uncached box, and its result `a` and post-state value `w` satisfy `Q a w`. It is a Hoare
triple over the pure runner, with the start pinned to one value. `KeepsUncachedFrom`
(`EthCLLib/Proofs/KeepsUncached.lean`) is the case `Q = fun _ _ => True`. A theorem that a
spec step keeps an invariant, or leaves a set of fields alone, is a `RunEnsures` fact with
that property as `Q`.

The start is one value, not every value, because the spec bodies read the state into a local:
`let state ← get` hands the continuation the box itself. A fact about the continuation must
know that this box is the start, and a per-start triple carries exactly that.

## Weakest preconditions

Each closure lemma states its premise as what must hold *before* the construct so that `Q`
holds after it. `runEnsures_bind` asks the first action to ensure "the rest ensures `Q`":

    RunEnsures v x (fun a w => RunEnsures w (f a) Q) → RunEnsures v (x >>= f) Q

So a proof walks the body from the front, and no lemma asks for an intermediate condition the
author has to guess. The `run_ensures` tactic applies these lemmas through straight-line code,
gates, and state writes. It stops at a call to another spec step, where the author applies that
step's own `RunEnsures` fact through `RunEnsures.weaken`, and at a loop, where the author names
the invariant.

## Loops

A loop needs an invariant, which no tactic can guess. `runEnsures_forIn_range` takes one that
also sees the iteration index, `I i b w`. `process_slots` needs that form: its body adds one to
the slot, and only a counter of the form `slot = start + i < target` excludes a wrap. The
position-free forms (`runEnsures_forIn_range_inv`, `_list_inv`, `_array_inv`,
`runEnsures_forM_array_inv`) cover the loops whose invariant is a fixed property of the state.

## Relations

`KeepsUncachedWith R act` is the all-starts, relational reading: every successful run relates
its start and end values by `R`. It suits frame facts, where `R v w` says some projection of
`w` equals that of `v`, and invariant preservation, where `R v w` is `I v → I w`. Both are
preorders, and `keepsUncachedWith_bind` composes two steps by transitivity.

Like `KeepsUncached.lean`, this module is box-level infrastructure in the framework: its
statements name no fork constant, so the plain-value check never visits it.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (HasherTag ErrorConv liftErr getStateRoot sszGetIdx IdxRead)
open SizzLean (SSZRepr)
open SizzLean.Cache

/-- Every successful run of `act` from `pureState v` ends on an uncached box, and the run's
result and post-state value satisfy `Q`. -/
def RunEnsures {T ε α : Type} [SSZRepr T] [HasherTag] (v : T)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) (Q : α → T → Prop) : Prop :=
  ∀ a s, act.run (pureState v) = .ok (a, s) → s = pureState s.view ∧ Q a s.view

/-! ## Reducing the uncached box -/

/-- The uncached box of `v` is the `.uncached` constructor around `v`. Stated here because the
constructor's builder `Box.ofPure` is private to SizzLean. With it, `simp` reduces the `match`
a record update makes on the box. -/
@[box_reduce] theorem pureState_eq_uncached {T : Type} [SSZRepr T] [HasherTag] (v : T) :
    (pureState v : SSZ.Box HasherTag.H T) = .uncached (UncachedSSZ.ofValue HasherTag.H v) := rfl

/-- The view of a fresh uncached wrapper is the value it wraps. -/
@[box_reduce] theorem uncachedSSZ_ofValue_view {T : Type} [SSZRepr T] [HasherTag] (v : T) :
    (UncachedSSZ.ofValue HasherTag.H v).view = v := rfl

/-- The view of an `.uncached` box is its wrapper's view. -/
@[box_reduce] theorem box_view_uncached {T : Type} [SSZRepr T] [HasherTag]
    (t : UncachedSSZ HasherTag.H T) : (SSZ.Box.uncached t).view = t.view := rfl

attribute [box_reduce] SizzLean.Proofs.view_uncachedBox
/-- The root of an `.uncached` box is the spec root of its view, and the box comes back
unchanged. -/
@[box_reduce] theorem box_hashTreeRoot_uncached {T : Type} [SSZRepr T] [HasherTag]
    (t : UncachedSSZ HasherTag.H T) :
    (SSZ.Box.uncached t).hashTreeRoot = (t.hashTreeRoot, SSZ.Box.uncached t) := rfl

/-- `pure` in `Id` is the value itself. With `Id.run` unfolded, a pure `do` block over the box
reduces to the box it returns. -/
@[box_reduce] theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- `bind` in `Id` is application. -/
@[box_reduce] theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

attribute [box_reduce] EthCLLib.Spec.stateRoot Id.run


/-! ## Reading and weakening -/

section Reading

variable {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}
  {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}

/-- A weaker postcondition follows from a stronger one. This is how a proof applies a
sub-step's own fact at a call site: the call site's postcondition is whatever the rest of the
body needs, and `hPQ` derives it. -/
theorem RunEnsures.weaken {P : α → T → Prop} (h : RunEnsures v act P)
    (hPQ : ∀ a w, P a w → Q a w) : RunEnsures v act Q :=
  fun a s hs => ⟨(h a s hs).1, hPQ a s.view (h a s hs).2⟩

/-- Two facts about one run combine into their conjunction. A frame fact and a value fact,
proved apart, join here. -/
theorem RunEnsures.and {P : α → T → Prop} (hP : RunEnsures v act P) (hQ : RunEnsures v act Q) :
    RunEnsures v act (fun a w => P a w ∧ Q a w) :=
  fun a s hs => ⟨(hP a s hs).1, (hP a s hs).2, (hQ a s hs).2⟩

/-- The flavour half of the triple. -/
theorem RunEnsures.keepsUncachedFrom (h : RunEnsures v act Q) : KeepsUncachedFrom v act :=
  fun a s hs => (h a s hs).1

/-- The value-level reading: a successful `runPure` satisfies the postcondition. This is the
form a fork-body theorem states, over plain values. -/
theorem RunEnsures.runPure_ok (h : RunEnsures v act Q) {a : α} {w : T}
    (hrun : runPure act v = .ok (a, w)) : Q a w := by
  rw [runPure_eq] at hrun
  cases hr : act.run (pureState v) with
  | error e =>
    rw [hr] at hrun
    simp [Except.map] at hrun
  | ok p =>
    obtain ⟨a', s⟩ := p
    rw [hr] at hrun
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact (h a' s hr).2

/-- Build a triple from the flavour fact and a value-level reading. This reuses an existing
`KeepsUncachedFrom` proof, such as the Gloas operation handlers', and adds the postcondition
on top. -/
theorem runEnsures_of_keepsUncachedFrom (hk : KeepsUncachedFrom v act)
    (hq : ∀ a w, runPure act v = .ok (a, w) → Q a w) : RunEnsures v act Q := by
  intro a s hs
  refine ⟨hk a s hs, hq a s.view ?_⟩
  rw [runPure_eq, hs]
  rfl

/-- Congruence: the triple transfers along an equality of actions. It carries a fact across
an unfolding or a `match` reduced by `cases`. -/
theorem runEnsures_congr {act' : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (heq : act = act') (h : RunEnsures v act Q) : RunEnsures v act' Q :=
  heq ▸ h

end Reading

/-! ## Leaves -/

section Leaves

variable {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}

/-- `pure a` returns `a` and the start: `Q a v` is all it needs. -/
theorem runEnsures_pure {a : α} {Q : α → T → Prop} (h : Q a v) :
    RunEnsures v (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q := by
  intro a' s hs
  rw [run_pure] at hs
  injection hs with hs
  injection hs with ha hs
  subst ha hs
  exact ⟨rfl, h⟩

/-- `throw` never succeeds, so every postcondition holds. -/
theorem runEnsures_throw (e : ε) {Q : α → T → Prop} :
    RunEnsures v (throw e : StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q := by
  intro a s hs
  rw [run_throw] at hs
  simp at hs

/-- `get` returns the start box and keeps it. -/
theorem runEnsures_get {Q : SSZ.Box HasherTag.H T → T → Prop} (h : Q (pureState v) v) :
    RunEnsures v (get : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)) Q := by
  intro a s hs
  rw [show ((get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)).run (pureState v)) = .ok (pureState v, pureState v) from rfl] at hs
  injection hs with hs
  injection hs with ha hs
  subst ha hs
  exact ⟨rfl, h⟩

/-- `set` of a rebuilt box lands on that box. -/
theorem runEnsures_set {w : T} {Q : PUnit → T → Prop} (h : Q ⟨⟩ w) :
    RunEnsures v (set (pureState w) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q := by
  intro a s hs
  rw [show ((set (pureState w) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit).run
      (pureState v)) = .ok (⟨⟩, pureState w) from rfl] at hs
  injection hs with hs
  injection hs with ha hs
  subst ha hs
  exact ⟨rfl, h⟩

/-- `modifyThe` through a writer that maps the start box to the uncached box of some `w`. A
record update through `sszUpdate` does that by `rfl`, and `modifyState` unfolds to this form.
The existential lets a tactic pick `w` by unification. -/
theorem runEnsures_modifyThe {f : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T}
    {Q : PUnit → T → Prop} (h : ∃ w, f (pureState v) = pureState w ∧ Q ⟨⟩ w) :
    RunEnsures v (modifyThe (SSZ.Box HasherTag.H T) f :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q := by
  obtain ⟨w, hw, hq⟩ := h
  intro a s hs
  rw [show ((modifyThe (SSZ.Box HasherTag.H T) f : StateT (SSZ.Box HasherTag.H T)
      (Except ε) PUnit).run (pureState v)) = .ok (⟨⟩, f (pureState v)) from rfl, hw] at hs
  injection hs with hs
  injection hs with ha hs
  subst ha hs
  exact ⟨rfl, hq⟩

/-- A write of a box held in a variable: the box must be the uncached box of some value.
`appendState`'s `some` branch writes the box `sszAppend?` returned this way. -/
theorem runEnsures_modifyThe_const {b : SSZ.Box HasherTag.H T} {Q : PUnit → T → Prop}
    (h : ∃ w, b = pureState w ∧ Q ⟨⟩ w) :
    RunEnsures v (modifyThe (SSZ.Box HasherTag.H T) (fun _ => b) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q :=
  runEnsures_modifyThe h

/-- A write through `f` that maps the start box to the uncached box of its own view. The new
state is named `(f (pureState v)).view`, a term the size of `f`'s application. The
existential form `runEnsures_modifyThe` names it by the record `f` computes instead, and a run of
several writes then nests one whole record inside each field of the next. -/
theorem runEnsures_modifyThe_view {f : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T}
    {Q : PUnit → T → Prop} (hf : f (pureState v) = pureState (f (pureState v)).view)
    (h : Q ⟨⟩ (f (pureState v)).view) :
    RunEnsures v (modifyThe (SSZ.Box HasherTag.H T) f :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q :=
  runEnsures_modifyThe ⟨_, hf, h⟩

/-- `set b` of a box that is the uncached box of its own view, naming the new state `b.view`.
The compact form of `runEnsures_set`, for `set (sszUpdate state with …)`. -/
theorem runEnsures_set_view {b : SSZ.Box HasherTag.H T} {Q : PUnit → T → Prop}
    (hb : b = pureState b.view) (h : Q ⟨⟩ b.view) :
    RunEnsures v (set b : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) Q := by
  rw [hb]
  exact runEnsures_set h

/-- `getStateRoot` returns the start value's root and keeps the uncached box, which
`hashTreeRoot_uncachedBox` hands back unchanged. -/
theorem runEnsures_getStateRoot {Q : ByteArray → T → Prop}
    (h : Q (SizzLean.SSZ.hashTreeRoot HasherTag.H v) v) :
    RunEnsures v (getStateRoot (S := SSZ.Box HasherTag.H T) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) ByteArray) Q := by
  intro a s hs
  rw [show ((getStateRoot (S := SSZ.Box HasherTag.H T) : StateT (SSZ.Box HasherTag.H T)
      (Except ε) ByteArray).run (pureState v))
      = .ok (((pureState v).hashTreeRoot).1, ((pureState v).hashTreeRoot).2) from rfl,
    SizzLean.Proofs.hashTreeRoot_uncachedBox] at hs
  injection hs with hs
  injection hs with ha hs
  subst ha hs
  exact ⟨rfl, h⟩

/-- `liftErr x`, the spec's checked op or fallible read: on success it returns `x`'s value and
keeps the start. -/
theorem runEnsures_liftErr {ε' : Type} [ErrorConv ε' ε] {x : Except ε' α} {Q : α → T → Prop}
    (h : ∀ b, x = .ok b → Q b v) :
    RunEnsures v (liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
      StateT (SSZ.Box HasherTag.H T) (Except ε) α) Q := by
  intro a s hs
  cases x with
  | error e =>
    rw [run_liftErr_of_error (e := ErrorConv.conv e) _ _ rfl] at hs
    simp at hs
  | ok b =>
    rw [run_liftErr_of_ok (a := b) _ _ rfl] at hs
    injection hs with hs
    injection hs with ha hs
    subst ha hs
    exact ⟨rfl, h b rfl⟩

/-- `sszGetIdx xs i`, the spec's bounds-checked read: on success it returns the element and
keeps the start. -/
theorem runEnsures_sszGetIdx {ρ : Type} [IdxRead ρ α] [ErrorConv IndexError ε] (xs : ρ)
    (i : Nat) {Q : α → T → Prop} (h : ∀ y, IdxRead.get? xs i = some y → Q y v) :
    RunEnsures v (sszGetIdx (E := ε) (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) xs i) Q := by
  intro a s hs
  cases hq : IdxRead.get? xs i with
  | some y =>
    rw [run_sszGetIdx_some xs i _ hq] at hs
    injection hs with hs
    injection hs with ha hs
    subst ha hs
    exact ⟨rfl, h y hq⟩
  | none =>
    rw [run_sszGetIdx_none xs i _ hq] at hs
    simp at hs

end Leaves

/-! ## Combinators -/

section Combinators

variable {T ε α β : Type} [SSZRepr T] [HasherTag] {v : T}

/-- Bind, in weakest-precondition form: the first action must ensure that the continuation,
run on its result and post-state, ensures `Q`. -/
theorem runEnsures_bind {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β} {Q : β → T → Prop}
    (h : RunEnsures v x (fun a w => RunEnsures w (f a) Q)) : RunEnsures v (x >>= f) Q := by
  intro b s hs
  rw [run_bind] at hs
  cases hx : x.run (pureState v) with
  | error e =>
    rw [hx, except_bind_error] at hs
    simp at hs
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hx, except_bind_ok] at hs
    obtain ⟨hs', hk⟩ := h a s' hx
    rw [hs'] at hs
    exact hk b s hs

/-- `get` then a continuation on the read box: the continuation runs from the start with the
start's own box in hand. The splice for `let state ← get` and every `(← get)`. -/
theorem runEnsures_get_bind
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}
    (h : RunEnsures v (g (pureState v)) Q) : RunEnsures v (get >>= g) Q :=
  runEnsures_bind (runEnsures_get h)

/-- `if`: each branch under its own guard. `assert` expands to this, with `throw` on the
failing branch. -/
theorem runEnsures_ite {c : Prop} [Decidable c] {x y : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {Q : α → T → Prop} (hx : c → RunEnsures v x Q) (hy : ¬c → RunEnsures v y Q) :
    RunEnsures v (if c then x else y) Q := by
  intro a s hs
  split at hs
  · exact hx (by assumption) a s hs
  · exact hy (by assumption) a s hs

/-- Dependent `if`: each branch under its own guard. `assertH` expands to this. -/
theorem runEnsures_dite {c : Prop} [Decidable c]
    {t : c → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {e : ¬c → StateT (SSZ.Box HasherTag.H T) (Except ε) α} {Q : α → T → Prop}
    (ht : ∀ hc : c, RunEnsures v (t hc) Q) (he : ∀ hc : ¬c, RunEnsures v (e hc) Q) :
    RunEnsures v (dite c t e) Q := by
  intro a s hs
  split at hs
  · exact ht (by assumption) a s hs
  · exact he (by assumption) a s hs

end Combinators

/-! ## Loops -/

/-- What a loop body's step must establish. A `yield` carries the loop on, so its accumulator
and state must satisfy the invariant `I`. A `done` ends the loop, so they must satisfy the
loop's postcondition `Q`. -/
def loopStepPost {β T : Type} (I Q : β → T → Prop) : ForInStep β → T → Prop
  | .yield b, w => I b w
  | .done b, w => Q b w

@[simp] theorem loopStepPost_yield {β T : Type} (I Q : β → T → Prop) (b : β) (w : T) :
    loopStepPost I Q (.yield b) w = I b w := rfl

@[simp] theorem loopStepPost_done {β T : Type} (I Q : β → T → Prop) (b : β) (w : T) :
    loopStepPost I Q (.done b) w = Q b w := rfl

section Loops

variable {T ε α β : Type} [SSZRepr T] [HasherTag]

/-- `List.forIn` with an invariant on the list still to walk. Each step from `x :: rest` must
re-establish the invariant at `rest`, or end the loop in `Q`; the empty list must imply `Q`.
The general form the indexed and position-free loop rules reduce to. -/
theorem runEnsures_forIn_list {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : List α → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ x rest b w, I (x :: rest) b w → RunEnsures w (f x b) (loopStepPost (I rest) Q))
    (hnil : ∀ b w, I [] b w → Q b w) :
    ∀ (l : List α) (init : β) (v : T), I l init v → RunEnsures v (forIn l init f) Q := by
  intro l
  induction l with
  | nil =>
    intro init v hI
    rw [List.forIn_nil]
    exact runEnsures_pure (hnil init v hI)
  | cons x rest ih =>
    intro init v hI
    rw [List.forIn_cons]
    refine runEnsures_bind ((hstep x rest init v hI).weaken ?_)
    intro step w hw
    cases step with
    | done b => exact runEnsures_pure hw
    | yield b => exact ih b w hw

/-- `List.forIn` with an invariant on the accumulator and state alone. -/
theorem runEnsures_forIn_list_inv
    {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : β → T → Prop) (hstep : ∀ x b w, I b w → RunEnsures w (f x b) (loopStepPost I I))
    (l : List α) (init : β) {v : T} (hinit : I init v) :
    RunEnsures v (forIn l init f) I :=
  runEnsures_forIn_list (fun _ => I) I (fun x _ b w hI => hstep x b w hI) (fun _ _ h => h)
    l init v hinit

/-- The walk of `List.range' s k`, with an invariant indexed by the next position. The
auxiliary induction behind `runEnsures_forIn_range`. -/
private theorem runEnsures_forIn_range'
    {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)} (n : Nat)
    (I : Nat → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ i b w, i < n → I i b w → RunEnsures w (f i b) (loopStepPost (I (i + 1)) Q))
    (hend : ∀ b w, I n b w → Q b w) :
    ∀ (k s : Nat) (b : β) (w : T), s + k = n → I s b w →
      RunEnsures w (forIn (List.range' s k) b f) Q := by
  intro k
  induction k with
  | zero =>
    intro s b w hs hI
    have hsn : s = n := by omega
    subst hsn
    rw [List.range'_zero, List.forIn_nil]
    exact runEnsures_pure (hend b w hI)
  | succ k ih =>
    intro s b w hs hI
    rw [List.range'_succ, List.forIn_cons]
    refine runEnsures_bind ((hstep s b w (by omega) hI).weaken ?_)
    intro step w' hw
    cases step with
    | done b' => exact runEnsures_pure hw
    | yield b' => exact ih (s + 1) b' w' (by omega) hw

/-- `for i in [0:n]` with an invariant that sees the index: `I i b w` holds before step `i`.
Step `i` must re-establish it at `i + 1`, or end the loop in `Q`, and `I n` must imply `Q`.
`process_slots` reads its slot counter this way. -/
theorem runEnsures_forIn_range
    {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)} (n : Nat)
    (I : Nat → β → T → Prop) (Q : β → T → Prop)
    (hstep : ∀ i b w, i < n → I i b w → RunEnsures w (f i b) (loopStepPost (I (i + 1)) Q))
    (hend : ∀ b w, I n b w → Q b w) (init : β) {v : T} (hinit : I 0 init v) :
    RunEnsures v (forIn [0:n] init f) Q := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl]
  exact runEnsures_forIn_range' n I Q hstep hend n 0 init v (by omega) hinit

/-- `for i in [0:n]` with an invariant on the accumulator and state alone. -/
theorem runEnsures_forIn_range_inv
    {f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)} (n : Nat)
    (I : β → T → Prop) (hstep : ∀ i b w, i < n → I b w → RunEnsures w (f i b) (loopStepPost I I))
    (init : β) {v : T} (hinit : I init v) :
    RunEnsures v (forIn [0:n] init f) I :=
  runEnsures_forIn_range n (fun _ => I) I hstep (fun _ _ h => h) init hinit

/-- `Array.forIn` with an invariant on the accumulator and state alone: the array walk is the
walk of its `toList`. -/
theorem runEnsures_forIn_array_inv
    {f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)}
    (I : β → T → Prop) (hstep : ∀ x b w, I b w → RunEnsures w (f x b) (loopStepPost I I))
    (xs : Array α) (init : β) {v : T} (hinit : I init v) :
    RunEnsures v (forIn xs init f) I := by
  rw [← Array.forIn_toList]
  exact runEnsures_forIn_list_inv I hstep xs.toList init hinit

/-- `List.foldlM` with an invariant on the accumulator and state. -/
theorem runEnsures_foldlM_list_inv {f : β → α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (I : β → T → Prop) (hstep : ∀ b x w, I b w → RunEnsures w (f b x) I) :
    ∀ (l : List α) (init : β) (v : T), I init v → RunEnsures v (l.foldlM f init) I := by
  intro l
  induction l with
  | nil =>
    intro init v hI
    rw [List.foldlM_nil]
    exact runEnsures_pure hI
  | cons x rest ih =>
    intro init v hI
    rw [List.foldlM_cons]
    exact runEnsures_bind ((hstep init x v hI).weaken fun b w hb => ih b w hb)

/-- `Array.foldlM` with an invariant on the accumulator and state: the array fold is the fold of
its `toList`. -/
theorem runEnsures_foldlM_array_inv {f : β → α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (I : β → T → Prop) (hstep : ∀ b x w, I b w → RunEnsures w (f b x) I) (xs : Array α)
    (init : β) {v : T} (hinit : I init v) : RunEnsures v (xs.foldlM f init) I := by
  rw [← Array.foldlM_toList]
  exact runEnsures_foldlM_list_inv I hstep xs.toList init v hinit

/-- `ForM.forM` over an `Array`, the shape of the operation loops, with an invariant on the
state: the fold is `List.foldlM` over the elements. -/
theorem runEnsures_forM_array_inv
    {handler : α → StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit} (I : T → Prop)
    (hstep : ∀ x w, I w → RunEnsures w (handler x) (fun _ w' => I w')) (xs : Array α) {v : T}
    (hinit : I v) : RunEnsures v (ForM.forM xs handler) (fun _ w => I w) := by
  rw [show (ForM.forM xs handler) = (xs.foldlM (fun _ => handler) ⟨⟩) from rfl,
    ← Array.foldlM_toList]
  exact runEnsures_foldlM_list_inv (fun _ w => I w) (fun _ x w hI => hstep x w hI)
    xs.toList ⟨⟩ v hinit

end Loops

/-! ## The relational reading -/

/-- Every successful run of `act`, from any start, ends on an uncached box whose value is
related to the start's by `R`. -/
def KeepsUncachedWith {T ε α : Type} [SSZRepr T] [HasherTag] (R : T → T → Prop)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) : Prop :=
  ∀ v, RunEnsures v act (fun _ w => R v w)

section Relational

variable {T ε α β : Type} [SSZRepr T] [HasherTag] {R : T → T → Prop}

/-- The flavour half: the trivial relation recovers `KeepsUncached`. -/
theorem KeepsUncachedWith.keepsUncached {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (h : KeepsUncachedWith R act) : KeepsUncached act :=
  fun v a s hs => (h v a s hs).1

/-- The value-level reading: a successful `runPure` relates its start and end by `R`. -/
theorem KeepsUncachedWith.runPure_ok {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (h : KeepsUncachedWith R act) {v w : T} {a : α} (hrun : runPure act v = .ok (a, w)) :
    R v w :=
  (h v).runPure_ok hrun

/-- A weaker relation follows from a stronger one. -/
theorem KeepsUncachedWith.weaken {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {R' : T → T → Prop} (h : KeepsUncachedWith R act) (hR : ∀ v w, R v w → R' v w) :
    KeepsUncachedWith R' act :=
  fun v => (h v).weaken fun _ w hvw => hR v w hvw

/-- Bind composes by transitivity, when the continuation's fact holds for every bound value.
A continuation that reads the bound box, the `let state ← get` shape, needs the per-start
`runEnsures_get_bind` instead. -/
theorem keepsUncachedWith_bind (htrans : ∀ u v w, R u v → R v w → R u w)
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (hx : KeepsUncachedWith R x) (hf : ∀ a, KeepsUncachedWith R (f a)) :
    KeepsUncachedWith R (x >>= f) :=
  fun v => runEnsures_bind ((hx v).weaken fun a w hvw =>
    (hf a w).weaken fun _ w' hww' => htrans v w w' hvw hww')

/-- `pure` relates its start to itself. -/
theorem keepsUncachedWith_pure (hrefl : ∀ v, R v v) (a : α) :
    KeepsUncachedWith R (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) :=
  fun v => runEnsures_pure (hrefl v)

/-- `throw` never succeeds. -/
theorem keepsUncachedWith_throw (e : ε) :
    KeepsUncachedWith R (throw e : StateT (SSZ.Box HasherTag.H T) (Except ε) α) :=
  fun _ => runEnsures_throw e

/-- `get` then a continuation on the read box, from every start. -/
theorem keepsUncachedWith_get_bind
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hg : ∀ v, RunEnsures v (g (pureState v)) (fun _ w => R v w)) :
    KeepsUncachedWith R (get >>= g) :=
  fun v => runEnsures_get_bind (hg v)

end Relational

/-! ## The tactic -/

/-- One structural rule of the `run_ensures` walk. Each rule is its own `macro_rules` entry, so
a later module adds rules for its own constructs; Lean tries the entries from the most recently
declared back, and moves on when one fails. Every rule here matches at reducible transparency.
The bind rule is declared first, so every leaf is tried before it. The `if` rule closes a branch
whose guard `simp` refutes on its own, such as `¬ (n == n) = true`, so a walk through
`set_or_append_list` does not follow the branches its index rules out. -/
syntax "run_ensures_step" : tactic

/-- The write rules of the `run_ensures` walk, tried only when every structural rule fails.
They run at default transparency, because their `rfl` checks that the written box is uncached.
They name the new state by the written box's view, `(f (pureState v)).view` or `b.view`, so a
run of writes keeps a term linear in its length. -/
syntax "run_ensures_fallback" : tactic

macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible refine runEnsures_bind ?_)
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_dite (fun _ => ?_) (fun _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| (with_reducible refine runEnsures_ite (fun hc => ?_) (fun hc => ?_))
              <;> try (simp [box_reduce] at hc; done))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_liftErr (fun _ _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| with_reducible refine runEnsures_sszGetIdx _ _ (fun _ _ => ?_))
macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible refine runEnsures_getStateRoot ?_)
macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible refine runEnsures_set ?_)
macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible refine runEnsures_get ?_)
macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible refine runEnsures_pure ?_)
macro_rules
  | `(tactic| run_ensures_step) => `(tactic| with_reducible exact runEnsures_throw _)

macro_rules
  | `(tactic| run_ensures_fallback) => `(tactic| refine runEnsures_modifyThe_const ?_)
macro_rules
  | `(tactic| run_ensures_fallback) => `(tactic| refine runEnsures_set_view rfl ?_)
macro_rules
  | `(tactic| run_ensures_fallback) => `(tactic| refine runEnsures_modifyThe_view rfl ?_)

open Lean Elab Tactic Meta in
/-- Guard for the write rules: the goal is a `RunEnsures` triple whose action is, at its head, a
write: `modifyThe`, a fork's `modifyState`, or `set`. The head is read after `whnfCore`, which
reduces a leading `let` or beta-redex and unfolds no definition. Without the guard a write rule at default
transparency would also match a callee whose whole body unfolds to one write, and the walk would
pass over the call without its own fact. -/
elab "run_ensures_is_write" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOf ``RunEnsures do throwError "run_ensures_is_write: not a RunEnsures goal"
  let act ← whnfCore (t.getArg! 6)
  let isModifyState : Name → Bool
    | .str _ s => s == "modifyState"
    | _ => false
  let ok : Bool := match act.getAppFn.constName? with
    | some n => n == ``modifyThe || n == ``MonadStateOf.set || n == ``MonadState.set ||
        isModifyState n
    | none => false
  unless ok do throwError "run_ensures_is_write: the action is not a write"

open Lean Elab Tactic Meta in
/-- Beta-reduce the head of the goal, and the head of a triple's action. A
weakest-precondition goal arrives as `(fun a w => RunEnsures w (k a) Q) a₀ w₀`, and a rule
elaborated against that unreduced type can leave an instance argument, such as an `if`'s
`Decidable`, stuck. An action that opens with `have x := e` waits on its body the same way. -/
elab "run_ensures_beta" : tactic => liftMetaTactic fun g => do
  let t := (← instantiateMVars (← g.getType)).headBeta
  -- On a triple, also reduce the action's head: a leading `have` or `let` from a `do` block,
  -- or a beta-redex. `whnfCore` unfolds no definition, so a call stays a call.
  let t ← if t.isAppOfArity ``RunEnsures 8 then do
      let act ← whnfCore (t.getArg! 6)
      pure (mkAppN t.getAppFn (t.getAppArgs.set! 6 act))
    else pure t
  return [← g.replaceTargetDefEq t]

open Lean Elab Tactic Meta in
/-- Tidy a postcondition leaf the walk left: read `(pureState w).view` back as `w` and reduce
a loop step's postcondition. A goal that is still a `RunEnsures` triple is left alone, because
rewriting inside its action term would change the term the next walk matches. -/
elab "run_ensures_tidy" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOf ``RunEnsures do
    evalTactic (← `(tactic| try simp only [loopStepPost_yield, loopStepPost_done,
      SizzLean.Proofs.view_uncachedBox, uncachedSSZ_ofValue_view]))

/-- Walk a `RunEnsures` goal through straight-line code: leaves (`pure`, `throw`, `get`, `set`
of a rebuilt box, `getStateRoot`, `sszGetIdx`, `liftErr`, and a record-update `modifyThe` or
`modifyState`), gates (`if`, `dite`, and so `assert` and `assertH`), and binds. It leaves the
postcondition goals it reaches for the author, with `(pureState w).view` read back as `w`, and
leaves a goal it stops at, a call or a loop or a `match`, untouched.

The structural rules match at reducible transparency, so a call to another spec step stays a
call: `processEpoch >>= k` splits into `processEpoch` and `k`, and the goal for `processEpoch`
is left for its own `RunEnsures` fact. At default transparency the bind rule would unfold the
callee's definition and walk into its body. The write rules run at default transparency,
because the record-update rule's `rfl` computes the update and because `modifyState` is a plain
definition over `modifyThe`. A callee whose whole body is one `modifyState`, such as
`processSlot`, is therefore walked as a write. A `set` of a record update on the read box,
`set (sszUpdate state with …)`, is a write too. The walk stops at a loop, where the author names
the invariant, and at a `match`, where the author splits. -/
macro "run_ensures" : tactic => `(tactic|
  (repeat' (run_ensures_beta; first | run_ensures_step | (run_ensures_is_write; run_ensures_fallback)))
  <;> run_ensures_tidy)

/-! ## Examples -/

/-- The `process_slots` shape: a counter that a loop advances by one per step reaches
`start + n`, with no wrap, when the sum stays below `2 ^ 64`. The indexed invariant
`w = start + i` is what rules out the wrap at each step. -/
example [HasherTag] (n : Nat) (start : UInt64) (hn : start.toNat + n < 2 ^ 64) :
    RunEnsures start
      (forIn [0:n] PUnit.unit (fun _ _ => do
        modifyThe (SSZ.Box HasherTag.H UInt64) (fun s => pureState (s.view + 1))
        pure (ForInStep.yield PUnit.unit)) :
        StateT (SSZ.Box HasherTag.H UInt64) (Except Unit) PUnit)
      (fun _ w => w.toNat = start.toNat + n) := by
  refine runEnsures_forIn_range n
    (fun (i : Nat) (_ : PUnit) (w : UInt64) => w.toNat = start.toNat + i) _ ?_
    (fun _ _ h => h) _ (by simp)
  intro i b w hi hw
  run_ensures
  rw [UInt64.toNat_add, hw]
  simp only [UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- A frame fact composes by transitivity: two steps that each keep the value keep it
together. -/
example [HasherTag] (x y : StateT (SSZ.Box HasherTag.H UInt64) (Except Unit) PUnit)
    (hx : KeepsUncachedWith (fun v w => w = v) x) (hy : KeepsUncachedWith (fun v w => w = v) y) :
    KeepsUncachedWith (fun v w => w = v) (x >>= fun _ => y) :=
  keepsUncachedWith_bind (fun _ _ _ h1 h2 => h2.trans h1) hx (fun _ => hy)

end EthCLLib.Proofs
