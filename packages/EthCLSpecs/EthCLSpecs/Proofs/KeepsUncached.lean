import EthCLLib.Spec.State
import EthCLSpecs.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLSpecs.Proofs.KeepsUncached`: actions that never leave the uncached box

`runPure` reads only the post-state's *view*, which is why it has no bind law in
general: an action run on the uncached box of `v` may land on a *cached* box, and
`runPure` of the continuation would then run on `pureState w` while the composite
ran on that cached box. `KeepsUncached act` is exactly the property whose absence
blocks the law: every successful run of `act` that starts on `pureState v` ends on
an uncached box. Under it the bind law holds
(`runPure_bind_of_keepsUncached`), and a composite body's `runPure` equation
splits into its steps'.

The predicate is generic over the SSZ value type `T`, the error `ε`, and the
result `α`, the same way `runPure` is. The closure lemmas cover the constructs the
spec bodies use: `pure`, `throw`, `bind`, `get`, `set` of a rebuilt box,
`modify` through a writer that maps `pureState v` to `pureState` of a value (the
shape `modBalance_pureState` supplies), `liftErr` and `assert`-shaped gates, `if`,
and the `for` / `forM` folds over `List`, `Array`, and `SSZList`. A `match` on a
plain value reduces to its branch by `cases` on the scrutinee, and
`keepsUncached_congr` carries the fact across such a reduction.

`KeepsUncached` is a claim about the *box flavour a run threads*, not about
behavior: it says nothing about which value the run writes or whether it rejects.
The fork-body lemmas that discharge it (`Proofs/Gloas/ProcessOperations.lean` and
siblings) are therefore supporting facts, untagged, and each one is a
construction over these closure lemmas rather than an unfolding of the fork body's
effect.

This module is box-level infrastructure. Its lemmas quantify over boxes by
design, in their hypotheses and conclusions: they are claims about the box
flavour itself. The plain-value rule (`SPECS_ARCHITECTURE.md` §11.1) keeps
fork-body theorem statements over plain values, and it does not apply here.
The check scopes itself to theorems whose statement names a fork constant,
these lemmas mention none, and the same holds for the generic lemmas in
`Proofs/Run.lean`, so the scope leaves both alone and none needs the
`box_generic` marker. A box-level lemma that later names a fork constant
enters the scope and carries the marker.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag ErrorConv)
open EthCLLib.Spec
open SizzLean (SSZRepr)
open SizzLean.Cache

/-- `act`, run on an uncached box, returns an uncached box whenever it succeeds.
Every successful run that starts on `pureState v` lands on `pureState` of the
post-state's own view, which is the defining property of the uncached flavour. -/
def KeepsUncached {T ε α : Type} [SSZRepr T] [HasherTag]
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) : Prop :=
  ∀ v a s, act.run (pureState v) = .ok (a, s) → s = pureState s.view

/-- Congruence: `KeepsUncached` transfers along a definitional equality of actions.
Carries the fact across a `match` reduced by `cases` on its scrutinee. -/
theorem keepsUncached_congr {T ε α : Type} [SSZRepr T] [HasherTag]
    {x y : StateT (SSZ.Box HasherTag.H T) (Except ε) α} (h : x = y)
    (hx : KeepsUncached x) : KeepsUncached y := h ▸ hx

/-- `pure` returns the state it was handed. -/
theorem keepsUncached_pure {T ε α : Type} [SSZRepr T] [HasherTag] (a : α) :
    KeepsUncached (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  intro v a' s h
  rw [run_pure] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- `throw` never succeeds, so the obligation is vacuous. -/
theorem keepsUncached_throw {T ε α : Type} [SSZRepr T] [HasherTag] (e : ε) :
    KeepsUncached (throw e : StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  intro v a s h
  rw [run_throw] at h
  simp at h

/-- Bind keeps the flavour when the first action and every continuation do: the
first action's post-state is `pureState s'.view`, so the continuation runs on the
uncached box of its own view, which is what its own `KeepsUncached` quantifies
over. -/
theorem keepsUncached_bind {T ε α β : Type} [SSZRepr T] [HasherTag]
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (hx : KeepsUncached x) (hf : ∀ a, KeepsUncached (f a)) :
    KeepsUncached (x >>= f) := by
  intro v a s h
  rw [run_bind] at h
  cases hx1 : x.run (pureState v) with
  | error e =>
    rw [hx1, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨a', s'⟩ := p
    rw [hx1, except_bind_ok] at h
    rw [hx v a' s' hx1] at h
    exact hf a' s'.view a s h

/-- `get` returns the state it was handed. -/
theorem keepsUncached_get {T ε : Type} [SSZRepr T] [HasherTag] :
    KeepsUncached (get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)) := by
  intro v a s h
  rw [show ((get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)).run (pureState v)) = .ok (pureState v, pureState v) from rfl] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- `set` of a rebuilt box lands on that box. -/
theorem keepsUncached_set {T ε : Type} [SSZRepr T] [HasherTag] (w : T) :
    KeepsUncached (set (pureState w) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) := by
  intro v a s h
  rw [show ((set (pureState w) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit).run
      (pureState v)) = .ok ((), pureState w) from rfl] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- `modify` through a writer that maps `pureState v` to `pureState` of some value.
The hypothesis is what a pure `State → State` writer fact such as
`modBalance_pureState` supplies. -/
theorem keepsUncached_modify {T ε : Type} [SSZRepr T] [HasherTag] (f : SSZ.Box HasherTag.H T →
    SSZ.Box HasherTag.H T)
    (hf : ∀ v : T, ∃ w, f (pureState v) = pureState w) :
    KeepsUncached (modifyThe (SSZ.Box HasherTag.H T) f :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) := by
  intro v a s h
  obtain ⟨w, hw⟩ := hf v
  rw [show ((modifyThe (SSZ.Box HasherTag.H T) f : StateT (SSZ.Box HasherTag.H T)
      (Except ε) PUnit).run (pureState v)) = .ok ((), f (pureState v)) from rfl, hw] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- `getStateRoot` writes back the box `Box.hashTreeRoot` returned, and
`hashTreeRoot_uncachedBox` says the uncached box comes back unchanged. -/
theorem keepsUncached_getStateRoot {T ε : Type} [SSZRepr T] [HasherTag] :
    KeepsUncached (getStateRoot (S := SSZ.Box HasherTag.H T) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) ByteArray) := by
  intro v a s h
  rw [show ((getStateRoot (S := SSZ.Box HasherTag.H T) : StateT (SSZ.Box HasherTag.H T)
      (Except ε) ByteArray).run (pureState v))
      = .ok (((pureState v).hashTreeRoot).1, ((pureState v).hashTreeRoot).2) from rfl,
    SizzLean.Proofs.hashTreeRoot_uncachedBox] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- `liftErr` of a pure `Except` value passes the state through unchanged; the
flavour never leaves the box it started on. -/
theorem keepsUncached_liftErr {T ε ε' α : Type} [SSZRepr T] [HasherTag] [ErrorConv ε' ε]
    (x : Except ε' α) :
    KeepsUncached (liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
      StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  intro v a s h
  cases hx : (x.mapError ErrorConv.conv : Except ε α) with
  | error e =>
    rw [show ((liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
        StateT (SSZ.Box HasherTag.H T) (Except ε) α).run (pureState v))
        = .error e from by rw [liftErr, hx]; rfl] at h
    simp at h
  | ok b =>
    rw [show ((liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
        StateT (SSZ.Box HasherTag.H T) (Except ε) α).run (pureState v))
        = .ok (b, pureState v) from by rw [liftErr, hx]; rfl] at h
    injection h with h1
    injection h1 with _ h2
    subst h2
    rfl

/-- `dite` keeps the flavour when both branches do. `if` and the `assert` /
`assertH` expansions are special cases. -/
theorem keepsUncached_dite {T ε α : Type} [SSZRepr T] [HasherTag] {c : Prop} [Decidable c]
    {t : c → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {e : ¬c → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (ht : ∀ h : c, KeepsUncached (t h)) (he : ∀ h : ¬c, KeepsUncached (e h)) :
    KeepsUncached (dite c t e) := by
  intro v a s h
  split at h
  · exact ht (by assumption) v a s h
  · exact he (by assumption) v a s h

/-- `if` keeps the flavour when both branches do. -/
theorem keepsUncached_ite {T ε α : Type} [SSZRepr T] [HasherTag] {c : Prop} [Decidable c]
    {x y : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hx : c → KeepsUncached x) (hy : ¬c → KeepsUncached y) :
    KeepsUncached (if c then x else y) := by
  intro v a s h
  split at h
  · exact hx (by assumption) v a s h
  · exact hy (by assumption) v a s h

/-- `List.forIn` keeps the flavour when every step body does: by induction, the
`yield` continuation is the rest of the loop and the `done` continuation is
`pure`. -/
theorem keepsUncached_forIn_list {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (hf : ∀ a b, KeepsUncached (f a b)) :
    ∀ (l : List α) (init : β), KeepsUncached (forIn l init f) := by
  intro l
  induction l with
  | nil =>
    intro init
    rw [List.forIn_nil]
    exact keepsUncached_pure init
  | cons a rest ih =>
    intro init
    rw [List.forIn_cons]
    exact keepsUncached_bind (hf a init) (fun step => by
      cases step with
      | done x => exact keepsUncached_pure x
      | yield b => exact ih b)

/-- `List.foldlM` keeps the flavour when every step does. -/
theorem keepsUncached_foldlM_list {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : β → α → StateT (SSZ.Box HasherTag.H T) (Except ε) β)
    (hf : ∀ b a, KeepsUncached (f b a)) :
    ∀ (l : List α) (init : β), KeepsUncached (l.foldlM f init) := by
  intro l
  induction l with
  | nil =>
    intro init
    rw [List.foldlM_nil]
    exact keepsUncached_pure init
  | cons a rest ih =>
    intro init
    rw [List.foldlM_cons]
    exact keepsUncached_bind (hf init a) (fun b => ih b)

/-- `forIn` over a `Std.Legacy.Range` keeps the flavour when every step body
does: the range walk is the walk of `List.range n`, the same reduction the loop
proofs run. This is the shape `for i in [0:n]` elaborates to, with or without
`let mut` accumulators threading through the body. -/
theorem keepsUncached_forIn_range {T ε β : Type} [SSZRepr T] [HasherTag]
    (f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (hf : ∀ i b, KeepsUncached (f i b)) :
    ∀ (n : Nat) (init : β), KeepsUncached (forIn [0:n] init f) := by
  intro n init
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact keepsUncached_forIn_list f hf (List.range n) init

/-- `Array.forIn` keeps the flavour when every step body does: the array walk is
the walk of its `toList`. -/
theorem keepsUncached_forIn_array {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (hf : ∀ a b, KeepsUncached (f a b)) :
    ∀ (xs : Array α) (init : β), KeepsUncached (forIn xs init f) := by
  intro xs init
  rw [← Array.forIn_toList]
  exact keepsUncached_forIn_list f hf xs.toList init

/-- `ForM.forM` over an `Array` keeps the flavour when the handler does: the fold
is `List.forIn` over the elements, always yielding. This is the shape of
`processOperationsForM`, the named fold of `processOperations`'s operation
loops. -/
theorem keepsUncached_forM_array {T ε α : Type} [SSZRepr T] [HasherTag]
    (handler : α → StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit)
    (hf : ∀ a, KeepsUncached (handler a)) :
    ∀ xs : Array α, KeepsUncached (ForM.forM xs handler) := by
  intro xs
  rw [show (ForM.forM xs handler) = (xs.foldlM (fun _ => handler) ⟨⟩) from rfl,
    ← Array.foldlM_toList]
  exact keepsUncached_foldlM_list (fun _ a => handler a) (fun _ a => hf a) xs.toList ⟨⟩

/-- One `KeepsUncached` obligation at a time, from the closure lemmas alone: a
leaf (`pure`, `throw`, `get`, a `liftErr`-shaped read or checked op), a gate or
`match` (`dite` splitting, `split`), a state write through the record update, a
loop or fold, or a bind to split. Nothing unfolds a handler body by hand; a
handler proof is one `unfold` of its body and this tactic. -/
macro "keeps_uncached" : tactic => `(tactic| fail)
macro_rules
  | `(tactic| keeps_uncached) => `(tactic|
      repeat' first
        | exact keepsUncached_get
        | exact keepsUncached_pure _
        | exact keepsUncached_throw _
        | refine keepsUncached_dite (fun _ => ?_) (fun _ => ?_)
        | (apply keepsUncached_modify; intro v; exact ⟨_, by rfl⟩)
        | (apply keepsUncached_forIn_range; intro i b; keeps_uncached)
        | (apply keepsUncached_forM_array; intro a; keeps_uncached)
        | refine keepsUncached_bind ?_ (fun a => ?_)
        | exact keepsUncached_liftErr _
        | split)

/-! ## Flavour from one start, and through local bindings

`KeepsUncached` quantifies over every start value. Two refinements carry the
flavour through the constructs the first closure set cannot see: a per-start
form, and actions that return a box. -/

/-- `act`, run on the uncached box of this one start value `v`, returns an
uncached box whenever it succeeds. The per-start form a `get` continuation
needs: the continuation runs on the box `get` handed back, which is the uncached
box of the read value, and the fact about it is stated at that value. -/
def KeepsUncachedFrom {T ε α : Type} [SSZRepr T] [HasherTag] (v : T)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) : Prop :=
  ∀ a s, act.run (pureState v) = .ok (a, s) → s = pureState s.view

/-- The per-start form is the same claim at one start; the two forms convert. -/
theorem keepsUncached_iff_forall_from {T ε α : Type} [SSZRepr T] [HasherTag]
    {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α} :
    KeepsUncached act ↔ ∀ v, KeepsUncachedFrom v act :=
  ⟨fun h v a s hs => h v a s hs, fun h v a s hs => h v a s hs⟩

/-- Bind at one start: the continuation's fact is stated at any post-value and
any post-start, because the first action's own conclusion hands over
`pureState s'.view` as the box the continuation actually runs on. -/
theorem keepsUncachedFrom_bind {T ε α β : Type} [SSZRepr T] [HasherTag]
    {v : T} {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (hx : KeepsUncachedFrom v x) (hf : ∀ a w, KeepsUncachedFrom w (f a)) :
    KeepsUncachedFrom v (x >>= f) := by
  intro a s h
  rw [run_bind] at h
  cases hx1 : x.run (pureState v) with
  | error e =>
    rw [hx1, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨a', s'⟩ := p
    rw [hx1, except_bind_ok] at h
    rw [hx a' s' hx1] at h
    exact hf a' s'.view a s h

/-- Per-start leaves, for chains that thread a known start box: `pure`. -/
theorem keepsUncachedFrom_pure {T ε α : Type} [SSZRepr T] [HasherTag] (v : T) (a : α) :
    KeepsUncachedFrom v (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  intro a' s h
  rw [run_pure] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- Per-start leaves: `throw`. -/
theorem keepsUncachedFrom_throw {T ε α : Type} [SSZRepr T] [HasherTag] (v : T) (e : ε) :
    KeepsUncachedFrom v (throw e : StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  intro a s h
  rw [run_throw] at h
  simp at h

/-- Per-start leaves: `liftErr`-shaped reads and checked ops. -/
theorem keepsUncachedFrom_liftErr {T ε ε' α : Type} [SSZRepr T] [HasherTag] [ErrorConv ε' ε]
    (v : T) (x : Except ε' α) :
    KeepsUncachedFrom v (liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
      StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  cases hx : (x.mapError ErrorConv.conv : Except ε α) with
  | error e =>
    intro a s h
    rw [show ((liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
        StateT (SSZ.Box HasherTag.H T) (Except ε) α).run (pureState v))
        = .error e from by rw [liftErr, hx]; rfl] at h
    simp at h
  | ok b =>
    intro a s h
    rw [show ((liftErr (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) x :
        StateT (SSZ.Box HasherTag.H T) (Except ε) α).run (pureState v))
        = .ok (b, pureState v) from by rw [liftErr, hx]; rfl] at h
    injection h with h1
    injection h1 with _ h2
    subst h2
    rfl

/-- Per-start leaves: `dite`. -/
theorem keepsUncachedFrom_dite {T ε α : Type} [SSZRepr T] [HasherTag] {v : T} {c : Prop}
    [Decidable c]
    {t : c → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {e : ¬c → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (ht : ∀ h : c, KeepsUncachedFrom v (t h)) (he : ∀ h : ¬c, KeepsUncachedFrom v (e h)) :
    KeepsUncachedFrom v (dite c t e) := by
  intro a s h
  split at h
  · exact ht (by assumption) a s h
  · exact he (by assumption) a s h

/-- Per-start leaves: `get`, which hands back the uncached box of its own
start value. -/
theorem keepsUncachedFrom_get {T ε : Type} [SSZRepr T] [HasherTag] (v : T) :
    KeepsUncachedFrom v (get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)) := by
  intro a s h
  rw [show ((get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)).run (pureState v)) = .ok (pureState v, pureState v) from rfl] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- Per-start leaves: `ite`. -/
theorem keepsUncachedFrom_ite {T ε α : Type} [SSZRepr T] [HasherTag] {v : T} {c : Prop}
    [Decidable c] {x y : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hx : c → KeepsUncachedFrom v x) (hy : ¬c → KeepsUncachedFrom v y) :
    KeepsUncachedFrom v (if c then x else y) := by
  intro a s h
  split at h
  · exact hx (by assumption) a s h
  · exact hy (by assumption) a s h

/-- `set` of a rebuilt box lands on that box, from any start. -/
theorem keepsUncachedFrom_set {T ε : Type} [SSZRepr T] [HasherTag] (v w : T) :
    KeepsUncachedFrom v (set (pureState w) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) := by
  intro a s h
  rw [show ((set (pureState w) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit).run
      (pureState v)) = .ok ((), pureState w) from rfl] at h
  injection h with h1
  injection h1 with _ h2
  subst h2
  rfl

/-- `get` at one start, handing its continuation the uncached box of that
start's value. The splice the locally-threaded-state proofs need: after it, the
body is stated with `pureState v` in place of the box, and the local writes on
it reduce to record updates. -/
theorem keepsUncachedFrom_get_bind {T ε α : Type} [SSZRepr T] [HasherTag] {v : T}
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hg : ∀ w, KeepsUncachedFrom w (g (pureState w))) :
    KeepsUncachedFrom v (get >>= g) := by
  intro a s h
  rw [run_bind,
    show ((get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)).run (pureState v)) = .ok (pureState v, pureState v) from rfl,
    except_bind_ok] at h
  exact hg v a s h

/-- `throw` short-circuits a bind: the continuation never runs. -/
theorem keepsUncachedFrom_throw_bind {T ε α β : Type} [SSZRepr T] [HasherTag] {v : T}
    (e : ε) (k : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β) :
    KeepsUncachedFrom v (throw e >>= k) := by
  intro a s h
  rw [run_bind, run_throw, except_bind_error] at h
  simp at h

/-- `get` hands its continuation the uncached box of the value it read. The
lemma that carries a locally-threaded state: after it, writes on the read box
reduce to record updates on the read value, and a `set` of that term closes
with `keepsUncached_set`. -/
theorem keepsUncached_get_bind {T ε α : Type} [SSZRepr T] [HasherTag]
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hg : ∀ v, KeepsUncachedFrom v (g (pureState v))) :
    KeepsUncached (get >>= g) := by
  intro v a s h
  rw [run_bind,
    show ((get : StateT (SSZ.Box HasherTag.H T) (Except ε)
      (SSZ.Box HasherTag.H T)).run (pureState v)) = .ok (pureState v, pureState v) from rfl,
    except_bind_ok] at h
  exact hg v a s h

/-- `act` returns `pureState` of some value and keeps the flavour of the
threaded state. The shape of `increaseBalance` and `decreaseBalance`: they take
the state they write as an explicit argument and return the new one as their
value, so the box a later `set` receives is their return value. -/
def ReturnsUncached {T ε : Type} [SSZRepr T] [HasherTag]
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)) : Prop :=
  ∀ v b s, act.run (pureState v) = .ok (b, s) → (∃ w, b = pureState w) ∧ s = pureState s.view

/-- Bind through an action that returns a box, at one start: the same
composition as `returnsUncached_bind`, stated per-start so a proof that threads
a known start box can chain it. -/
theorem returnsUncachedFrom_bind {T ε α : Type} [SSZRepr T] [HasherTag]
    {v : T} {x : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)}
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hx : ReturnsUncached x)
    (hg : ∀ w w', KeepsUncachedFrom w' (g (pureState w))) :
    KeepsUncachedFrom v (x >>= g) := by
  intro a s h
  rw [run_bind] at h
  cases hx1 : x.run (pureState v) with
  | error e =>
    rw [hx1, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨b, s'⟩ := p
    rw [hx1, except_bind_ok] at h
    obtain ⟨⟨w, hbw⟩, hsw⟩ := hx v b s' hx1
    rw [hbw, hsw] at h
    exact hg w s'.view a s h

/-- Bind through an action that returns a box: the bound value is `pureState w`
for some `w`, and the continuation's per-start fact holds at any start, so the
composition keeps the flavour. -/
theorem returnsUncached_bind {T ε α : Type} [SSZRepr T] [HasherTag]
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)}
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hx : ReturnsUncached x)
    (hg : ∀ w w', KeepsUncachedFrom w' (g (pureState w))) :
    KeepsUncached (x >>= g) := by
  intro v a s h
  rw [run_bind] at h
  cases hx1 : x.run (pureState v) with
  | error e =>
    rw [hx1, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨b, s'⟩ := p
    rw [hx1, except_bind_ok] at h
    obtain ⟨⟨w, hbw⟩, hsw⟩ := hx v b s' hx1
    rw [hbw, hsw] at h
    exact hg w s'.view a s h


/-- A loop whose accumulator carries a box keeps the flavour, and hands back an
accumulator that still satisfies `P`, provided every body does the same for a
`P`-holding accumulator. `P` says what the box component of the accumulator is
(usually: it equals `pureState` of something). This is the form the
`let mut stateAcc` loops need: the box rides the accumulator, not the monad. -/
theorem keepsUncachedFrom_forIn_list_inv {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (l : List α) :
    ∀ (init : β) (v : T), P init →
      KeepsUncachedFrom v (forIn l init f) ∧
        ∀ r s, (forIn l init f).run (pureState v) = .ok (r, s) → P r := by
  induction l with
  | nil =>
    intro init v hinit
    refine ⟨fun a s h => ?_, fun r s h => ?_⟩
    · rw [List.forIn_nil] at h
      injection h with h1
      injection h1 with _ h3
      subst h3
      rfl
    · rw [List.forIn_nil] at h
      injection h with h1
      injection h1 with h2 _
      subst h2
      exact hinit
  | cons x rest ih =>
    intro init v hinit
    rw [List.forIn_cons]
    refine ⟨?_, ?_⟩
    · intro a s h
      rw [run_bind] at h
      cases hstep : (f x init).run (pureState v) with
      | error e =>
        rw [hstep, except_bind_error] at h
        simp at h
      | ok p =>
        obtain ⟨st, s'⟩ := p
        rw [hstep, except_bind_ok] at h
        simp only at h
        obtain ⟨hthread, hP⟩ := hf x init v st s' hinit hstep
        rw [hthread] at h
        cases st with
        | done x' => exact keepsUncached_pure x' s'.view a s h
        | yield b =>
          change (forIn rest b f).run (pureState s'.view) = .ok (a, s) at h
          exact (ih b s'.view hP).1 a s h
    · intro r s h
      rw [run_bind] at h
      cases hstep : (f x init).run (pureState v) with
      | error e =>
        rw [hstep, except_bind_error] at h
        simp at h
      | ok p =>
        obtain ⟨st, s'⟩ := p
        rw [hstep, except_bind_ok] at h
        simp only at h
        obtain ⟨hthread, hP⟩ := hf x init v st s' hinit hstep
        rw [hthread] at h
        cases st with
        | done x' =>
          injection h with h1
          injection h1 with h2 _
          subst h2
          exact hP
        | yield b =>
          change (forIn rest b f).run (pureState s'.view) = .ok (r, s) at h
          exact (ih b s'.view hP).2 r s h

/-- The `Array` form of the invariant loop: the array walk is the walk of its
`toList`. -/
theorem keepsUncachedFrom_forIn_array_inv {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (xs : Array α) :
    ∀ (init : β) (v : T), P init →
      KeepsUncachedFrom v (forIn xs init f) ∧
        ∀ r s, (forIn xs init f).run (pureState v) = .ok (r, s) → P r := by
  simp only [← Array.forIn_toList]
  exact keepsUncachedFrom_forIn_list_inv f P hf xs.toList

/-- A loop whose every body keeps the flavour keeps it too, and no invariant
constrains the accumulator. The shape of the `slashedAny` loop and of accumulator
walks whose carried values are plain (no box). -/
theorem keepsUncachedFrom_forIn_array_of_keeps {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (hf : ∀ x b v, KeepsUncachedFrom v (f x b))
    (xs : Array α) (init : β) {v : T} :
    KeepsUncachedFrom v (forIn xs init f) :=
  (keepsUncachedFrom_forIn_array_inv f (fun _ => True)
    (fun x b v' r s _ h => ⟨hf x b v' r s h, trivial⟩) xs init v trivial).1

/-- The invariant loop composed with its continuation: the value the loop returns
satisfies `P`, and the continuation's fact is stated *under* that `P`, so a proof
about what follows the loop can name the box component of the accumulator. This is
the shape of the `let mut stateAcc` loop in `processAttestation`. -/
theorem keepsUncachedFrom_forIn_list_bind_P {T ε α β γ : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ b w', P b → KeepsUncachedFrom w' (k b))
    (l : List α) (init : β) {v : T} (hinit : P init) :
    KeepsUncachedFrom v (forIn l init f >>= k) := by
  obtain ⟨h1, h2⟩ := keepsUncachedFrom_forIn_list_inv f P hf l init v hinit
  intro a s h
  rw [run_bind] at h
  cases hx : (forIn l init f).run (pureState v) with
  | error e =>
    rw [hx, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨a', s'⟩ := p
    rw [hx, except_bind_ok] at h
    rw [h1 a' s' hx] at h
    exact hk a' s'.view (h2 a' s' hx) a s h

/-- The `Array` form of the invariant loop bound to its continuation: the array
walk is the walk of its `toList`. -/
theorem keepsUncachedFrom_forIn_array_bind_P {T ε α β γ : Type} [SSZRepr T] [HasherTag]
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ b w', P b → KeepsUncachedFrom w' (k b))
    (xs : Array α) (init : β) {v : T} (hinit : P init) :
    KeepsUncachedFrom v (forIn xs init f >>= k) := by
  simp only [← Array.forIn_toList]
  exact keepsUncachedFrom_forIn_list_bind_P f k P hf hk xs.toList init hinit

/-- The `Std.Legacy.Range` form of the invariant loop bound to its continuation,
the `for i in [0:n]` spelling with a `let mut` accumulator. The walk is the walk of
`List.range n`, the same reduction `keepsUncached_forIn_range` runs. -/
theorem keepsUncachedFrom_forIn_range_bind_P {T ε β γ : Type} [SSZRepr T] [HasherTag]
    (f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ b w', P b → KeepsUncachedFrom w' (k b))
    (n : Nat) (init : β) {v : T} (hinit : P init) :
    KeepsUncachedFrom v (forIn [0:n] init f >>= k) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact keepsUncachedFrom_forIn_list_bind_P f k P hf hk (List.range n) init hinit

/-- The run-level half of an invariant-loop fact: a successful run of `act`
passes the start `w` through and returns a `P` value. A named predicate because
three statements below use the shape; spelling it out three times would repeat
the two conjuncts and bury what each statement is about. -/
def RunPassesP {T ε α : Type} [SSZRepr T] [HasherTag] (P : α → Prop)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) (w : T) : Prop :=
  ∀ r s, act.run (pureState w) = .ok (r, s) → s = pureState s.view ∧ P r

set_option linter.unusedVariables false in
/-- The invariant loop over a `Std.Legacy.Range`, the `for i in [0:n]` spelling:
the run-level facts a nested-loop proof reads, at the same `List.range` reduction. -/
theorem keepsUncachedFrom_forIn_range_inv {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (n : Nat) :
    ∀ (init : β) (v : T), P init →
      KeepsUncachedFrom v (forIn [0:n] init f) ∧
        ∀ r s, (forIn [0:n] init f).run (pureState v) = .ok (r, s) → P r := by
  intro init v hinit
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsize, show ([:n] : Std.Legacy.Range).start = 0 from rfl,
    show ([:n] : Std.Legacy.Range).step = 1 from rfl, ← List.range_eq_range']
  exact keepsUncachedFrom_forIn_list_inv f P hf (List.range n) init v hinit

/-- The run-level half of the invariant loop over a `Std.Legacy.Range`, paired into
one fact: a successful run of the walk passes the start through and returns a `P`
value. What a nested-loop body proof reads of the inner walk. -/
theorem keepsUncachedFrom_forIn_range_run_inv {T ε α β : Type} [SSZRepr T] [HasherTag]
    (f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (n : Nat) (init : β) (v : T) (hinit : P init) :
    RunPassesP P (forIn [0:n] init f) v := by
  intro r s h
  have hpair := keepsUncachedFrom_forIn_range_inv (α := α) f P hf n init v hinit
  exact ⟨hpair.1 r s h, hpair.2 r s h⟩

theorem run_sszGetIdx_some {α : Type} {cap : Nat} {σ ε : Type} [ErrorConv IndexError ε] {y : α}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (sb : σ)
    (hq : xs.val[i]? = some y) :
    (EthCLLib.Spec.sszGetIdx (E := ε) (m := StateT σ (Except ε)) xs i).run sb = .ok (y, sb) := by
  show (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
    (Except.mapError (ErrorConv.conv (F := ε))
      (match xs.val[i]? with
      | some a => Except.ok a
      | none => .error (SizzLean.Cache.IndexError.indexError i xs.val.size)))).run sb = _
  rw [hq]
  exact run_ofExcept_ok sb

theorem run_sszGetIdx_none {α : Type} {cap : Nat} {σ ε : Type} [ErrorConv IndexError ε]
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (sb : σ)
    (hq : xs.val[i]? = none) :
    (EthCLLib.Spec.sszGetIdx (E := ε) (m := StateT σ (Except ε)) xs i).run sb
      = .error (ErrorConv.conv (SizzLean.Cache.IndexError.indexError i xs.val.size)) := by
  show (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
    (Except.mapError (ErrorConv.conv (F := ε))
      (match xs.val[i]? with
      | some a => Except.ok a
      | none => .error (SizzLean.Cache.IndexError.indexError i xs.val.size)))).run sb = _
  rw [hq]
  exact run_ofExcept_error sb

set_option linter.unusedVariables false in
/-- Run-level transfer through a bind: a first action whose successful runs pass
the start through and return a `P` value, composed with a continuation that turns
`P` into `Q`. The shape a nested-loop body proof reads: the inner loop's run facts
transfer through the code that follows it. -/
theorem run_bind_inv {T ε α β γ : Type} [SSZRepr T] [HasherTag] (w : T)
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {k : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (P : α → Prop) (Q : β → Prop)
    (hx : ∀ r s, x.run (pureState w) = .ok (r, s) → s = pureState s.view ∧ P r)
    (hk : ∀ (r : α) (s' : T), P r → ∀ a s, (k r).run (pureState s') = .ok (a, s) →
      s = pureState s.view ∧ Q a) :
    RunPassesP Q (do let r ← x; k r) w := by
  intro a s h
  rw [show ((do let r ← x; k r) = (x >>= k)) from rfl] at h
  rw [run_bind] at h
  cases hr : x.run (pureState w) with
  | error e =>
    rw [hr, except_bind_error] at h
    simp at h
  | ok p =>
    obtain ⟨r, s'⟩ := p
    rw [hr, except_bind_ok] at h
    simp only at h
    obtain ⟨h1, h2⟩ := hx r s' hr
    rw [h1] at h
    exact hk r s'.view h2 a s h

/-- The run-level half of the invariant loop over a `Std.Legacy.Range`, bound to
its continuation: a run of the loop followed by `k` passes the start through and
returns a `Q` value, given the body's run facts and the continuation's own. The
composed form a nested-loop body proof applies. -/
theorem keepsUncachedFrom_forIn_range_bind_run_inv {T ε α β γ : Type} [SSZRepr T] [HasherTag]
    (f : Nat → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop) (Q : γ → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ (r : β) (s' : T), P r → ∀ a s, (k r).run (pureState s') = .ok (a, s) →
      s = pureState s.view ∧ Q a)
    (n : Nat) (init : β) (v : T) (hinit : P init) :
    RunPassesP Q (do let r ← forIn [0:n] init f; k r) v := by
  intro r s h
  exact run_bind_inv (T := T) (ε := ε) (α := β) (γ := γ) v P Q
    (keepsUncachedFrom_forIn_range_run_inv (α := α) f P hf n init v hinit) hk r s h


/-- The bind law the predicate buys: under `KeepsUncached x`, `runPure` of a bind
is the bind of the `runPure`s. The first action's post-state is the uncached box
of its own view, so the continuation's `runPure` runs on exactly the box the
composite ran it on. Without the hypothesis the law fails: `runPure` reads only
the view, and a first action that returns a cached box makes the two sides run
the continuation on different boxes. -/
theorem runPure_bind_of_keepsUncached {T ε α β : Type} [SSZRepr T] [HasherTag]
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {f : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (hx : KeepsUncached x) (v : T) :
    runPure (x >>= f) v = (runPure x v) >>= fun p => runPure (f p.1) p.2 := by
  rw [runPure_eq, runPure_eq, run_bind]
  cases h : x.run (pureState v) with
  | error e =>
    simp only [except_bind_error, Except.map]
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [except_bind_ok, hx v a s h]
    simp only [Except.map, except_bind_ok, runPure_eq]
    rfl

end EthCLSpecs.Proofs
