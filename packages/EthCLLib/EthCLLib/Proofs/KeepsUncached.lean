import EthCLLib.Spec.State
import EthCLLib.Spec.Header
import EthCLLib.Proofs.Run
import SizzLean.Proofs.UncachedBox

/-!
# `EthCLLib.Proofs.KeepsUncached`: actions that never leave the uncached box

`runPure` reads only the post-state's *view*, which is why it has no bind law in
general: an action run on the uncached box of `v` may land on a *cached* box, and
`runPure` of the continuation would then run on `pureState w` while the composite
ran on that cached box. `KeepsUncached act` is exactly the property whose absence
blocks the law: every successful run of `act` that starts on `pureState v` ends on
an uncached box. Under it the bind law holds
(`runPure_bind_of_keepsUncached`), and a composite body's `runPure` equation
splits into its steps'.

The predicate is generic over the SSZ value type `T`, the error `ε`, and the
result `α`, the same way `runPure` is. The closure lemmas cover these constructs of
the spec bodies:

* the leaves `pure`, `throw`, `get`, `getStateRoot`, `liftErr`, the checked list
  constructor `sszOfArrayM`, and `set` of a rebuilt box.
* `bind`, `if` / `dite` and `assert`-shaped gates.
* `modify` through a writer that maps `pureState v` to `pureState` of a value (the
  shape `modBalance_pureState` supplies). A writer that branches on the box or loops
  over it in `Id` proves that hypothesis through `IsPure`.
* the `appendState` and `setOrAppendState` expansions.
* the `for` folds over `List`, `Array`, a range, and `SSZList`, the `forM` fold over
  `Array`, and `fuelLoop`.
* actions that return a box (`ReturnsUncached`), with a range loop that returns its
  box accumulator.

A `match` on a plain value reduces to its branch by `cases` on the scrutinee, and
`keepsUncached_congr` carries the fact across such a reduction. Under
`KeepsUncached`, a `runPure` fact and a `.run` fact on `pureState` convert
(`runPure_iff_run_of_keepsUncached`), and a successful bind splits at a `pureState`
midpoint (`run_bind_eq_ok_pure`).

`KeepsUncached` is a claim about the *box flavour a run threads*, not about
behavior: it says nothing about which value the run writes or whether it rejects.
The fork-body lemmas that discharge it (`EthCLSpecs/Proofs/Gloas/ProcessOperations.lean` and
siblings) are therefore supporting facts, untagged, and each one is a
construction over these closure lemmas rather than an unfolding of the fork body's
effect.

This module is box-level infrastructure. Its lemmas quantify over boxes by
design, in their hypotheses and conclusions: they are claims about the box
flavour itself. The plain-value rule (`SPECS_ARCHITECTURE.md` §11.1) keeps
fork-body theorem statements over plain values, and it does not apply here.
The check walks the theorems under `EthCLSpecs.Proofs`, and this module sits in
the framework, under `EthCLLib.Proofs`, so the walk never visits it. The scope
rule would spare these lemmas regardless: their statements name no fork
constant, and the same holds for the generic lemmas in `EthCLLib/Proofs/Run.lean`.
A theorem under `EthCLSpecs.Proofs` whose statement names a fork constant and
quantifies over the box is the case the `box_generic` marker is for.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

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

/-- `sszOfArrayM`, the spec's `List[T, N](a)`, returns the list or raises `.listFull`
through `throwListFull`, a `liftErr`. Neither branch writes the state. -/
theorem keepsUncached_sszOfArrayM {T ε α : Type} [SSZRepr T] [HasherTag]
    [ErrorConv StateTransitionError ε] {cap : Nat} (field : String) (a : Array α) :
    KeepsUncached (sszOfArrayM (m := StateT (SSZ.Box HasherTag.H T) (Except ε)) (cap := cap)
      field a) := by
  unfold sszOfArrayM
  split
  · exact keepsUncached_pure _
  · unfold throwListFull
    exact keepsUncached_liftErr _

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

/-- `Array.mapM` keeps the flavour when each step does. The run maps the list of the
array, and each step of that list map is a bind. -/
theorem keepsUncached_arrayMapM {T ε β γ : Type} [SSZRepr T] [HasherTag]
    (f : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ)
    (hf : ∀ b, KeepsUncached (f b)) (xs : Array β) : KeepsUncached (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  refine keepsUncached_bind ?_ (fun _ => keepsUncached_pure _)
  generalize xs.toList = l
  induction l with
  | nil => exact keepsUncached_pure _
  | cons b l ih =>
    rw [List.mapM_cons]
    exact keepsUncached_bind (hf b) (fun _ => keepsUncached_bind ih (fun _ => keepsUncached_pure _))

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

/-- Per-start leaves: `sszOfArrayM`. -/
theorem keepsUncachedFrom_sszOfArrayM {T ε α : Type} [SSZRepr T] [HasherTag]
    [ErrorConv StateTransitionError ε] {cap : Nat} (v : T) (field : String) (a : Array α) :
    KeepsUncachedFrom v (sszOfArrayM (m := StateT (SSZ.Box HasherTag.H T) (Except ε))
      (cap := cap) field a) :=
  keepsUncached_iff_forall_from.mp (keepsUncached_sszOfArrayM field a) v

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

/-- Under `KeepsUncached`, a `runPure` fact and a `.run` fact on the uncached box say
the same thing. The forward direction is the one a restated theorem needs: it names
the post-box of a successful run as `pureState w`. -/
theorem runPure_iff_run_of_keepsUncached {T ε α : Type} [SSZRepr T] [HasherTag]
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α} (hx : KeepsUncached x)
    (v w : T) (a : α) :
    runPure x v = .ok (a, w) ↔ x.run (pureState v) = .ok (a, pureState w) := by
  refine ⟨fun h => ?_, runPure_of_run_ok⟩
  rw [runPure_eq] at h
  cases hr : x.run (pureState v) with
  | error e =>
    rw [hr] at h
    cases h
  | ok p =>
    obtain ⟨a', s⟩ := p
    rw [hr] at h
    injection h with h1
    injection h1 with ha hs
    dsimp only at ha hs
    rw [hx v a' s hr, ha, hs]

/-- A successful bind whose first action keeps the flavour splits at a `pureState`
midpoint. The first run ends on `pureState w`, and the continuation runs from it. -/
theorem run_bind_eq_ok_pure {T ε α β : Type} [SSZRepr T] [HasherTag]
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {k : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β} (hx : KeepsUncached x)
    {v : T} {r : β × SSZ.Box HasherTag.H T} (h : (x >>= k).run (pureState v) = .ok r) :
    ∃ a w, x.run (pureState v) = .ok (a, pureState w) ∧ (k a).run (pureState w) = .ok r := by
  obtain ⟨a, s1, h1, h2⟩ := run_bind_eq_ok x k (pureState v) r h
  have hs1 := hx v a s1 h1
  rw [hs1] at h1 h2
  exact ⟨a, s1.view, h1, h2⟩

/-! ## `for` over `SSZList`, and `fuelLoop`

`for x in xs` over an `SSZList` runs the `Array` loop on `xs.val`: the `ForIn`
instance delegates to the array (`SizzLean/Repr/Instances.lean`). Each lemma here is
the array lemma at `xs.val`, and the two sides agree by unfolding that instance. -/

/-- A `for` loop over an `SSZList` keeps the flavour when every step body does. The
shape of the six operation loops of `processOperations`. -/
theorem keepsUncached_forIn_sszList {T ε α β : Type} [SSZRepr T] [HasherTag] {cap : Nat}
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (hf : ∀ a b, KeepsUncached (f a b)) (xs : SizzLean.Repr.SSZList α cap) (init : β) :
    KeepsUncached (forIn xs init f) :=
  keepsUncached_forIn_array f hf xs.val init

/-- The `SSZList` form of the invariant loop (`keepsUncachedFrom_forIn_array_inv`). -/
theorem keepsUncachedFrom_forIn_sszList_inv {T ε α β : Type} [SSZRepr T] [HasherTag]
    {cap : Nat}
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β)) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (xs : SizzLean.Repr.SSZList α cap) :
    ∀ (init : β) (v : T), P init →
      KeepsUncachedFrom v (forIn xs init f) ∧
        ∀ r s, (forIn xs init f).run (pureState v) = .ok (r, s) → P r :=
  keepsUncachedFrom_forIn_array_inv f P hf xs.val

/-- The `SSZList` form of `keepsUncachedFrom_forIn_array_of_keeps`: no invariant on
the accumulator. -/
theorem keepsUncachedFrom_forIn_sszList_of_keeps {T ε α β : Type} [SSZRepr T] [HasherTag]
    {cap : Nat}
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (hf : ∀ x b v, KeepsUncachedFrom v (f x b))
    (xs : SizzLean.Repr.SSZList α cap) (init : β) {v : T} :
    KeepsUncachedFrom v (forIn xs init f) :=
  keepsUncachedFrom_forIn_array_of_keeps f hf xs.val init

/-- The `SSZList` form of the invariant loop bound to its continuation
(`keepsUncachedFrom_forIn_array_bind_P`). -/
theorem keepsUncachedFrom_forIn_sszList_bind_P {T ε α β γ : Type} [SSZRepr T] [HasherTag]
    {cap : Nat}
    (f : α → β → StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep β))
    (k : β → StateT (SSZ.Box HasherTag.H T) (Except ε) γ) (P : β → Prop)
    (hf : ∀ x b v r s, P b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ P r.value)
    (hk : ∀ b w', P b → KeepsUncachedFrom w' (k b))
    (xs : SizzLean.Repr.SSZList α cap) (init : β) {v : T} (hinit : P init) :
    KeepsUncachedFrom v (forIn xs init f >>= k) :=
  keepsUncachedFrom_forIn_array_bind_P f k P hf hk xs.val init hinit

/-- `fuelLoop` keeps the flavour when every step does. Induction on the fuel: a
`done` step returns through `pure`, and a `next` step runs the loop with one unit of
fuel less. The shape of `ppdLoop` and `pcLoop`. -/
theorem keepsUncached_fuelLoop {T ε δ α : Type} [SSZRepr T] [HasherTag] (exhausted : α)
    (step : δ → StateT (SSZ.Box HasherTag.H T) (Except ε) (EthCLLib.Spec.Step δ α))
    (hstep : ∀ b, KeepsUncached (step b)) :
    ∀ (fuel : Nat) (init : δ),
      KeepsUncached (EthCLLib.Spec.fuelLoop fuel init exhausted step) := by
  intro fuel
  induction fuel with
  | zero => intro init; exact keepsUncached_pure exhausted
  | succ fuel ih =>
    intro init
    simp only [EthCLLib.Spec.fuelLoop]
    refine keepsUncached_bind (hstep init) fun st => ?_
    cases st with
    | done a => exact keepsUncached_pure a
    | next b => exact ih b

/-! ## The pure box predicate -/

/-- `IsPure b`: the box `b` is the uncached box of some value. The claim a writer
fact makes about the box it returns, and the hypothesis of `keepsUncached_modify`
spelled as a predicate. A writer that branches on the box (`ite`, `dite`) or runs an
`Id` loop over it proves `IsPure` through the closure lemmas below, where `rfl` alone
cannot pick the branch. -/
def IsPure {T : Type} [SSZRepr T] [HasherTag] (b : SSZ.Box HasherTag.H T) : Prop :=
  ∃ w, b = pureState w

/-! ## `appendState` and `setOrAppendState`

Both macros (`EthCLLib/Spec/Header.lean`) open with `getThe`, so the box the rest
reads is the start box. On `pureState v`, `sszAppend?` is `Option.map` of an
`sszUpdate` of `pureState v`, and that update reduces to `pureState` of the record
update. The lemmas take the field reads and writes as abstract functions, so one
lemma serves every field. -/

/-- `getThe` at one start hands its continuation the uncached box of that start's
value. The `getThe` spelling of `keepsUncached_get_bind`, which the two macros
read the state with. -/
theorem keepsUncached_getThe_bind {T ε α : Type} [SSZRepr T] [HasherTag]
    {g : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    (hg : ∀ v, KeepsUncachedFrom v (g (pureState v))) :
    KeepsUncached ((getThe (SSZ.Box HasherTag.H T) :
      StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)) >>= g) := by
  intro v a s h
  rw [run_bind, run_getThe, except_bind_ok] at h
  exact hg v a s h

/-- A box that `Option.map u` returns is pure when `u` returns pure boxes. After
`get` hands the `appendState` expansion the start box `pureState v`, the `some`
branch carries the hypothesis `(push? …).map (fun l => sszUpdate (pureState v) with
f := l) = some s'`, and this lemma names `s'` as pure. -/
theorem isPure_of_map_eq_some {T L : Type} [SSZRepr T] [HasherTag] {o : Option L}
    {u : L → SSZ.Box HasherTag.H T} {s' : SSZ.Box HasherTag.H T}
    (hu : ∀ l, IsPure (u l)) (h : o.map u = some s') : IsPure s' := by
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact hu l

/-- `modify` through a constant writer `fun _ => s'` keeps the flavour when `s'` is
pure. The `some` branch of the `appendState` expansion writes this way.

The expansion is a `match` on `sszAppend? s f x`. Lean elaborates each `match` to a
matcher constant of the declaration that holds it, so a lemma that states the whole
expansion with a `match` of its own does not unify with the spec's. A proof reads the
start box with `keepsUncached_get_bind` or `keepsUncached_getThe_bind`, splits the
spec's `match`, closes the `some` branch with this lemma and `isPure_of_map_eq_some`,
and closes the `none` branch, a `throwListFull`, with `keepsUncached_liftErr`. -/
theorem keepsUncached_modify_const {T ε : Type} [SSZRepr T] [HasherTag]
    (s' : SSZ.Box HasherTag.H T) (hs : IsPure s') :
    KeepsUncached (modifyThe (SSZ.Box HasherTag.H T) (fun _ => s') :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) :=
  keepsUncached_modify _ (fun _ => hs)

/-- The `setOrAppendState f i x` expansion keeps the flavour. The index `i` and the
length `n` are reads of the start box. The first branch is an `appendState`, and
`happ` is its fact. The second branch writes entry `i` through `g`. The third raises
the `IndexError` through `liftErr`. The expansion holds no `match`, so this lemma
unifies with it directly. -/
theorem keepsUncached_setOrAppendState {T ε : Type} [SSZRepr T] [HasherTag]
    [ErrorConv IndexError ε] (i n : SSZ.Box HasherTag.H T → Nat)
    (app : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit)
    (happ : ∀ s, KeepsUncached (app s))
    (g : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T)
    (hg : ∀ s v, IsPure (g s (pureState v))) :
    KeepsUncached ((do
      let s ← getThe (SSZ.Box HasherTag.H T)
      if i s == n s then app s
      else if i s < n s then modifyThe (SSZ.Box HasherTag.H T) (g s)
      else liftErr (Except.error (IndexError.indexError (i s) (n s)) :
        Except IndexError PUnit)) : StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) := by
  refine keepsUncached_getThe_bind (fun w => ?_)
  refine keepsUncachedFrom_ite (fun _ => keepsUncached_iff_forall_from.mp (happ _) w)
    (fun _ => ?_)
  exact keepsUncachedFrom_ite
    (fun _ => keepsUncached_iff_forall_from.mp (keepsUncached_modify _ (hg _)) w)
    (fun _ => keepsUncachedFrom_liftErr w _)

/-! ## Writers that branch on the box or loop over it: `IsPure`

`keepsUncached_modify` asks a writer `f` to map `pureState v` to `pureState` of a
value. A record update closes that by `rfl`. A writer whose body holds an `if` on a
condition `c` about the box does not: `rfl` cannot pick the branch while `c` is open.
The closure below proves `IsPure` one construct at a time. `isPure_apply` covers a
`let`, and an `sszUpdate` of a box that is already pure. `isPure_ite` and
`isPure_dite` split a branch. The `Id` loop lemmas carry `IsPure` through a
`for` loop that runs inside the writer. -/

/-- The uncached box of a value is pure. -/
theorem isPure_pureState {T : Type} [SSZRepr T] [HasherTag] (w : T) :
    IsPure (pureState w) :=
  ⟨w, rfl⟩

/-- `if` of two pure boxes is pure. -/
theorem isPure_ite {T : Type} [SSZRepr T] [HasherTag] {c : Prop} [Decidable c]
    {x y : SSZ.Box HasherTag.H T} (hx : c → IsPure x) (hy : ¬c → IsPure y) :
    IsPure (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx hc
  · rw [if_neg hc]
    exact hy hc

/-- `dite` of two pure boxes is pure. -/
theorem isPure_dite {T : Type} [SSZRepr T] [HasherTag] {c : Prop} [Decidable c]
    {x : c → SSZ.Box HasherTag.H T} {y : ¬c → SSZ.Box HasherTag.H T}
    (hx : ∀ h : c, IsPure (x h)) (hy : ∀ h : ¬c, IsPure (y h)) :
    IsPure (dite c x y) := by
  by_cases hc : c
  · rw [dif_pos hc]
    exact hx hc
  · rw [dif_neg hc]
    exact hy hc

/-- A box function `g` applied to a pure box is pure when `g` maps every uncached
box to a pure one. `let y := b; k y` is `k b` up to `zeta`, so this lemma carries a
`let` (with `g := k`). An `sszUpdate` of a pure box is the case `g := fun s =>
sszUpdate s with …`, whose premise closes by `fun _ => ⟨_, rfl⟩`. -/
theorem isPure_apply {T : Type} [SSZRepr T] [HasherTag] {b : SSZ.Box HasherTag.H T}
    (g : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T) (hb : IsPure b)
    (hg : ∀ w, IsPure (g (pureState w))) : IsPure (g b) := by
  obtain ⟨w, rfl⟩ := hb
  exact hg w

/-- `modify` through a writer that maps every uncached box to a pure one. The
hypothesis of `keepsUncached_modify`, spelled as `IsPure`. -/
theorem keepsUncached_modify_of_isPure {T ε : Type} [SSZRepr T] [HasherTag]
    (f : SSZ.Box HasherTag.H T → SSZ.Box HasherTag.H T)
    (hf : ∀ v : T, IsPure (f (pureState v))) :
    KeepsUncached (modifyThe (SSZ.Box HasherTag.H T) f :
      StateT (SSZ.Box HasherTag.H T) (Except ε) PUnit) :=
  keepsUncached_modify f hf

/-- An invariant of a `for` loop over a list in `Id`. Each body step takes an
accumulator that satisfies `P` to a step whose value satisfies `P`, so the loop
result satisfies `P`. The `Id` counterpart of `view_forIn_list`
(`EthCLLib/Proofs/Frame.lean`), for any invariant. -/
theorem id_forIn_list_inv {δ β : Type} (P : β → Prop) (body : δ → β → Id (ForInStep β))
    (hbody : ∀ d b, P b → P (body d b).run.value) :
    ∀ (l : List δ) (init : β), P init → P (forIn l init body).run := by
  intro l
  induction l with
  | nil => intro init hinit; exact hinit
  | cons d rest ih =>
    intro init hinit
    rw [List.forIn_cons]
    have hd := hbody d init hinit
    revert hd
    cases body d init with
    | done a => intro hd; exact hd
    | yield a => intro hd; exact ih a hd

/-- `id_forIn_list_inv` for a loop over an array. -/
theorem id_forIn_array_inv {δ β : Type} (P : β → Prop) (body : δ → β → Id (ForInStep β))
    (hbody : ∀ d b, P b → P (body d b).run.value) (xs : Array δ) (init : β)
    (hinit : P init) : P (forIn xs init body).run := by
  rw [← Array.forIn_toList]
  exact id_forIn_list_inv P body hbody xs.toList init hinit

/-- `id_forIn_list_inv` for a loop over a range. -/
theorem id_forIn_range_inv {β : Type} (P : β → Prop) (body : Nat → β → Id (ForInStep β))
    (hbody : ∀ d b, P b → P (body d b).run.value) (r : Std.Legacy.Range) (init : β)
    (hinit : P init) : P (forIn r init body).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact id_forIn_list_inv P body hbody _ init hinit

/-- `id_forIn_list_inv` for a loop over an `SSZList`, through its array. -/
theorem id_forIn_sszList_inv {δ β : Type} {cap : Nat} (P : β → Prop)
    (body : δ → β → Id (ForInStep β)) (hbody : ∀ d b, P b → P (body d b).run.value)
    (xs : SizzLean.Repr.SSZList δ cap) (init : β) (hinit : P init) :
    P (forIn xs init body).run :=
  id_forIn_array_inv P body hbody xs.val init hinit

/-- An `Id` loop over a list whose accumulator is the box keeps it pure, when each
body step maps an uncached box to a pure one. The shape of a `let mut state` loop
inside a `modifyState` writer. -/
theorem isPure_id_forIn_list {T δ : Type} [SSZRepr T] [HasherTag]
    (body : δ → SSZ.Box HasherTag.H T → Id (ForInStep (SSZ.Box HasherTag.H T)))
    (hbody : ∀ d w, IsPure (body d (pureState w)).run.value)
    (l : List δ) (init : SSZ.Box HasherTag.H T) (hinit : IsPure init) :
    IsPure (forIn l init body).run :=
  id_forIn_list_inv IsPure body
    (fun d b hb => by obtain ⟨w, rfl⟩ := hb; exact hbody d w) l init hinit

/-- `isPure_id_forIn_list` for a loop over an array. The shape of
`processInactivityUpdates`. -/
theorem isPure_id_forIn_array {T δ : Type} [SSZRepr T] [HasherTag]
    (body : δ → SSZ.Box HasherTag.H T → Id (ForInStep (SSZ.Box HasherTag.H T)))
    (hbody : ∀ d w, IsPure (body d (pureState w)).run.value)
    (xs : Array δ) (init : SSZ.Box HasherTag.H T) (hinit : IsPure init) :
    IsPure (forIn xs init body).run :=
  id_forIn_array_inv IsPure body
    (fun d b hb => by obtain ⟨w, rfl⟩ := hb; exact hbody d w) xs init hinit

/-- `isPure_id_forIn_list` for a loop over a range. The shape of
`processEffectiveBalanceUpdates`. -/
theorem isPure_id_forIn_range {T : Type} [SSZRepr T] [HasherTag]
    (body : Nat → SSZ.Box HasherTag.H T → Id (ForInStep (SSZ.Box HasherTag.H T)))
    (hbody : ∀ d w, IsPure (body d (pureState w)).run.value)
    (r : Std.Legacy.Range) (init : SSZ.Box HasherTag.H T) (hinit : IsPure init) :
    IsPure (forIn r init body).run :=
  id_forIn_range_inv IsPure body
    (fun d b hb => by obtain ⟨w, rfl⟩ := hb; exact hbody d w) r init hinit

/-! ## A loop that returns the box

`applyDeltas` takes the state as an argument, threads it through a range loop of
balance writes, and returns it as its value. `ReturnsUncached` is the fact its
callers bind on. `ReturnsPureVia p` generalizes it to an action whose value carries
a box at the projection `p`, such as a loop body that returns `ForInStep State`. -/

/-- `act`, run on an uncached box, keeps the flavour of the threaded state, and the
box at `p` of its value is pure. `ReturnsUncached` is the case `p := id`. -/
def ReturnsPureVia {T ε α : Type} [SSZRepr T] [HasherTag] (p : α → SSZ.Box HasherTag.H T)
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) : Prop :=
  ∀ v a s, act.run (pureState v) = .ok (a, s) → IsPure (p a) ∧ s = pureState s.view

/-- `ReturnsUncached` is `ReturnsPureVia id`. -/
theorem returnsUncached_of_returnsPureVia {T ε : Type} [SSZRepr T] [HasherTag]
    {act : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)}
    (h : ReturnsPureVia id act) : ReturnsUncached act :=
  h

/-- `pure a` returns `a` and keeps the threaded state. -/
theorem returnsPureVia_pure {T ε α : Type} [SSZRepr T] [HasherTag]
    {p : α → SSZ.Box HasherTag.H T} (a : α) (ha : IsPure (p a)) :
    ReturnsPureVia p (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) := by
  intro v a' s h
  rw [run_pure] at h
  injection h with h1
  injection h1 with h2 h3
  subst h2
  subst h3
  exact ⟨ha, rfl⟩

/-- A bind whose first action keeps the flavour returns what its continuation
returns. -/
theorem returnsPureVia_bind_keeps {T ε α β : Type} [SSZRepr T] [HasherTag]
    {p : β → SSZ.Box HasherTag.H T} {x : StateT (SSZ.Box HasherTag.H T) (Except ε) α}
    {k : α → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (hx : KeepsUncached x) (hk : ∀ a, ReturnsPureVia p (k a)) :
    ReturnsPureVia p (x >>= k) := by
  intro v b s h
  obtain ⟨a, w, h1, h2⟩ := run_bind_eq_ok_pure hx h
  exact hk a w b s h2

/-- A bind through an action that returns a box: the bound box is `pureState w`, so
the continuation's fact at `pureState w` applies. -/
theorem returnsPureVia_bind_returns {T ε β : Type} [SSZRepr T] [HasherTag]
    {p : β → SSZ.Box HasherTag.H T}
    {x : StateT (SSZ.Box HasherTag.H T) (Except ε) (SSZ.Box HasherTag.H T)}
    {k : SSZ.Box HasherTag.H T → StateT (SSZ.Box HasherTag.H T) (Except ε) β}
    (hx : ReturnsUncached x) (hk : ∀ w, ReturnsPureVia p (k (pureState w))) :
    ReturnsPureVia p (x >>= k) := by
  intro v b s h
  obtain ⟨a, s1, h1, h2⟩ := run_bind_eq_ok x k (pureState v) (b, s) h
  obtain ⟨⟨w, hw⟩, hs1⟩ := hx v a s1 h1
  rw [hw, hs1] at h2
  exact hk w s1.view b s h2

/-- A `for` loop over a list whose accumulator is the box returns a pure box, when
the start accumulator is pure and each body maps an uncached accumulator to a step
whose value is pure. -/
theorem returnsUncached_forIn_list {T ε δ : Type} [SSZRepr T] [HasherTag]
    (f : δ → SSZ.Box HasherTag.H T →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T)))
    (hf : ∀ d w, ReturnsPureVia ForInStep.value (f d (pureState w)))
    (l : List δ) (init : SSZ.Box HasherTag.H T) (hinit : IsPure init) :
    ReturnsUncached (forIn l init f) := by
  intro v b s h
  have hf' : ∀ x b v r s, IsPure b → (f x b).run (pureState v) = .ok (r, s) →
      s = pureState s.view ∧ IsPure r.value := by
    intro x b' v' r s' hb hrun
    obtain ⟨w, rfl⟩ := hb
    obtain ⟨h1, h2⟩ := hf x w v' r s' hrun
    exact ⟨h2, h1⟩
  have hpair := keepsUncachedFrom_forIn_list_inv f IsPure hf' l init v hinit
  exact ⟨hpair.2 b s h, hpair.1 b s h⟩

/-- `returnsUncached_forIn_list` for a loop over a range, the `for i in [0:n]`
spelling of `applyDeltas`. -/
theorem returnsUncached_forIn_range {T ε : Type} [SSZRepr T] [HasherTag]
    (f : Nat → SSZ.Box HasherTag.H T →
      StateT (SSZ.Box HasherTag.H T) (Except ε) (ForInStep (SSZ.Box HasherTag.H T)))
    (hf : ∀ d w, ReturnsPureVia ForInStep.value (f d (pureState w)))
    (r : Std.Legacy.Range) (init : SSZ.Box HasherTag.H T) (hinit : IsPure init) :
    ReturnsUncached (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact returnsUncached_forIn_list f hf _ init hinit

/-! ## The `is_pure` and `keeps_uncached` tactics -/

/-- Close an `IsPure` goal about a writer's result, or fail and leave the goal as it
was. The arms are a record update of `pureState w` (`⟨_, rfl⟩`), an `if` or `dite`
on the box, an `Id` loop over an array, a range, or a list whose accumulator is the
box, and `split` for a `match`. `split` cannot see an `if` under a `have`, which is
how a `do` block spells a local binding, so `dsimp only` runs first to inline the
bindings. `focus … done` makes the tactic all or nothing, so a
caller's `first` falls through to its next arm when this one cannot close the goal. -/
macro "is_pure" : tactic => `(tactic| focus
  repeat' first
    | exact ⟨_, rfl⟩
    | refine isPure_ite (fun _ => ?_) (fun _ => ?_)
    | refine isPure_dite (fun _ => ?_) (fun _ => ?_)
    | refine isPure_id_forIn_array _ (fun _ _ => ?_) _ _ ?_
    | refine isPure_id_forIn_range _ (fun _ _ => ?_) _ _ ?_
    | refine isPure_id_forIn_list _ (fun _ _ => ?_) _ _ ?_
    | dsimp only
    | split
  done)

/-- One `KeepsUncached` obligation at a time, from the closure lemmas alone: a
leaf (`pure`, `throw`, `get`, a `liftErr`-shaped read or checked op, `set` of a
rebuilt box), a gate or `match` (`ite`, `dite`, `split`), a state write through
the record update, through a writer that `is_pure` closes, or through the `some`
branch of an `appendState`, a loop, fold, or `Array.mapM`,
a bind to split, or a `get` whose continuation reads the box. That last arm hands
the continuation `pureState v`, so a final `set (sszUpdate state with …)` reduces
to `set` of a rebuilt box. Nothing unfolds a handler body by hand; a handler proof
is one `unfold` of its body and this tactic.

The order of the arms matters. The `get` arm comes before the plain bind arm, which
would forget that the box `get` returns is the start box. The `set` arm comes last
but one, because a failed `set` trial unfolds the goal action.

The two `get` arms unify at reducible transparency (`with_reducible`). The reason is
an inference: at `StateT`, `get >>= fun _ => x` is defeq to `x` by eta, so at the
default transparency `keepsUncached_get_bind` unifies with every goal, and
`repeat'` never stops. At reducible transparency the arm fires only on a goal whose
action is a `get` or `getThe` bind as written.

`keeps_uncached_using [l₁, …]` runs the same loop, and it tries `exact lᵢ` before every
other arm. A body that calls a function with a lemma of its own needs this form. The
plain bind arm unifies at the default transparency, so it unfolds a callee such as
`balanceAfterWithdrawals` to its own body and leaves goals inside that body. With the
callee lemma in the list, the loop closes the callee goal first. `keeps_uncached` is
`keeps_uncached_using []`. -/
syntax "keeps_uncached_using " "[" term,* "]" : tactic

/-- `keeps_uncached_using []`: the closure loop with no callee lemmas. The docstring of
`keeps_uncached_using` describes the arms. -/
macro "keeps_uncached" : tactic => `(tactic| keeps_uncached_using [])

macro_rules
  | `(tactic| keeps_uncached_using [$ls,*]) => do
    let callees ← ls.getElems.mapM fun l => `(tactic| exact $l)
    let callee ← if callees.isEmpty then `(tactic| fail)
      else `(tactic| first $[| $callees:tactic]*)
    `(tactic|
      repeat' first
        | $callee:tactic
        | exact keepsUncached_get
        | exact keepsUncached_pure _
        | exact keepsUncached_throw _
        | refine keepsUncached_dite (fun _ => ?_) (fun _ => ?_)
        | refine keepsUncached_ite (fun _ => ?_) (fun _ => ?_)
        | (apply keepsUncached_modify; intro v; exact ⟨_, by rfl⟩)
        | (apply keepsUncached_modify_of_isPure; intro v; is_pure)
        | (refine keepsUncached_modify_const _ (isPure_of_map_eq_some ?_ (by assumption))
           intro _; exact ⟨_, rfl⟩)
        | (apply keepsUncached_forIn_range; intro i b; keeps_uncached_using [$ls,*])
        | (apply keepsUncached_forIn_sszList; intro a b; keeps_uncached_using [$ls,*])
        | (apply keepsUncached_forIn_array; intro a b; keeps_uncached_using [$ls,*])
        | (apply keepsUncached_forIn_list; intro a b; keeps_uncached_using [$ls,*])
        | (apply keepsUncached_forM_array; intro a; keeps_uncached_using [$ls,*])
        | (apply keepsUncached_arrayMapM; intro a; keeps_uncached_using [$ls,*])
        | with_reducible
            refine keepsUncached_get_bind (fun _ => keepsUncached_iff_forall_from.mp ?_ _)
        | with_reducible
            refine keepsUncached_getThe_bind (fun _ => keepsUncached_iff_forall_from.mp ?_ _)
        | refine keepsUncached_bind ?_ (fun a => ?_)
        | exact keepsUncached_liftErr _
        | exact keepsUncached_sszOfArrayM _ _
        | exact keepsUncached_set _
        | split)

end EthCLLib.Proofs
