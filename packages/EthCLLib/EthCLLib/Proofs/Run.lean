import EthCLLib.Spec.Errors
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.Loop

/-!
# `EthCLLib.Proofs.Run`: the monad facts and the pure box the pure runners share

`EStateM` ships `run_bind` / `run_pure` as `simp` lemmas. The `StateT`-over-`Except`
stack does not, because both steps are definitional there (`StateT.run x s` is `x s`,
and `StateT.bind` threads the pair through `Except`'s own bind). Every Gloas and Heze
run proof needs the same rewrites, so they live once here rather than as a
`simp [StateT.bind, Bind.bind, ...]` unfolding repeated per call site, and rather than
under a fork's runner name.

All five close by `rfl`. They exist to be `rw`/`simp` targets with a readable right-hand
side. Stated at any `σ` / `ε`: nothing in either proof is specific to a fork's state,
and the general form applies to `GloasRun` and `ForkChoiceStoreRun` alike.
`fuelLoop_run_of_next` runs one iteration of the framework loop `fuelLoop`
(`EthCLLib/Spec/Loop.lean`).

The runner names remain in their own modules: `GloasRun` is in
`EthCLSpecs/Proofs/Gloas/Run.lean`, while the fork-neutral `ForkChoiceStoreRun` is
in `EthCLLib/Proofs/StoreRun.lean`.

Two inversion lemmas start from a successful run. `run_bind_eq_ok` splits a successful
bind into its two runs. `run_pure_eq_ok` reads the value of a successful `pure`. Three
invariant lemmas carry a property through a loop:

- `forIn_run_inv`, for a `for` loop over a list.
- `foldlM_run_mem`, for a fold whose step returns one of its arguments.
- `fuelLoop_run_inv`, for `fuelLoop`.

## The pure box: `pureState` and `runPure`

The runners pin the monad. This module also pins the box: a fork-body theorem states
its claim over the plain SSZ value and never binds a fork `State` (an `SSZ.Box`) of
its own. `pureState v` is the uncached box of `v`, the only box a theorem builds. A
contract theorem states the run at the box level,
`act.run (pureState v) = .ok (a, pureState w)`, because that is a `.run` fact and the
fork-choice bridge consumes `.run` facts by application. Reading theorems state the
`runPure` form and derive it through `runPure_of_run_ok`. The bind between two actions
has no `runPure` form, because `runPure` views each intermediate state, and a general
bind law would have to know that the intermediate box is uncached; a proof about a
composite body goes through `runPure_eq` to the box level, where `run_bind` and
`run_pure` apply.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (HasherTag ErrorConv liftErr)
open SizzLean (SSZRepr)
open SizzLean.Cache

/-- `.run` of a bind: run the first action, and on success run the continuation from the
value and state it produced. The `Except` bind on the right short-circuits a reject. -/
theorem run_bind {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f).run s = (x.run s) >>= fun p => (f p.1).run p.2 := rfl

/-- `.run` of a `pure`: the value paired with the state, unchanged. -/
theorem run_pure {σ ε α : Type} (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α).run s = .ok (a, s) := rfl

/-- `.run` of `getThe σ`: the state, as the value and as the unchanged state. `appendState`
opens with this read. -/
theorem run_getThe {σ ε : Type} (s : σ) :
    (getThe σ : StateT σ (Except ε) σ).run s = .ok (s, s) := rfl

/-- `.run` of a `throw`: the error alone. This is where the two monads part company.
`EStateM`'s throw carries the state it had reached, which is what the pyspec runner needs
and what a proof about a rejecting path then has to say something about. Here a reject is
just the error, so a theorem about one has no post-state to characterize. -/
theorem run_throw {σ ε α : Type} (e : ε) (s : σ) :
    (throw e : StateT σ (Except ε) α).run s = .error e := rfl

/-- `Except`'s bind on the success branch, the step that fires after `run_bind` on a
run known to have succeeded. Core has no `simp` lemma in this shape, and unfolding
`Bind.bind` / `Except.bind` at each call site obscures what is being rewritten. -/
theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- `Except`'s bind on the error branch: the continuation is skipped. -/
theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = .error e := rfl

/-- `do x` for a lone `for`-loop `x` elaborates as `x >>= fun _ => pure ()`. This lemma
removes that wrapper. A fact about the bare loop run then connects to a use site that runs
the bare `forIn` before more code. The wrapper succeeds with the same post-state and
discards the loop's own value. -/
theorem run_of_run_seq_pure {ε σ β : Type} (x : StateT σ (Except ε) β) (s0 s1 : σ)
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

/-- The reject half of `run_of_run_seq_pure`. The `pure ()` wrapper never raises. So when
`x >>= fun _ => pure ()` rejects, `x` rejects with the same error. -/
theorem run_of_run_seq_pure_error {ε σ β : Type} (x : StateT σ (Except ε) β)
    (s0 : σ) (e : ε)
    (h : (x >>= fun _ => (pure () : StateT σ (Except ε) Unit)).run s0 = .error e) :
    x.run s0 = .error e := by
  rw [run_bind] at h
  cases hx : x.run s0 with
  | ok p =>
    obtain ⟨a, s⟩ := p
    rw [hx] at h
    rw [except_bind_ok, run_pure] at h
    cases h
  | error e' =>
    rw [hx, except_bind_error] at h
    injection h with h'
    rw [h']

/-- The converse of `run_bind` on a successful run: the first action succeeds, and the
continuation succeeds from its value and state. -/
theorem run_bind_eq_ok {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) (r : β × σ)
    (h : (x >>= f).run s = .ok r) :
    ∃ a s1, x.run s = .ok (a, s1) ∧ (f a).run s1 = .ok r := by
  rw [run_bind] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

/-- A successful run of `pure a` returns `a`. -/
theorem run_pure_eq_ok {σ ε α : Type} (a b : α) (s s' : σ)
    (h : (pure a : StateT σ (Except ε) α).run s = .ok (b, s')) : b = a := by
  rw [run_pure] at h
  injection h with h
  injection h with h
  exact h.symm

/-- An invariant of a `for` loop over a list. The loop starts from an accumulator that
satisfies `P`. Each body run takes an accumulator that satisfies `P` to a step whose
value satisfies `P`. The step can continue (`yield`) or stop (`done`). Then a successful
run of the loop returns an accumulator that satisfies `P`. -/
theorem forIn_run_inv {σ ε α β : Type} (P : β → Prop)
    (f : α → β → StateT σ (Except ε) (ForInStep β)) :
    ∀ (l : List α),
      (∀ a ∈ l, ∀ (r : β) (s s' : σ) (st : ForInStep β),
        P r → (f a r).run s = .ok (st, s') → P st.value) →
      ∀ (init : β) (s s' : σ) (r : β),
        P init → (forIn l init f).run s = .ok (r, s') → P r := by
  intro l
  induction l with
  | nil =>
    intro _ init s s' r hinit h
    rw [List.forIn_nil, run_pure] at h
    injection h with h
    injection h with h
    exact h ▸ hinit
  | cons a rest ih =>
    intro hstep init s s' r hinit h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    have hst := hstep a List.mem_cons_self init s s1 st hinit hbody
    cases st with
    | done b =>
      have hr := run_pure_eq_ok b r s1 s' hrest
      exact hr ▸ hst
    | yield b =>
      exact ih (fun a' ha' => hstep a' (List.mem_cons_of_mem a ha')) b s1 s' r hst hrest

/-- A left fold whose step `f` returns one of its two arguments. A successful run
returns the initial value or an element of the list. -/
theorem foldlM_run_mem {σ ε α : Type} (f : α → α → StateT σ (Except ε) α)
    (hf : ∀ (a b x : α) (s s' : σ), (f a b).run s = .ok (x, s') → x = a ∨ x = b) :
    ∀ (l : List α) (init x : α) (s s' : σ),
      (l.foldlM f init).run s = .ok (x, s') → x = init ∨ x ∈ l := by
  intro l
  induction l with
  | nil =>
    intro init x s s' h
    exact Or.inl (run_pure_eq_ok init x s s' h)
  | cons a rest ih =>
    intro init x s s' h
    rw [List.foldlM_cons] at h
    obtain ⟨y, s1, hy, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    rcases ih y x s1 s' hrest with hx | hx
    · rcases hf init a y s s1 hy with hy' | hy'
      · exact Or.inl (hx.trans hy')
      · exact Or.inr (hx ▸ hy' ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem a hx)

/-- One iteration of `fuelLoop` with fuel left. When the step at `init` returns
`.next b` and the state `s'`, the loop continues from `b` in `s'`, with one unit of
fuel less. -/
theorem fuelLoop_run_of_next {σ ε β α : Type} (fuel : Nat) (init : β) (exhausted : α)
    (step : β → StateT σ (Except ε) (EthCLLib.Spec.Step β α)) (b : β) (s s' : σ)
    (h : (step init).run s = .ok (.next b, s')) :
    (EthCLLib.Spec.fuelLoop (fuel + 1) init exhausted step).run s
      = (EthCLLib.Spec.fuelLoop fuel b exhausted step).run s' := by
  simp only [EthCLLib.Spec.fuelLoop, run_bind, h, except_bind_ok]

/-- An invariant of `fuelLoop`. `P` holds of the loop value, and `Q` holds of the result.
Three conditions:

- A `.next` step keeps `P`.
- A `.done` step from a value that satisfies `P` returns a result that satisfies `Q`.
- The fuel-out value `exhausted` satisfies `Q`.

Then a successful run of the loop from a value that satisfies `P` returns a result that
satisfies `Q`. -/
theorem fuelLoop_run_inv {σ ε β α : Type} (P : β → Prop) (Q : α → Prop) (exhausted : α)
    (step : β → StateT σ (Except ε) (EthCLLib.Spec.Step β α))
    (hnext : ∀ (b b' : β) (s s' : σ), P b → (step b).run s = .ok (.next b', s') → P b')
    (hdone : ∀ (b : β) (a : α) (s s' : σ), P b → (step b).run s = .ok (.done a, s') → Q a)
    (hexhausted : Q exhausted) :
    ∀ (fuel : Nat) (init : β) (s s' : σ) (a : α),
      P init → (EthCLLib.Spec.fuelLoop fuel init exhausted step).run s = .ok (a, s') → Q a := by
  intro fuel
  induction fuel with
  | zero =>
    intro init s s' a _ h
    simp only [EthCLLib.Spec.fuelLoop] at h
    exact (run_pure_eq_ok exhausted a s s' h) ▸ hexhausted
  | succ fuel ih =>
    intro init s s' a hinit h
    simp only [EthCLLib.Spec.fuelLoop] at h
    obtain ⟨st, s1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    cases st with
    | done d =>
      have ha := run_pure_eq_ok d a s1 s' hrest
      exact ha ▸ hdone init d s s1 hinit hstep
    | next b => exact ih b s1 s' a (hnext init b s s1 hinit hstep) hrest

/-- `ofExcept` of an `.ok a`: the run succeeds and passes the state through
unchanged. The run-level shape the loop-body proofs read the spec's indexed reads
and checked ops at (`liftErr` unfolds to `ofExcept` of the converted value). -/
theorem run_ofExcept_ok {σ ε α : Type} {a : α} (sb : σ) :
    (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
      (Except.ok a : Except ε α)).run sb = .ok (a, sb) := rfl

/-- `ofExcept` of an `.error e`: the run rejects with the error alone, no state. -/
theorem run_ofExcept_error {σ ε α : Type} {e : ε} (sb : σ) :
    (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
      (Except.error e : Except ε α)).run sb = .error e := rfl

/-- `liftErr` of an `Except` value whose converted form is `.ok a`: the run
succeeds and passes the state through unchanged. -/
theorem run_liftErr_of_ok {σ ε' ε α : Type} [ErrorConv ε' ε] {a : α}
    (x : Except ε' α) (sb : σ)
    (h : Except.mapError (ErrorConv.conv (F := ε)) x = Except.ok a) :
    (liftErr (m := StateT σ (Except ε)) (E := ε') (F := ε) x).run sb = .ok (a, sb) := by
  show (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
    (Except.mapError ErrorConv.conv x)).run sb = _
  rw [h]
  exact run_ofExcept_ok sb

/-- `liftErr` of an `Except` value whose converted form is `.error e`: the run
rejects with the converted error alone, no state. -/
theorem run_liftErr_of_error {σ ε' ε α : Type} [ErrorConv ε' ε] {e : ε}
    (x : Except ε' α) (sb : σ)
    (h : Except.mapError (ErrorConv.conv (F := ε)) x = Except.error e) :
    (liftErr (m := StateT σ (Except ε)) (E := ε') (F := ε) x).run sb = .error e := by
  show (MonadExcept.ofExcept (ε := ε) (m := StateT σ (Except ε))
    (Except.mapError ErrorConv.conv x)).run sb = _
  rw [h]
  exact run_ofExcept_error sb

/-! ## The pure box and the pure runner

`pureState` and `runPure` are generic over the SSZ value type `T`, so one copy serves
every fork and every store. A theorem binds `v : T` and never runs an action on a
boxed state it bound itself. A contract theorem states the run at the box level, on
`pureState v`: that is a `.run` fact, the shape `runNestedStateTransition_of_ok`
consumes, so fork choice reuses the contract by application. Reading theorems state
the `runPure` form and take it from the contract through `runPure_of_run_ok`. -/

/-- The uncached box of a plain value: the only box a fork-body theorem builds. The
`HasherTag` supplies the hasher, so the box is over `HasherTag.H`, the same hasher the
fork's `State` boxes over. An `abbrev`, so `pureState v` and `SSZ.UncachedBox
HasherTag.H v` unify directly. -/
abbrev pureState {T : Type} [SSZRepr T] [HasherTag] (v : T) : SSZ.Box HasherTag.H T :=
  SSZ.UncachedBox HasherTag.H v

/-- Run a state step on the uncached box of `v`, and return the value it produces: the
result paired with the post-state's view. This is the value-level reading of a run; the
box never escapes into a reading theorem's conclusion. -/
def runPure {T ε α : Type} [SSZRepr T] [HasherTag]
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) (v : T) : Except ε (α × T) :=
  (act.run (pureState v)).map fun p => (p.1, p.2.view)

/-- `runPure` unfolds to a run on the uncached box, with the result state viewed. The
bridge from a `runPure`-level goal to the box-level `run_bind` / `run_pure` /
`run_throw` facts. -/
theorem runPure_eq {T ε α : Type} [SSZRepr T] [HasherTag]
    (act : StateT (SSZ.Box HasherTag.H T) (Except ε) α) (v : T) :
    runPure act v = (act.run (pureState v)).map (fun p => (p.1, p.2.view)) := rfl

/-- The `runPure` form of a box-level run fact. A contract theorem states
`act.run (pureState v) = .ok (a, pureState w)` so the fork-choice bridge can consume
it; this derives the value-level `runPure act v = .ok (a, w)` by unfolding `runPure`
(`runPure_eq`) and substituting the fact. -/
theorem runPure_of_run_ok {T ε α : Type} [SSZRepr T] [HasherTag]
    {act : StateT (SSZ.Box HasherTag.H T) (Except ε) α} {v : T} {a : α} {w : T}
    (h : act.run (pureState v) = .ok (a, pureState w)) :
    runPure act v = .ok (a, w) := by
  rw [runPure_eq, h]
  rfl

/-- `runPure` of a `pure`: the value paired with `v`, unchanged. -/
theorem runPure_pure {T ε α : Type} [SSZRepr T] [HasherTag] (a : α) (v : T) :
    (runPure (pure a : StateT (SSZ.Box HasherTag.H T) (Except ε) α) v) = .ok (a, v) := rfl

/-- `runPure` of a `throw`: the error alone, no post-state. -/
theorem runPure_throw {T ε α : Type} [SSZRepr T] [HasherTag] (e : ε) (v : T) :
    (runPure (throw e : StateT (SSZ.Box HasherTag.H T) (Except ε) α) v) = .error e := rfl

end EthCLLib.Proofs
