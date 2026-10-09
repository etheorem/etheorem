import EthCLLib.Spec.Errors
import EthCLLib.Spec.Hasher

/-!
# `EthCLSpecs.Proofs.Run`: the monad facts and the pure box the pure runners share

`EStateM` ships `run_bind` / `run_pure` as `simp` lemmas. The `StateT`-over-`Except`
stack does not, because both steps are definitional there (`StateT.run x s` is `x s`,
and `StateT.bind` threads the pair through `Except`'s own bind). Every Gloas and Heze
run proof needs the same rewrites, so they live once here rather than as a
`simp [StateT.bind, Bind.bind, ...]` unfolding repeated per call site, and rather than
under a fork's runner name.

All five close by `rfl`. They exist to be `rw`/`simp` targets with a readable right-hand
side. Stated at any `σ` / `ε`: nothing in either proof is specific to a fork's state,
and the general form applies to `GloasRun` and `ForkChoiceStoreRun` alike.

The runner names remain in their existing modules: `GloasRun` is in
`Proofs/Gloas/Run.lean`, while the fork-neutral `ForkChoiceStoreRun` is in
`Proofs/StoreRun.lean`.

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

namespace EthCLSpecs.Proofs

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

end EthCLSpecs.Proofs
