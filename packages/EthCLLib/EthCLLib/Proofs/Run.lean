import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Proofs.Run`: the monad facts the pure runners share

`EStateM` ships `run_bind` / `run_pure` as `simp` lemmas. The `StateT`-over-`Except`
stack does not, because both steps are definitional there (`StateT.run x s` is `x s`,
and `StateT.bind` threads the pair through `Except`'s own bind). Every Gloas and Heze
run proof needs the same rewrites, so they live once here rather than as a
`simp [StateT.bind, Bind.bind, ...]` unfolding repeated per call site, and rather than
under a fork's runner name.

All five close by `rfl`. They exist to be `rw`/`simp` targets with a readable right-hand
side. Stated at any `σ` / `ε`: nothing in either proof is specific to a fork's state,
and the general form applies to `GloasRun` and `ForkChoiceStoreRun` alike.

The runner names remain in their own modules: `GloasRun` is in
`EthCLSpecs/Proofs/Gloas/Run.lean`, while the fork-neutral `ForkChoiceStoreRun` is
in `EthCLLib/Proofs/StoreRun.lean`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (ErrorConv liftErr StateTransitionError throwArithmetic
  throwZeroDivision)

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

/-- `.run` of `throwArithmetic` at the pure runner: the fault, converted by the machine's
own `ErrorConv` and carried alone, like `run_throw`. At the state machine
(`ε := StateTransitionError`, identity conversion) the fault surfaces as the bare
`.arithmetic`; at the store machine it arrives as `.transition (.arithmetic …)`. Closes by
`rfl` without unfolding `liftErr`. -/
theorem throwArithmetic_run {σ α ε : Type} [ErrorConv StateTransitionError ε]
    (descr : String) (s : σ) :
    (throwArithmetic (m := StateT σ (Except ε)) (E := ε) descr : StateT σ (Except ε) α).run s
      = .error (ErrorConv.conv (StateTransitionError.arithmetic descr)) := rfl

/-- `.run` of `throwZeroDivision` at the pure runner, the zero-divisor class's twin of
`throwArithmetic_run`: the fault, converted by the machine's own `ErrorConv` and carried
alone. Closes by `rfl` without unfolding `liftErr`. -/
theorem throwZeroDivision_run {σ α ε : Type} [ErrorConv StateTransitionError ε]
    (descr : String) (s : σ) :
    (throwZeroDivision (m := StateT σ (Except ε)) (E := ε) descr : StateT σ (Except ε) α).run s
      = .error (ErrorConv.conv (StateTransitionError.zeroDivision descr)) := rfl

/-- `Except`'s bind on the success branch, the step that fires after `run_bind` on a
run known to have succeeded. Core has no `simp` lemma in this shape, and unfolding
`Bind.bind` / `Except.bind` at each call site obscures what is being rewritten. -/
theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- `Except`'s bind on the error branch: the continuation is skipped. -/
theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = .error e := rfl

/-- A bind distributes over an `if`. The do-notation `let x ← if c then a else b; rest`
elaborates to the right-hand side, with `rest` copied into both branches. Rewriting right
to left recovers the one bind, so a proof handles `rest` once. -/
theorem ite_bind {m : Type → Type} [Monad m] {α β : Type} {c : Prop} [Decidable c]
    (x y : m α) (f : α → m β) :
    ((if c then x else y) >>= f) = (if c then x >>= f else y >>= f) := by
  split <;> rfl

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

end EthCLLib.Proofs
