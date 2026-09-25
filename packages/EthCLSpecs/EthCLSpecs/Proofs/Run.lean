import EthCLLib.Spec.Loop

/-!
# `EthCLSpecs.Proofs.Run`: `StateT`-over-`Except` facts every pure runner shares

`EStateM` ships `run_bind` / `run_pure` as `simp` lemmas. The `StateT`-over-`Except`
stack does not, because both steps are definitional there (`StateT.run x s` is `x s`,
and `StateT.bind` threads the pair through `Except`'s own bind). Every Gloas and Heze
run proof needs the same rewrites, so they live once here rather than as a
`simp [StateT.bind, Bind.bind, ...]` unfolding repeated per call site, and rather than
under a fork's runner name.

The five bind, pure, and throw equations close by `rfl`. They exist to be `rw`/`simp`
targets with a readable right-hand side. `fuelLoop_run_of_next` runs one iteration of
the framework loop `fuelLoop` (`EthCLLib/Spec/Loop.lean`). Stated at any `σ` / `ε`: nothing in either proof is specific to a fork's state,
and the general form applies to `GloasRun` and `ForkChoiceStoreRun` alike.

The runner names remain in their existing modules: `GloasRun` is in
`Proofs/Gloas/Run.lean`, while the fork-neutral `ForkChoiceStoreRun` is in
`Proofs/StoreRun.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

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

/-- One iteration of `fuelLoop` with fuel left. When the step at `init` returns
`.next b` and the state `s'`, the loop continues from `b` in `s'`, with one unit of
fuel less. -/
theorem fuelLoop_run_of_next {σ ε β α : Type} (fuel : Nat) (init : β) (exhausted : α)
    (step : β → StateT σ (Except ε) (EthCLLib.Spec.Step β α)) (b : β) (s s' : σ)
    (h : (step init).run s = .ok (.next b, s')) :
    (EthCLLib.Spec.fuelLoop (fuel + 1) init exhausted step).run s
      = (EthCLLib.Spec.fuelLoop fuel b exhausted step).run s' := by
  simp only [EthCLLib.Spec.fuelLoop, run_bind, h, except_bind_ok]

end EthCLSpecs.Proofs
