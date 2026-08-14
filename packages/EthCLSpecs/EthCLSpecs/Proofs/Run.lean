import EthCLSpecs.Gloas.State

/-!
# `EthCLSpecs.Proofs.Run`: the Gloas state-transition runner these proofs run against

A theorem about a `forkdef`'s effect has to pin down the monad the spec body is
elaborated into, since `StateTransition` is a parameter of the fork body rather than a
fixed type. Every Gloas proof in this directory pins the same one, so it is named once
here and instantiated at each theorem through `(StateTransition := GloasRun)`.

## Which monad, and why not the fast one

`SPEC_AUTHORING_MODEL.md` sets out a fast/pure duality across four axes, and names
`StateT State (Except StateTransitionError)` as the proving column's effect monad;
`SPECS_ARCHITECTURE.md` §11.1 states that the fast configuration (`FastBox`, `EStateM`,
`hashMap`) is never a proof target. This is that monad.

No fork body names it. The three raw constraints `state_section` emits (`Monad`,
`MonadStateOf State`, `MonadExceptOf StateTransitionError`) all resolve for `StateT` over
`Except`, so every `forkdef` elaborates at it.

The runner is on `EStateM` instead, and the difference is the reject branch.
`EthCLLib/PySpecTests/Interface.lean` depends on `EStateM.Result` carrying the store on
that branch, which is how it matches the reference pyspec mutating in place and catching
the expected raise. `StateT` over `Except` cannot express that: a rejected run returns
the error alone. That is exactly why the proofs want it. A run either produces a state or
does not, so a theorem about a rejecting path has nothing to say about a half-written
state, and the equations stay about values.

Fork choice reaches the same monad. `NestedStateMachine` (`EthCLLib/Spec/NestedMachine.lean`)
resolves a handler's nested state machine from the store's monad, and at the pure store
monad it resolves to this one. So every theorem below is a theorem about the step running
under fork choice too. Carrying one over is function application:
`runNestedStateTransition_of_ok` (`EthCLLib/Spec/NestedMachine.lean`) takes a step's
`.run` fact and returns the store-machine statement, for any action.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Fulu (Preset)
open EthCLSpecs.Gloas (State)

/-- The monad the Gloas spec bodies are proved at: `StateT` over `Except`, threading the
boxed Gloas `BeaconState` and rejecting with `StateTransitionError`. `abbrev`
(reducible) so a goal mentioning it unifies with the spelled-out
`StateT State (Except StateTransitionError)`.

`.run` here yields `Except StateTransitionError (α × State)`, so a successful run reads
`.ok (a, state')` and a rejecting one reads `.error e`, carrying no state. -/
abbrev GloasRun [Preset] [HasherTag] : Type → Type :=
  StateT State (Except StateTransitionError)

/-! ## Running a bind

`EStateM` ships `run_bind` / `run_pure` as `simp` lemmas; the `StateT`-over-`Except`
stack does not, because both steps are definitional there (`StateT.run x s` is `x s`,
and `StateT.bind` threads the pair through `Except`'s own bind). Every proof in this
directory needs the same two rewrites, so they are stated once here rather than as a
`simp [StateT.bind, Bind.bind, ...]` unfolding repeated per call site. Both close by
`rfl`; they exist to be `rw`/`simp` targets with a readable right-hand side.

Stated at any `σ` / `ε` rather than at `State` / `StateTransitionError`: nothing in
either proof is specific to the fork's state, and the general form applies to the
`PUnit`-valued loop bodies without an instantiation dance. -/

/-- `.run` of a bind: run the first action, and on success run the continuation from the
value and state it produced. The `Except` bind on the right short-circuits a reject. -/
theorem GloasRun.run_bind {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f).run s = (x.run s) >>= fun p => (f p.1).run p.2 := rfl

/-- `.run` of a `pure`: the value paired with the state, unchanged. -/
theorem GloasRun.run_pure {σ ε α : Type} (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α).run s = .ok (a, s) := rfl

/-- `.run` of a `throw`: the error alone. This is where the two monads part company.
`EStateM`'s throw carries the state it had reached, which is what the pyspec runner needs
and what a proof about a rejecting path then has to say something about. Here a reject is
just the error, so a theorem about one has no post-state to characterize. -/
theorem GloasRun.run_throw {σ ε α : Type} (e : ε) (s : σ) :
    (throw e : StateT σ (Except ε) α).run s = .error e := rfl

/-- `Except`'s bind on the success branch, the step that fires after
`GloasRun.run_bind` on a run known to have succeeded. Core has no `simp` lemma
in this shape, and unfolding `Bind.bind` / `Except.bind` at each call site
obscures what is being rewritten. -/
theorem GloasRun.except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

/-- `Except`'s bind on the error branch: the continuation is skipped. -/
theorem GloasRun.except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = .error e := rfl

end EthCLSpecs.Proofs
