import EthCLSpecs.Gloas.State
import EthCLSpecs.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Gloas.Run`: the Gloas state-transition runner these proofs run against

A theorem about a `forkdef`'s effect has to pin down the monad the spec body is
elaborated into, since `StateTransition` is a parameter of the fork body rather than a
fixed type. Every Gloas proof in this directory pins the same one, so it is named once
here and instantiated at each theorem through `(StateTransition := GloasRun)`. The store
machine's counterpart is the pure store runner in `Proofs/StoreRun.lean`.

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

The `StateT`-over-`Except` bind, throw, and `Except` facts that every run proof rewrites
with live in `Proofs/Run.lean`, at any state and error type. This file re-exports them
under `GloasRun` so existing Gloas call sites keep a runner-qualified name. A Heze
proof imports `Proofs/Run.lean` directly and does not name `GloasRun`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Gloas (Preset)
open EthCLSpecs.Gloas (State)

/-- The monad the Gloas spec bodies are proved at: `StateT` over `Except`, threading the
boxed Gloas `BeaconState` and rejecting with `StateTransitionError`. `abbrev`
(reducible) so a goal mentioning it unifies with the spelled-out
`StateT State (Except StateTransitionError)`.

`.run` here yields `Except StateTransitionError (α × State)`, so a successful run reads
`.ok (a, state')` and a rejecting one reads `.error e`, carrying no state. -/
abbrev GloasRun [Preset] [HasherTag] : Type → Type :=
  StateT State (Except StateTransitionError)

/-- `.run` of a bind at `GloasRun`. The statement is `EthCLSpecs.Proofs.run_bind`. -/
theorem GloasRun.run_bind {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f).run s = (x.run s) >>= fun p => (f p.1).run p.2 :=
  EthCLSpecs.Proofs.run_bind x f s

/-- `.run` of a `pure` at `GloasRun`. The statement is `EthCLSpecs.Proofs.run_pure`. -/
theorem GloasRun.run_pure {σ ε α : Type} (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α).run s = .ok (a, s) :=
  EthCLSpecs.Proofs.run_pure a s

/-- `.run` of a `throw` at `GloasRun`. The statement is `EthCLSpecs.Proofs.run_throw`. -/
theorem GloasRun.run_throw {σ ε α : Type} (e : ε) (s : σ) :
    (throw e : StateT σ (Except ε) α).run s = .error e :=
  EthCLSpecs.Proofs.run_throw e s

/-- `Except`'s bind on the success branch. The statement is
`EthCLSpecs.Proofs.except_bind_ok`. -/
theorem GloasRun.except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a :=
  EthCLSpecs.Proofs.except_bind_ok a f

/-- `Except`'s bind on the error branch. The statement is
`EthCLSpecs.Proofs.except_bind_error`. -/
theorem GloasRun.except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = .error e :=
  EthCLSpecs.Proofs.except_bind_error e f

end EthCLSpecs.Proofs.Gloas
