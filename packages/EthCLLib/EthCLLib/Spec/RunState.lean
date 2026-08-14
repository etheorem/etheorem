import EthCLLib.Spec.State

/-!
# `EthCLLib.Spec.RunState`: running a state machine from outside it

A state machine's monad is a `variable` in every spec body (`state_section` emits it), so
anything that wants to *run* one has to name a concrete monad, and the three constraints
that section emits offer no way to get a value back out: `Monad` gives `pure` and `bind`,
`MonadStateOf` gives `get` and `set`, `MonadExceptOf` gives `throw` and `tryCatch`.

`MonadRunState` is that missing capability, and it is the whole of it. Every consumer that
discharges a state machine goes through it: `runToRoot` below, which the `PySpecTests`
state-transition entry points end with, and `runNestedStateTransition` (`Spec/NestedMachine.lean`),
which a fork-choice handler runs a nested transition with. Neither names a monad. -/

set_option autoImplicit false

open SizzLean
open SizzLean.Cache

namespace EthCLLib.Spec

/-- A monad `M` that runs a state machine over `S`, from a starting state to a value and a
post-state, or a reject.

`S` is an `outParam` read off `M`, so a consumer names only the monad and usually not even
that, the ascription on the action being enough.

The result shape is `Except StateTransitionError (α × S)`, which is what *every* instance
can honour truthfully. `EStateM ε S` also carries a state on its error branch, and the
instance below drops it; the shape that kept it would force `StateT S (Except ε)`, which
produces no state when it rejects, to invent one. No consumer reads it: `runToRoot` takes
a root off the success branch alone, and both `Spec/NestedMachine.lean` bridges throw. The one
place that keeps an error-branch state, `PySpecTests/Interface.lean`'s `runOn`, is applied
to fork-choice *store* actions, a different machine. -/
class MonadRunState (S : outParam Type) (M : Type → Type) where
  /-- Run `act` from `pre`, yielding its value and post-state, or the reject. -/
  runFrom : {α : Type} → S → M α → Except StateTransitionError (α × S)

/-- The pure column: `.run` is already this shape. -/
instance instMonadRunStateT (S : Type) :
    MonadRunState S (StateT S (Except StateTransitionError)) where
  runFrom pre act := act.run pre

/-- The fast column: reshape `EStateM.Result`, dropping the error-branch state as the class
docstring explains. -/
instance instMonadRunEStateM (S : Type) :
    MonadRunState S (EStateM StateTransitionError S) where
  runFrom pre act := match act.run pre with
    | .ok a s    => .ok (a, s)
    | .error e _ => .error e

/-- Run a state-machine action on a boxed state and project the result to the post-state
root, or the reject. The state-machine twin of `runOn` (`PySpecTests.Interface`, which does
the same for a fork-choice store): a `PySpecTests` entry point decodes a pre-state, builds
its action, and ends with `runToRoot box0 action`, replacing the open-coded match on the
run.

Generic over the monad through `MonadRunState`, so the entry point's own ascription on
`action` picks the column and this stays out of it. The box dies right after, so
`stateRoot!` (the cache-dropping form) is correct here. -/
@[inline] def runToRoot {H T : Type} {M : Type → Type} [Hasher H] [SSZRepr T]
    [MonadRunState (SSZ.Box H T) M] (box0 : SSZ.Box H T) (act : M Unit) :
    Except StateTransitionError ByteArray :=
  match MonadRunState.runFrom box0 act with
  | .ok (_, post) => .ok (stateRoot! post)
  | .error e      => .error e

end EthCLLib.Spec
