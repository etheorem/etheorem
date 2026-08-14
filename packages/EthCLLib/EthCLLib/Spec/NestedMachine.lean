import EthCLLib.Spec.RunState

/-!
# `EthCLLib.Spec.NestedMachine`: the nested-machine bridge

A fork-choice handler runs the state machine inside `on_block`, `on_tick` and
`on_attestation` (`FRAMEWORK_ARCHITECTURE.md` §7.2). This module is that bridge, plus the
class deciding which state machine a given store monad runs. It is one-way by
construction: the store machine runs the state machine, never the reverse.

The fork-choice half of the spec is monad-generic. `fork_choice_section` emits
`{StoreTransition : Type → Type}` with raw constraints, mirroring `state_section`, so a
handler never names a concrete monad. Running a nested state machine from one needs two
separate things, and they are two separate classes.

*How* to run it is `MonadRunState` (`Spec/RunState.lean`), which is not specific to fork
choice: `runToRoot` uses the same class to discharge a `PySpecTests` state-transition entry
point, with no store anywhere.

*Which* machine to run is `NestedStateMachine` below, and that part is specific to a caller
inside the store machine.

*What its reject becomes* is neither class's business. Both bridges lift through `liftErr`
and `ErrorConv` (`Spec/Errors.lean`), the framework's existing error-boundary adapter, so
the caller's own error type decides. Nothing here names `StoreTransitionError`. -/

set_option autoImplicit false

namespace EthCLLib.Spec

universe u

/-- Which state machine a store monad runs. The store handler's monad `m` and the state
type `S` are the inputs; `M`, the state machine's monad, is the `outParam` read off the
instance. The capability to actually run `M` is `MonadRunState`, kept separate because
consumers outside fork choice need it without needing this.

`M` has to be an `outParam` for the threading to work. A store handler calling another
store handler leaves the callee's `M` as a metavariable, and with `M` an input there are as
many solutions as there are instances, so resolution is ambiguous and the elaborator
reports a stuck instance problem. Determined by `(m, S)`, it resolves from the local
instance at every call site, and no spec body names a monad.

`S` stays an input because `m` does not mention it: a store monad threads a `Store`, which
says nothing about the `BeaconState` type a nested machine threads. Call sites supply it
from `pre`.

The class has no fields. It is a type-level choice, keyed on `m` the way `MonadLift` is
keyed on its source monad. -/
class NestedStateMachine (m : Type → Type) (S : Type) (M : outParam (Type → Type))

/-- The pure column: a store machine at `StateT`/`Except` runs its state machine at the
same shape, which is the monad `EthCLSpecs/Proofs/` already pins. -/
instance instNestedPure (Store S : Type) :
    NestedStateMachine (StateT Store (Except StoreTransitionError)) S
      (StateT S (Except StateTransitionError)) := {}

/-- The fast column: a store machine at `EStateM` runs its state machine at `EStateM` too,
two layers rather than a stack built over the store's own monad. -/
instance instNestedFast (Store S : Type) :
    NestedStateMachine (EStateM StoreTransitionError Store) S
      (EStateM StateTransitionError S) := {}

/-- Run the state machine from a store action: execute `act` (the specialised
`state_transition` / `process_slots`) on `pre`, returning the post-state, or re-throwing
the inner failure in the caller's own error (`FRAMEWORK_ARCHITECTURE.md` §6, §7.2). The
store handler binds the result in its own monad `m`. This is the one-way bridge: the store
machine runs the state machine, never the reverse.

The inner reject rides out through `liftErr`, so this names no error type of its own:
`E` is read off the caller's `MonadExcept`, and `[ErrorConv StateTransitionError E]`
supplies the conversion. In a fork-choice handler that resolves to `E :=
StoreTransitionError` and the `.transition` wrapper, which is the only conversion that
ships; a caller whose own error is `StateTransitionError` gets the identity instance.
Spec bodies call this exactly as before; `M` is resolved by `NestedStateMachine` from the
handler's own monad, so no `forkdef` names it. -/
@[inline] def runNestedStateTransition {S : Type} {M m : Type → Type} {E : Type}
    [NestedStateMachine m S M] [MonadRunState S M] [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (pre : S) (act : M Unit) : m S :=
  liftErr ((MonadRunState.runFrom pre act).map Prod.snd)

/-- The value-returning sibling of `runNestedStateTransition`: execute `act` on `pre` and hand
back its *result*, discarding the post-state, or re-throw the inner failure converted to
the caller's error.

`runNestedStateTransition` serves the state machine's *steps*, whose result is the new state. A
store handler that needs a state-machine *query* wants the value instead, and `get_ptc` is
the case: it is a state-file `forkdef`, so its rejects are `StateTransitionError`, and
`on_payload_attestation_message` runs in the store machine and cannot call it directly. The
bridge stays one-way, the store machine running the state machine and never the reverse. -/
@[inline] def evalNestedStateTransition {S α : Type} {M m : Type → Type} {E : Type}
    [NestedStateMachine m S M] [MonadRunState S M] [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (pre : S) (act : M α) : m α :=
  liftErr ((MonadRunState.runFrom pre act).map Prod.fst)

/-- The bridge carries a value out, at the pure column. -/
example : (evalNestedStateTransition (m := StateT Nat (Except StoreTransitionError)) (0 : Nat)
    (pure 7 : StateT Nat (Except StateTransitionError) Nat)).run 0 = .ok (7, 0) := rfl

/-- … and wraps an inner reject as `.transition`, exactly as `runNestedStateTransition` does. -/
example : (evalNestedStateTransition (m := StateT Nat (Except StoreTransitionError)) (0 : Nat)
    (throw (.assert "x") : StateT Nat (Except StateTransitionError) Nat)).run 0
    = .error (.transition (.assert "x")) := rfl

/-- The same handler shape at the fast column, which is the point of the class: the store
monad changed, and the state machine followed it without any spec body being touched. -/
example : (evalNestedStateTransition (m := EStateM StoreTransitionError Nat) (0 : Nat)
    (throw (.assert "x") : EStateM StateTransitionError Nat Nat)).run 0
    = .error (.transition (.assert "x")) 0 := rfl

/-- `ErrorConv` is the only thing deciding what the reject becomes, so the wrapper is not
baked into either bridge. What still keys them to the store is `NestedStateMachine`, whose
two instances are the two store columns; a caller with a different error would come with
its own instance, and the conversion would follow from `ErrorConv` with no edit here. -/
example : ErrorConv StateTransitionError StoreTransitionError := inferInstance

/-! ## What the bridge preserves

A step's own theorem characterizes its run: `(step).run pre = .ok ((), post)`. These four
carry such a fact across the bridge, once, for every action. A caller supplies its step's
theorem and gets the store-machine statement with no unfolding of `liftErr` and no
per-step reproof.

The hypotheses are in `MonadRunState.runFrom` form because that is what the bridge calls.
At the pure column that is definitionally `act.run pre`, so a `.run` theorem discharges one
directly. -/

/-- A run that succeeds: the bridge hands its post-state back with `pure`, so the store
handler's `let post ← runNestedStateTransition …` binds exactly that state. -/
theorem runNestedStateTransition_of_ok {S : Type} {M m : Type → Type} {E : Type}
    [NestedStateMachine m S M] [MonadRunState S M] [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] {pre post : S} {act : M Unit}
    (h : MonadRunState.runFrom pre act = .ok ((), post)) :
    runNestedStateTransition pre act = (pure post : m S) := by
  simp only [runNestedStateTransition, h]
  rfl

/-- A run that rejects: the bridge throws the converted reject, and no post-state reaches
the store handler. -/
theorem runNestedStateTransition_of_error {S : Type} {M m : Type → Type} {E : Type}
    [NestedStateMachine m S M] [MonadRunState S M] [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] {pre : S} {act : M Unit}
    {e : StateTransitionError} (h : MonadRunState.runFrom pre act = .error e) :
    runNestedStateTransition pre act = (throw (ErrorConv.conv e) : m S) := by
  simp only [runNestedStateTransition, h]
  rfl

/-- The query sibling on a succeeding run: the value comes out, the post-state is dropped. -/
theorem evalNestedStateTransition_of_ok {S α : Type} {M m : Type → Type} {E : Type}
    [NestedStateMachine m S M] [MonadRunState S M] [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] {pre post : S} {a : α} {act : M α}
    (h : MonadRunState.runFrom pre act = .ok (a, post)) :
    evalNestedStateTransition pre act = (pure a : m α) := by
  simp only [evalNestedStateTransition, h]
  rfl

/-- The query sibling on a rejecting run. -/
theorem evalNestedStateTransition_of_error {S α : Type} {M m : Type → Type} {E : Type}
    [NestedStateMachine m S M] [MonadRunState S M] [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] {pre : S} {act : M α}
    {e : StateTransitionError} (h : MonadRunState.runFrom pre act = .error e) :
    evalNestedStateTransition pre act = (throw (ErrorConv.conv e) : m α) := by
  simp only [evalNestedStateTransition, h]
  rfl

end EthCLLib.Spec
