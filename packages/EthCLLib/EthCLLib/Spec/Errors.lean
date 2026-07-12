/-!
# `EthCLLib.Spec.Errors`: the two reject types

One error type per state machine (`FRAMEWORK_ARCHITECTURE.md` §6). The
state-transition machine rejects with `StateTransitionError`; the fork-choice
machine with `StoreTransitionError`, which embeds the state type because
`onBlock` runs the state machine inside the store machine.

Each constructor carries a *typed* term per failure kind, in keeping with the
project's stringly-typed-is-a-smell principle. The `String` payloads
(`assert`'s `descr`, `todo`'s / `outOfScope`'s `what`) are diagnostic only: they
are printed on a vector mismatch and never branched on. The harness branches on
the *constructor* (its classify mode), which is typed:

| Constructor | Classify-mode meaning |
|---|---|
| `assert` | an expected rejection; an invalid vector should hit one |
| `todo` | an unimplemented branch we intend to fill; a work-queue item, reported `xfail` |
| `outOfScope` | a branch we deliberately do not model; reported `skip`, not counted as work |
| `outOfBounds` / `missingKey` | a smell; well-formed input should not hit these |

`todo` and `outOfScope` both name a branch that does not run, the distinction is
intent: a `todo` is expected to pass once the work-queue reaches it, an
`outOfScope` never will (a runner or type we chose not to implement), so it must
not inflate the `xfail` work-queue.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The state-transition machine's reject type.

`outOfBounds` is state-side (an indexed access ran past the end). `assert` is a
failed spec assertion; `todo` a deliberate, documented deferral (the deferral
work-queue of `FRAMEWORK_ARCHITECTURE.md` §6.1). -/
inductive StateTransitionError where
  /-- A spec assertion failed; `descr` is the rendered condition, diagnostic only. -/
  | assert (descr : String)
  /-- An unimplemented branch we intend to fill: a work-queue deferral, reported `xfail`. -/
  | todo (what : String)
  /-- A branch we deliberately do not model (an out-of-scope runner / type); reported `skip`. -/
  | outOfScope (what : String)
  /-- Indexed access past the end: index `idx` against bound `bound`. -/
  | outOfBounds (idx bound : Nat)
  /-- A `uint64` arithmetic fault (over/underflow): the spec's `uintN` op raises Python
  `ValueError`, which the reference runner's `expect_assertion_error` does NOT catch (it
  catches only `AssertionError` and `IndexError`, `context.py:429-433`). So it is not an
  expected rejection but a likely bug, distinct from a guarded `assert`. `descr` names the
  faulting op, diagnostic only. The standing case is `get_balance_after_withdrawals`'
  `state.balances[i] - withdrawn` (`capella/beacon-chain.md:378`), a bare subtraction. -/
  | arithmetic (descr : String)
  deriving Inhabited, Repr, DecidableEq

/-- The fork-choice store machine's reject type.

Carries its own `assert` / `todo`, plus `missingKey` (a store-side `FcMap`
lookup miss) and `transition`, which wraps a nested `StateTransitionError` from
the state machine `onBlock` runs through `runStateTransition`. Only the store
type embeds the state type, the asymmetry the error split is built on. -/
inductive StoreTransitionError where
  /-- A spec assertion failed; diagnostic only. -/
  | assert (descr : String)
  /-- An unimplemented branch we intend to fill: a work-queue deferral, reported `xfail`. -/
  | todo (what : String)
  /-- A branch we deliberately do not model (an out-of-scope runner / type); reported `skip`. -/
  | outOfScope (what : String)
  /-- An `FcMap` lookup found no entry for `key` (the 32-byte block root). -/
  | missingKey (key : Vector UInt8 32)
  /-- A nested state-transition failure surfaced through `runStateTransition`. -/
  | transition (e : StateTransitionError)
  deriving Inhabited, Repr, DecidableEq

/-- The classify buckets the pyspec harness reports
(`FRAMEWORK_ARCHITECTURE.md` §13.3). Derived from a reject's constructor, never
from its diagnostic string. -/
inductive ClassifyBucket where
  /-- The case matched (a valid vector's post-state root, or expected output). -/
  | passing
  /-- An `assert` reject; correct for a vector marked invalid. -/
  | expectedRejection
  /-- A `todo` reject; an unimplemented work-queue branch. Reported `xfail`. -/
  | todo
  /-- An `outOfScope` reject; a branch we deliberately do not model. Reported `skip`. -/
  | outOfScope
  /-- An `outOfBounds` / `missingKey` reject; a likely framework or spec bug. -/
  | likelyBug
  deriving Inhabited, Repr, DecidableEq

namespace ClassifyBucket

/-- A short tag for wire reporting and human-readable output. `todo` reports as
`xfail` work-queue; `outOfScope` reports as a `skip` the harness does not count. -/
def tag : ClassifyBucket → String
  | .passing           => "pass"
  | .expectedRejection => "reject"
  | .todo              => "todo"
  | .outOfScope        => "skip"
  | .likelyBug         => "bug"

end ClassifyBucket

/-- Classify a state-transition reject by its constructor. -/
def StateTransitionError.classify : StateTransitionError → ClassifyBucket
  | .assert _        => .expectedRejection
  | .todo _          => .todo
  | .outOfScope _    => .outOfScope
  | .outOfBounds _ _ => .likelyBug
  | .arithmetic _    => .likelyBug

/-- Classify a store-transition reject by its constructor. A wrapped nested
state failure classifies by the inner reject. -/
def StoreTransitionError.classify : StoreTransitionError → ClassifyBucket
  | .assert _      => .expectedRejection
  | .todo _        => .todo
  | .outOfScope _  => .outOfScope
  | .missingKey _  => .likelyBug
  | .transition e  => e.classify

/-- Whether a store reject is the expected rejection of a `valid: false` fork-choice step.
The reference runner (`context.py:429-433`'s `expect_assertion_error`) catches `AssertionError`
and `IndexError`, so exactly `.assert` (bare and `.transition`-wrapped) and the store machine's
only index-miss shape, `.transition (.outOfBounds …)`, count; `.missingKey` (an uncaught
`KeyError`), `.transition (.arithmetic …)` (an uncaught `uint64` `ValueError`), `.todo` /
`.outOfScope` (our own deferrals), and anything else do not.

This is a *different question* from `classify`, which buckets a reject for reporting (a
`.transition (.outOfBounds)` is still a `likelyBug` there): `classify` answers "how do we
report this reject", `isExpectedRejection` answers "does the reference accept it as the
invalid step's expected raise". `checkStepValidity` is the sole caller; keeping the caught
set here, next to `classify`, makes the two policies visibly distinct and edited in one
place each. -/
def StoreTransitionError.isExpectedRejection : StoreTransitionError → Bool
  | .assert _
  | .transition (.assert _) | .transition (.outOfBounds _ _) => true
  | _ => false

/-- Build the `assert` / `todo` reject of an error type from its diagnostic descriptor.
The `assert` macro and the `todo` helper resolve `E` from the section's monad, so the
*same* `assert` / `todo` work in both machines: in a state section `E` is
`StateTransitionError`, in a fork-choice section it is `StoreTransitionError`. Both error
types share the `assert (descr)` / `todo (what)` constructor shape, so the instances are
just the constructors. -/
class SpecReject (E : Type) where
  /-- The failed-assertion reject. -/
  assert : String → E
  /-- The unimplemented-branch reject; a work-queue deferral, reported `xfail`. -/
  todo   : String → E
  /-- The deliberately-unmodelled-branch reject; reported `skip`, not a work-queue item. -/
  outOfScope : String → E

instance : SpecReject StateTransitionError := ⟨.assert, .todo, .outOfScope⟩
instance : SpecReject StoreTransitionError := ⟨.assert, .todo, .outOfScope⟩

/-- The reporting bucket of a typed reject, as a class so a runner error generic over the
spec reject it wraps (`RunError`) can defer to whichever spec error is inside. The two spec
error types are the only instances; both already expose a `classify`. -/
class Classify (E : Type) where
  /-- The bucket this error reports as. -/
  classify : E → ClassifyBucket

instance : Classify StateTransitionError := ⟨StateTransitionError.classify⟩
instance : Classify StoreTransitionError := ⟨StoreTransitionError.classify⟩

/-- A runner-level error, the wire-boundary failures that sit one level above a spec reject.
The runner deserializes a vector's SSZ inputs before any spec code runs; a parse failure there
is a bug in our decoder or container types, not a consensus rejection, so it is modeled here,
not as a spec error (`SPEC_AUTHORING_MODEL.md` §11). `spec` carries an inner reject `E` through
unchanged; `decode` names the input the runner could not deserialize. The driver runs on
`RunError E` and classifies through `RunError.classify`. -/
inductive RunError (E : Type) where
  /-- Wire bytes the runner could not deserialize; `what` names the type. A likely bug. -/
  | decode (what : String)
  /-- An inner spec reject, classified by `E`'s own `classify`. -/
  | spec (err : E)
  deriving Repr

/-- Classify a runner error: a decode failure is always a likely bug (a well-formed vector
decodes), a wrapped spec reject classifies by its own constructor. -/
def RunError.classify {E : Type} [Classify E] : RunError E → ClassifyBucket
  | .decode _ => .likelyBug
  | .spec e   => Classify.classify e

/-- Lift a spec-level `Except` into the runner error by tagging its reject `spec`. The bridge
a `ForkInterface` method crosses once it leaves decoding and runs spec code: the spec run's
`Except E` becomes the method's `Except (RunError E)`. Decoding stays the method's own
`RunError.decode`. -/
@[inline] def RunError.ofSpec {E α : Type} (x : Except E α) : Except (RunError E) α :=
  x.mapError RunError.spec

/-- Convert a source error `E` into the context error `F`. One instance per conversion the
spec needs, so a computation that throws `E` slots into any monad whose error is `F`: its
error becomes the context's. The nested-state-failure lift is here; the index-miss lifts
(`IndexError → …`) are with `sszGetIdx` (where `IndexError` is in scope). -/
class ErrorConv (E F : Type) where
  /-- The conversion. -/
  conv : E → F

/-- The identity conversion: any error converts to itself. This lets a pure query run in its
own `Except E` monad (e.g. a `forkdef … : Except IndexError α` reusing `sszGetIdx` directly),
and a monadic caller then carries that `E` onward with `liftErr` through the cross-type
instances below. The exact-same-type pair never overlaps those, so resolution stays
unambiguous. -/
instance {α : Type} : ErrorConv α α where
  conv := id

/-- A nested state-transition failure surfaced inside a store step (`runStateTransition`). -/
instance : ErrorConv StateTransitionError StoreTransitionError where
  conv := .transition

universe u

/-- Lift a computation that may throw `E` into a monad whose error is `F`, converting the
reject through `[ErrorConv E F]`. The single `Except`-to-monad adapter at an error boundary;
`F` is the monad's own error (read off `MonadExcept`), so the call names neither error. The
two halves are stdlib: `Except.mapError` converts the error, `MonadExcept.ofExcept` injects
it; `ErrorConv` is just the per-pair conversion that stdlib leaves to the caller. -/
@[inline] def liftErr {m : Type → Type u} {α E F : Type} [Monad m] [MonadExcept F m]
    [ErrorConv E F] (x : Except E α) : m α :=
  MonadExcept.ofExcept (x.mapError ErrorConv.conv)

end EthCLLib.Spec
