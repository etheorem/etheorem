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
| `assert` | an expected rejection, unless the case's own wrapper catches only `ValueError` |
| `todo` | an unimplemented branch we intend to fill; a work-queue item, reported `xfail` |
| `outOfScope` | a branch we deliberately do not model; reported `skip`, not counted as work |
| `outOfBounds` / `decodeFailure` | a smell; well-formed input should not hit these, though the reference catches `IndexError` |
| `missingKey` | a fault the reference propagates rather than catches, so it never rejects a vector |
| `arithmetic` | a checked range fault (`ValueError` at the pin), the same, except under a case whose own wrapper catches `ValueError` |
| `zeroDivision` | a zero-divisor fault (a bare `ZeroDivisionError` at the pin), uncaught under every wrapper |
| `listFull` | a list over its limit, a `ValueError` at the pin: caught only by the `except ValueError` wrapper |
| `notInList` | a `list.index` lookup miss, a plain `ValueError` at the pin: caught only by the `except ValueError` wrapper |

`todo` and `outOfScope` both name a branch that does not run, the distinction is
intent: a `todo` is expected to pass once the work-queue reaches it, an
`outOfScope` never will (a runner or type we chose not to implement), so it must
not inflate the `xfail` work-queue.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The reference exception class of a checked-arithmetic fault, read off the pinned
integer library `eth-ssz-specs` 0.1.0 (`SPEC_ARITHMETIC.md` §1). The runner's caught sets
branch on the Python class a raise carries, so the model keeps the distinction typed and
never recovers it from the diagnostic string. The `Checked` / `ArithFault` core
(`Spec/Checked.lean`) reuses this type as its cause field; the two `StateTransitionError`
constructors below are its carriers on the reject surface. -/
inductive ArithCause where
  /-- A range, cast, or shift fault. The library raises `SSZValueError`, a subclass of
  Python `ValueError`, so `expect_assertion_error` lets it escape and the one
  `except ValueError` wrapper catches it. -/
  | range
  /-- A zero divisor (`x // 0`, `x % 0`, `i % len([])`). The library raises a bare Python
  `ZeroDivisionError` (`ArithmeticError`), which is neither a `ValueError` nor an
  `AssertionError` nor an `IndexError`, so no reference wrapper catches it. -/
  | zeroDivision
  deriving Inhabited, Repr, DecidableEq

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
  /-- A checked range fault (`ArithCause.range`): a `uint64` over/underflow or a bad cast.
  At the pin, `eth-ssz-specs` 0.1.0 raises `SSZValueError`, a subclass of Python
  `ValueError`, which the reference runner's `expect_assertion_error` does NOT catch (it
  catches only `AssertionError` and `IndexError`, `context.py:451-462`). So it is not an
  expected rejection but a genuine error, distinct from a guarded `assert`: it `classify`s
  as `ClassifyBucket.uncaughtFault`, so an invalid vector that rejects this way fails,
  unless the case's own wrapper catches `ValueError` (`RunnerCaughtSet.valueError`).
  `descr` names the faulting op, diagnostic only. A checked operator's fault reaches this
  constructor through `StateTransitionError.ofArithFault` (`Spec/Checked.lean`). An example
  is `get_balance_after_withdrawals`' `state.balances[i] - withdrawn`
  (`capella/beacon-chain.md:421`), a bare subtraction. On the store machine the same fault
  arrives wrapped as `.transition (.arithmetic …)`, as in Heze's `Slot(state.slot - 1)`
  underflow. -/
  | arithmetic (descr : String)
  /-- A zero-divisor fault (`ArithCause.zeroDivision`): `x // 0`, `x % 0`, or
  `i % len(indices)` on an empty list. At the pin, `eth-ssz-specs` 0.1.0 raises a bare
  Python `ZeroDivisionError` (`ArithmeticError`), which is neither an `AssertionError`,
  an `IndexError`, nor a `ValueError`, so NO reference wrapper catches it: not
  `expect_assertion_error` (`context.py:451-462`) and not the one `except ValueError`
  wrapper (`RunnerCaughtSet.valueError`). It `classify`s as
  `ClassifyBucket.uncaughtFault` under every wrapper, so an invalid vector that rejects
  this way fails everywhere. `descr` names the faulting op, diagnostic only. A checked
  operator's zero divisor reaches this constructor through
  `StateTransitionError.ofArithFault`. An example is `get_inclusion_list_committee`'s
  `indices[i % len(indices)]` on an empty committee (`heze/beacon-chain.md:274-276`), the
  `CLInt` `%` in `cyclicSample`. -/
  | zeroDivision (descr : String)
  /-- An SSZ list over its limit. At the pin, `eth-ssz-specs` 0.1.0 raises a `ValueError`
  in both places: `List.append` on a full list raises `SSZValueError` (a `ValueError`
  subclass), and the `List` constructor on too many elements raises pydantic's
  `ValidationError` (also a `ValueError` subclass). Neither is an `AssertionError` or an
  `IndexError`, so `expect_assertion_error` does not catch it, while the one
  `except ValueError` wrapper does (`RunnerCaughtSet.valueError`).
  It `classify`s as `ClassifyBucket.uncaughtFault`, the reporting bucket for a fault the
  default wrapper propagates. `field` names the list, diagnostic only. `appendState` raises
  it for the append case, and `sszOfArrayM` for the constructor case. Every `appendState`
  in the fork bodies can raise it, except where a spec-mirrored length guard runs first
  (`pending_partial_withdrawals`, `pending_consolidations`). -/
  | listFull (field : String)
  /-- A value absent from a Python list that the spec searches with `list.index`. At the
  pin, `list.index` raises a plain Python `ValueError` when no element equals the value.
  That is neither an `AssertionError` nor an `IndexError`, so `expect_assertion_error`
  does not catch it, while the one `except ValueError` wrapper does
  (`RunnerCaughtSet.valueError`). It `classify`s as `ClassifyBucket.uncaughtFault` and
  carries no `ArithCause`, since a lookup is not an arithmetic operator. `descr` names the
  lookup, diagnostic only. The standing case is `process_sync_aggregate`'s
  `all_pubkeys.index(pubkey)` (`fulu/minimal.py:4515-4517`) on a current-sync-committee
  pubkey that no validator carries. -/
  | notInList (descr : String)
  deriving Inhabited, Repr, DecidableEq

/-- The fork-choice store machine's reject type.

Carries its own `assert` / `todo`, plus `missingKey` (a store-side `FcMap`
lookup miss) and `transition`, which wraps a nested `StateTransitionError` from
the state machine `onBlock` runs through `runNestedStateTransition`. Only the store
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
  /-- A fork-choice step's SSZ input could not be deserialized; `what` names the input. A
  decoder / container bug, never a spec rejection: fork-choice vectors are always well-formed
  (malformed-wire testing lives in the `ssz_generic` suite), so a decode miss here is our bug,
  not the invalid step's expected raise. Kept distinct from `.assert` so it is NOT an expected
  rejection (`isExpectedRejection`), the mirror of the state-transition machine's
  `RunError.decode`. -/
  | decodeFailure (what : String)
  /-- A nested state-transition failure surfaced through `runNestedStateTransition`. -/
  | transition (e : StateTransitionError)
  deriving Inhabited, Repr, DecidableEq

/-- The classify buckets the pyspec harness reports
(`FRAMEWORK_ARCHITECTURE.md` §13.3). Derived from a reject's constructor, never
from its diagnostic string. -/
inductive ClassifyBucket where
  /-- The case matched (a valid vector's post-state root, or expected output). -/
  | passing
  /-- A reject the case's own wrapper catches; correct for a vector marked invalid. Usually an
  `assert`, or a `ValueError`-class fault under a wrapper that catches `ValueError`: an
  `.arithmetic`, a `.listFull`, or a `.notInList` fault. -/
  | expectedRejection
  /-- A `todo` reject; an unimplemented work-queue branch. Reported `xfail`. -/
  | todo
  /-- An `outOfScope` reject; a branch we deliberately do not model. Reported `skip`. -/
  | outOfScope
  /-- An `outOfBounds` / `decodeFailure` reject; a likely framework or spec bug. For an invalid
  vector, an `outOfBounds` (`IndexError`) counts as a rejection where the case's own wrapper
  catches it (`context.py`'s `expect_assertion_error` does), so the driver passes it (flagged).
  Under a wrapper that catches only `ValueError` it fails, still flagged. -/
  | likelyBug
  /-- An uncaught Python fault the reference runner does NOT catch: an `SSZValueError`
  (a `ValueError`) from `.arithmetic`, a bare `ZeroDivisionError` from `.zeroDivision`, a
  bare-`Dict` `KeyError` from `.missingKey`, the `ValueError` of a list over its limit
  from `.listFull`, or the `ValueError` of a `list.index` miss from `.notInList`. Reports as
  a bug like `likelyBug`. It is a valid rejection only where the case's own wrapper catches
  the fault. Under `expect_assertion_error` the reference propagates every one of these, so
  the driver fails the vector. Under the one wrapper that catches `ValueError`, an
  `.arithmetic`, a `.listFull`, and a `.notInList` fault pass instead, while a
  `.zeroDivision` fault still fails (a bare `ZeroDivisionError` is not a `ValueError`). This
  is the reporting-side counterpart of `isExpectedRejection` excluding `.missingKey` and the
  `.transition`-wrapped `.arithmetic`, `.zeroDivision`, `.listFull`, and `.notInList`. -/
  | uncaughtFault
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
  | .uncaughtFault     => "bug"

end ClassifyBucket

/-- Classify a state-transition reject by its constructor, against the exception classes
`eth-ssz-specs` 0.1.0 raises. A range fault and a zero
divisor land in the same reporting bucket: `expect_assertion_error`, the wrapper that
scores almost every case, propagates both. -/
def StateTransitionError.classify : StateTransitionError → ClassifyBucket
  | .assert _        => .expectedRejection
  | .todo _          => .todo
  | .outOfScope _    => .outOfScope
  | .outOfBounds _ _ => .likelyBug
  | .arithmetic _    => .uncaughtFault
  | .zeroDivision _  => .uncaughtFault
  | .listFull _      => .uncaughtFault
  | .notInList _     => .uncaughtFault

/-- Classify a store-transition reject by its constructor. A wrapped nested
state failure classifies by the inner reject. -/
def StoreTransitionError.classify : StoreTransitionError → ClassifyBucket
  | .assert _      => .expectedRejection
  | .todo _        => .todo
  | .outOfScope _  => .outOfScope
  | .missingKey _  => .uncaughtFault
  | .decodeFailure _ => .likelyBug
  | .transition e  => e.classify

/-- Whether a store reject is the expected rejection of a `valid: false` fork-choice step
under `expect_assertion_error` (`context.py:451-462`), which catches `AssertionError` and
`IndexError`. So exactly `.assert` (bare and `.transition`-wrapped) and the store machine's
only index-miss shape, `.transition (.outOfBounds …)`, count; at the `eth-ssz-specs` 0.1.0
pin, `.missingKey` (an uncaught
`KeyError`), `.transition (.arithmetic …)` (an uncaught `SSZValueError`, a `ValueError`),
`.transition (.zeroDivision …)` (an uncaught bare `ZeroDivisionError`),
`.transition (.listFull …)` and `.transition (.notInList …)` (uncaught `ValueError`s), `.todo` /
`.outOfScope` (our own deferrals), and anything else do not.

That wrapper scores the attestation, attester-slashing, envelope, and PTC-message steps. The
block step is scored by `add_block`'s own `except (AssertionError, BlockNotFoundException)`
(`fork_choice.py:381-389`), which never catches `IndexError`, so its admitted set is this one
minus the index miss. `FcStepKind.admits` applies that narrowing; `isIndexMiss` is the shape
it subtracts.

This is a *different question* from `classify`, which buckets a reject for reporting (a
`.transition (.outOfBounds)` is still a `likelyBug` there): `classify` answers "how do we
report this reject", `isExpectedRejection` answers "does the reference accept it as the
invalid step's expected raise". Keeping the caught set here, next to `classify`, makes the two
policies visibly distinct and edited in one place each. -/
def StoreTransitionError.isExpectedRejection : StoreTransitionError → Bool
  | .assert _
  | .transition (.assert _) | .transition (.outOfBounds _ _) => true
  | _ => false

/-- The store machine's index-miss shape, the reject standing for the spec's `IndexError`.
`StoreTransitionError` has no bare `.outOfBounds`, so it is always the wrapped one. Split out
so the step kinds whose reference wrapper does not catch `IndexError` can subtract exactly
this from `isExpectedRejection`. -/
def StoreTransitionError.isIndexMiss : StoreTransitionError → Bool
  | .transition (.outOfBounds _ _) => true
  | _ => false

/-- The Python exceptions a case's reference wrapper catches. This decides which rejects
count as an invalid vector's expected raise. It is the state machine's counterpart to
`FcStepKind` (`PySpecTests/Interface.lean`), which answers the same question one level down, per
fork-choice step.

The pinned reference holds two sets. It scores almost every invalid vector through
`expect_assertion_error` (`context.py:451-462`), which catches `AssertionError` and `IndexError`.
One test never reaches that helper. `test_invalid_large_withdrawable_epoch`
(`test/phase0/epoch_processing/test_process_registry_updates.py`) writes its own
`except ValueError`. It raises `AssertionError("expected ValueError")` when no `ValueError`
arrives. So that test passes on the uncaught `uint64` fault.

`admits` matches every reject constructor. `FcStepKind` closes on a wildcard. This one does not,
so a new constructor breaks the build here. -/
inductive RunnerCaughtSet where
  /-- `expect_assertion_error`: `AssertionError` and `IndexError`. -/
  | assertionAndIndex
  /-- `test_invalid_large_withdrawable_epoch`'s own `except ValueError` wrapper. -/
  | valueError
  deriving DecidableEq, Repr

/-- Whether `e` is the expected raise of an invalid vector under this caught set, at the
`eth-ssz-specs` 0.1.0 pin.

`.assert` is the `AssertionError` and `.outOfBounds` is the `IndexError`, so
`expect_assertion_error` takes both. `.arithmetic` is an `SSZValueError`, `.listFull` is a
pydantic `ValidationError`, and `.notInList` is the plain `ValueError` of a `list.index` miss.
All three are Python `ValueError`s, so the `except ValueError` wrapper takes them and
`expect_assertion_error` takes none of them. `.zeroDivision` is a bare
`ZeroDivisionError`, which neither set catches. `.todo` and `.outOfScope` record our own
deferrals, and the reference raises neither. -/
def RunnerCaughtSet.admits : RunnerCaughtSet → StateTransitionError → Bool
  | .assertionAndIndex, .assert _        => true
  | .assertionAndIndex, .outOfBounds _ _ => true
  | .assertionAndIndex, .arithmetic _    => false
  | .assertionAndIndex, .zeroDivision _  => false
  | .assertionAndIndex, .listFull _      => false
  | .assertionAndIndex, .notInList _     => false
  | .assertionAndIndex, .todo _          => false
  | .assertionAndIndex, .outOfScope _    => false
  | .valueError,        .arithmetic _    => true
  | .valueError,        .listFull _      => true
  | .valueError,        .notInList _     => true
  | .valueError,        .zeroDivision _  => false
  | .valueError,        .assert _        => false
  | .valueError,        .outOfBounds _ _ => false
  | .valueError,        .todo _          => false
  | .valueError,        .outOfScope _    => false

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

/-- A nested state-transition failure surfaced inside a store step (`runNestedStateTransition`). -/
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

/-- The typed cause of an arithmetic reject, read back as `ArithCause`; `none` on every
other constructor. `StateTransitionError.ofArithFault_arithCause` (`Spec/Checked.lean`)
proves the lift keeps a fault's cause through this map, and the classification tests pin
the constructor-to-cause map: a re-classification of a
constructor cannot drift away from its reference class silently. The distinction lives in
the constructor tag, never in `descr`. -/
def StateTransitionError.arithCause : StateTransitionError → Option ArithCause
  | .arithmetic _   => some .range
  | .zeroDivision _ => some .zeroDivision
  | _               => none

/-! ## Checked `uint64` arithmetic

The spec's `uintN` arithmetic is *checked*: `eth-ssz-specs` 0.1.0's `Uint64` computes in
Python's unbounded `int` and tests the result against `[0, 2**64 - 1]` after every
`+` / `-` / `*`, so an over- or underflow raises `SSZValueError`, a Python `ValueError`.
That `ValueError` is not an `AssertionError`, so the reference runner's
`expect_assertion_error` does not catch it (`context.py`); it is the `.arithmetic` uncaught
fault (`classify`s as `uncaughtFault`, an expected rejection only under the one
`except ValueError` wrapper). Lean's raw `UInt64` ops wrap instead of raising.

A fork body does not use the helpers below for spec arithmetic. It writes the `CLUint64`
and `CLInt` operators (`Spec/CLUint.lean`, `Spec/CLInt.lean`), and their faults reach the
reject surface through `StateTransitionError.ofArithFault` (`Spec/Checked.lean`). The
helpers below are the raw-word form of the same classes: `checkedAdd`, `checkedSub`, and
`checkedMul` raise through `throwArithmetic`, the range class's constructor site, and a
zero divisor raises through `throwZeroDivision`, its own reference class. Their callers are
the framework tests and proofs; the one fork-body caller is `checkedSucc`, the structural
loop counter. `descr` names the faulting op, diagnostic only. -/

/-- Raise the `.arithmetic` fault, the `ArithCause.range` class (an `SSZValueError`, a
Python `ValueError`, at the 0.1.0 pin). The single place the raw-word helpers construct
the reject, so no call site names the wrapper its context needs: the
`[ErrorConv StateTransitionError E]` bound carries the fault in as `.arithmetic` on the
state machine (identity) and
`.transition (.arithmetic …)` on the store machine, so one definition serves both, exactly
as `sszGetIdx` does for `IndexError`. The checked operators below are the `uint64`
over/underflows; a zero divisor reaches its own class through `throwZeroDivision`. -/
@[inline] def throwArithmetic {m : Type → Type u} {α E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (descr : String) : m α :=
  liftErr (E := StateTransitionError) (.error (.arithmetic descr))

/-- Raise the `.zeroDivision` fault, the `ArithCause.zeroDivision` class: a bare Python
`ZeroDivisionError` at the 0.1.0 pin, which no reference wrapper catches, so the reject
never counts as an expected rejection under any `RunnerCaughtSet`. Same
`[ErrorConv StateTransitionError E]` shape as `throwArithmetic`, so one definition serves
both machines. The spec's example is `get_inclusion_list_committee`'s empty-committee
`indices[i % len(indices)]` (`heze/beacon-chain.md:274-276`); the fork body reaches that
class through the `CLInt` `%` and `StateTransitionError.ofArithFault`, not through this
helper. -/
@[inline] def throwZeroDivision {m : Type → Type u} {α E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (descr : String) : m α :=
  liftErr (E := StateTransitionError) (.error (.zeroDivision descr))

/-- Checked `uint64` addition: the sum, or the `.arithmetic` fault on overflow (`a + b` wraps below
`a`, the unsigned carry test). Mirrors `eth-ssz-specs` 0.1.0's `Uint64.__add__`. A raw-word
helper with no fork-body caller; spec arithmetic uses the `CLUint64` `+`. -/
@[inline] def checkedAdd {m : Type → Type u} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a b : UInt64) (descr : String) : m UInt64 :=
  if a + b < a then throwArithmetic descr else pure (a + b)

/-- Checked `uint64` subtraction: the difference, or the `.arithmetic` fault on underflow
(`b > a`). Mirrors `eth-ssz-specs` 0.1.0's `Uint64.__sub__`. A raw-word helper with no
fork-body caller; spec arithmetic uses the `CLUint64` `-`. -/
@[inline] def checkedSub {m : Type → Type u} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a b : UInt64) (descr : String) : m UInt64 :=
  if b > a then throwArithmetic descr else pure (a - b)

/-- Checked `uint64` multiplication: the product, or the `.arithmetic` fault on overflow (`a ≠ 0`
and the truncating `a * b / a` fails to recover `b`). Mirrors `eth-ssz-specs` 0.1.0's
`Uint64.__mul__`. A raw-word helper with no fork-body caller; spec arithmetic uses the
`CLUint64` `*`. -/
@[inline] def checkedMul {m : Type → Type u} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (a b : UInt64) (descr : String) : m UInt64 :=
  if a != 0 && a * b / a != b then throwArithmetic descr else pure (a * b)

/-- Checked `uint64` counter successor: the spec's loop-counter increment `i += 1`, or the
`.arithmetic` fault past `2**64 - 1`. The value operators above return a bare `uint64`, but the
counter's consumer is the caller's `termination_by`, so the `.ok` result is a subtype stating
the sum and its range, `j = i + 1 ∧ j < 2**64`. In the loop below that property is the
hypothesis the decrease obligation reads: with `let s ← checkedSucc …`, the default
`decreasing_tactic` closes `counterBudgetUInt64 s.val < counterBudgetUInt64 i` from
`s.property`, and a bare `Nat` return would leave it nothing to work with.

Another context reads the property through the same two doors. The do-bind keeps it on the
subtype as `s.property`. A `match` destructure, `.ok ⟨j, hj⟩`, turns it into a plain hypothesis
any tactic can cite, `omega`, `exact`, and `simp` alike. A loop-invariant proof consumes it
there: the counter moved exactly one step and stayed in range. The fault side has a reading
too: the throw fires exactly when `i + 1 ≥ 2**64`, and `checkedSucc`'s equations hand that
condition to a proof about the error arm.

The step is fixed at `1` because the proof needs it: a general addend `k` would state
`j = i + k`, which shows no progress unless the call site instantiates `k` with a literal.
The bound takes no parameter either: the modeled surface has exactly one counter-driven loop,
`compute_balance_weighted_selection`. -/
@[inline] def checkedSucc {m : Type → Type u} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (i : Nat) (descr : String) :
    m { j : Nat // j = i + 1 ∧ j < UInt64.size } :=
  if h : i + 1 < UInt64.size then pure ⟨i + 1, rfl, h⟩
  else throwArithmetic descr

/-- The `uint64` counter's remaining budget: `2**64 - i`, the number of increments before the
`.arithmetic` fault. `checkedSucc` consumes exactly one unit per step, so a loop recursing on
the successor measures termination by this function. -/
abbrev counterBudgetUInt64 (i : Nat) : Nat := UInt64.size - i

@[simp] theorem counterBudgetUInt64_eq (i : Nat) : counterBudgetUInt64 i = UInt64.size - i := rfl

/-! ## Lists over their limit -/

/-- Raise the `.listFull` fault for the list `field`. At the pin the fault is a `ValueError`
(`SSZValueError` on an append, a pydantic `ValidationError` on the constructor), so the
`except ValueError` set admits it while `expect_assertion_error` does not. Like
`throwArithmetic`, the `[ErrorConv StateTransitionError E]` bound lets one definition serve
both machines. The state-threading `appendState` and the list constructor `sszOfArrayM`
call it. -/
@[inline] def throwListFull {m : Type → Type u} {α E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] (field : String) : m α :=
  liftErr (E := StateTransitionError) (.error (.listFull field))

end EthCLLib.Spec
