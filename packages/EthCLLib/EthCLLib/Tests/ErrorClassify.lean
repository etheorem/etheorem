import EthCLLib

/-!
# `EthCLLib.Tests.ErrorClassify`: the runner classification table

The classification surface the pyspec runner branches on, pinned row by row against the
pinned reference (`v1.7.0-beta.4` with `eth-ssz-specs` 0.1.0 as the integer library). At
that pin a checked range/cast fault raises `SSZValueError` (a `ValueError`), a zero divisor
raises a bare `ZeroDivisionError`, a list over its limit raises a `ValueError`
(`SSZValueError` on an append, a pydantic `ValidationError` on the constructor), and
`expect_assertion_error` (`context.py:451-462`) catches only `AssertionError` and
`IndexError`. A `list.index` miss raises a plain `ValueError`. One case writes its own
`except ValueError` wrapper
(`RunnerCaughtSet.valueError`). The four sections pin, in order: the admit table, the
reporting buckets, the cause-preserving lifts, and the state-disposal and decode rules.

Distinct from `FrameworkUtils.lean`, which pins the arithmetic layer's own throws; this
module pins what the runner does with every reject shape once it exists. See
`FRAMEWORK_ARCHITECTURE.md` §13.3 for the reporting buckets and `SPEC_ARITHMETIC.md` §1
for the runner's caught-set contract.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests

namespace EthCLLib.Tests.ErrorClassify

/-! ## The typed arithmetic causes

Each arithmetic constructor carries its reference class by construction, and
`arithCause` reads it back typed. `listFull` and `notInList` carry no `ArithCause`: their
faults are a collection's capacity and a lookup miss, not a numeric operator. Their reference
class (`ValueError` at the pin) is a property of the admit table, not of a cause tag. -/

#guard StateTransitionError.arithCause (.arithmetic "x") == some ArithCause.range
#guard StateTransitionError.arithCause (.zeroDivision "x") == some ArithCause.zeroDivision
#guard StateTransitionError.arithCause (.assert "x") == none
#guard StateTransitionError.arithCause (.listFull "x") == none
#guard StateTransitionError.arithCause (.notInList "x") == none

/-! ## The admit table (`RunnerCaughtSet.admits`)

One row per constructor per set. `assert` is the `AssertionError` and `outOfBounds` the
`IndexError`, so the `assertionAndIndex` set (`expect_assertion_error`,
`context.py:451-462`) takes exactly those two. `arithmetic` (`SSZValueError` on a range
fault), `listFull` (`SSZValueError` on an append, pydantic `ValidationError` on the
constructor), and `notInList` (the plain `ValueError` of `list.index`) are `ValueError`s, so
only the `valueError` set takes them. `zeroDivision` is
a bare `ZeroDivisionError`, which neither class set holds, so no row admits it. -/

#guard RunnerCaughtSet.assertionAndIndex.admits (.assert "x") == true
#guard RunnerCaughtSet.assertionAndIndex.admits (.todo "x") == false
#guard RunnerCaughtSet.assertionAndIndex.admits (.outOfScope "x") == false
#guard RunnerCaughtSet.assertionAndIndex.admits (.outOfBounds 3 2) == true
#guard RunnerCaughtSet.assertionAndIndex.admits (.arithmetic "x") == false
#guard RunnerCaughtSet.assertionAndIndex.admits (.zeroDivision "x") == false
#guard RunnerCaughtSet.assertionAndIndex.admits (.listFull "x") == false
#guard RunnerCaughtSet.assertionAndIndex.admits (.notInList "x") == false

#guard RunnerCaughtSet.valueError.admits (.assert "x") == false
#guard RunnerCaughtSet.valueError.admits (.todo "x") == false
#guard RunnerCaughtSet.valueError.admits (.outOfScope "x") == false
#guard RunnerCaughtSet.valueError.admits (.outOfBounds 3 2) == false
#guard RunnerCaughtSet.valueError.admits (.arithmetic "x") == true
#guard RunnerCaughtSet.valueError.admits (.zeroDivision "x") == false
#guard RunnerCaughtSet.valueError.admits (.listFull "x") == true
#guard RunnerCaughtSet.valueError.admits (.notInList "x") == true

/-! ## The reporting buckets (`classify`)

`classify` assigns a reject its reporting bucket from the constructor, and `classifyReject`
later reads the case's caught set off that bucket to decide pass or fail.
Both arithmetic causes land in `uncaughtFault`: a zero divisor under every wrapper, a
range fault under every wrapper but `valueError`. A zero divisor stays there even under
`valueError`, the reporting-side fact the admit table states on its own rows. -/

#guard StateTransitionError.classify (.assert "x") == .expectedRejection
#guard StateTransitionError.classify (.todo "x") == .todo
#guard StateTransitionError.classify (.outOfScope "x") == .outOfScope
#guard StateTransitionError.classify (.outOfBounds 3 2) == .likelyBug
#guard StateTransitionError.classify (.arithmetic "x") == .uncaughtFault
#guard StateTransitionError.classify (.zeroDivision "x") == .uncaughtFault
#guard StateTransitionError.classify (.listFull "x") == .uncaughtFault
#guard StateTransitionError.classify (.notInList "x") == .uncaughtFault

/-- The store buckets, including the `.transition`-wrapped arithmetic of both causes: the
wrapper embeds the inner reject unchanged, so the store reports the same bucket the state
machine would. -/
example : StoreTransitionError.classify (.transition (.arithmetic "x")) = .uncaughtFault := rfl
example : StoreTransitionError.classify (.transition (.zeroDivision "x")) = .uncaughtFault := rfl
example : StoreTransitionError.classify (.transition (.assert "x")) = .expectedRejection := rfl
example : StoreTransitionError.classify (.transition (.outOfBounds 3 2)) = .likelyBug := rfl
#guard StoreTransitionError.classify (.assert "x") == .expectedRejection
#guard StoreTransitionError.classify (.todo "x") == .todo
#guard StoreTransitionError.classify (.outOfScope "x") == .outOfScope
#guard StoreTransitionError.classify (.missingKey (Vector.replicate 32 0)) == .uncaughtFault
#guard StoreTransitionError.classify (.decodeFailure "x") == .likelyBug

/-- Expected-rejection rows for a `valid: false` fork-choice step under
`expect_assertion_error`: exactly the bare and wrapped `assert`, plus the wrapped index
miss. Both wrapped arithmetic causes stay out, a bare `ZeroDivisionError` and an
`SSZValueError` alike, and so do the wrapped `listFull` and `notInList`. -/
example : StoreTransitionError.isExpectedRejection (.transition (.assert "x")) = true := rfl
example : StoreTransitionError.isExpectedRejection (.transition (.outOfBounds 3 2)) = true := rfl
example : StoreTransitionError.isExpectedRejection (.transition (.arithmetic "x")) = false := rfl
example : StoreTransitionError.isExpectedRejection (.transition (.zeroDivision "x")) = false := rfl
example : StoreTransitionError.isExpectedRejection (.transition (.listFull "x")) = false := rfl
example : StoreTransitionError.isExpectedRejection (.transition (.notInList "x")) = false := rfl
#guard StoreTransitionError.isExpectedRejection (.assert "x") == true
#guard StoreTransitionError.isExpectedRejection (.todo "x") == false
#guard StoreTransitionError.isExpectedRejection (.missingKey (Vector.replicate 32 0)) == false
#guard StoreTransitionError.isExpectedRejection (.decodeFailure "x") == false

/-- The one index-miss shape is the wrapped `outOfBounds`; both wrapped arithmetic causes
are different classes and do not subtract. -/
example : StoreTransitionError.isIndexMiss (.transition (.outOfBounds 3 2)) = true := rfl
example : StoreTransitionError.isIndexMiss (.transition (.arithmetic "x")) = false := rfl
example : StoreTransitionError.isIndexMiss (.transition (.zeroDivision "x")) = false := rfl

/-- The runner-level buckets: a decode failure is our bug, a wrapped spec reject reports
by its own constructor, both arithmetic causes as `uncaughtFault`. -/
example : RunError.classify (E := StateTransitionError) (.decode "pre.ssz_snappy") = .likelyBug := rfl
example : RunError.classify (E := StateTransitionError) (.spec (.assert "x")) = .expectedRejection := rfl
example : RunError.classify (E := StateTransitionError) (.spec (.arithmetic "x")) = .uncaughtFault := rfl
example : RunError.classify (E := StateTransitionError) (.spec (.zeroDivision "x")) = .uncaughtFault := rfl
example : RunError.classify (E := StateTransitionError) (.spec (.listFull "x")) = .uncaughtFault := rfl
example : RunError.classify (E := StateTransitionError) (.spec (.notInList "x")) = .uncaughtFault := rfl

/-! ## `FcStepKind` admission

The fork-choice step kinds score through `isExpectedRejection` narrowed by the index
rule. The rows here use `.attestation`, which runs under `expect_assertion_error`
(`catchesIndexError = true`), and `.block`, whose `add_block` wrapper never catches
`IndexError`. Neither arithmetic cause is admitted under either kind, a bare
`ZeroDivisionError` and an `SSZValueError` alike. -/

#guard FcStepKind.admits .attestation (.assert "x") == true
#guard FcStepKind.admits .attestation (.transition (.assert "x")) == true
#guard FcStepKind.admits .attestation (.transition (.outOfBounds 3 2)) == true
#guard FcStepKind.admits .attestation (.transition (.arithmetic "x")) == false
#guard FcStepKind.admits .attestation (.transition (.zeroDivision "x")) == false
#guard FcStepKind.admits .attestation (.transition (.listFull "x")) == false
#guard FcStepKind.admits .attestation (.transition (.notInList "x")) == false
#guard FcStepKind.admits .attestation (.missingKey (Vector.replicate 32 0)) == false
#guard FcStepKind.admits .block (.assert "x") == true
-- The block step's wrapper never catches `IndexError`, so its index-miss row is out.
#guard FcStepKind.admits .block (.transition (.outOfBounds 3 2)) == false
#guard FcStepKind.admits .block (.transition (.zeroDivision "x")) == false
#guard FcStepKind.admits .block (.transition (.arithmetic "x")) == false

/-! ## The cause-preserving lifts

One path per lift the runner crosses. Each row asserts the cause survives with its kind
intact, so the reference classes above stay attached from the throw site to the driver.
The pure `Except` helper goes through the identity `ErrorConv`; the store lift wraps as
`.transition`; the nested bridge surfaces an inner state throw on the store machine. -/

/-- Pure helper route: an `Except`-context helper throws, the identity conversion
carries the reject through unchanged. -/
example : (throwArithmetic "x" : Except StateTransitionError Nat) = .error (.arithmetic "x") := rfl
example : (throwZeroDivision "x" : Except StateTransitionError Nat)
    = .error (.zeroDivision "x") := rfl

/-- The identity `ErrorConv` behind the pure route, named directly. -/
example : (liftErr (F := StateTransitionError)
    (.error (.zeroDivision "x") : Except StateTransitionError Nat) :
    Except StateTransitionError Nat) = .error (.zeroDivision "x") := rfl

/-- State-machine lift, pure column: the fault leaves the `StateT` runner as the same
constructor. -/
example : ((throwArithmetic "x" : StateT Nat (Except StateTransitionError) Unit).run 7)
    = .error (.arithmetic "x") := rfl
example : ((throwZeroDivision "x" : StateT Nat (Except StateTransitionError) Unit).run 7)
    = .error (.zeroDivision "x") := rfl

/-! State-machine lift, fast column: the `EStateM` runner keeps the constructor too. -/
#guard ((throwArithmetic "x" : EStateM StateTransitionError Nat Unit).run 7)
  matches .error (.arithmetic "x") _
#guard ((throwZeroDivision "x" : EStateM StateTransitionError Nat Unit).run 7)
  matches .error (.zeroDivision "x") _

/-- Store lift: the same source faults arrive wrapped as `.transition`, the
`ErrorConv StateTransitionError StoreTransitionError` instance's shape, and both carry
their cause inside the wrapper. -/
example : ((throwArithmetic "x" : StateT Nat (Except StoreTransitionError) Unit).run 7)
    = .error (.transition (.arithmetic "x")) := rfl
example : ((throwZeroDivision "x" : StateT Nat (Except StoreTransitionError) Unit).run 7)
    = .error (.transition (.zeroDivision "x")) := rfl

/-- Nested state throw surfaced through `runNestedStateTransition`: the inner machine's
reject reaches the store machine as `.transition`, cause intact, for both causes. The
nested state `S` is `Int` (the store is the `Nat`), the pure column's pair. -/
example :
    (runNestedStateTransition
        (m := StateT Nat (Except StoreTransitionError)) ((7 : Int))
        (throwArithmetic "x" : StateT Int (Except StateTransitionError) Unit)).run 7
      = .error (.transition (.arithmetic "x")) := rfl
example :
    (runNestedStateTransition
        (m := StateT Nat (Except StoreTransitionError)) ((7 : Int))
        (throwZeroDivision "x" : StateT Int (Except StateTransitionError) Unit)).run 7
      = .error (.transition (.zeroDivision "x")) := rfl

/-- Runner classification keeps the cause: `RunError.ofSpec` tags the reject `spec`, and
the store-side wrapped fault classifies to the same bucket its inner reject carries. -/
example : RunError.ofSpec (.error (.zeroDivision "x") : Except StateTransitionError Nat)
    = .error (.spec (.zeroDivision "x")) := rfl
example : RunError.classify (E := StoreTransitionError)
    (.spec (.transition (.zeroDivision "x"))) = .uncaughtFault := rfl

/-! ## Failed-state disposal

A state machine that mutates and then throws hands the caller no state: `runFrom`, the
capability every consumer runs a machine through, returns the reject alone on the error
branch, in both columns. So the caller's threaded state is unchanged no matter what the
action wrote first. (The raw `EStateM` error branch does carry the error-time state; that
is the fork-choice store machine's documented pyspec-mutation contract, consumed by
`PySpecTests.Interface.runOn`, and it is not the state the caller threads.) -/

/-- Pure column: the `StateT`-over-`Except` throw discards the written state. -/
example :
    ((do set 5; throwArithmetic "x" : StateT Nat (Except StateTransitionError) Unit).run 0)
      = .error (.arithmetic "x") := rfl

/-- Pure column through `runFrom`: no post-state on the error branch. -/
example :
    (MonadRunState.runFrom (0 : Nat)
      (do set 5; throwArithmetic "x" : StateT Nat (Except StateTransitionError) Unit))
      = .error (.arithmetic "x") := rfl

/-- Fast column through `runFrom`: the `EStateM` instance drops the error-branch state,
so the caller sees the same shape. -/
example :
    (MonadRunState.runFrom (0 : Nat)
      (do set 5; throwArithmetic "x" : EStateM StateTransitionError Nat Unit))
      = .error (.arithmetic "x") := rfl

/-! Nested fast column, both properties in one run: the inner machine writes its state,
then throws the zero-divisor fault, and the reject value the bridge raises carries only
the wrapped cause, no post-state a caller could mistake for its own. -/
#guard ((runNestedStateTransition
      (m := EStateM StoreTransitionError Nat) ((7 : Int))
      (do modify (· + 1); throwZeroDivision "x" : EStateM StateTransitionError Int Unit)).run 7)
  matches .error (.transition (.zeroDivision "x")) _

/-! ## Decode failures stay separate

A `RunError.decode` is the runner's own deserialization failure, never a spec raise, so
it never reports as an expected rejection: its bucket is `likelyBug` under every path,
and the store machine's `decodeFailure` mirror is out of every step kind's admit set. A
broken decoder therefore cannot pass an `invalid_*` vector half. -/

example : RunError.classify (E := StateTransitionError) (.decode "w") != .expectedRejection := rfl
example : RunError.classify (E := StoreTransitionError) (.decode "w") != .expectedRejection := rfl
#guard FcStepKind.admits .attestation (.decodeFailure "w") == false
#guard FcStepKind.admits .block (.decodeFailure "w") == false
#guard (classifyReject .assertionAndIndex (.assert "x")).bucket == .expectedRejection

end EthCLLib.Tests.ErrorClassify
