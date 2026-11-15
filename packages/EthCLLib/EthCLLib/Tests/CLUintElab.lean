import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Tests.CLUintElab`: the scoped operator elaborator

Core's `binop%` reads the expected type. Under `let x ← a / b + 1` that type is the ambient
monad, no operand type compares with it, and instance search fails (§4.7 of
`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md`; §4.3 gives the binding shape and §4.4 the
lift). The scoped elaborator
`elabCheckedOp` in `EthCLLib.Spec` (§4.7, `@[scoped term_elab binop]` in
`EthCLLib/Spec/CLUint.lean`) retries the tree with no expected type, keeps the term when the
result is a `Checked` expression, and lets the `MonadLift (Except ArithFault) m` instance
bridge to the monad. Any other tree falls through to core unchanged, and an operand whose
type is still unknown waits.

This module pins one `example` per case the elaborator must handle, each with the computed
value asserted, and the cases it must leave alone, asserted with and without
`open EthCLLib.Spec`. The `open` sits inside the first section on purpose: the untouched
cases need a scope where the elaborator is not registered, while the operator instances,
which are global, stay in reach in both sections.
-/

set_option autoImplicit false

namespace EthCLLib.Tests.CLUintElab

/-! ## The cases the elaborator handles -/

section Handled

open EthCLLib.Spec

-- Case 1. A literal operand under `←` in a monad that is not `Checked` itself. Core, guided
-- by the expected monad type, searches `HAdd CLUint64 Nat (Except …)` and fails; without the
-- elaborator this exact tree does not compile.
example : (do
    let a : CLUint64 := 2
    let x ← a + 1
    pure x) = .ok 3 := rfl

-- Case 2. A lambda binder whose type a later argument fixes. The application fixes `x` at
-- `CLUint64`, so `x * 2` is checked arithmetic and the result is 6.
example : ((fun x => x * 2) (3 : CLUint64) : Checked CLUint64) = .ok 6 := rfl

-- Case 3. An arithmetic expression as a function's whole body, used where a `Checked` value
-- is expected: the body keeps its `Checked` result and one application with two arguments
-- computes 7.
example : ((fun (a b : CLUint64) => a * b + 1) 2 3 : Checked CLUint64) = .ok 7 := rfl

-- Case 4. Nested binds inside one `do`: each step is tested, and the second bind reads the
-- first. Core fails on the literal `3` the same way case 1 does.
example : (do
    let a : CLUint64 := 2
    let x ← a * 3
    let y ← x + 4
    pure y) = .ok 10 := rfl

-- Case 5. A branch condition that must be bound, the shape of §4.3's `if (← a + b) > c`,
-- here on the `else if` arm. Both conditions carry a literal operand, so each is a tree the
-- elaborator claims, and the taken branch asserts which condition computed `true`.
example : (do
    let a : CLUint64 := 3
    let c : CLUint64 := 5
    if (← a * 2) < c then
      pure 8
    else if (← a + 3) > c then
      pure 6
    else
      pure 7) = .ok 6 := rfl

/-! The untouched trees, in the scope where the elaborator is registered: the `Checked` test
rejects the result, the state is restored, and the tree falls through to core, so each
elaborates exactly as core does. The matching block below states the same three assertions
without the `open`. Each block pins its own type and value, and the two blocks stay
textually identical, so the same source elaborates in both scopes and a change to either
side shows as a diff against the other. The ascription pins the elaborated type, and the
`rfl` pins the value, which is the strongest identity the build can check here without
quoting the term. -/

-- `Nat` arithmetic keeps core's `Nat` addition.
example : (2 + 3 : Nat) = 5 := rfl
-- `UInt64` arithmetic keeps core's wrapping `UInt64` addition.
example : ((2 : UInt64) + 3 : UInt64) = 5 := rfl
-- A `Nat` sum coerced to `Int` keeps core's route.
example (n : Nat) : (n + 1 : Int) = (n : Int) + 1 := rfl

end Handled

/-! ## The cases the elaborator leaves alone

The same three trees with no `open EthCLLib.Spec`, so no scoped elaborator is registered and
core elaborates alone. Identical assertions on both sides pin that the elaborator's
fall-through changes nothing observable in type or value.
-/

section Untouched

-- `Nat` arithmetic keeps core's `Nat` addition.
example : (2 + 3 : Nat) = 5 := rfl
-- `UInt64` arithmetic keeps core's wrapping `UInt64` addition.
example : ((2 : UInt64) + 3 : UInt64) = 5 := rfl
-- A `Nat` sum coerced to `Int` keeps core's route.
example (n : Nat) : (n + 1 : Int) = (n : Int) + 1 := rfl

end Untouched

end EthCLLib.Tests.CLUintElab
