import EthCLLib

/-!
# `EthCLLib.Tests.CLCheckedElab`: operator elaboration and its baseline

`SPEC_ARITHMETIC.md` §4.7. The module pins, in order:

- **The ascription baseline.** Every hard shape compiles with an explicit
  `(expression : Checked _)` ascription, which fixes the expected type and
  needs no elaborator. This is the supported fallback everywhere.
- **The elaborated shapes.** The same shapes without the ascription, in the
  pure `Checked` context (core handles those through the expected type) and in
  the state, store, and abstract-machine monads (the scoped elaborator in
  `Spec/Elab.lean` claims the tree and the `MonadLift` bridges it). Each pin
  asserts the computed value by kernel `decide`, the same convention the
  Stage 2 operator pins use.
- **The untouched trees.** `Nat`, `Int`, and `UInt64` arithmetic, written
  identically inside and outside the authoring scope, closing by `rfl` in
  both. The elaborator restores the state and hands every non-checked tree
  back to core, so the terms match (`§4.7`, unchanged elaborated terms).
- **The spike's two hazards**, its findings 9 and 17 from the spike stage:
  the one-line `ofNat?` bind in both
  forms, and the prior do-bound dividend with a non-literal `Nat` operand, in
  both the bare and the ascription-escaped spelling.

A failing shape cannot be pinned in a building module. For the record, an
un-ascribed operator whose result is not a checked expression and whose
expected type is a monad fails under core alone with the mismatch at the
operator tree, for example `a * b has type Checked CLUint64 but is expected to
have type StateT Nat (Except StateTransitionError) ?m`. The error names the
offending expression, which is the §4.7 reporting rule, and the ascription
fixes it. -/

set_option autoImplicit false

namespace EthCLLib.Tests.CLCheckedElab

/-- A stand-in for the state machine: the fork sections' constraint shape is
the abstract-monad one further down; this concrete column keeps the pins
readable. -/
abbrev SM := StateT Nat (Except EthCLLib.Spec.StateTransitionError)

/-- Core ships no `DecidableEq` for a bare `Except`, so the run-level `decide`
pins below carry their own. Same shape as `Checked`'s derived instance; local
to this module, so no importer sees it. -/
local instance {E α : Type} [DecidableEq E] [DecidableEq α] :
    DecidableEq (Except E α) :=
  fun a b =>
    match a, b with
    | .ok x, .ok y => decidable_of_iff (x = y)
        (⟨fun h => by rw [h], fun h => Except.ok.inj h⟩ :
          (x = y) ↔ (Except.ok x = Except.ok y))
    | .ok _, .error _ => isFalse (fun h => by cases h)
    | .error _, .ok _ => isFalse (fun h => by cases h)
    | .error x, .error y => decidable_of_iff (x = y)
        (⟨fun h => by rw [h], fun h => Except.error.inj h⟩ :
          (x = y) ↔ (Except.error x = Except.error y))

section BaselineAscriptions

open EthCLLib.Spec

/-! The ascription fallback: one pin per hard shape. The ascription fixes the
expected type of the whole expression, so core's operator elaborator matches
the operand matrix directly, elaborator active or not. -/

-- A chained expression under `←`, the shape of §4.3's reward formula.
example : ((do
    let a : CLUint64 := 2
    let b : CLUint64 := 3
    let x ← (a * b + 1 : Checked _)
    pure x) : SM CLUint64).run 0 = .ok (7, 0) := by decide

-- A literal operand under `←`, on either side.
example : ((do
    let a : CLUint64 := 2
    let x ← (a + 1 : Checked _)
    pure x) : SM CLUint64).run 0 = .ok (3, 0) := by decide

example : ((do
    let a : CLUint64 := 2
    let x ← (1 + a : Checked _)
    pure x) : SM CLUint64).run 0 = .ok (3, 0) := by decide

-- A non-literal `Nat` operand combined with a prior do-bound value, at a
-- concrete operand, and the plain kind at a `CLInt` operand.
example : ((do
    let a : CLUint64 := 2
    let b : CLUint64 := 3
    let s ← (a * b : Checked _)
    let y ← (s + 4 : Checked _)
    pure y) : SM CLUint64).run 0 = .ok (10, 0) := by decide

example : ((do
    let k : CLInt := 7
    let d ← (k / 2 : Checked _)
    pure d) : SM CLInt).run 0 = .ok (3, 0) := by decide

-- The same shape at an arbitrary operand: the pin is that the tree compiles.
example (n : Nat) : SM CLUint64 := do
  let a : CLUint64 := 2
  let b : CLUint64 := 3
  let s ← (a * b : Checked _)
  let y ← (s + n : Checked _)
  pure y

-- A lambda binder whose type the later argument fixes.
example : (fun x => (x * 2 : Checked _)) (3 : CLUint64) = .ok 6 := by decide

-- An expression as a whole function body.
def ascribedBody (a b : CLUint64) : Checked CLUint64 :=
  (a * b + 1 : Checked _)

example : ascribedBody 2 3 = .ok 7 := by decide

-- An `else if` condition.
example : ((do
    let a : CLUint64 := 3
    let c : CLUint64 := 5
    if (← (a * 2 : Checked _)) < c then
      pure 8
    else if (← (a + 3 : Checked _)) > c then
      pure 6
    else
      pure 7) : SM CLUint64).run 0 = .ok (6, 0) := by decide

-- The same shape in the store machine's error channel.
example : ((do
    let a : CLUint64 := 2
    let x ← (a + 1 : Checked _)
    pure x) : StateT Nat (Except StoreTransitionError) CLUint64).run 0 = .ok (3, 0) := by decide

end BaselineAscriptions

section ElaboratedShapes

open EthCLLib.Spec

/-! The same shapes with no ascription. The scoped elaborator in
`Spec/Elab.lean` claims each checked tree and the lift bridges it to the
ambient monad. Every pin asserts a value or a type. -/

-- Chained expression under `←`, literal on the right.
example : ((do
    let a : CLUint64 := 2
    let b : CLUint64 := 3
    let x ← a * b + 1
    pure x) : SM CLUint64).run 0 = .ok (7, 0) := by decide

-- A literal on the left: the mixed `Nat`-operand row of the matrix.
example : ((do
    let a : CLUint64 := 2
    let x ← 1 + a
    pure x) : SM CLUint64).run 0 = .ok (3, 0) := by decide

-- A non-literal `Nat` operand with a prior do-bound value, at a concrete
-- operand and at an arbitrary one (the compile pin).
example : ((do
    let a : CLUint64 := 2
    let b : CLUint64 := 3
    let s ← a * b
    let y ← s + 4
    pure y) : SM CLUint64).run 0 = .ok (10, 0) := by decide

example (n : Nat) : SM CLUint64 := do
  let a : CLUint64 := 2
  let b : CLUint64 := 3
  let s ← a * b
  let y ← s + n
  pure y

-- The spike's finding 17 shape: `%` with a prior do-bound dividend and a
-- non-literal `Nat` divisor.
example : ((do
    let a : CLUint64 := 7
    let b : CLUint64 := 3
    let s ← a * b
    let y ← s % 4
    pure y) : SM CLUint64).run 0 = .ok (1, 0) := by decide

example (n : Nat) : SM CLUint64 := do
  let a : CLUint64 := 7
  let b : CLUint64 := 3
  let s ← a * b
  let y ← s % n
  pure y

-- The ascription escape for the same tree: forcing the result type always
-- works, elaborator active or not.
example : ((do
    let a : CLUint64 := 7
    let b : CLUint64 := 3
    let s ← a * b
    let y ← (s % 4 : Checked _)
    pure y) : SM CLUint64).run 0 = .ok (1, 0) := by decide

-- A lambda binder whose type the later argument fixes.
example : (fun x => x * 2) (3 : CLUint64) = (.ok 6 : Checked CLUint64) := by decide

-- An expression as a whole function body in the machine monad.
def monadBody (a b : CLUint64) : SM CLUint64 :=
  a * b + 1

example : (monadBody 2 3).run 0 = .ok (7, 0) := by decide

-- An `else if` condition under `←`.
example : ((do
    let a : CLUint64 := 3
    let c : CLUint64 := 5
    if (← a * 2) < c then
      pure 8
    else if (← a + 3) > c then
      pure 6
    else
      pure 7) : SM CLUint64).run 0 = .ok (6, 0) := by decide

-- Nested binds: each step is tested, and the second reads the first.
example : ((do
    let a : CLUint64 := 2
    let x ← a * 3
    let y ← x + 4
    let z ← y / 2
    pure z) : SM CLUint64).run 0 = .ok (5, 0) := by decide

-- The plain kind routes the same way: `CLInt` division under `←` in the
-- machine monad.
example : ((do
    let k : CLInt := 7
    let d ← k / 2
    pure d) : SM CLInt).run 0 = .ok (3, 0) := by decide

-- The one-line `ofNat?` bind, the spike's finding 9 hazard: the bind reads
-- one `Checked` layer, not two, and the fault travels with its cause. With a
-- checked or typed-literal right operand the tree elaborates un-ascribed.
def oneLineBind (delta : CLUint64) : SM CLUint64 := do
  let x ← CLUint64.ofNat? 5 + delta
  pure x

example : (oneLineBind 1).run 0 = .ok (6, 0) := by decide

-- The same one-line tree with a typed `Nat` literal.
example : ((do
    let x ← CLUint64.ofNat? 5 + (1 : Nat)
    pure x) : SM CLUint64).run 0 = .ok (6, 0) := by decide

-- A bare numeral beside a `Checked`-typed operand, on either side, does not
-- elaborate, ascription included: core's `binop%` types the numeral with the
-- checked operand's type first, the kernel literal gate rejects the `OfNat`
-- there, and no `Nat` retry follows. The error lands on the numeral, and the
-- escapes are the two forms above: bind the cast first (§4.3's two-bind form)
-- or type the literal. The two failing sources below pin the prose record as
-- enforced `#guard_msgs`, one corner per side.
--
-- The CLInt-cast mirror fails the same way, on `OfNat (Checked CLInt) 1`.

-- The right corner: `let x ← CLUint64.ofNat? 5 + 1`, with or without
-- `(… : Checked _)`.
/-- error: failed to synthesize instance of type class
  OfNat (Checked CLUint64) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Checked CLUint64
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def cornerRight : SM CLUint64 := do
  let x ← CLUint64.ofNat? 5 + 1
  pure x

-- The left corner: `let x ← 1 + CLUint64.ofNat? 5`.
/-- error: failed to synthesize instance of type class
  OfNat (Checked CLUint64) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Checked CLUint64
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def cornerLeft : SM CLUint64 := do
  let x ← 1 + CLUint64.ofNat? 5
  pure x

-- The two-bind spelling of the same computation, the §4.3 form.
example : ((do
    let v ← CLUint64.ofNat? 5
    let x ← v + 1
    pure x) : SM CLUint64).run 0 = .ok (6, 0) := by decide

-- The one-line form with a non-literal `Nat` operand, the `reserveChurn`
-- context of the spike's finding 9.
def reserveChurn (n : Nat) (delta : CLUint64) : SM CLUint64 := do
  let x ← CLUint64.ofNat? n + delta
  pure x

example : (reserveChurn 5 1).run 0 = .ok (6, 0) := by decide

-- The fault carries its cause through the lift: a range fault is
-- `.arithmetic`, a zero divisor `.zeroDivision`, in the machine channel.
example : ((do
    let x ← (0 : CLUint64) - 1
    pure x) : SM CLUint64).run 0 = .error (.arithmetic "-") := by decide

example : ((do
    let y ← (1 : CLUint64) % 0
    pure y) : SM CLUint64).run 0 = .error (.zeroDivision "%") := by decide

-- The store machine's error channel takes the same trees, wrapped as a
-- nested state reject.
example : ((do
    let a : CLUint64 := 2
    let x ← a + 1
    pure x) : StateT Nat (Except StoreTransitionError) CLUint64).run 0 = .ok (3, 0) := by decide

example : ((do
    let x ← (0 : CLUint64) - 1
    pure x) : StateT Nat (Except StoreTransitionError) CLUint64).run 0
  = .error (.transition (.arithmetic "-")) := by decide

-- The abstract-machine column, the constraint shape `state_section` emits:
-- the monad is a variable with `Monad`, `MonadStateOf`, and `MonadExceptOf`.
def abstractBody {m : Type → Type} [Monad m] [MonadStateOf Nat m]
    [MonadExceptOf StateTransitionError m] (n : Nat) (a b : CLUint64) : m CLUint64 := do
  let s ← a * b
  let y ← s + n
  pure y

example : (abstractBody (m := SM) 1 2 3).run 0 = .ok (7, 0) := by decide

end ElaboratedShapes

/-! ## The untouched trees

The three core trees below appear twice with identical text: once in a scope
where the elaborator is registered, once without. Both close by `rfl`, so the
elaborated terms agree in type and value whichever scope a module opens
(`SPEC_ARITHMETIC.md` §4.7). -/

section UntouchedWithScope

open EthCLLib.Spec

-- `Nat` arithmetic keeps core's `Nat` addition.
example : (2 + 3 : Nat) = 5 := rfl
-- `UInt64` arithmetic keeps core's wrapping `UInt64` addition.
example : ((2 : UInt64) + 3 : UInt64) = 5 := rfl
-- A `Nat` sum coerced to `Int` keeps core's route.
example (n : Nat) : (n + 1 : Int) = (n : Int) + 1 := rfl

end UntouchedWithScope

section UntouchedWithoutScope

-- `Nat` arithmetic keeps core's `Nat` addition.
example : (2 + 3 : Nat) = 5 := rfl
-- `UInt64` arithmetic keeps core's wrapping `UInt64` addition.
example : ((2 : UInt64) + 3 : UInt64) = 5 := rfl
-- A `Nat` sum coerced to `Int` keeps core's route.
example (n : Nat) : (n + 1 : Int) = (n : Int) + 1 := rfl

end UntouchedWithoutScope

end EthCLLib.Tests.CLCheckedElab
