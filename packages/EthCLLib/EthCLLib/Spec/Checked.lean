import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.Checked`: the type of an arithmetic expression

The pyspec has two integer kinds (`SPEC_ARITHMETIC.md` §3.1). The checked kind
(`Uint64`, `Uint8`, and their unit subclasses) raises on a result outside
`[0, 2**BITS - 1]` and on a zero divisor. `Checked` is the Lean type of such an
expression: a value, or an `ArithFault`. It is `Except ArithFault α`, so a `do`
block binds it with `←` and a `for` loop keeps its shape (`SPEC_ARITHMETIC.md`
§4.3).

`ArithFault` is the typed cause of the raise. It embeds `ArithCause`
(`Spec/Errors.lean`), the constructor-to-class seam the runner branches on: a
range fault is a Python `ValueError` at the pin and a zero divisor is a bare
`ZeroDivisionError`, so no wrapper may merge them. The fault also carries the
operator and the two operands as plain values, diagnostic only: the runner
never branches on them.

This module is the semantic core. It holds instances and definitions alone, so
the proof modules import it without any authoring elaborator. Stage 3 owns the
operator surface (`Spec/Elab.lean`, the scoped elaborator) and the lift into
the transition monads, which this module carries beside the fault type
(`SPEC_ARITHMETIC.md` §4.4).
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The typed cause of an arithmetic raise.

`cause` reuses `ArithCause`, the reference-exception-class seam Stage 1 pinned:
`.range` is an `SSZValueError` (a Python `ValueError`) at the pin and
`.zeroDivision` is a bare `ZeroDivisionError`, so the runner's caught sets can
keep the two apart without reading text.

`op`, `lhs`, and `rhs` are the operator and the operands the fault arose from,
diagnostic only: they name the site in a vector-mismatch report and are never
branched on. `rhs` is `0` where the operator reads one operand (a cast or a
narrowing); the operands are the values the operator computed on, before any
range test. `width` is the checked width the route computed at: `64` for a
`CLUint64` route, `8` for a `CLUint8` one, and `0` for a `CLInt` route. The
plain kind has no bound. -/
structure ArithFault where
  /-- The reference exception class of the raise. -/
  cause : ArithCause
  /-- The operator, diagnostic only. -/
  op : String
  /-- The checked width of the route, diagnostic only. `0` for the plain kind. -/
  width : Nat
  /-- The left operand the operator computed on, diagnostic only. -/
  lhs : Int
  /-- The right operand, diagnostic only. `0` where the operator reads one
  operand. -/
  rhs : Int
  deriving Repr, DecidableEq

namespace ArithFault

/-- A result outside the target range, or a failed cast or narrowing. `op` names
the operator or the cast, `w` is the checked width; `a` and `b` are its
operands, diagnostic only. -/
def range (op : String) (w : Nat) (a b : Int) : ArithFault :=
  ⟨.range, op, w, a, b⟩

/-- A `//` or `%` by zero. `op` is `"//"` or `"%"`, `w` is the checked width;
`a` is the dividend, diagnostic only. -/
def zeroDivisor (op : String) (w : Nat) (a : Int) : ArithFault :=
  ⟨.zeroDivision, op, w, a, 0⟩

end ArithFault

/-- The type of an arithmetic expression: a value, or a fault.

`Except` gives it the monad structure, so a spec body binds a checked
expression with `←` in a `do` block and a `for` loop keeps its shape
(`SPEC_ARITHMETIC.md` §4.3). The abbrev is reducible on purpose: the operator
instances in `Spec/CLUint.lean` and `Spec/CLInt.lean` are keyed on the
unwrapped `Except ArithFault` head, so instance search reads through the name. -/
abbrev Checked (α : Type) := Except ArithFault α

instance {α : Type} [DecidableEq α] : DecidableEq (Checked α) :=
  fun a b =>
    match a, b with
    | .ok x, .ok y =>
      decidable_of_iff (x = y)
        (⟨fun h => by rw [h], fun h => Except.ok.inj h⟩ :
          (x = y) ↔ (Except.ok x = Except.ok y))
    | .ok _, .error _ => isFalse (fun h => by cases h)
    | .error _, .ok _ => isFalse (fun h => by cases h)
    | .error x, .error y =>
      decidable_of_iff (x = y)
        (⟨fun h => by rw [h], fun h => Except.error.inj h⟩ :
          (x = y) ↔ (Except.error x = Except.error y))

/-! ## The lift into the machine monads (`SPEC_ARITHMETIC.md` §4.4)

A spec body binds a checked expression with `←` in any machine monad, so the
fault needs one route into each machine's error channel. The route preserves
the typed cause: a `.range` fault becomes `.arithmetic` (an `SSZValueError`, a
Python `ValueError`, at the pin) and a `.zeroDivision` fault becomes
`.zeroDivision` (a bare `ZeroDivisionError`), so the runner's caught sets keep
the two apart without reading text. The `op` field is the reject's diagnostic
payload, the same convention `throwArithmetic` uses. -/

/-- The machine reject an arithmetic fault becomes. The constructor follows the
fault's `cause`, so the reference exception class survives every lift
(`SPEC_ARITHMETIC.md` §4.4); `op` is the diagnostic payload, never branched on. -/
@[inline] def StateTransitionError.ofArithFault (e : ArithFault) : StateTransitionError :=
  match e.cause with
  | .range        => .arithmetic e.op
  | .zeroDivision => .zeroDivision e.op

/-- The conversion keeps the fault's own cause: the cause a fault carried on
the `Checked` side is the cause its reject carries on the machine side. -/
theorem StateTransitionError.ofArithFault_arithCause (e : ArithFault) :
    (StateTransitionError.ofArithFault e).arithCause = some e.cause := by
  cases e with
  | mk c _ _ _ _ => cases c <;> rfl

/-- The one lift (`SPEC_ARITHMETIC.md` §4.4): any monad whose error accepts a
`StateTransitionError` takes an arithmetic expression under `←`. The state
machine takes the fault directly (identity conversion) and the store machine
wraps it as a nested state reject, so one definition serves both, exactly as
`sszGetIdx` does for `IndexError`. The lift moves the whole expression's
fault, so it changes no operand type. -/
instance {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] : MonadLift (Except ArithFault) m where
  monadLift x := liftErr (x.mapError StateTransitionError.ofArithFault)

end EthCLLib.Spec
