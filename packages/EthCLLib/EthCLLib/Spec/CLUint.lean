import Lean
import SizzLean
import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.CLUint`: the pyspec's checked `Uint64` (SPIKE)

The pyspec computes with a checked integer type: every operator tests its result against
`[0, 2**64 - 1]` and raises outside it (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3). `CLUint64` is that type.
Its operators return a `Checked` value, so a fork body writes `a * b / c` as the pyspec does and
binds the expression once.

Spike quality. Width 64 only. A literal past `2^64` wraps.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- Why an arithmetic step raised. Under the rule the kind is free, so this is diagnostic. -/
inductive ArithFault where
  /-- A result outside `[0, 2^64)`: the operator and its two operands. -/
  | range (op : String) (a b : Nat)
  /-- A `//` or `%` by zero: the operator and the dividend. -/
  | zeroDivisor (op : String) (a : Nat)
  deriving Repr, DecidableEq

/-- The type of an arithmetic expression: a value, or a fault. `Except` gives it the monad
structure a `do` block and a `for` loop need. -/
abbrev Checked (α : Type) := Except ArithFault α

/-- The pyspec `Uint64`. A `structure` over `UInt64`, so no `UInt64` operator instance applies:
the wrapping `+` does not exist on this type. -/
structure CLUint64 where
  /-- The native value. -/
  val : UInt64
  deriving DecidableEq, Hashable, Ord

namespace CLUint64

/-- The value as a plain `int`: the pyspec's `int(x)`. The name is long on purpose. Arithmetic
on the result is unchecked, so each use is a site a reviewer must see. -/
@[inline] def toPlainInt (a : CLUint64) : Nat := a.val.toNat

instance : Inhabited CLUint64 := ⟨⟨0⟩⟩
instance : Repr CLUint64 := ⟨fun a _ => repr a.toPlainInt⟩
instance : ToString CLUint64 := ⟨fun a => toString a.toPlainInt⟩
instance {n : Nat} : OfNat CLUint64 n := ⟨⟨UInt64.ofNat n⟩⟩
instance : LT CLUint64 := ⟨fun a b => a.val < b.val⟩
instance : LE CLUint64 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : CLUint64) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : CLUint64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
instance : Max CLUint64 := ⟨fun a b => if a < b then b else a⟩
instance : Min CLUint64 := ⟨fun a b => if a < b then a else b⟩

/-- `Uint64(n)` from a plain `int`: the checked narrowing. -/
@[inline] def ofNat? (n : Nat) : Checked CLUint64 :=
  if n < UInt64.size then .ok ⟨UInt64.ofNat n⟩ else .error (.range "Uint64()" n 0)

/-- `saturating_sub(a, b)`: `a - b`, floored at zero. Total. -/
@[inline] def saturatingSub (a b : CLUint64) : CLUint64 := if a > b then ⟨a.val - b.val⟩ else 0

/-! The five operators on two values, with native-width tests. -/

@[inline] def add (a b : CLUint64) : Checked CLUint64 :=
  if a.val + b.val < a.val then .error (.range "+" a.toPlainInt b.toPlainInt) else .ok ⟨a.val + b.val⟩
@[inline] def sub (a b : CLUint64) : Checked CLUint64 :=
  if a.val < b.val then .error (.range "-" a.toPlainInt b.toPlainInt) else .ok ⟨a.val - b.val⟩
@[inline] def mul (a b : CLUint64) : Checked CLUint64 :=
  if a.val != 0 && a.val * b.val / a.val != b.val then .error (.range "*" a.toPlainInt b.toPlainInt)
  else .ok ⟨a.val * b.val⟩
@[inline] def div (a b : CLUint64) : Checked CLUint64 :=
  if b.val == 0 then .error (.zeroDivisor "//" a.toPlainInt) else .ok ⟨a.val / b.val⟩
@[inline] def mod (a b : CLUint64) : Checked CLUint64 :=
  if b.val == 0 then .error (.zeroDivisor "%" a.toPlainInt) else .ok ⟨a.val % b.val⟩

/-! The same five with one plain `int` operand: compute unbounded, then test the result, as the
pyspec does for `int op Uint`. -/

@[inline] def natAdd (a b : Nat) : Checked CLUint64 := ofNat? (a + b)
@[inline] def natMul (a b : Nat) : Checked CLUint64 := ofNat? (a * b)
@[inline] def natSub (a b : Nat) : Checked CLUint64 :=
  if b ≤ a then ofNat? (a - b) else .error (.range "-" a b)
@[inline] def natDiv (a b : Nat) : Checked CLUint64 :=
  if b = 0 then .error (.zeroDivisor "//" a) else ofNat? (a / b)
@[inline] def natMod (a b : Nat) : Checked CLUint64 :=
  if b = 0 then .error (.zeroDivisor "%" a) else ofNat? (a % b)

end CLUint64

open CLUint64

/-- One operator, every operand shape: a value, an expression, or a plain `int` on either side.
`Nat op Nat` is not listed, so plain arithmetic keeps its core meaning. No instance is a
`default_instance`: that attribute is global and would retype `1 + 1` in every importer. -/
local macro "lift_op " cls:ident core:ident natCore:ident : command => `(
  instance : $cls CLUint64 CLUint64 (Checked CLUint64) := ⟨$core⟩
  instance : $cls (Checked CLUint64) CLUint64 (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => $core x b⟩
  instance : $cls CLUint64 (Checked CLUint64) (Checked CLUint64) :=
    ⟨fun a b => b >>= fun y => $core a y⟩
  instance : $cls (Checked CLUint64) (Checked CLUint64) (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => b >>= fun y => $core x y⟩
  instance : $cls Nat CLUint64 (Checked CLUint64) := ⟨fun a b => $natCore a b.toPlainInt⟩
  instance : $cls CLUint64 Nat (Checked CLUint64) := ⟨fun a b => $natCore a.toPlainInt b⟩
  instance : $cls Nat (Checked CLUint64) (Checked CLUint64) :=
    ⟨fun a b => b >>= fun y => $natCore a y.toPlainInt⟩
  instance : $cls (Checked CLUint64) Nat (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => $natCore x.toPlainInt b⟩)

lift_op HAdd add natAdd
lift_op HSub sub natSub
lift_op HMul mul natMul
lift_op HDiv div natDiv
lift_op HMod mod natMod

/-- The one lift. Any monad whose error accepts a `StateTransitionError` takes an arithmetic
expression under `←`, so the state machine and the store machine share it. -/
instance {m : Type → Type} {E : Type} [Monad m] [MonadExcept E m]
    [ErrorConv StateTransitionError E] : MonadLift (Except ArithFault) m where
  monadLift x := match x with
    | .ok v => pure v
    | .error e => throwArithmetic (reprStr e)

open Lean Elab Term Meta in
/-- Core's `binop%` elaborator reads the expected type. Under `let x ← e` that type is the
ambient monad, which no operand type compares with; core then skips the step that types a
literal operand, and the result type unifies with the monad. This elaborator tries the tree
with no expected type first. If the result is a `Checked` expression it keeps the term and
lets the monad lift bridge to the expected type. Any other tree falls through to core. -/
@[scoped term_elab binop] def elabCheckedOp : TermElab := fun stx expectedType? => do
  let some expected := expectedType? | throwUnsupportedSyntax
  if (← instantiateMVars expected).isMVar then throwUnsupportedSyntax
  let saved ← saveState
  -- First pass, nothing forced: if an operand type is still unknown (a lambda binder that a
  -- later argument fixes), wait for it. Forcing the defaults now would pick core's `Add`.
  let unknown ← try
      let e ← elabTerm stx none
      pure (← instantiateMVars (← inferType e)).hasExprMVar
    catch _ => pure false
  saved.restore
  if unknown then tryPostpone
  let checked? ← try
      let e ← withSynthesize (elabTerm stx none)
      let ty ← whnfR (← instantiateMVars (← inferType e))
      if ty.isAppOfArity ``Except 2 && (ty.getArg! 0).isConstOf ``ArithFault then
        pure (some e)
      else pure none
    catch _ => pure none
  match checked? with
  | some e => ensureHasType expected e
  | none => saved.restore; throwUnsupportedSyntax

end EthCLLib.Spec

namespace SizzLean

/-- `SSZRepr CLUint64`: the wire format of `uint64`, 8 little-endian bytes. The iso is the
structure's projection and constructor, so both laws hold by `rfl`. -/
instance : SSZRepr EthCLLib.Spec.CLUint64 where
  shape    := .uintN 64
  toRepr   := (·.val)
  fromRepr := (⟨·⟩)
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

end SizzLean
