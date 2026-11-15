import Lean
import SizzLean
import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.CLUint`: the pyspec's checked `Uint64` (SPIKE)

The pyspec computes with a checked integer type: every operator tests its result against
`[0, 2**64 - 1]` and raises outside it (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3). `CLUint64` is that type.
Its operators return a `Checked` value, so a fork body writes `a * b / c` as the pyspec does and
binds the expression once.

Spike quality. Width 64 only.
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
  -- The constructor is private to the framework (`SPEC_ARITHMETIC.md` §4.5): `toUint64?` and
  -- `ofNat?` are the only routes from a plain number to a checked one, and a fork body that
  -- writes `CLUint64.mk x` fails to compile. The projection `val` stays public, so reads and
  -- the SSZ iso keep working. Inside this module the anonymous constructor still elaborates.
  private mk ::
  /-- The native value. -/
  val : UInt64
  deriving DecidableEq, Hashable, Ord

namespace CLUint64

/-- The framework's trusted route from a raw `UInt64`. It skips the range test because every
`UInt64` already sits inside `[0, 2^64)`, so the wrap cannot fault. Callers are the trusted
sites only: SSZ decode, preset constants, and internal witnesses that another check bounds.
A fork body builds values from computed numbers through `ofNat?`, the
operators, or a literal, never here; `trustedOfUInt64` serves decoded
values, preset constants, positions another check bounds (a loop
index under a container cap), and total bitwise writes over raw `UInt64`
operands (the builder-flag `|||`): the operation computes on the raw value, so
the wrapper adds no fault site. -/
@[inline] def trustedOfUInt64 (v : UInt64) : CLUint64 := ⟨v⟩

/-- The projection reflects equality: two checked values are equal when their native values
are. This is the public face of the private constructor's injectivity, so a proof outside
this module can reduce a wrapper equation to a plain `UInt64` one (the builder-flag
round-trip proofs hand the result to `bv_decide`). The reverse direction is `.val`
congruence. -/
theorem val_inj {a b : CLUint64} (h : a.val = b.val) : a = b :=
  congrArg mk h

/-- The value as a plain `int`: the pyspec's `int(x)`. The name is long on purpose. Arithmetic
on the result is unchecked, so each use is a site a reviewer must see. -/
@[inline] def toPlainInt (a : CLUint64) : Nat := a.val.toNat

instance : Inhabited CLUint64 := ⟨⟨0⟩⟩
instance : Repr CLUint64 := ⟨fun a _ => repr a.toPlainInt⟩
instance : ToString CLUint64 := ⟨fun a => toString a.toPlainInt⟩
-- The literal instance itself stays total; the `num` elaborator at the end of this module
-- raises before core reaches it, wherever `EthCLLib.Spec` is open, when the expected type is
-- `CLUint64` or a reducible alias of it and the literal is past `2^64 - 1`
-- (SPEC_ARITHMETIC.md §7, item 6). Outside that scope the wrap below is still reachable.
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

/-! ## Total division by a proof-carrying divisor

The checked `/` and `%` above raise on a zero divisor alone: a quotient and a remainder cannot
leave the range (`SPEC_ARITHMETIC.md` §3.2). For a divisor whose positivity the build already
knows, a preset constant such as `SLOTS_PER_EPOCH`, that raise is unreachable, and the site's
pyspec line is total. `compute_epoch_at_slot` is the shape: `Epoch(slot // SLOTS_PER_EPOCH)`
with `SLOTS_PER_EPOCH = Slot(32)` at mainnet and `Slot(8)` at minimal, and about 50 pure call
sites read the result. A `Checked` quotient would force a bind on every one of them
(§4.3), so the quotient is a plain value and the divisor's type carries the positivity.

Two alternatives lost. A method keyed on a hypothesis (`slot.tdiv n` with `[NeZero n]`)
loses the operator surface: the line stops reading as `slot // SLOTS_PER_EPOCH`. An `HDiv`
guarded by `[NeZero d]` on the existing `Nat` divisor route keeps the operator. That
instance and the checked instance both match `a / 32`. Instance search then picks the
route. The route is invisible at the site. The sibling `ValidModulus` class
(`Spec/Arith.lean`) loses the same way for a `/`. Its premise sits on a bare `Nat` value,
so the divisor's type never names the route. It also carries an `< 2^64` premise division
does not need. The wrapper makes the route syntactic: the divisor's type names the route,
at the site and in every signature. -/

/-- A divisor that carries its own positivity. The constructor takes the proof, so a wrong
positivity claim cannot be made silently: the kernel checks `pos` where the divisor is built,
once, and every division through the `HDiv` instance below trusts that single discharge. There
is no `OfNat` instance, so a bare literal never silently becomes a claimed-positive divisor;
a literal divisor keeps the checked `/` route, whose zero-divisor raise stays reachable. The
fork wraps each constant divisor once,
`forkabbrev slotsPerEpochDiv : PositiveDivisor := ⟨Const.slotsPerEpoch, Const.slotsPerEpochPos⟩`,
and the call sites read `slot / Const.slotsPerEpochDiv` from then on. -/
structure PositiveDivisor where
  /-- The divisor value. -/
  val : Nat
  /-- The divisor is positive. Discharged once, where the divisor is built. -/
  pos : 0 < val

/-- `a // d` for a proof-carrying divisor: total. The quotient floors as Python's `//` does on
non-negative values, and it is at most `a`, so it cannot leave the range and the constructor
route cannot fault. This is the route a constant divisor takes, so the line reads as the
pyspec's `slot // SLOTS_PER_EPOCH` with no bind. -/
instance : HDiv CLUint64 PositiveDivisor CLUint64 :=
  ⟨fun a b => ⟨UInt64.ofNat (a.toPlainInt / b.val)⟩⟩

/-- `a % d` for a proof-carrying divisor: total, the companion of the `HDiv` instance above.
The remainder is at most the dividend, so it cannot leave the range either. This makes the `%`
of an `amount - amount % INCREMENT` site total once `INCREMENT`'s positivity is discharged;
the `-` keeps its own checked test. That test never fires, because the remainder is at most
the dividend, but the type cannot see that, so the bind stays.

Both instances take the dividend as a plain `CLUint64`. A `Checked` dividend has no route:
`(a * b) / d` fails instance synthesis, and the author binds first, `let p ← a * b`, then
divides, per the §4.3 discipline. -/
instance : HMod CLUint64 PositiveDivisor CLUint64 :=
  ⟨fun a b => ⟨UInt64.ofNat (a.toPlainInt % b.val)⟩⟩

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

open Lean Elab Term Meta in
/-- The literal gate (SPEC_ARITHMETIC.md §7, item 6). Core's `num` elaborator builds any
literal through the `OfNat` instance, and `UInt64.ofNat` wraps modulo `2^64`, so a literal
past `2^64 - 1` would silently become a small value. This scoped elaborator runs before
core's wherever `EthCLLib.Spec` is open, the same discipline as `elabCheckedOp`. It reads the
expected type only: any type but `CLUint64`, or a reducible alias of it such as the fork
body's `Gwei`, falls through to core with `throwUnsupportedSyntax`, and an in-range literal
falls through too, so `Nat`, `UInt64`, `Int`, and every other type keeps core's path. An
out-of-range literal raises with the value and the bound named. The gate sees through
reducible aliases only; a plain `def` alias of `CLUint64` would escape it. The fork DSL
authors every type alias through `forkabbrev`, which emits an `abbrev`, so no fork body
writes the escaping shape. -/
@[scoped term_elab num] def elabCheckedNumLit : TermElab := fun stx expectedType? => do
  let some expected := expectedType? | throwUnsupportedSyntax
  -- `whnfR` sees through reducible aliases (`abbrev` / `forkabbrev`) and leaves a
  -- metavariable-headed type stuck, so both the fall-through and the postponement behave
  -- exactly as the plain constant check would.
  unless (← whnfR (← instantiateMVars expected)).isConstOf ``CLUint64 do
    throwUnsupportedSyntax
  let some n := stx.isNatLit? | throwUnsupportedSyntax
  unless n < UInt64.size do
    throwError "literal `{n}` is out of range for `CLUint64`: the type holds `[0, 2^64 - 1]`, and the maximum is `18446744073709551615`"
  throwUnsupportedSyntax

end EthCLLib.Spec

namespace SizzLean

/-- `SSZRepr CLUint64`: the wire format of `uint64`, 8 little-endian bytes. The iso is the
structure's projection and the named constructor `trustedOfUInt64`, so both laws hold by
`rfl`. -/
instance : SSZRepr EthCLLib.Spec.CLUint64 where
  shape    := .uintN 64
  toRepr   := (·.val)
  fromRepr := (EthCLLib.Spec.CLUint64.trustedOfUInt64)
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

end SizzLean
