import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Spec.CLInt`: the pyspec's plain `int`

The pyspec has a second integer kind beside the checked one: Python's
unbounded, signed `int` (`SPEC_ARITHMETIC.md` §3.1). It comes from `len`, from
a `range` variable, from a literal, and from `sum` of an empty sequence.
`CLInt` is that kind, a `structure` over Lean `Int`, so core's Euclidean `/`
and `%` do not apply to it.

`+`, `-`, and `*` never raise on range (`SPEC_ARITHMETIC.md` §4.2), so they
stay total and return a `CLInt`. `/` and `%` floor toward minus infinity, as
Python does, and raise on a zero divisor (`Int.fdiv` / `Int.fmod` carry the
flooring; §5.2 pins `7 // -2 = -4`, `7 % -2 = -1`, `-7 % 2 = 1`).

The module also builds the mixed routes a spec body writes:

- `Nat op CLInt` in either order: the `Nat` coerces, the result is a `CLInt`,
  total, for `+ - *`.
- `CLInt op CLUint64` in either order: the pyspec's plain-int operand meeting
  a `Uint64`. The route computes on the original operands in `Int`, then runs
  the one range test into `CLUint64`, so the result is a `Checked CLUint64`
  and the plain operand is never narrowed first (`§4.2`: `Uint64(0) * (2**64)`
  succeeds with zero).

The cross-kind conversions carry the settled names (`§4.1`): `toPlainInt`
returns a Lean `Int`, `toCLUint64?` is the checked narrowing into
`CLUint64`, and the namespace-qualified `CLUint64.ofCLInt?` names its result
through its namespace. The plain routes out of the checked kind
(`CLUint64.toCLInt`, `CLUint8.toCLInt`) live here, beside the `CLInt` type
they produce.

Literal divisors: a bare integer defaults to `Nat` and a negated one to
`Int`, so `/` and `%` take a `Nat` or `Int` operand on either side of a
`CLInt` as well. Arithmetic on `CLInt` never raises on range (`§3.1`), so
construction is total and the constructor is public: every `Int` is a valid
`CLInt`.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The pyspec plain `int`. A `structure` over `Int`, so core's Euclidean `/`
and `%` do not apply (`SPEC_ARITHMETIC.md` §4.1). Unbounded and signed, so the
constructor is public and total: every `Int` is a valid plain value. -/
structure CLInt where
  /-- The underlying signed value. -/
  val : Int
  deriving DecidableEq, Hashable, Ord

namespace CLInt

instance : Repr CLInt := ⟨fun a _ => repr a.val⟩
instance : ToString CLInt := ⟨fun a => toString a.val⟩
/-- A plain literal is an unbounded literal until an explicit checked
construction (`SPEC_ARITHMETIC.md` §4.5). Total: no bound. -/
instance {n : Nat} : OfNat CLInt n := ⟨⟨n⟩⟩
/-- A Lean `Nat` (a size, a loop variable) enters the plain kind by cast. -/
instance : NatCast CLInt := ⟨fun n => ⟨n⟩⟩
instance : IntCast CLInt := ⟨fun n => ⟨n⟩⟩
instance : Inhabited CLInt := ⟨⟨0⟩⟩

instance : Neg CLInt := ⟨fun a => ⟨-a.val⟩⟩
instance : LT CLInt := ⟨fun a b => a.val < b.val⟩
instance : LE CLInt := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : CLInt) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : CLInt) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))

/-! `+`, `-`, and `*` never raise, so they stay total and return a plain
value (`SPEC_ARITHMETIC.md` §4.2). -/
instance : Add CLInt := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub CLInt := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Mul CLInt := ⟨fun a b => ⟨a.val * b.val⟩⟩

/-- `max(a, b)` of two plain values: the larger operand (`SPEC_ARITHMETIC.md`
§4.5). Total, a comparison. -/
instance : Max CLInt := ⟨fun a b => if a < b then b else a⟩

/-- `min(a, b)` of two plain values: the smaller operand. Total, a
comparison. -/
instance : Min CLInt := ⟨fun a b => if a < b then a else b⟩

/-- The signed value as a Lean `Int` (the settled name,
`SPEC_ARITHMETIC.md` §4.1). The result is unchecked, so each executable use
is a site a reviewer sees (`SPEC_ARITHMETIC.md` §5.6). -/
@[inline] def toPlainInt (a : CLInt) : Int := a.val

/-- `a // b`: Python floor division. Raises on a zero divisor; the flooring
itself is `Int.fdiv` (`SPEC_ARITHMETIC.md` §5.2: `7 // -2 = -4`,
`-7 // 2 = -4`). -/
@[inline] def fdiv (a b : CLInt) : Checked CLInt :=
  if b.val = 0 then .error (ArithFault.zeroDivisor "//" a.val)
  else .ok ⟨Int.fdiv a.val b.val⟩

/-- `a % b`: Python's `%`, the sign of the divisor. Raises on a zero divisor;
the flooring is `Int.fmod` (`§5.2`: `7 % -2 = -1`, `-7 % 2 = 1`). -/
@[inline] def fmod (a b : CLInt) : Checked CLInt :=
  if b.val = 0 then .error (ArithFault.zeroDivisor "%" a.val)
  else .ok ⟨Int.fmod a.val b.val⟩

/-- `len(xs)`: the pyspec's plain-integer length. The floor-division partner
of the raising `%` in `indices[i % len(indices)]`. -/
@[inline] def len {α : Type} (xs : Array α) : CLInt := ⟨xs.size⟩

/-- `Uint64(n)`: the checked narrowing into the checked kind. Raises for a
negative number and for one past `2^64 - 1` (`SPEC_ARITHMETIC.md` §4.5). The
body delegates to `CLUint64.ofInt?`, so the `Uint64(n)` range test has one
canonical home. -/
@[inline] def toCLUint64? (n : CLInt) : Checked CLUint64 := CLUint64.ofInt? n.val

end CLInt

/-! ## The cross-kind conversions

The plain routes out of the checked kind (`int(x)`, always succeeds) and the
namespace-qualified form of the checked narrowing. They live beside `CLInt`,
the type the plain routes produce. -/

/-- `int(x)` at width 64: always succeeds. -/
@[inline] def CLUint64.toCLInt (a : CLUint64) : CLInt := ⟨a.toPlainNat⟩

/-- `int(x)` at width 8: always succeeds. -/
@[inline] def CLUint8.toCLInt (a : CLUint8) : CLInt := ⟨a.toPlainNat⟩

/-- `Uint64(n)` from a `CLInt`, the namespace-qualified form of
`CLInt.toCLUint64?` (`SPEC_ARITHMETIC.md` §4.5). -/
@[inline] def CLUint64.ofCLInt? (n : CLInt) : Checked CLUint64 := n.toCLUint64?

/-- The checked narrowing round-trips a checked value: the range test reads
the value's own bound, so it cannot fire. -/
theorem CLUint64.toCLInt_toCLUint64? (a : CLUint64) :
    a.toCLInt.toCLUint64? = .ok a := by
  have hlt : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
  show CLUint64.ofInt? (a.toPlainNat : Int) = .ok a
  unfold CLUint64.ofInt?
  rw [dite_eq_left (show 0 ≤ (a.toPlainNat : Int) ∧
    (a.toPlainNat : Int) < 18446744073709551616 by omega)]
  refine congrArg _ (val_inj (UInt64.toNat_inj.1 ?_))
  simp only [ofNatLT, UInt64.toNat_ofNatLT, toPlainNat]
  omega

/-! ## The operator matrix (`SPEC_ARITHMETIC.md` §4.2)

`I` is `CLInt`, `U` is `CLUint64`, and `Ç` marks a `Checked` operand, an
expression not bound yet. The rows:

| Operands | Operators | Result | Raises |
|---|---|---|---|
| `I, I` | `+ - *` | `I` | never |
| `I, I` | `/ %` | `Checked I` | zero divisor |
| `Nat, I` in either order | `+ - *` | `I` | never |
| `Nat, I` in either order | `/ %` | `Checked I` | zero divisor |
| `I, U` in either order | `+ - * / %` | `Checked U` | outside `[0, 2^64)`, or zero divisor |
| supported pairs with a `Ç` operand | same | `Checked` of the same type | the operand's fault, then the operator's |

A fault on the left passes first: the right operand never computes, the
pyspec's left-to-right raise order. No instance is a `default_instance`
(`§5.6`). -/

instance : HDiv CLInt CLInt (Checked CLInt) := ⟨CLInt.fdiv⟩
instance : HMod CLInt CLInt (Checked CLInt) := ⟨CLInt.fmod⟩

/-! A bare integer literal is a `Nat` and a negated one is an `Int`, so the
partial operators also take a `Nat` or `Int` operand on either side of a
`CLInt`. -/

instance : HDiv CLInt Nat (Checked CLInt) := ⟨fun a b => CLInt.fdiv a ⟨b⟩⟩
instance : HDiv Nat CLInt (Checked CLInt) := ⟨fun a b => CLInt.fdiv ⟨a⟩ b⟩
instance : HDiv CLInt Int (Checked CLInt) := ⟨fun a b => CLInt.fdiv a ⟨b⟩⟩
instance : HDiv Int CLInt (Checked CLInt) := ⟨fun a b => CLInt.fdiv ⟨a⟩ b⟩
instance : HMod CLInt Nat (Checked CLInt) := ⟨fun a b => CLInt.fmod a ⟨b⟩⟩
instance : HMod Nat CLInt (Checked CLInt) := ⟨fun a b => CLInt.fmod ⟨a⟩ b⟩
instance : HMod CLInt Int (Checked CLInt) := ⟨fun a b => CLInt.fmod a ⟨b⟩⟩
instance : HMod Int CLInt (Checked CLInt) := ⟨fun a b => CLInt.fmod ⟨a⟩ b⟩

/-! `Nat op CLInt`, either order, for `+ - *`: the `Nat` coerces, the result
is a `CLInt`, total (`§4.2`). -/

instance : HAdd Nat CLInt CLInt := ⟨fun a b => ⟨a⟩ + b⟩
instance : HAdd CLInt Nat CLInt := ⟨fun a b => a + ⟨b⟩⟩
instance : HSub Nat CLInt CLInt := ⟨fun a b => ⟨a⟩ - b⟩
instance : HSub CLInt Nat CLInt := ⟨fun a b => a - ⟨b⟩⟩
instance : HMul Nat CLInt CLInt := ⟨fun a b => ⟨a⟩ * b⟩
instance : HMul CLInt Nat CLInt := ⟨fun a b => a * ⟨b⟩⟩

/-! A `Checked` operand on either side of a supported pair: the operand's
fault passes first, then the operator's own raise (`§4.2`). The pairs are
`I, I` (with the `Nat` and `Int` literal sides for `/ %`) for the plain kind,
and the `I, U` pair for the mixed route. -/

private def andThen2 {α : Type} (f : α → α → Checked α)
    (a : Except ArithFault α) (b : α) : Checked α := a >>= fun x => f x b

private def andThenL {α : Type} (f : α → α → Checked α)
    (a : α) (b : Except ArithFault α) : Checked α := b >>= fun y => f a y

private def andThen3 {α : Type} (f : α → α → Checked α)
    (a b : Except ArithFault α) : Checked α := a >>= fun x => b >>= fun y => f x y

instance : HAdd (Checked CLInt) CLInt (Checked CLInt) := ⟨andThen2 (fun x y => pure (x + y))⟩
instance : HAdd CLInt (Checked CLInt) (Checked CLInt) := ⟨andThenL (fun x y => pure (x + y))⟩
instance : HAdd (Checked CLInt) (Checked CLInt) (Checked CLInt) :=
  ⟨andThen3 (fun x y => pure (x + y))⟩
instance : HAdd (Checked CLInt) Nat (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => pure (x + ⟨b⟩)⟩
instance : HAdd Nat (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => pure (⟨a⟩ + y)⟩

instance : HSub (Checked CLInt) CLInt (Checked CLInt) := ⟨andThen2 (fun x y => pure (x - y))⟩
instance : HSub CLInt (Checked CLInt) (Checked CLInt) := ⟨andThenL (fun x y => pure (x - y))⟩
instance : HSub (Checked CLInt) (Checked CLInt) (Checked CLInt) :=
  ⟨andThen3 (fun x y => pure (x - y))⟩
instance : HSub (Checked CLInt) Nat (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => pure (x - ⟨b⟩)⟩
instance : HSub Nat (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => pure (⟨a⟩ - y)⟩

instance : HMul (Checked CLInt) CLInt (Checked CLInt) := ⟨andThen2 (fun x y => pure (x * y))⟩
instance : HMul CLInt (Checked CLInt) (Checked CLInt) := ⟨andThenL (fun x y => pure (x * y))⟩
instance : HMul (Checked CLInt) (Checked CLInt) (Checked CLInt) :=
  ⟨andThen3 (fun x y => pure (x * y))⟩
instance : HMul (Checked CLInt) Nat (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => pure (x * ⟨b⟩)⟩
instance : HMul Nat (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => pure (⟨a⟩ * y)⟩

instance : HDiv (Checked CLInt) CLInt (Checked CLInt) := ⟨andThen2 CLInt.fdiv⟩
instance : HDiv CLInt (Checked CLInt) (Checked CLInt) := ⟨andThenL CLInt.fdiv⟩
instance : HDiv (Checked CLInt) (Checked CLInt) (Checked CLInt) := ⟨andThen3 CLInt.fdiv⟩
instance : HDiv (Checked CLInt) Nat (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => CLInt.fdiv x ⟨b⟩⟩
instance : HDiv Nat (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => CLInt.fdiv ⟨a⟩ y⟩
instance : HDiv (Checked CLInt) Int (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => CLInt.fdiv x ⟨b⟩⟩
instance : HDiv Int (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => CLInt.fdiv ⟨a⟩ y⟩

instance : HMod (Checked CLInt) CLInt (Checked CLInt) := ⟨andThen2 CLInt.fmod⟩
instance : HMod CLInt (Checked CLInt) (Checked CLInt) := ⟨andThenL CLInt.fmod⟩
instance : HMod (Checked CLInt) (Checked CLInt) (Checked CLInt) := ⟨andThen3 CLInt.fmod⟩
instance : HMod (Checked CLInt) Nat (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => CLInt.fmod x ⟨b⟩⟩
instance : HMod Nat (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => CLInt.fmod ⟨a⟩ y⟩
instance : HMod (Checked CLInt) Int (Checked CLInt) :=
  ⟨fun a b => a >>= fun x => CLInt.fmod x ⟨b⟩⟩
instance : HMod Int (Checked CLInt) (Checked CLInt) :=
  ⟨fun a b => b >>= fun y => CLInt.fmod ⟨a⟩ y⟩

/-! `I op U`, either order, for `+ - * / %`: compute on the original operands
in `Int`, then run the one range test into `CLUint64`. The plain operand is
never narrowed first, so `Uint64(0) * (2**64)` succeeds with zero (`§4.2`).
The `/` and `%` of the mixed routes floor as Python does (`Int.fdiv` /
`Int.fmod`, `§5.2`), so a negative divisor drives the result out of the range
and raises, exactly where the pyspec raises. The fault carries the operator
and both original operands. -/

private def mixIntoUint (op : String) (f : Int → Int → Int)
    (a : Int) (b : CLUint64) : Checked CLUint64 :=
  CLUint64.mixBin op f a b.asInt

private def mixIntoUint' (op : String) (f : Int → Int → Int)
    (a : CLUint64) (b : Int) : Checked CLUint64 :=
  CLUint64.mixBin op f a.asInt b

private def mixIntoUintDiv (op : String) (f : Int → Int → Int)
    (a : Int) (b : CLUint64) : Checked CLUint64 :=
  CLUint64.mixBinDiv op f a b.asInt

private def mixIntoUintDiv' (op : String) (f : Int → Int → Int)
    (a : CLUint64) (b : Int) : Checked CLUint64 :=
  CLUint64.mixBinDiv op f a.asInt b

private def mixUintAdd (a : CLInt) (b : CLUint64) : Checked CLUint64 :=
  mixIntoUint "+" (· + ·) a.val b
private def mixUintSub (a : CLInt) (b : CLUint64) : Checked CLUint64 :=
  mixIntoUint "-" (· - ·) a.val b
private def mixUintMul (a : CLInt) (b : CLUint64) : Checked CLUint64 :=
  mixIntoUint "*" (· * ·) a.val b
private def mixUintDiv (a : CLInt) (b : CLUint64) : Checked CLUint64 :=
  mixIntoUintDiv "//" Int.fdiv a.val b
private def mixUintMod (a : CLInt) (b : CLUint64) : Checked CLUint64 :=
  mixIntoUintDiv "%" Int.fmod a.val b

private def uintMixAdd (a : CLUint64) (b : CLInt) : Checked CLUint64 :=
  mixIntoUint' "+" (· + ·) a b.val
private def uintMixSub (a : CLUint64) (b : CLInt) : Checked CLUint64 :=
  mixIntoUint' "-" (· - ·) a b.val
private def uintMixMul (a : CLUint64) (b : CLInt) : Checked CLUint64 :=
  mixIntoUint' "*" (· * ·) a b.val
private def uintMixDiv (a : CLUint64) (b : CLInt) : Checked CLUint64 :=
  mixIntoUintDiv' "//" Int.fdiv a b.val
private def uintMixMod (a : CLUint64) (b : CLInt) : Checked CLUint64 :=
  mixIntoUintDiv' "%" Int.fmod a b.val

instance : HAdd CLInt CLUint64 (Checked CLUint64) := ⟨mixUintAdd⟩
instance : HAdd CLUint64 CLInt (Checked CLUint64) := ⟨uintMixAdd⟩
instance : HAdd (Checked CLInt) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixUintAdd x b⟩
instance : HAdd CLInt (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixUintAdd a y⟩
instance : HAdd CLUint64 (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => uintMixAdd a y⟩
instance : HAdd (Checked CLUint64) CLInt (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => uintMixAdd x b⟩
instance : HAdd (Checked CLInt) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mixUintAdd x y⟩
instance : HAdd (Checked CLUint64) (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => uintMixAdd x y⟩

instance : HSub CLInt CLUint64 (Checked CLUint64) := ⟨mixUintSub⟩
instance : HSub CLUint64 CLInt (Checked CLUint64) := ⟨uintMixSub⟩
instance : HSub (Checked CLInt) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixUintSub x b⟩
instance : HSub CLInt (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixUintSub a y⟩
instance : HSub CLUint64 (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => uintMixSub a y⟩
instance : HSub (Checked CLUint64) CLInt (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => uintMixSub x b⟩
instance : HSub (Checked CLInt) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mixUintSub x y⟩
instance : HSub (Checked CLUint64) (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => uintMixSub x y⟩

instance : HMul CLInt CLUint64 (Checked CLUint64) := ⟨mixUintMul⟩
instance : HMul CLUint64 CLInt (Checked CLUint64) := ⟨uintMixMul⟩
instance : HMul (Checked CLInt) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixUintMul x b⟩
instance : HMul CLInt (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixUintMul a y⟩
instance : HMul CLUint64 (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => uintMixMul a y⟩
instance : HMul (Checked CLUint64) CLInt (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => uintMixMul x b⟩
instance : HMul (Checked CLInt) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mixUintMul x y⟩
instance : HMul (Checked CLUint64) (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => uintMixMul x y⟩

instance : HDiv CLInt CLUint64 (Checked CLUint64) := ⟨mixUintDiv⟩
instance : HDiv CLUint64 CLInt (Checked CLUint64) := ⟨uintMixDiv⟩
instance : HDiv (Checked CLInt) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixUintDiv x b⟩
instance : HDiv CLInt (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixUintDiv a y⟩
instance : HDiv CLUint64 (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => uintMixDiv a y⟩
instance : HDiv (Checked CLUint64) CLInt (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => uintMixDiv x b⟩
instance : HDiv (Checked CLInt) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mixUintDiv x y⟩
instance : HDiv (Checked CLUint64) (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => uintMixDiv x y⟩

instance : HMod CLInt CLUint64 (Checked CLUint64) := ⟨mixUintMod⟩
instance : HMod CLUint64 CLInt (Checked CLUint64) := ⟨uintMixMod⟩
instance : HMod (Checked CLInt) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixUintMod x b⟩
instance : HMod CLInt (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixUintMod a y⟩
instance : HMod CLUint64 (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => uintMixMod a y⟩
instance : HMod (Checked CLUint64) CLInt (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => uintMixMod x b⟩
instance : HMod (Checked CLInt) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mixUintMod x y⟩
instance : HMod (Checked CLUint64) (Checked CLInt) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => uintMixMod x y⟩

end EthCLLib.Spec
