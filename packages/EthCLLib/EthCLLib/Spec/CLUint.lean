import SizzLean
import EthCLLib.Spec.Checked

/-!
# `EthCLLib.Spec.CLUint`: the pyspec's checked `Uint64` and `Uint8`

The pyspec computes with a checked integer kind: every operator computes in
Python's unbounded `int`, tests the result against `[0, 2**BITS - 1]`, and
raises outside it (`SPEC_ARITHMETIC.md` §3.1). `CLUint64` is that kind at width
64, the type behind `Uint64` and every 64-bit unit (`Slot`, `Epoch`, `Gwei`,
`ValidatorIndex`). `CLUint8` is the same kind at width 8, the type behind the
pinned `ParticipationFlags`.

Both are `structure`s over the core fixed-width type. No core operator instance
applies to them, so the wrapping `UInt64` addition does not exist on a
`CLUint64` value: the only routes in are the checked constructors below, and
the only operators are the checked ones. The operators that can fault return a
`Checked` value (`Spec/Checked.lean`), so a spec body binds the expression once
with `←` (`SPEC_ARITHMETIC.md` §4.3).

## Safe construction

The constructors are private to this module. The routes from a plain number
are:

- `ofNat?` / `ofInt?` / `ofCLInt?`: the checked narrowings, the pyspec's
  `Uint64(n)` cast (`SPEC_ARITHMETIC.md` §4.5).
- `ofNatLT`: proof-carrying construction from a `Nat` with a kernel-checked
  range proof. Framework-facing: SSZ decode helpers and preset constants.
- `trustedOfUInt64`: the wire iso's inverse, for a raw `UInt64` the framework
  already holds. Every `UInt64` sits inside `[0, 2^64)`, so the wrap cannot
  fault. Callers are SSZ decode and the codec only; a trusted constructor
  never repairs an operator elaboration error (`SPEC_ARITHMETIC.md` §4.5).

## Kernel-checked literals

The `OfNat` instance carries a decidable bound premise,
`NeZero (18446744073709551616 - n)` for width 64 and `NeZero (256 - n)` for
width 8. Core's instance search discharges it through the core
`NeZero (n + 1)` instance: the kernel reduces the subtraction on literals, and
`?m + 1` unifies with the result exactly when the value is positive, that is,
when `n < 2^64` (or `n < 2^8`). An out-of-range literal therefore fails
instance synthesis, a compile error with no elaborator involved. The gate
lives in the `OfNat` construction itself, so it holds at a direct literal,
through a reducible alias, under a delayed expected type, and in a module that
never opens this file's namespace.

The bound is spelled as a numeral because the instance key reduces `Nat.sub`
on literals only when both arguments are already literals. `UInt64.size` is an
`abbrev`, and the key unifier never unfolds it inside the key, so the literal
form is the one that works. Each width names its bound once, here.

## Widths 64 and 8

The two widths duplicate the wrapper shape. A shared generic over a width
parameter cannot carry the literal gate: the premise key needs the width's
bound as a written numeral, and the wire shapes (`.uintN 64` and `.uintN 8`)
differ. The shared content is the mechanism, the naming, and the fault shape,
documented here once. The operations differ too: width 64 carries the full
five-operator matrix (`SPEC_ARITHMETIC.md` §4.2), width 8 carries construction
and the flag masks only, the surface `add_flag` / `has_flag` use. No width
beyond 8 and 64 is built: the Stage 0 inventory found no arithmetic consumer
at `uint32` or `uint256` (those widths appear only at the codec boundary,
which Stage 8 audits).

Settled conversion names (`SPEC_ARITHMETIC.md` §4.1): `toPlainNat` returns a
Lean `Nat`, `toCLInt` returns a `CLInt`, and a checked conversion to a checked
type is named `toCLUint64?` on the source type.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The pyspec `Uint64` and its 64-bit units. A `structure` over `UInt64`, so
no `UInt64` operator instance applies: the wrapping `+` does not exist on this
type (`SPEC_ARITHMETIC.md` §4.1).

The constructor is private to this module (`SPEC_ARITHMETIC.md` §4.5): the
routes from a plain number are `ofNat?`, `ofInt?`, `ofCLInt?`, `ofNatLT`, and
the wire iso's `trustedOfUInt64`. The projection `val` stays public, so reads,
the SSZ iso, and the proofs keep working. -/
structure CLUint64 where
  private mk ::
  /-- The native value. -/
  val : UInt64
  deriving DecidableEq, Hashable, Ord

namespace CLUint64

/-- The wire iso's inverse: wrap a raw `UInt64`. Every `UInt64` already sits in
`[0, 2^64)`, so the wrap cannot fault and the route needs no range test.

Callers are the framework's codec sites only: SSZ decode, preset constants,
and total bitwise writes over raw operands. A spec body builds values from
computed numbers through `ofNat?`, `ofInt?`, `ofCLInt?`, `ofNatLT`, the
operators, or a literal. A trusted constructor never repairs an operator
elaboration error (`SPEC_ARITHMETIC.md` §4.5). -/
@[inline] def trustedOfUInt64 (v : UInt64) : CLUint64 := ⟨v⟩

/-- Proof-carrying construction from a `Nat` whose range the kernel checked.
The range proof is visible at the call site, so a constant or a decode bound
pays for its own admission (`SPEC_ARITHMETIC.md` §4.5). -/
@[inline] def ofNatLT (n : Nat) (h : n < UInt64.size) : CLUint64 :=
  ⟨UInt64.ofNatLT n h⟩

/-- The projection reflects equality: two checked values are equal when their
native values are. This is the public face of the private constructor's
injectivity, so a proof outside this module reduces a wrapper equation to a
plain `UInt64` one. -/
theorem val_inj {a b : CLUint64} (h : a.val = b.val) : a = b :=
  congrArg mk h

/-- The value as a Lean `Nat` (the settled name, `SPEC_ARITHMETIC.md` §4.1).
The pyspec's `int(x)` at width 64. The result is unchecked, so each executable
use is a site a reviewer sees (`SPEC_ARITHMETIC.md` §5.6). -/
@[inline] def toPlainNat (a : CLUint64) : Nat := a.val.toNat

instance : Inhabited CLUint64 := ⟨⟨0⟩⟩
instance : Repr CLUint64 := ⟨fun a _ => repr a.toPlainNat⟩
instance : ToString CLUint64 := ⟨fun a => toString a.toPlainNat⟩

/-- The literal instance. The `NeZero` premise is the kernel-checked bound: core
instance search discharges it through `NeZero (n + 1)` exactly when
`n < 2^64`, so an out-of-range literal fails to synthesize and the module
fails to build. See the module docstring for the numeral in the key. -/
instance {n : Nat} [NeZero (18446744073709551616 - n)] : OfNat CLUint64 n :=
  ⟨mk (UInt64.ofNat n)⟩

instance : LT CLUint64 := ⟨fun a b => a.val < b.val⟩
instance : LE CLUint64 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : CLUint64) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : CLUint64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))

/-- `max(a, b)` of two checked values: the larger operand (`SPEC_ARITHMETIC.md`
§4.5). Total, a comparison. -/
instance : Max CLUint64 := ⟨fun a b => if a < b then b else a⟩

/-- `min(a, b)` of two checked values: the smaller operand. Total, a
comparison. -/
instance : Min CLUint64 := ⟨fun a b => if a < b then a else b⟩

/-- A literal built through the gate carries its value across: the kernel
checked `n < 2^64`, so the wrap in `UInt64.ofNat` never fires. -/
theorem ofNat_toPlainNat {n : Nat} (h : NeZero (18446744073709551616 - n)) :
    (OfNat.ofNat n : CLUint64).toPlainNat = n := by
  have hlt : n < UInt64.size := by
    have := h.out
    show n < 18446744073709551616
    omega
  show (⟨UInt64.ofNat n⟩ : CLUint64).toPlainNat = n
  simp only [toPlainNat, UInt64.toNat_ofNat_of_lt' hlt]

/-- `ofNatLT` is the exact value: the range proof makes the wrap dead. -/
theorem ofNatLT_toPlainNat (n : Nat) (h : n < UInt64.size) :
    (ofNatLT n h).toPlainNat = n := by
  simp only [toPlainNat, ofNatLT, UInt64.toNat_ofNatLT]

/-- `Uint64(n)` from a plain `int`: the checked narrowing
(`SPEC_ARITHMETIC.md` §4.5). Raises, as `.range` with the cast as the
operator, past `2^64 - 1`. -/
@[inline] def ofNat? (n : Nat) : Checked CLUint64 :=
  if h : n < UInt64.size then .ok (ofNatLT n h) else .error (ArithFault.range "Uint64()" 64 n 0)

/-- `Uint64(n)` from a signed plain `int`: the checked narrowing. Raises for a
negative number and past `2^64 - 1`. -/
@[inline] def ofInt? (n : Int) : Checked CLUint64 :=
  if h : 0 ≤ n ∧ n < 18446744073709551616 then
    .ok (ofNatLT n.toNat (by have := h.2; show n.toNat < 18446744073709551616; omega))
  else
    .error (ArithFault.range "Uint64()" 64 n 0)

/-- The narrowing succeeds in range, with the proof-carrying value. -/
theorem ofNat?_ok (n : Nat) (h : n < UInt64.size) :
    ofNat? n = .ok (ofNatLT n h) := by simp [ofNat?, h]

/-- The narrowing raises past the maximum, with the operands in the fault. -/
theorem ofNat?_fault (n : Nat) (h : UInt64.size ≤ n) :
    ofNat? n = .error (ArithFault.range "Uint64()" 64 n 0) := by
  simp only [ofNat?, dite_eq_right (Nat.not_lt.mpr h)]

/-- `saturating_sub(a, b)`: `a - b`, floored at zero. Total
(`SPEC_ARITHMETIC.md` §3.5, §4.5). -/
@[inline] def saturatingSub (a b : CLUint64) : CLUint64 :=
  if a > b then ⟨a.val - b.val⟩ else 0

/-- `saturatingSub` reads back as the truncating `Nat` difference. -/
theorem saturatingSub_toPlainNat (a b : CLUint64) :
    (a.saturatingSub b).toPlainNat = a.toPlainNat - b.toPlainNat := by
  rw [saturatingSub]
  split
  · rename_i h
    show (a.val - b.val).toNat = a.toPlainNat - b.toPlainNat
    show (a.val - b.val).toNat = a.val.toNat - b.val.toNat
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)]
  · rename_i h
    have hle : a.toPlainNat ≤ b.toPlainNat := by
      have h' : ¬(b.toPlainNat < a.toPlainNat) := fun hlt =>
        h (UInt64.lt_iff_toNat_lt.mpr hlt)
      omega
    show (0 : UInt64).toNat = a.toPlainNat - b.toPlainNat
    rw [show (0 : UInt64).toNat = (0 : Nat) from rfl]
    omega

/-! ## The five operators on two checked values

The pyspec computes unbounded and range-tests the result. The model uses the
native width where the test is exact at the width: `+` tests the carry, `-`
the borrow, and `*` the truncating product. Division and modulo of two
in-range values cannot leave the range (`SPEC_ARITHMETIC.md` §3.2); the only
raise is a zero divisor. The fault carries the operator and the operands the
operator computed on, diagnostic only.
-/

/-- Checked addition: raises past `2^64 - 1`, where the native sum would wrap. -/
@[inline] def add (a b : CLUint64) : Checked CLUint64 :=
  if a.val + b.val < a.val then
    .error (ArithFault.range "+" 64 a.toPlainNat b.toPlainNat)
  else
    .ok ⟨a.val + b.val⟩

/-- Checked subtraction: raises below zero, where the native difference would
wrap. -/
@[inline] def sub (a b : CLUint64) : Checked CLUint64 :=
  if a.val < b.val then
    .error (ArithFault.range "-" 64 a.toPlainNat b.toPlainNat)
  else
    .ok ⟨a.val - b.val⟩

/-- Checked multiplication: raises past `2^64 - 1`. The test is the truncating
product: with `a ≠ 0`, the wrapped product divided by `a` recovers `b` exactly
when no high bits were lost. Mirrors `checkedMul` in `Spec/Errors.lean`. -/
@[inline] def mul (a b : CLUint64) : Checked CLUint64 :=
  if a.val != 0 && a.val * b.val / a.val != b.val then
    .error (ArithFault.range "*" 64 a.toPlainNat b.toPlainNat)
  else
    .ok ⟨a.val * b.val⟩

/-- Checked division: raises on a zero divisor. The quotient of two in-range
values is in range (`SPEC_ARITHMETIC.md` §3.2). -/
@[inline] def div (a b : CLUint64) : Checked CLUint64 :=
  if b.val == 0 then .error (ArithFault.zeroDivisor "//" 64 a.toPlainNat)
  else .ok ⟨a.val / b.val⟩

/-- Checked modulo: raises on a zero divisor. The remainder of two in-range
values is in range. -/
@[inline] def mod (a b : CLUint64) : Checked CLUint64 :=
  if b.val == 0 then .error (ArithFault.zeroDivisor "%" 64 a.toPlainNat)
  else .ok ⟨a.val % b.val⟩

/-! ## The mixed route: a plain `int` operand on either side

The pyspec computes on the original operands and tests the result
(`SPEC_ARITHMETIC.md` §4.2). The model never narrows the plain operand first:
`Uint64(0) * (2**64)` succeeds with zero, where a narrowed `2**64` would be
the cast raise. The helpers compute in `Int` on the operands as given, then
run the one range test, and the fault names the operator with both original
operands.
-/

/-- Compute `f` on the plain values, then run the one range test. The fault
names `op` with both original operands. The mixed-route engine behind the
`Nat`-operand instances here and the `CLInt`-operand instances in
`Spec/CLInt.lean`. -/
@[inline] def mixBin (op : String) (f : Int → Int → Int)
    (a b : Int) : Checked CLUint64 :=
  let r := f a b
  let n := r.toNat
  if h : 0 ≤ r ∧ r < 18446744073709551616 then
    .ok (ofNatLT n (by have := h.2; show n < 18446744073709551616; omega))
  else
    .error (ArithFault.range op 64 a b)

/-- `f`, guarding the zero divisor first: Lean's `Int` division and modulo of
`x` by `0` are defined, and the pyspec raises, so the raise comes first. -/
@[inline] def mixBinDiv (op : String) (f : Int → Int → Int)
    (a b : Int) : Checked CLUint64 :=
  if b = 0 then .error (ArithFault.zeroDivisor op 64 a) else mixBin op f a b

@[inline] private def mixAdd (a b : Int) : Checked CLUint64 := mixBin "+" (· + ·) a b
@[inline] private def mixSub (a b : Int) : Checked CLUint64 := mixBin "-" (· - ·) a b
@[inline] private def mixMul (a b : Int) : Checked CLUint64 := mixBin "*" (· * ·) a b
@[inline] private def mixDiv (a b : Int) : Checked CLUint64 := mixBinDiv "//" Int.fdiv a b
@[inline] private def mixMod (a b : Int) : Checked CLUint64 := mixBinDiv "%" Int.fmod a b

/-- The operand as a plain `int`, the value the mixed route computes on. The
`Spec/CLInt.lean` mixed instances use it on their `CLUint64` side. -/
@[inline] def asInt (a : CLUint64) : Int := a.toPlainNat

/-! One operator, every supported operand shape (`SPEC_ARITHMETIC.md` §4.2):
the two checked operands, the `Nat` operand in either order, and the
`Checked` forms with the checked operand on either side or on both. A fault on
the left passes first: the right operand never computes, which is the
pyspec's left-to-right raise order. No instance is a `default_instance`: that
attribute is global and would retype unrelated arithmetic in every importer
(`SPEC_ARITHMETIC.md` §5.6). -/

instance : HAdd CLUint64 CLUint64 (Checked CLUint64) := ⟨add⟩
instance : HAdd Nat CLUint64 (Checked CLUint64) := ⟨fun a b => mixAdd a b.asInt⟩
instance : HAdd CLUint64 Nat (Checked CLUint64) := ⟨fun a b => mixAdd a.asInt b⟩
instance : HAdd (Checked CLUint64) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => add x b⟩
instance : HAdd CLUint64 (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => add a y⟩
instance : HAdd (Checked CLUint64) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => add x y⟩
instance : HAdd Nat (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixAdd a y.asInt⟩
instance : HAdd (Checked CLUint64) Nat (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixAdd x.asInt b⟩

instance : HSub CLUint64 CLUint64 (Checked CLUint64) := ⟨sub⟩
instance : HSub Nat CLUint64 (Checked CLUint64) := ⟨fun a b => mixSub a b.asInt⟩
instance : HSub CLUint64 Nat (Checked CLUint64) := ⟨fun a b => mixSub a.asInt b⟩
instance : HSub (Checked CLUint64) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => sub x b⟩
instance : HSub CLUint64 (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => sub a y⟩
instance : HSub (Checked CLUint64) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => sub x y⟩
instance : HSub Nat (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixSub a y.asInt⟩
instance : HSub (Checked CLUint64) Nat (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixSub x.asInt b⟩

instance : HMul CLUint64 CLUint64 (Checked CLUint64) := ⟨mul⟩
instance : HMul Nat CLUint64 (Checked CLUint64) := ⟨fun a b => mixMul a b.asInt⟩
instance : HMul CLUint64 Nat (Checked CLUint64) := ⟨fun a b => mixMul a.asInt b⟩
instance : HMul (Checked CLUint64) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mul x b⟩
instance : HMul CLUint64 (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mul a y⟩
instance : HMul (Checked CLUint64) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mul x y⟩
instance : HMul Nat (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixMul a y.asInt⟩
instance : HMul (Checked CLUint64) Nat (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixMul x.asInt b⟩

instance : HDiv CLUint64 CLUint64 (Checked CLUint64) := ⟨div⟩
instance : HDiv Nat CLUint64 (Checked CLUint64) := ⟨fun a b => mixDiv a b.asInt⟩
instance : HDiv CLUint64 Nat (Checked CLUint64) := ⟨fun a b => mixDiv a.asInt b⟩
instance : HDiv (Checked CLUint64) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => div x b⟩
instance : HDiv CLUint64 (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => div a y⟩
instance : HDiv (Checked CLUint64) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => div x y⟩
instance : HDiv Nat (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixDiv a y.asInt⟩
instance : HDiv (Checked CLUint64) Nat (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixDiv x.asInt b⟩

instance : HMod CLUint64 CLUint64 (Checked CLUint64) := ⟨mod⟩
instance : HMod Nat CLUint64 (Checked CLUint64) := ⟨fun a b => mixMod a b.asInt⟩
instance : HMod CLUint64 Nat (Checked CLUint64) := ⟨fun a b => mixMod a.asInt b⟩
instance : HMod (Checked CLUint64) CLUint64 (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mod x b⟩
instance : HMod CLUint64 (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mod a y⟩
instance : HMod (Checked CLUint64) (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => b >>= fun y => mod x y⟩
instance : HMod Nat (Checked CLUint64) (Checked CLUint64) :=
  ⟨fun a b => b >>= fun y => mixMod a y.asInt⟩
instance : HMod (Checked CLUint64) Nat (Checked CLUint64) :=
  ⟨fun a b => a >>= fun x => mixMod x.asInt b⟩

end CLUint64

/-! ## The pyspec `Uint8`, the type behind `ParticipationFlags`

At the pin, `ParticipationFlags` is a `Uint8` subclass, and the pinned
`add_flag` / `has_flag` compute on it: each forms the mask
`ParticipationFlags(2**flag_index)`, which range-tests the mask against
`[0, 255]` and raises past flag index 7, then combines with the width-8 `|`
(in `add_flag`) or `&` and `==` (in `has_flag`). The `|` and `&` of two
in-range values cannot leave the range, so those two are total here and return
the value, matching the §5.1 row for same-width bitwise operators. The masks
raise, so `addFlag` and `hasFlag` return a `Checked` result: the raise is the
pyspec's, and Stage 8 migrates the raw-`UInt8` helpers in
`Spec/Arith.lean` (`hasFlag` / `addFlag`) onto this surface. -/

/-- The pyspec `Uint8`. Same shape as `CLUint64`: no core operator instance
applies, the constructor is private, and `ofNat?` is the checked route from a
plain number, the pyspec's `Uint8(x)` / `ParticipationFlags(x)` cast. The
literal gate is the same kernel-checked `NeZero` premise at bound `2^8`. -/
structure CLUint8 where
  private mk ::
  /-- The native value. -/
  val : UInt8
  deriving DecidableEq, Hashable, Ord

namespace CLUint8

/-- The wire iso's inverse: wrap a raw `UInt8`. Same callers as
`CLUint64.trustedOfUInt64`. -/
@[inline] def trustedOfUInt8 (v : UInt8) : CLUint8 := ⟨v⟩

/-- Proof-carrying construction from a `Nat` the kernel range-checked. -/
@[inline] def ofNatLT (n : Nat) (h : n < UInt8.size) : CLUint8 :=
  ⟨UInt8.ofNatLT n h⟩

/-- The value as a Lean `Nat`, the settled name (`SPEC_ARITHMETIC.md` §4.1). -/
@[inline] def toPlainNat (a : CLUint8) : Nat := a.val.toNat

instance : Inhabited CLUint8 := ⟨⟨0⟩⟩
instance : Repr CLUint8 := ⟨fun a _ => repr a.toPlainNat⟩
instance : ToString CLUint8 := ⟨fun a => toString a.toPlainNat⟩

/-- The literal instance at bound `2^8`. Same gate shape as the width-64 one
above. -/
instance {n : Nat} [NeZero (256 - n)] : OfNat CLUint8 n :=
  ⟨mk (UInt8.ofNat n)⟩

instance : LT CLUint8 := ⟨fun a b => a.val < b.val⟩
instance : LE CLUint8 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : CLUint8) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : CLUint8) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))

/-- A literal built through the gate carries its value across. -/
theorem ofNat_toPlainNat {n : Nat} (h : NeZero (256 - n)) :
    (OfNat.ofNat n : CLUint8).toPlainNat = n := by
  have hlt : n < UInt8.size := by
    have := h.out
    show n < 256
    omega
  show (⟨UInt8.ofNat n⟩ : CLUint8).toPlainNat = n
  simp only [toPlainNat, UInt8.toNat_ofNat_of_lt' hlt]

/-- `ofNatLT` is the exact value. -/
theorem ofNatLT_toPlainNat (n : Nat) (h : n < UInt8.size) :
    (ofNatLT n h).toPlainNat = n := by
  simp only [toPlainNat, ofNatLT, UInt8.toNat_ofNatLT]

/-- `Uint8(n)` from a plain `int`: the checked narrowing, the cast every
`ParticipationFlags` construction goes through. Raises past `255`. -/
@[inline] def ofNat? (n : Nat) : Checked CLUint8 :=
  if h : n < UInt8.size then .ok (ofNatLT n h) else .error (ArithFault.range "Uint8()" 8 n 0)

/-- The narrowing succeeds in range, with the proof-carrying value. -/
theorem ofNat?_ok (n : Nat) (h : n < UInt8.size) :
    ofNat? n = .ok (ofNatLT n h) := by simp [ofNat?, h]

/-- The narrowing raises past the maximum, with the operand in the fault. -/
theorem ofNat?_fault (n : Nat) (h : UInt8.size ≤ n) :
    ofNat? n = .error (ArithFault.range "Uint8()" 8 n 0) := by
  simp [ofNat?, Nat.not_lt.mpr h]

/-- `|` on two in-range values: total, the `add_flag` combine
(`SPEC_ARITHMETIC.md` §5.1, same-width bitwise row). -/
@[inline] def bitOr (a b : CLUint8) : CLUint8 := ⟨a.val ||| b.val⟩

/-- `&` on two in-range values: total, the `has_flag` combine. -/
@[inline] def bitAnd (a b : CLUint8) : CLUint8 := ⟨a.val &&& b.val⟩

/-- Set participation-flag bit `idx`: the pyspec's
`flags | ParticipationFlags(2**idx)`. The mask is a checked width-8 value, so
the construction raises past flag index 7, exactly where the pinned
`add_flag` raises (`eth-ssz-specs` 0.1.0, the mask cast). -/
@[inline] def addFlag (flags : CLUint8) (idx : Nat) : Checked CLUint8 := do
  let mask ← ofNat? (2 ^ idx)
  .ok (bitOr flags mask)

/-- Test participation-flag bit `idx`: the pyspec's
`flags & ParticipationFlags(2**idx) == ParticipationFlags(2**idx)`. The mask
raise is the pyspec's, past flag index 7; a comparison never raises, so the
result is a `Checked Bool` only through the mask. -/
@[inline] def hasFlag (flags : CLUint8) (idx : Nat) : Checked Bool := do
  let mask ← ofNat? (2 ^ idx)
  .ok (bitAnd flags mask == mask)

end CLUint8

/-- The `|` of two checked width-8 values, the `add_flag` combine as an
operator. Total: two in-range values cannot leave the range. -/
instance : HOr CLUint8 CLUint8 CLUint8 := ⟨CLUint8.bitOr⟩

/-- The `&` of two checked width-8 values, the `has_flag` combine as an
operator. Total. -/
instance : HAnd CLUint8 CLUint8 CLUint8 := ⟨CLUint8.bitAnd⟩

/-! ## The SSZ wire iso

`SSZRepr` instances for the two wrappers. The shape is the corresponding
`uintN`, so a container field of the checked type packs, serializes, and
merkleizes exactly as the raw `UInt64` / `UInt8` field it replaced
(`SPEC_ARITHMETIC.md` §4.8): the bytes are the little-endian integer, the
root is the leaf hash. The iso is the projection and the wire route
`trustedOfUInt64` / `trustedOfUInt8`, so both laws close by `rfl`. -/

instance : SizzLean.SSZRepr CLUint64 where
  shape := .uintN 64
  toRepr := (·.val)
  fromRepr := (CLUint64.trustedOfUInt64)
  to_from := fun _ => rfl
  from_to := fun _ => rfl

instance : SizzLean.SSZRepr CLUint8 where
  shape := .uintN 8
  toRepr := (·.val)
  fromRepr := (CLUint8.trustedOfUInt8)
  to_from := fun _ => rfl
  from_to := fun _ => rfl

end EthCLLib.Spec
