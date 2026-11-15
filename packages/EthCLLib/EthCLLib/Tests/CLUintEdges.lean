import EthCLLib.Spec.Arith
import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Tests.CLUintEdges`: edge behaviour of `CLUint64` and `CLUint8`

The pyspec's checked integers compute in unbounded Python `int` and raise outside
`[0, 2**BITS - 1]`; division and modulo raise on a zero divisor alone, since their result
cannot leave the range (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3.2). This module pins
each row of the operator table (§4.2) for `U = CLUint64`: the exact result value in range,
the exact `ArithFault` payload at each raise, the `Nat` operand on either side, a `Checked`
operand on either side, and the per-operation test in `a * b / c`. It also pins the last
three §5.1 rows, `a ** n`, `a << n`, and `a >> n`, and the `Uint8` rows behind the pinned
`ParticipationFlags`: the `Uint8()` cast, the total `|` / `&`, and the
`add_flag` / `has_flag` mask raise past flag index 7. Every raise quoted in a section
comment was run against the built pyspec in `.spike/pyspec-venv` (`eth-ssz-specs` 0.1.0).

Two elaboration facts shape the assertions. A bare integer literal defaults to `Nat`, so the
`U, U` rows ascribe both operands and the `Nat` rows pin the literal route. The `Eq` of an
assertion fixes its type from the `.ok` / `.error` side, so each left-hand side carries a
`: Checked CLUint64` ascription, as `CLIntSpike.lean` does.

The constructor `CLUint64.mk` is private to `Spec/CLUint.lean` (§7, item 6), so the tests build
operands through the named constructor `CLUint64.trustedOfUInt64` or the `OfNat` literals.
A literal past `2^64 - 1` fails to compile (§7, item 6); the `#guard_msgs` block at the end
pins the message, and the assertions around it pin that the maximum literal still builds and
that out-of-range `Nat` and `UInt64` literals keep core's wrapping path.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLUintEdges

/-- The `Uint64` maximum, `2^64 - 1`. A test operand only. -/
def maxValue : CLUint64 := CLUint64.trustedOfUInt64 0xffffffffffffffff

/-- `2^63`, the smallest value whose double leaves the range. -/
def halfMax : CLUint64 := CLUint64.trustedOfUInt64 0x8000000000000000

/-! ## `U, U` on `+`, `-`, `*`: in range, and the raise at each edge (§4.2 row 1) -/

-- In range, the operator returns the exact value.
example : ((2 : CLUint64) + (3 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 5) := rfl
example : ((5 : CLUint64) - (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 3) := rfl
example : ((3 : CLUint64) * (4 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 12) := rfl
-- `maxValue + 1` raises: the wrap would be `0`.
example : (maxValue + (1 : CLUint64) : Checked CLUint64) = .error (.range "+" 18446744073709551615 1) := rfl
-- The pyspec tests `1 + Uint64(MAX)` too, and the raise records both operands in order.
example : ((1 : CLUint64) + maxValue : Checked CLUint64) = .error (.range "+" 1 18446744073709551615) := rfl
-- `0 - 1` raises: the wrap would be `2^64 - 1`.
example : ((0 : CLUint64) - (1 : CLUint64) : Checked CLUint64) = .error (.range "-" 0 1) := rfl
-- `2^63 * 2` raises: the product would wrap to `0`.
example : (halfMax * (2 : CLUint64) : Checked CLUint64) = .error (.range "*" 9223372036854775808 2) := rfl

/-! ## `U, U` on `/`, `%`: in range, and the zero-divisor raise (§4.2 row 2) -/

-- Division and modulo cannot leave the range (§3.2), so the only raise is a zero divisor.
example : ((7 : CLUint64) / (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 3) := rfl
example : ((7 : CLUint64) % (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 1) := rfl
example : ((1 : CLUint64) / (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "//" 1) := rfl
example : ((1 : CLUint64) % (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "%" 1) := rfl

/-! ## `Nat`, `U` in either order on `+ - * / %` (§4.2 row 6)

A `Nat` operand is the pyspec's plain `int` in the role of a literal or a loop variable.
`+` and `*` compute unbounded and narrow once, so their range raise is a `Uint64()` fault.
`-` tests below zero first and raises the `-` fault. For the rows pinned here, the only other
raise is the zero divisor. A bare literal is a `Nat`
operand: `maxValue + 1` picks the `Nat` route, as the last two assertions of the `+` group pin.
-/

-- `Nat + U` and `U + Nat`, in range and at the edge.
example : ((2 : Nat) + (3 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 5) := rfl
example : ((3 : CLUint64) + (2 : Nat) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 5) := rfl
example : ((1 : Nat) + maxValue : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : (maxValue + (1 : Nat) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
-- A bare literal is a plain `int`: the `Nat` route, with the unbounded sum in the fault.
example : (maxValue + 1 : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : (1 + maxValue : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
-- `Nat - U` and `U - Nat`, in range and below zero.
example : ((5 : Nat) - (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 3) := rfl
example : ((5 : CLUint64) - (2 : Nat) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 3) := rfl
example : ((2 : Nat) - (5 : CLUint64) : Checked CLUint64) = .error (.range "-" 2 5) := rfl
example : ((2 : CLUint64) - (5 : Nat) : Checked CLUint64) = .error (.range "-" 2 5) := rfl
-- `Nat * U` and `U * Nat`, in range and past the maximum.
example : ((3 : Nat) * (4 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 12) := rfl
example : ((3 : CLUint64) * (4 : Nat) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 12) := rfl
example : ((2 : Nat) * halfMax : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : (halfMax * (2 : Nat) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
-- `Nat / U` and `U / Nat`, in range and by zero.
example : ((7 : Nat) / (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 3) := rfl
example : ((7 : CLUint64) / (2 : Nat) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 3) := rfl
example : ((1 : Nat) / (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "//" 1) := rfl
example : ((1 : CLUint64) / (0 : Nat) : Checked CLUint64) = .error (.zeroDivisor "//" 1) := rfl
-- `Nat % U` and `U % Nat`, in range and by zero.
example : ((7 : Nat) % (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 1) := rfl
example : ((7 : CLUint64) % (2 : Nat) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 1) := rfl
example : ((1 : Nat) % (0 : CLUint64) : Checked CLUint64) = .error (.zeroDivisor "%" 1) := rfl
example : ((1 : CLUint64) % (0 : Nat) : Checked CLUint64) = .error (.zeroDivisor "%" 1) := rfl

/-! ## A `Checked` operand on either side: the operand's fault passes first (§4.2 row 9)

For `+` and `/`, one assertion with a `.ok` operand on the left that computes on, and one with
a fault that stays. A fault on the left wins: the right operand never computes.
-/

-- A `.ok` operand on the left computes on.
example : (((2 : CLUint64) + (3 : CLUint64)) + (4 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 9) := rfl
example : (((7 : CLUint64) / (2 : CLUint64)) / (2 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 1) := rfl
-- A fault on the left stays, and the other operand never computes.
example : ((maxValue + (1 : CLUint64)) + (4 : CLUint64) : Checked CLUint64) = .error (.range "+" 18446744073709551615 1) := rfl
example : ((maxValue + (1 : CLUint64)) / (2 : CLUint64) : Checked CLUint64) = .error (.range "+" 18446744073709551615 1) := rfl
-- A fault on the right passes through the left value.
example : ((2 : CLUint64) + (maxValue + (1 : CLUint64)) : Checked CLUint64) = .error (.range "+" 18446744073709551615 1) := rfl
-- A `Checked` right operand for `/` still raises on its own zero divisor.
example : ((7 : CLUint64) / (Except.ok (0 : CLUint64) : Checked CLUint64) : Checked CLUint64) = .error (.zeroDivisor "//" 7) := rfl
-- Both operands fault: the left fault passes first.
example : ((maxValue + (1 : CLUint64)) + ((0 : CLUint64) - (1 : CLUint64)) : Checked CLUint64) =
    .error (.range "+" 18446744073709551615 1) := rfl

/-! ## Each step is tested (§3.2) -/

-- The product raises although the quotient `2^62` would fit.
example : ((halfMax * (2 : CLUint64)) / (2 : CLUint64) : Checked CLUint64) = .error (.range "*" 9223372036854775808 2) := rfl

/-! ## `a ** n` raises past the maximum (§5.1 row 5)

The wheel computes `pow(int(self), int(value))` unbounded and range-tests the result
(`ssz/uint.py`, `BaseUint.__pow__` ends in `cls._wrap`). Run at the pin:
`Uint64(2) ** 64` raises `SSZValueError`, `Uint64(2) ** 63` is `Uint64(9223372036854775808)`,
`Uint64(0) ** 0` is `Uint64(1)`, and `2 ** Uint64(64)` (the `__rpow__` route) raises too. The
wheel also takes three-argument `pow`, which the in-scope text never uses, and it raises on a
negative exponent, which a `Nat` exponent cannot be. -/

-- In range, the exact value.
example : ((2 : CLUint64) ^ (63 : CLUint64) : Checked CLUint64) = .ok halfMax := rfl
example : ((2 : Nat) ^ (63 : CLUint64) : Checked CLUint64) = .ok halfMax := rfl
example : (halfMax ^ (1 : Nat) : Checked CLUint64) = .ok halfMax := rfl
-- `2^64` raises, in both operand orders.
example : ((2 : CLUint64) ^ (64 : CLUint64) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : ((2 : Nat) ^ (64 : CLUint64) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
-- The unbounded power names itself in the fault.
example : (maxValue ^ (2 : Nat) : Checked CLUint64) =
    .error (.range "Uint64()" 340282366920938463426481119284349108225 0) := rfl
-- `0 ** 0` is `1`, as in Python.
example : ((0 : CLUint64) ^ (0 : CLUint64) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 1) := rfl
-- A fault on the left passes first.
example : (((0 : CLUint64) - (1 : CLUint64)) ^ (2 : CLUint64) : Checked CLUint64) = .error (.range "-" 0 1) := rfl

/-! ## `a << n` raises past the maximum (§5.1 row 6)

The wheel computes `int.__lshift__` unbounded and range-tests the result
(`BaseUint.__lshift__` ends in `cls._wrap`). Run at the pin: `Uint64(1) << 64` raises,
`Uint64(1) << 63` is `Uint64(9223372036854775808)`, `1 << Uint64(64)` (the `__rlshift__`
route) raises too. Lean's native `UInt64` `<<<` cannot raise, so the model computes on the
plain values and narrows once. -/

-- In range, the exact value.
example : ((1 : CLUint64) <<< (63 : CLUint64) : Checked CLUint64) = .ok halfMax := rfl
example : ((1 : Nat) <<< (63 : CLUint64) : Checked CLUint64) = .ok halfMax := rfl
example : ((7 : CLUint64) <<< (0 : Nat) : Checked CLUint64) = .ok (CLUint64.trustedOfUInt64 7) := rfl
-- `1 << 64` raises, in both operand orders.
example : ((1 : CLUint64) <<< (64 : CLUint64) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : ((1 : Nat) <<< (64 : CLUint64) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : (halfMax <<< (1 : Nat) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl

/-! ## `a >> n` is total (§5.1 row 7)

The wheel computes `int.__rshift__` and range-tests the result like every operator, but for
`n ≥ 0` the result is at most `a`, and `a` is in range, so the test cannot fire. The count is
not taken modulo 64. Run at the pin: `Uint64(7) >> 64` is `Uint64(0)`, and so is
`Uint64(7) >> 1000`. The result is the value itself, no bind. -/

example : ((7 : CLUint64) >>> (1 : CLUint64)) = CLUint64.trustedOfUInt64 3 := rfl
example : ((7 : CLUint64) >>> (64 : CLUint64)) = (CLUint64.trustedOfUInt64 0) := rfl
example : ((7 : CLUint64) >>> 1000) = (CLUint64.trustedOfUInt64 0) := rfl
example : ((7 : CLUint64) >>> (1 : Nat)) = CLUint64.trustedOfUInt64 3 := rfl
-- The `Nat`-left route is the one `>>` route that can fault: the wheel's `__rrshift__`
-- range-tests the result, and the base is a plain `int`. Run at the pin:
-- `(2**63) >> Uint64(0)` is `Uint64(2**63)`, `(2**64) >> Uint64(0)` raises,
-- `(2**64) >> Uint64(1)` is `Uint64(2**63)`.
example : ((2 ^ 63 : Nat) >>> (0 : CLUint64) : Checked CLUint64) = .ok halfMax := rfl
example : ((2 ^ 64 : Nat) >>> (0 : CLUint64) : Checked CLUint64) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
example : ((2 ^ 64 : Nat) >>> (1 : CLUint64) : Checked CLUint64) = .ok halfMax := rfl

/-! ## The `Uint8` rows: `ParticipationFlags` at the pin

At the pin, `ParticipationFlags` is a `Uint8` subclass (`eth-ssz-specs` 0.1.0,
`altair/mainnet.py`: `class ParticipationFlags(Uint8)`), and `add_flag` / `has_flag` form the
mask `ParticipationFlags(2**flag_index)` before combining, a range test against `[0, 255]`.
Run at the pin: `ParticipationFlags(2**7)` is `Uint8(128)`; `add_flag` and `has_flag` at
flag index 8 raise `SSZValueError: 256 is out of range for ParticipationFlags [0, 255]`;
the mask power for a `Uint64` index of 64 raises at the `Uint64` wrap first, so the raise a
caller sees starts at flag index 8 either way. `|` and `&` on two in-range values never
leave the range (`Uint8(0b101) | Uint8(0b010)` is `Uint8(7)`). -/

-- The `Uint8()` cast: in range, and one past the maximum.
example : (CLUint8.ofNat? 255) = .ok (CLUint8.trustedOfUInt8 255) := rfl
example : (CLUint8.ofNat? 256) = .error (.range "Uint8()" 256 0) := rfl
-- `|` and `&` are total on two in-range values.
example : ((5 : CLUint8) ||| (2 : CLUint8)) = (7 : CLUint8) := rfl
example : ((5 : CLUint8) &&& (1 : CLUint8)) = (1 : CLUint8) := rfl

-- The literal gate covers `CLUint8`: the maximum builds, one past it fails.
example : (255 : CLUint8) = CLUint8.trustedOfUInt8 255 := rfl
example : (255 : CLUint8).toPlainInt = 255 := rfl

/-- error: literal `256` is out of range for `CLUint8`: the type holds `[0, 2^8 - 1]`, and the maximum is `255` -/
#guard_msgs in
example : CLUint8 := 256

/-! ## `add_flag` / `has_flag` raise exactly past flag index 7

The mask `2**flag_index` is the only raise site: `add_flag(flags, 7)` builds
`ParticipationFlags(133)` from `0b101`, and `add_flag(flags, 8)` raises. -/

-- The mask at the edge: flag index 7 fits, flag index 8 raises.
example : (EthCLLib.Spec.participationFlagMask 7) = .ok (CLUint8.trustedOfUInt8 128) := rfl
example : (EthCLLib.Spec.participationFlagMask 8) = .error (.range "Uint8()" 256 0) := rfl
-- `add_flag`: the combine is total; the mask carries the raise.
example : (EthCLLib.Spec.addFlag (5 : CLUint8) 7 : Checked CLUint8) = .ok (CLUint8.trustedOfUInt8 133) := rfl
example : (EthCLLib.Spec.addFlag (5 : CLUint8) 8 : Checked CLUint8) = .error (.range "Uint8()" 256 0) := rfl
-- `has_flag`: `flags & flag == flag`.
example : (EthCLLib.Spec.hasFlag (5 : CLUint8) 0 : Checked Bool) = .ok true := rfl
example : (EthCLLib.Spec.hasFlag (5 : CLUint8) 1 : Checked Bool) = .ok false := rfl
example : (EthCLLib.Spec.hasFlag (5 : CLUint8) 8 : Checked Bool) = .error (.range "Uint8()" 256 0) := rfl

/-! ## Conversions and the saturating subtraction (§4.5) -/

-- `Uint64(n)` from a plain `int`: in range, and past the maximum.
example : (CLUint64.ofNat? 5) = .ok (CLUint64.trustedOfUInt64 5) := rfl
example : (CLUint64.ofNat? 18446744073709551616) = .error (.range "Uint64()" 18446744073709551616 0) := rfl
-- `saturating_sub` floors at zero and never raises.
example : (maxValue.saturatingSub 1) = CLUint64.trustedOfUInt64 0xfffffffffffffffe := rfl
example : ((1 : CLUint64).saturatingSub 5) = (CLUint64.trustedOfUInt64 0) := rfl
-- `int(x)`: the plain value.
example : maxValue.toPlainInt = 18446744073709551615 := rfl

/-! ## The constructor is private (§4.5)

`CLUint64.mk` is private to `Spec/CLUint.lean`, so this importing module can neither apply the
anonymous constructor nor name `mk`. The two `#guard_msgs` blocks pin the exact failures, so a
revert of the privacy fails this build.
-/

/-- error: Invalid `⟨...⟩` notation: Constructor for `EthCLLib.Spec.CLUint64` is marked as private -/
#guard_msgs in
example : CLUint64 := ⟨5⟩

/-- error: Unknown constant `EthCLLib.Spec.CLUint64.mk` -/
#guard_msgs in
example : CLUint64 := CLUint64.mk 5

/-! ## Literals are range-checked (§7, item 6)

Core's `num` elaborator builds a literal through the `OfNat` instance, and `UInt64.ofNat`
wraps modulo `2^64`. The scoped `num` elaborator in `Spec/CLUint.lean` runs first wherever
`EthCLLib.Spec` is open, so an out-of-range literal raises with the value and the bound named,
and the assertions pin the boundary: the maximum literal builds and holds the exact value, the
literal one past it fails, and out-of-range literals of other types keep core's wrapping path.
-/

-- The maximum literal builds, and the value is the maximum.
example : CLUint64 := 18446744073709551615
example : (18446744073709551615 : CLUint64) = CLUint64.trustedOfUInt64 0xffffffffffffffff := rfl
example : (18446744073709551615 : CLUint64).toPlainInt = 18446744073709551615 := rfl
-- In-range `farFutureEpoch`-style constants build on the same route.
example : (18446744073709551614 : CLUint64) = CLUint64.trustedOfUInt64 0xfffffffffffffffe := rfl

-- One past the maximum fails to compile: the wrap would be `0`.
/-- error: literal `18446744073709551616` is out of range for `CLUint64`: the type holds `[0, 2^64 - 1]`, and the maximum is `18446744073709551615` -/
#guard_msgs in
example : CLUint64 := 18446744073709551616

/-! The same gate through a reducible alias: the fork body writes balance literals at
`forkabbrev Gwei := CLUint64`, a `@[reducible]` abbrev, and the gate reads the expected type
through it (`whnfR` in `elabCheckedNumLit`). A local abbrev pins the shape here, since the
tests cannot import `EthCLSpecs`.
-/

/-- A stand-in for the fork body's `Gwei`. -/
abbrev CLUnit := CLUint64

example : CLUnit := 18446744073709551615

/-- error: literal `18446744073709551616` is out of range for `CLUint64`: the type holds `[0, 2^64 - 1]`, and the maximum is `18446744073709551615` -/
#guard_msgs in
example : CLUnit := 18446744073709551616

-- The failure is scoped to `CLUint64`: out-of-range literals of other types keep core's path.
example : (18446744073709551616 : Nat) = 18446744073709551616 := rfl
example : (18446744073709551616 : UInt64).toNat = 0 := rfl
-- A `UInt64` literal past `2^64 - 1` keeps core's wrapping `UInt64.ofNat`.
example : ((18446744073709551616 : UInt64) + 1) = (1 : UInt64) := rfl

end EthCLLib.Tests.CLUintEdges
