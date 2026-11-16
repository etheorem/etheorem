import EthCLLib.Spec.CLInt

/-!
# `EthCLLib.Tests.CLUintArith`: the checked-width operation matrix

This module pins the §4.2 operator table and the §5.1 edge behavior for
`CLUint64` and `CLUint8` (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md`). Each
assertion is a kernel `decide`, so the kernel checks the exact result value or
the exact `ArithFault` payload. The constructor is private, so operands come
from literals or from the wire route `trustedOfUInt64`.

The `decide` route over `rfl` follows the rationale recorded in
`CLIntArith.lean`: `rfl` unifies through the elaborator's `whnf`, whose
`Nat.sub` reduction on `Nat.succ` applications falls back to unary structural
recursion, and the wide pins here build exactly such terms. `decide`
evaluates in the kernel, which carries GMP support for every comparison these
pins touch.

A bare integer literal next to a `CLUint64` operand stays a `Nat` where the
pin says so; those lines ascribe the literal explicitly. The `Nat` literals
that name edge values (`18446744073709551616`, `2^63`) are out of the gate's
range on purpose: a `CLUint64` literal there would not compile.
-/

set_option autoImplicit false
-- The kernel-checked `rfl` pins reduce the native-width tests through the
-- `UInt64` wrapper stack; the default elaborator recursion limit is too small
-- for the larger operands here.
set_option maxRecDepth 8192

open EthCLLib.Spec

namespace EthCLLib.Tests.CLUintArith

/-- The `Uint64` maximum, `2^64 - 1`. A test operand. -/
def maxValue : CLUint64 := CLUint64.trustedOfUInt64 18446744073709551615

/-- `2^63`, the smallest value whose double leaves the range. -/
def halfMax : CLUint64 := CLUint64.trustedOfUInt64 9223372036854775808

/-! ## `U, U` on `+ - *`: in range, and the raise at each edge (§5.1) -/

example : ((2 : CLUint64) + 3 : Checked CLUint64) = .ok 5 := by decide
example : ((5 : CLUint64) - 2 : Checked CLUint64) = .ok 3 := by decide
example : ((3 : CLUint64) * 4 : Checked CLUint64) = .ok 12 := by decide
-- `max + 1` raises; the raise records both operands in order.
example : (maxValue + 1 : Checked CLUint64) = .error (.range "+" 18446744073709551615 1) := by decide
-- `1 + max` raises too; the pyspec tests it from the right as well.
example : ((1 : CLUint64) + maxValue : Checked CLUint64) =
    .error (.range "+" 1 18446744073709551615) := by decide
-- `0 - 1` raises.
example : ((0 : CLUint64) - 1 : Checked CLUint64) = .error (.range "-" 0 1) := by decide
-- `2^63 * 2` raises.
example : (halfMax * 2 : Checked CLUint64) =
    .error (.range "*" 9223372036854775808 2) := by decide

/-! ## `U, U` on `/ %`: the zero divisor is the only raise (§3.2) -/

example : ((7 : CLUint64) / 2 : Checked CLUint64) = .ok 3 := by decide
example : ((7 : CLUint64) % 2 : Checked CLUint64) = .ok 1 := by decide
example : ((1 : CLUint64) / 0 : Checked CLUint64) = .error (.zeroDivisor "//" 1) := by decide
example : ((1 : CLUint64) % 0 : Checked CLUint64) = .error (.zeroDivisor "%" 1) := by decide

/-! ## A `Nat` operand on each side (§4.2 row `Nat, U`)

The route computes unbounded in `Int`, then runs the one range test, so the
fault names the operator with both original operands. `-` of a larger plain
value raises on the range test alone; nothing narrows first.
-/

example : (((2 : Nat) + (3 : CLUint64)) : Checked CLUint64) = .ok 5 := by decide
example : ((maxValue + (1 : Nat)) : Checked CLUint64) =
    .error (.range "+" 18446744073709551615 1) := by decide
example : (((3 : CLUint64) + (2 : Nat)) : Checked CLUint64) = .ok 5 := by decide
example : ((maxValue + 18446744073709551616 : Checked CLUint64)) =
    .error (.range "+" 18446744073709551615 18446744073709551616) := by decide

example : (((5 : Nat) - (2 : CLUint64)) : Checked CLUint64) = .ok 3 := by decide
example : (((2 : Nat) - (5 : CLUint64)) : Checked CLUint64) = .error (.range "-" 2 5) := by decide
example : (((5 : CLUint64) - (2 : Nat)) : Checked CLUint64) = .ok 3 := by decide
example : (((2 : CLUint64) - (5 : Nat)) : Checked CLUint64) = .error (.range "-" 2 5) := by decide

example : (((3 : Nat) * (4 : CLUint64)) : Checked CLUint64) = .ok 12 := by decide
example : (((3 : CLUint64) * (4 : Nat)) : Checked CLUint64) = .ok 12 := by decide
example : ((halfMax * (2 : Nat)) : Checked CLUint64) =
    .error (.range "*" 9223372036854775808 2) := by decide

example : (((7 : Nat) / (2 : CLUint64)) : Checked CLUint64) = .ok 3 := by decide
example : (((7 : CLUint64) / (2 : Nat)) : Checked CLUint64) = .ok 3 := by decide
example : (((1 : Nat) / (0 : CLUint64)) : Checked CLUint64) = .error (.zeroDivisor "//" 1) := by decide
example : (((1 : CLUint64) / (0 : Nat)) : Checked CLUint64) = .error (.zeroDivisor "//" 1) := by decide

example : (((7 : Nat) % (2 : CLUint64)) : Checked CLUint64) = .ok 1 := by decide
example : (((7 : CLUint64) % (2 : Nat)) : Checked CLUint64) = .ok 1 := by decide
example : (((1 : Nat) % (0 : CLUint64)) : Checked CLUint64) = .error (.zeroDivisor "%" 1) := by decide
example : (((1 : CLUint64) % (0 : Nat)) : Checked CLUint64) = .error (.zeroDivisor "%" 1) := by decide

/-! ## The no-narrow rule (§4.2)

The mixed route computes on the original operands, then checks the result. The
pyspec's `Uint64(0) * (2**64)` succeeds with zero; narrowing `2**64` first
would be the cast raise.
-/

example : (((0 : CLUint64) * (18446744073709551616 : Nat) : Checked CLUint64)) = .ok 0 := by decide
example : ((halfMax * (2 : Nat) : Checked CLUint64)) =
    .error (.range "*" 9223372036854775808 2) := by decide

/-! ## A `Checked` operand on each side (§4.2 row `Checked` operand)

The operand's fault passes first: the right operand never computes, which is
the pyspec's left-to-right raise order.
-/

-- A `.ok` operand on the left computes on.
example : (((2 : CLUint64) + 3) + 4 : Checked CLUint64) = .ok 9 := by decide
example : (((7 : CLUint64) / 2) / 2 : Checked CLUint64) = .ok 1 := by decide
-- A fault on the left stays.
example : ((maxValue + 1) + 4 : Checked CLUint64) =
    .error (.range "+" 18446744073709551615 1) := by decide
example : ((maxValue + 1) / 2 : Checked CLUint64) =
    .error (.range "+" 18446744073709551615 1) := by decide
-- A fault on the right passes through the left value.
example : ((2 : CLUint64) + (maxValue + 1) : Checked CLUint64) =
    .error (.range "+" 18446744073709551615 1) := by decide
-- Both operands fault: the left fault passes first.
example : ((maxValue + 1) + (0 - (1 : CLUint64)) : Checked CLUint64) =
    .error (.range "+" 18446744073709551615 1) := by decide
-- A `Checked` right operand keeps its own zero divisor.
example : ((7 : CLUint64) / (Except.ok (0 : CLUint64) : Checked CLUint64) : Checked CLUint64) =
    .error (.zeroDivisor "//" 7) := by decide

/-! ## Comparisons are total and return a `Bool` (§5.1) -/

example : decide ((5 : CLUint64) < (6 : CLUint64)) = true := by decide
example : decide (maxValue < (5 : CLUint64)) = false := by decide
example : decide ((5 : CLUint64) ≤ maxValue) = true := by decide
example : (if (5 : CLUint64) ≤ 5 then 1 else 2 : Nat) = 1 := by decide
example : (max (5 : CLUint64) 9) = 9 := by decide
example : (min (5 : CLUint64) 9) = 5 := by decide

/-! ## `saturating_sub` (§3.5) -/

example : ((5 : CLUint64).saturatingSub 2) = 3 := by decide
example : ((2 : CLUint64).saturatingSub 5) = 0 := by decide

/-! ## Conversions (§4.5, settled names) -/

example : ((7 : CLUint64).toPlainNat) = 7 := by decide
example : ((7 : CLUint64).toCLInt) = 7 := by decide
example : (CLUint64.ofNat? 7) = .ok 7 := by decide
example : (CLUint64.ofNat? 18446744073709551616) =
    .error (.range "Uint64()" 18446744073709551616 0) := by decide
example : (CLUint64.ofInt? (-1)) = .error (.range "Uint64()" (-1) 0) := by decide
example : (CLUint64.ofCLInt? (7 : CLInt)) = .ok 7 := by decide
example : ((7 : CLInt).toCLUint64?) = .ok 7 := by decide
example : ((18446744073709551616 : CLInt).toCLUint64?) =
    .error (.range "Uint64()" 18446744073709551616 0) := by decide
example : ((7 : CLUint64).toCLInt.toCLUint64?) = .ok 7 := by decide
example : (CLUint64.ofNatLT 7 (by decide)) = 7 := by decide

/-! ## The wire iso: same bytes and root as the raw `UInt64` (§4.8)

`native_decide` here: the byte and root computations run through the
byte-array codec, whose kernel reduction is heavier than the arithmetic pins
above. The proposition is still an equality of computed values.
-/

example : SizzLean.SSZ.serialize (5 : CLUint64) = SizzLean.SSZ.serialize (5 : UInt64) := by
  native_decide
example : SizzLean.SSZ.serialize (200 : CLUint8) = SizzLean.SSZ.serialize (200 : UInt8) := by
  native_decide
example : SizzLean.SSZ.hashTreeRoot (H := SizzLean.Hasher.Sha256) (5 : CLUint64)
    = SizzLean.SSZ.hashTreeRoot (H := SizzLean.Hasher.Sha256) (5 : UInt64) := by
  native_decide

/-! ## The `Uint8` rows behind `ParticipationFlags`

`add_flag` and `has_flag` form the mask `ParticipationFlags(2**flag_index)`,
which range-tests the mask and raises past flag index 7. The `|` / `&` of two
in-range values are total (§5.1).
-/

example : (CLUint8.addFlag 0 3) = .ok 8 := by decide
example : (CLUint8.addFlag 255 0) = .ok 255 := by decide
example : (CLUint8.addFlag 0 8) =
    .error (.range "Uint8()" 256 0) := by decide
example : (CLUint8.hasFlag 8 3) = .ok true := by decide
example : (CLUint8.hasFlag 8 4) = .ok false := by decide
example : (CLUint8.hasFlag 0 8) = .error (.range "Uint8()" 256 0) := by decide
example : ((8 : CLUint8) ||| (1 : CLUint8)) = 9 := by decide
example : ((9 : CLUint8) &&& (1 : CLUint8)) = 1 := by decide
example : ((200 : CLUint8).toPlainNat) = 200 := by decide
example : (CLUint8.ofNat? 256) = .error (.range "Uint8()" 256 0) := by decide

end EthCLLib.Tests.CLUintArith
