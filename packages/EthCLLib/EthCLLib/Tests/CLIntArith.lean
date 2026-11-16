import EthCLLib.Spec.CLInt

/-!
# `EthCLLib.Tests.CLIntArith`: the plain-kind operation matrix

This module pins the §4.2 rows for `CLInt` and the mixed `CLInt` / `CLUint64`
routes, and the §5.2 floor-division pins
(`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md`): `7 // -2 = -4`,
`7 % -2 = -1`, `-7 % 2 = 1`. Each pin is a kernel `decide`.

The `decide` route over `rfl` is deliberate. `rfl` unifies through the
elaborator's `whnf`, whose reduction of `Nat.sub` on a `Nat.succ` application
falls back to unary structural recursion; `Int`'s `decLt` builds such terms
(`subNatNat`), so a large `Int` comparison that the kernel settles in
microseconds can stall `rfl`. `decide` evaluates in the kernel, which carries
GMP support for every comparison these pins touch. The same holds for the
`Checked`-result pins: `Checked` carries a `DecidableEq` instance, so the
whole equation decides.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLIntArith

/-! ## `I, I` on `+ - *`: total, unbounded (§4.2) -/

example : ((2 : CLInt) + 3 : CLInt) = 5 := by decide
example : ((7 : CLInt) - 9 : CLInt) = -2 := by decide
example : ((3 : CLInt) * 4 : CLInt) = 12 := by decide
example : ((0 : CLInt) - 9 : CLInt) = -9 := by decide

/-! ## `I, I` on `/ %`: zero divisor raises, floor semantics (§5.2) -/

example : ((7 : CLInt) / 2 : Checked CLInt) = .ok 3 := by decide
example : ((7 : CLInt) % 2 : Checked CLInt) = .ok 1 := by decide
example : ((7 : CLInt) / (-2 : CLInt) : Checked CLInt) = .ok (-4) := by decide
example : ((7 : CLInt) % (-2 : CLInt) : Checked CLInt) = .ok (-1) := by decide
example : (((-7 : CLInt)) / 2 : Checked CLInt) = .ok (-4) := by decide
example : (((-7 : CLInt)) % 2 : Checked CLInt) = .ok 1 := by decide
example : ((1 : CLInt) / 0 : Checked CLInt) = .error (.zeroDivisor "//" 1) := by decide
example : ((1 : CLInt) % 0 : Checked CLInt) = .error (.zeroDivisor "%" 1) := by decide

/-! ## `Nat, I` in either order: the `Nat` coerces (§4.2) -/

example : (((2 : Nat) + (3 : CLInt)) : CLInt) = 5 := by decide
example : (((3 : CLInt) + (2 : Nat)) : CLInt) = 5 := by decide
example : (((2 : Nat) - (5 : CLInt)) : CLInt) = -3 := by decide
example : (((5 : CLInt) - (2 : Nat)) : CLInt) = 3 := by decide
example : (((3 : Nat) * (4 : CLInt)) : CLInt) = 12 := by decide
example : (((3 : CLInt) * (4 : Nat)) : CLInt) = 12 := by decide
example : (((7 : Nat) / (2 : CLInt)) : Checked CLInt) = .ok 3 := by decide
example : (((7 : CLInt) / (2 : Nat)) : Checked CLInt) = .ok 3 := by decide
example : (((1 : Nat) % (0 : CLInt)) : Checked CLInt) = .error (.zeroDivisor "%" 1) := by decide
example : (((1 : CLInt) % (0 : Nat)) : Checked CLInt) = .error (.zeroDivisor "%" 1) := by decide

/-! ## Literal divisors of both signs on `/ %` -/

example : ((7 : CLInt) % 2 : Checked CLInt) = .ok 1 := by decide
example : ((7 : CLInt) % (-2 : Int) : Checked CLInt) = .ok (-1) := by decide

/-! ## A `Checked` operand on either side (§4.2) -/

example : ((pure ((2 : CLInt) + 3 + 4) : Checked CLInt)) = .ok 9 := by decide
example : (((7 : CLInt) / 2) / 2 : Checked CLInt) = .ok 1 := by decide
example : (((1 : CLInt) / 0) + 4 : Checked CLInt) = .error (.zeroDivisor "//" 1) := by decide
example : ((2 : CLInt) + ((1 : CLInt) / 0) : Checked CLInt) = .error (.zeroDivisor "//" 1) := by decide

/-! ## Comparisons are total (§5.2) -/

example : decide (((-2 : CLInt)) < 3) = true := by decide
example : decide ((5 : CLInt) ≤ (-5 : CLInt)) = false := by decide
example : (if (7 : CLInt) < 9 then 1 else 2 : Nat) = 1 := by decide
example : (max (5 : CLInt) (-9 : CLInt)) = 5 := by decide
example : (min (5 : CLInt) (-9 : CLInt)) = -9 := by decide

/-! ## `len` and the plain routes (§4.5) -/

example : (CLInt.len #[1, 2, 3]) = 3 := by decide
example : ((3 : CLInt).toPlainInt) = 3 := by decide
example : (((-4 : CLInt)).toPlainInt) = -4 := by decide

/-! ## `I, U` in either order: compute plain, then one range test (§4.2)

The mixed route computes on the original operands and never narrows the plain
operand first: `Uint64(0) * (2**64)` succeeds with zero.
-/

example : (((3 : CLInt) + (4 : CLUint64)) : Checked CLUint64) = .ok 7 := by decide
example : (((4 : CLUint64) + (3 : CLInt)) : Checked CLUint64) = .ok 7 := by decide
example : (((3 : CLUint64) - (5 : CLInt)) : Checked CLUint64) =
    .error (.range "-" 3 5) := by decide
example : (((2 : Nat) * (3 : CLInt) * (4 : CLUint64)) : Checked CLUint64) = .ok 24 := by decide
example : (((0 : CLUint64) * (18446744073709551616 : Nat) : Checked CLUint64)) = .ok 0 := by
  decide
example : (((0 : CLInt) * (18446744073709551615 : CLUint64)) : Checked CLUint64) = .ok 0 := by
  decide
-- The side the plain operand is on makes no difference (§3.1).
example : (((18446744073709551616 : Nat) * (0 : CLUint64)) : Checked CLUint64) = .ok 0 := by
  decide
-- The range fault records the original operands.
example : (((18446744073709551616 : CLInt) * (1 : CLUint64)) : Checked CLUint64) =
    .error (.range "*" 18446744073709551616 1) := by decide
example : (((7 : CLInt) / (0 : CLUint64)) : Checked CLUint64) =
    .error (.zeroDivisor "//" 7) := by decide
example : (((7 : CLUint64) / (0 : CLInt)) : Checked CLUint64) =
    .error (.zeroDivisor "//" 7) := by decide
-- The `/` and `%` of the mixed routes floor as Python does, so a negative
-- divisor drives the result negative and the range test raises, where a
-- truncating route would succeed with a small value.
example : (((1 : CLUint64) / (-2 : CLInt)) : Checked CLUint64) =
    .error (.range "//" 1 (-2)) := by decide
example : (((7 : CLUint64) % (-2 : CLInt)) : Checked CLUint64) =
    .error (.range "%" 7 (-2)) := by decide
example : (((0 : CLUint64) / (-2 : CLInt)) : Checked CLUint64) = .ok 0 := by decide
example : (((0 : CLUint64) % (-2 : CLInt)) : Checked CLUint64) = .ok 0 := by decide

/-! ## The cross-kind conversions (§4.5) -/

example : ((7 : CLUint64).toCLInt) = 7 := by decide
example : ((7 : CLUint8).toCLInt) = 7 := by decide
example : ((7 : CLInt).toCLUint64?) = .ok 7 := by decide
example : ((18446744073709551616 : CLInt).toCLUint64?) =
    .error (.range "Uint64()" 18446744073709551616 0) := by decide
example : (((-1 : CLInt)).toCLUint64?) = .error (.range "Uint64()" (-1) 0) := by decide
example : (CLUint64.ofCLInt? (7 : CLInt)) = .ok 7 := by decide

end EthCLLib.Tests.CLIntArith
