import EthCLLib.Spec.CLInt

/-!
# `EthCLLib.Tests.CLIntSpike`: the `CLInt` behaviour pins

`CLInt` and its operator instances live in `EthCLLib.Spec.CLInt` since the §5.5
promotion; this module keeps the behaviour tests, the same split `EthCLLib.Tests.CLIndex`
took at 5.1 when `ToIndex` moved beside the class. Each row of §4.2's `CLInt` block pins
here as an `example` the build checks: the total `+` / `-` / `*`, the `/` / `%` flooring
with the raise on a zero divisor (negative divisors included), the `I, U` mixes in both
orders, and the `Nat, I` coercions. The final pin is the withdrawal-sweep shape,
`(x + 1) % len validators`, raising on an empty registry.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLIntSpike

/-- The `Uint64` maximum, `2^64 - 1`. A test operand only. -/
def maxValue : CLUint64 := CLUint64.trustedOfUInt64 0xffffffffffffffff

/-! ## §4.2, row `I, I` with `+ - *`: total, plain result -/

-- Subtraction of two plain values never raises: `7 - 9` is `-2`, as in Python.
example : ((7 : CLInt) - 9) = ⟨-2⟩ := rfl
-- Addition and multiplication stay total the same way.
example : ((7 : CLInt) + 9) = ⟨16⟩ := rfl
example : ((7 : CLInt) * 9) = ⟨63⟩ := rfl

/-! ## §4.2, row `I, I` with `/ %`: `Checked`, Python flooring, raise on a zero divisor -/

-- `//` and `%` floor toward minus infinity, with the divisor's sign handled either way.
example : ((-7 : CLInt) / 2 : Checked CLInt) = .ok ⟨-4⟩ := rfl
example : ((-7 : CLInt) % 2 : Checked CLInt) = .ok ⟨1⟩ := rfl
example : ((7 : CLInt) / -2 : Checked CLInt) = .ok ⟨-4⟩ := rfl
example : ((7 : CLInt) % -2 : Checked CLInt) = .ok ⟨-1⟩ := rfl
-- A zero divisor raises, both operators.
example : ((7 : CLInt) / 0 : Checked CLInt) = .error (.zeroDivisor "//" 7) := rfl
example : ((7 : CLInt) % 0 : Checked CLInt) = .error (.zeroDivisor "%" 7) := rfl

/-! ## §4.2, row `I, U` in either order: `Checked U`, computed in plain `int`, one narrow -/

example : ((3 : CLInt) * (5 : CLUint64)) = .ok (CLUint64.trustedOfUInt64 15) := rfl
example : ((3 : CLInt) - (5 : CLUint64)) = .error (.range "Uint64()" 2 0) := rfl
-- The operand order does not change the raise set: same result, `Uint64` on the left.
example : ((5 : CLUint64) + (3 : CLInt)) = .ok (CLUint64.trustedOfUInt64 8) := rfl
example : ((7 : CLUint64) / (2 : CLInt)) = .ok (CLUint64.trustedOfUInt64 3) := rfl
-- The plain side may push the result past the maximum; the single narrow raises.
example : ((3 : CLInt) * maxValue) = .error (.range "Uint64()" 55340232221128654845 0) := rfl
-- The mix computes in plain `int` and narrows once, so `0 * maxValue` is `0` and the sum fits.
example : ((0 : CLInt) * maxValue + (7 : CLInt)) = .ok (CLUint64.trustedOfUInt64 7) := rfl

/-! ## §4.2, row `Nat, I`: the `Nat` coerces, plain result -/

example : ((3 : Nat) + (4 : CLInt)) = ⟨7⟩ := rfl
example : ((4 : CLInt) + (3 : Nat)) = ⟨7⟩ := rfl
example : ((3 : Nat) * (4 : CLInt)) = ⟨12⟩ := rfl

/-! ## §4.5: `len`, `min`, `max`, and the two long-named conversions -/

example : (CLInt.len #[1, 2, 3] - 5) = ⟨-2⟩ := rfl
example : (min (CLInt.len #[1, 2]) (5 : CLInt)) = ⟨2⟩ := rfl
example : (max (CLInt.len #[1, 2]) (5 : CLInt)) = ⟨5⟩ := rfl
-- `Uint64(-2)` raises, and so does a negative index.
example : ((CLInt.len #[1, 2, 3] - 5).toUint64?) = .error (.range "Uint64()" 2 0) := rfl
example : ((CLInt.len #[1, 2, 3] - 5).toIndex?) = .error (.range "index" 2 0) := rfl

/-! ## The operand shapes a fork body writes -/

-- Total and partial operators mix. One quirk: Lean types a literal-only `10 / 4` as
-- `Nat` division, so the quotient enters the sum unchecked. With the outer
-- `: Checked CLInt` ascription the line does not elaborate; the sum below is a plain
-- `CLInt`, and the value is `8` either way, since `Nat.div 10 4` is also `2`
-- (SPEC_ARITHMETIC.md §4.2's third property).
example : ((2 : CLInt) * 3 + ((10 / 4 : Nat) : CLInt)) = ⟨8⟩ := rfl
-- A partial operator inside a total one: the sum binds the quotient's `Checked`.
example : ((2 : CLInt) * 3 + ((7 : CLInt) / 2 : Checked CLInt)) = .ok ⟨9⟩ := rfl
-- A `Nat` literal divisor has no type of its own, so the partial operators also take a
-- `Nat` operand (the `lit_int` family); Python floors the same way.
example : ((7 : CLInt) / (2 : Nat) : Checked CLInt) = .ok ⟨3⟩ := rfl
example : ((-7 : CLInt) % (2 : Nat) : Checked CLInt) = .ok ⟨1⟩ := rfl

section
variable (a : CLUint64) (n : CLInt) (k : Nat) (xs : Array Nat)

-- `int op Uint` narrows, so the result is a checked `Uint64`.
example : Checked CLUint64 := n * a
example : Checked CLUint64 := n - a
-- A Lean `Nat` operand coerces into `CLInt`.
example : CLInt := k + n
-- Plain arithmetic stays plain: no bind until the expression divides.
example : CLInt := CLInt.len xs - 1
-- Core `Nat` subtraction floors at zero. A fork body writes `len xs - 1` when it means Python.
example : Nat := xs.size - 1

end

/-! ## The withdrawal-sweep shape

`(last + 1) % len validators` (`fulu/beacon-chain.md` sweep cursor,
`update_next_withdrawal_validator_index`): the `+` is total, the `%` raises on a zero
divisor, and an empty registry is exactly that raise. -/

example : (((3 : CLInt) + 1) % CLInt.len (#[] : Array CLUint64) : Checked CLInt)
    = .error (.zeroDivisor "%" 4) := rfl

end EthCLLib.Tests.CLIntSpike
