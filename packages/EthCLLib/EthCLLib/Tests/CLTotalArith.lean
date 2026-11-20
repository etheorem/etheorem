import EthCLLib.Spec.CLTotal

/-!
# `EthCLLib.Tests.CLTotalArith`: the total routes and checked shifts

Executable pins for `Spec/CLTotal.lean` (`SPEC_ARITHMETIC.md` §4.2 and §5.1):
division and modulo by a `PositiveDivisor`, the same-width bitwise operators,
the total right shift with its `count ≥ 64` behavior, the checked mixed right
shift, and the checked power and left shift with their early range decisions.
Every pin runs in the kernel through `decide`; none touches the FFI.
-/

set_option maxRecDepth 10000

set_option autoImplicit false

namespace EthCLLib.Tests.CLTotalArith

open EthCLLib.Spec

/-- The `Uint64` maximum, `2^64 - 1`. A test operand. -/
def maxValue : CLUint64 := CLUint64.trustedOfUInt64 18446744073709551615

/-! ## Division and modulo by a `PositiveDivisor`: total (§4.2)

The wrapper has no literal instance, so each construction shows its proof. The
result is a value, and it feeds a checked sum without a bind. -/

example : ((7 : CLUint64) / (⟨2, by decide⟩ : PositiveDivisor)) = 3 := by decide
example : ((7 : CLUint64) % (⟨2, by decide⟩ : PositiveDivisor)) = 1 := by decide
example : ((7 : CLUint64) / (⟨1, by decide⟩ : PositiveDivisor)) = 7 := by decide
example : (((7 : CLUint64) / (⟨2, by decide⟩ : PositiveDivisor)) + 1 : Checked CLUint64) = .ok 4 := by decide

/-! ## Same-width bitwise operators: total (§5.1) -/

example : ((12 : CLUint64) &&& (10 : CLUint64)) = 8 := by decide
example : ((12 : CLUint64) ||| (10 : CLUint64)) = 14 := by decide
example : ((12 : CLUint64) ^^^ (10 : CLUint64)) = 6 := by decide

/-! ## Total right shift: zero from a count of 64 (§5.1)

The pinned pyspec `shr` is total and does not take the count modulo 64, so
`7 >>> 64 = 0`. -/

example : ((7 : CLUint64) >>> (1 : Nat)) = 3 := by decide
example : ((7 : CLUint64) >>> (64 : Nat)) = 0 := by decide
example : ((7 : CLUint64) >>> (100 : Nat)) = 0 := by decide
example : (maxValue >>> (63 : Nat)) = 1 := by decide

/-! ## Checked mixed right shift: `(2^64) >> Uint64(0)` raises (§5.1)

A plain left operand with a checked count keeps the result range test. The two
routes stay distinct on purpose. -/

example : ((18446744073709551616 : Nat) >>> (0 : CLUint64) : Checked CLUint64) =
    .error (.range ">>" 64 18446744073709551616 0) := by decide
example : ((7 : Nat) >>> (0 : CLUint64) : Checked CLUint64) = .ok 7 := by decide
example : ((5 : Nat) >>> (1 : CLUint64) : Checked CLUint64) = .ok 2 := by decide
-- The signed-count route raises on a negative count (direct call; the
-- operator surface only supplies `CLUint64` counts, which are nonnegative).
example : CLUint64.rshiftChecked 5 (-1) = .error (.range ">>" 64 5 (-1)) := by
  decide
-- A large checked count answers in bounded time: an in-range nonnegative
-- dividend floors to zero.
example : ((7 : Nat) >>> (18446744073709551615 : CLUint64) : Checked CLUint64) =
    .ok 0 := by
  decide
-- An out-of-range dividend keeps the mixed route's range test, also for a
-- large count: `2^64 >> Uint64(2^64 - 1)` shifts to zero and succeeds, while
-- `2^64 >> Uint64(0)` raises.
example : ((18446744073709551616 : Nat) >>> (18446744073709551615 : CLUint64) :
    Checked CLUint64) = .ok 0 := by
  decide

/-! ## Checked power: early decision, zero bases and `0 ^ 0` included (§5.1) -/

example : ((2 : CLUint64) ^ (63 : Nat) : Checked CLUint64) = .ok 9223372036854775808 := by decide
example : ((2 : CLUint64) ^ (64 : Nat) : Checked CLUint64) = .error (.range "**" 64 2 64) := by decide
example : ((0 : CLUint64) ^ (0 : Nat) : Checked CLUint64) = .ok 1 := by decide
example : ((0 : CLUint64) ^ (5 : Nat) : Checked CLUint64) = .ok 0 := by decide
-- The mixed plain-base power: `2 ^ Uint64(64)` raises.
example : ((2 : Nat) ^ (64 : CLUint64) : Checked CLUint64) = .error (.range "**" 64 2 64) := by decide
-- A large exponent answers in bounded time: a base of at least 2 overflows
-- by exponent 64.
example : ((2 : Nat) ^ (18446744073709551615 : CLUint64) : Checked CLUint64) =
    .error (.range "**" 64 2 18446744073709551615) := by
  decide
example : ((2 : Nat) ^ (3 : CLUint64) : Checked CLUint64) = .ok 8 := by decide
-- The signed-base power: an even exponent takes the magnitude, an odd one
-- raises.
example : (((-2 : Int)) ^ (2 : CLUint64) : Checked CLUint64) = .ok 4 := by decide
example : (((-2 : Int)) ^ (3 : CLUint64) : Checked CLUint64) = .error (.range "**" 64 (-2) 3) := by decide

/-! ## Checked left shift: early decision, zero base at a wide count (§5.1) -/

example : ((3 : CLUint64) <<< (2 : Nat) : Checked CLUint64) = .ok 12 := by decide
example : ((maxValue <<< (1 : Nat) : Checked CLUint64)) = .error (.range "<<" 64 18446744073709551615 1) := by
  decide
-- A count of 64 or more leaves the range unless the value is zero.
example : ((5 : CLUint64) <<< (64 : Nat) : Checked CLUint64) = .error (.range "<<" 64 5 64) := by decide
example : ((0 : CLUint64) <<< (64 : Nat) : Checked CLUint64) = .ok 0 := by decide

end EthCLLib.Tests.CLTotalArith
