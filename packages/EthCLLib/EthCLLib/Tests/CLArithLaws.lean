import EthCLLib.Proofs.CLInt

/-!
# `EthCLLib.Tests.CLArithLaws`: the law library at work

Executable pins for the fused laws of `Proofs/CLUint.lean` and
`Proofs/CLInt.lean` (`SPEC_ARITHMETIC.md` §4.9): the `simp_arith` chain
reduction, the checked fold, the conversion round-trips, the `Checked` lift
laws, and the reward-shaped division formula Stage 4 reuses. Concrete pins run
in the kernel through `decide`; the law-shaped pins cite the theorems. A few
facts restate a pin from `Tests/CLUintArith.lean` or `Tests/CLIntArith.lean`
on purpose: each law carries its own executable witness beside its theorem.
-/

set_option maxRecDepth 10000

set_option autoImplicit false

namespace EthCLLib.Tests.CLArithLaws

open EthCLLib.Proofs
open EthCLLib.Spec

/-- The `Uint64` maximum, `2^64 - 1`. A test operand. -/
def maxValue : CLUint64 := CLUint64.trustedOfUInt64 18446744073709551615

/-! ## The `simp_arith` chain reduction (§4.9)

One call exposes both `Nat` facts of a checked chain. The general pin repeats
the chain pin of `Proofs/CLUint.lean`; the concrete pins show the same chain
evaluating to its value and to its fault. -/

example (a b c r : CLUint64) :
    ((a * b / c : Checked CLUint64)) = .ok r ↔
      ∃ m : CLUint64, (a.toPlainNat * b.toPlainNat < UInt64.size ∧
        m.toPlainNat = a.toPlainNat * b.toPlainNat) ∧
        c.toPlainNat ≠ 0 ∧
        r.toPlainNat = m.toPlainNat / c.toPlainNat := by
  simp_arith

example : (((2 : CLUint64) * 3 / 4 : Checked CLUint64)) = .ok 1 := by decide
-- The product faults before the division computes, so the fault names `*`.
example : ((maxValue * 2 / 4 : Checked CLUint64)) =
    .error (.range "*" 64 18446744073709551615 2) := by decide
-- A zero divisor faults the division, not the product.
example : (((6 : CLUint64) * 3 / 0 : Checked CLUint64)) = .error (.zeroDivisor "//" 64 18) := by decide

/-! ## The checked fold (§4.5)

`sum(xs)` succeeds exactly when every running sum stays in range, and the
result is the final running sum. -/

example : ([1, 2, 3].foldlM (fun acc x => acc + x) (0 : CLUint64)) = .ok 6 := by
  decide
-- A running sum crosses the maximum: the fold raises at the second addition.
example : ([maxValue, 1].foldlM (fun acc x => acc + x) (0 : CLUint64)) =
    .error (.range "+" 64 18446744073709551615 1) := by
  decide
-- The law behind the two pins: success iff every running sum stays in range.
example : (∃ c, [maxValue, 1].foldlM (fun acc x => acc + x) (0 : CLUint64) = .ok c) ↔
    ∀ i ≤ [maxValue, 1].length,
      Proofs.runSum (0 : CLUint64) [maxValue, 1] i < UInt64.size :=
  Proofs.foldlM_add_ok_iff _ _

/-! ## The conversion round-trips (§4.5) -/

example : CLUint64.ofNat? 5 = .ok 5 := by decide
example : CLUint64.ofNat? 18446744073709551616 =
    .error (.range "Uint64()" 64 18446744073709551616 0) := by
  decide
example : (CLUint64.ofNat? (7 : CLUint64).toPlainNat) = .ok 7 :=
  Proofs.ofNat_roundtrip 7
example : ((5 : CLInt).toCLUint64? : Checked CLUint64) = .ok 5 := by decide
example : ((-1 : CLInt).toCLUint64? : Checked CLUint64) = .error (.range "Uint64()" 64 (-1) 0) := by
  decide
example : ((-7 : CLInt) / 2 : Checked CLInt) = .ok (-4) := by decide
example : ((-7 : CLInt) % 2 : Checked CLInt) = .ok 1 := by decide

/-! ## The `Checked` lift laws (§4.4)

A fault on the left passes first; the right operand never computes. -/

example (x : Checked CLUint64) : (x >>= pure) = x := by
  cases x with
  | ok v => rfl
  | error e => rfl
example (x : Checked CLUint64) (f g : CLUint64 → Checked CLUint64) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  cases x with
  | ok v => rfl
  | error e => rfl

/-! ## The reward-shaped formula (§4.9)

The pyspec computes the reward numerator as one product, divides by the
increments product, and adds the delta. An all-`CLUint64` spelling of the
chain is one `simp_arith` subject; the concrete pins below carry `Nat`
literal factors, so they close by `decide`. -/

-- `2000 // 160 = 12`, all intermediates in range.
-- `WEIGHT_DENOMINATOR` times the active increments: `40 * 4 = 160`.
example : (((100 : CLUint64) * 2 * 10 / (160 : CLUint64) : Checked CLUint64)) = .ok 12 := by
  decide
-- The numerator overflows first: the fault names the first `*`.
example : ((maxValue * 2 * 10 / (160 : CLUint64) : Checked CLUint64)) =
    .error (.range "*" 64 18446744073709551615 2) := by decide

end EthCLLib.Tests.CLArithLaws
