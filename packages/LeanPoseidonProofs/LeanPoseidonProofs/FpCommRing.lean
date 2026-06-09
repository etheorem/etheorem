import LeanPoseidon.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# `LeanPoseidonProofs.FpCommRing`: the `CommRing (Fp p)` instance

The core's `Fp p` (`{ val : Nat // val < p }`, with `Nat`-mod arithmetic)
is given a `CommRing` structure here, in the mathlib-bearing proofs
package, so the core stays mathlib-free. The instance is what lets the
`ring` tactic discharge the linear-layer identities in `Equivalence.lean`
over the concrete field.

## How (transport, keeping the core's operations)

We use mathlib's `Function.Injective.commRing` along the injection

  `toZMod : Fp p → ZMod p`,  `a ↦ (a.val : ZMod p)`,

which *transports* `ZMod p`'s `CommRing` laws back to `Fp p` **while
keeping `Fp p`'s own `+`, `*`, `-`, `0`, `1` as the ring operations**
(that is the point of the `Injective` transport, vs. an `Equiv` transport
that would replace them and break `ring` on `Fp`-arithmetic goals). It is
generic in `p`, so it covers `Bn254Fr` and `Bls12Fr` (and any future
`Fp`-based field) with one instance; it needs only `[NeZero p]` (so the
field is nonempty / `0 < p`), not primality. The layer identities are
ring facts, independent of `p` being prime.

The four operations mathlib's transport also requires, `ℕ`/`ℤ`
scalar multiplication and `Nat`/`Int` casts, are defined here *via*
`ZMod p` (mathlib-side, so no mathlib leaks into the core), which makes
their `toZMod`-preservation proofs immediate (`ZMod.natCast_zmod_val`).
-/

set_option autoImplicit false

namespace LeanPoseidon

namespace Fp

variable {p : Nat} [NeZero p]

/-- The canonical embedding into `ZMod p`. -/
def toZMod (a : Fp p) : ZMod p := (a.val : ZMod p)

-- The four extra carriers mathlib's transport needs, defined through
-- `ZMod p` so `toZMod` preserves them definitionally up to `natCast_zmod_val`.
instance : NatCast (Fp p) := ⟨fun n => ⟨(n : ZMod p).val, ZMod.val_lt _⟩⟩
instance : IntCast (Fp p) := ⟨fun i => ⟨(i : ZMod p).val, ZMod.val_lt _⟩⟩
instance : SMul ℕ (Fp p)  := ⟨fun n a => ⟨(n • (a.val : ZMod p)).val, ZMod.val_lt _⟩⟩
instance : SMul ℤ (Fp p)  := ⟨fun z a => ⟨(z • (a.val : ZMod p)).val, ZMod.val_lt _⟩⟩

-- `.val` of each operation, definitionally (the `Fp` ops are `Nat`-mod).
private theorem val_zero : (0 : Fp p).val = 0 := rfl
private theorem val_one  : (1 : Fp p).val = 1 % p := rfl
private theorem val_add (a b : Fp p) : (a + b).val = (a.val + b.val) % p := rfl
private theorem val_mul (a b : Fp p) : (a * b).val = (a.val * b.val) % p := rfl
private theorem val_neg (a : Fp p)   : (-a).val = (p - a.val) % p := rfl
private theorem val_sub (a b : Fp p) : (a - b).val = (a.val + (p - b.val)) % p := rfl
private theorem val_nsmul (n : ℕ) (a : Fp p) : (n • a).val = (n • (a.val : ZMod p)).val := rfl
private theorem val_zsmul (z : ℤ) (a : Fp p) : (z • a).val = (z • (a.val : ZMod p)).val := rfl
private theorem val_natCast (n : ℕ) : ((n : Fp p)).val = (n : ZMod p).val := rfl
private theorem val_intCast (i : ℤ) : ((i : Fp p)).val = (i : ZMod p).val := rfl
private theorem pow_succ' (a : Fp p) (n : ℕ) : a ^ (n + 1) = a ^ n * a := rfl
private theorem pow_zero' (a : Fp p) : a ^ 0 = 1 := rfl

omit [NeZero p] in
theorem toZMod_injective : Function.Injective (toZMod : Fp p → ZMod p) := by
  intro a b h
  have hmod : a.val % p = b.val % p := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hval : a.val = b.val := by
    rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
  obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; simpa using hval

theorem toZMod_zero : toZMod (0 : Fp p) = 0 := by
  simp only [toZMod, val_zero, Nat.cast_zero]
theorem toZMod_one : toZMod (1 : Fp p) = 1 := by
  simp only [toZMod, val_one, ZMod.natCast_mod, Nat.cast_one]
theorem toZMod_add (a b : Fp p) : toZMod (a + b) = toZMod a + toZMod b := by
  simp only [toZMod, val_add, ZMod.natCast_mod, Nat.cast_add]
theorem toZMod_mul (a b : Fp p) : toZMod (a * b) = toZMod a * toZMod b := by
  simp only [toZMod, val_mul, ZMod.natCast_mod, Nat.cast_mul]
theorem toZMod_neg (a : Fp p) : toZMod (-a) = -toZMod a := by
  simp only [toZMod, val_neg, ZMod.natCast_mod, Nat.cast_sub a.isLt.le, ZMod.natCast_self,
    zero_sub]
theorem toZMod_sub (a b : Fp p) : toZMod (a - b) = toZMod a - toZMod b := by
  simp only [toZMod, val_sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub b.isLt.le,
    ZMod.natCast_self]
  ring
theorem toZMod_nsmul (n : ℕ) (a : Fp p) : toZMod (n • a) = n • toZMod a := by
  simp only [toZMod, val_nsmul, ZMod.natCast_zmod_val]
theorem toZMod_zsmul (z : ℤ) (a : Fp p) : toZMod (z • a) = z • toZMod a := by
  simp only [toZMod, val_zsmul, ZMod.natCast_zmod_val]
theorem toZMod_natCast (n : ℕ) : toZMod (n : Fp p) = (n : ZMod p) := by
  simp only [toZMod, val_natCast, ZMod.natCast_zmod_val]
theorem toZMod_intCast (i : ℤ) : toZMod (i : Fp p) = (i : ZMod p) := by
  simp only [toZMod, val_intCast, ZMod.natCast_zmod_val]
theorem toZMod_npow (a : Fp p) (n : ℕ) : toZMod (a ^ n) = (toZMod a) ^ n := by
  induction n with
  | zero => rw [pow_zero', toZMod_one, pow_zero]
  | succ k ih => rw [pow_succ', toZMod_mul, ih, pow_succ]

/-- `Fp p` is a commutative ring (for `p ≠ 0`), with the core's own
arithmetic as the ring operations, transported from `ZMod p` along the
injection `toZMod`. -/
instance instCommRing : CommRing (Fp p) :=
  toZMod_injective.commRing toZMod
    toZMod_zero toZMod_one toZMod_add toZMod_mul toZMod_neg toZMod_sub
    toZMod_nsmul toZMod_zsmul toZMod_npow toZMod_natCast toZMod_intCast

end Fp

end LeanPoseidon
