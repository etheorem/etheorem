import LeanPoseidonProofs.FpCommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# `LeanPoseidonProofs.FpField` — the `Field (Fp p)` instance (prime `p`)

`FpCommRing` gives `Fp p` a `CommRing` for any `[NeZero p]`. The Phase 6
structural proofs — chiefly that the Poseidon2 permutation is a *bijection* —
need `Fp p` to be a **field**: the `x ↦ x⁵` S-box is bijective because the
multiplicative group of a finite field is cyclic of order `p − 1` and
`gcd(5, p−1) = 1`, and the dense linear layers are invertible because their
determinants are nonzero, hence units (in a field, nonzero ⇒ unit).

A field needs `p` prime, so this file works under `[Fact (Nat.Prime p)]`. The
standardised concrete moduli (`bn254FrModulus`, `blsFrModulus`) discharge that
hypothesis via the cited primality axioms in `Primality.lean`; the generic
structural theorems keep it as a hypothesis and stay axiom-clean.

## How (mirroring mathlib's own `Field (ZMod p)`)

We add a single new carrier — `Inv (Fp p)`, computed through `ZMod p`'s inverse
— and build the `Field` instance exactly the way mathlib builds `Field (ZMod p)`
(`Mathlib/Algebra/Field/ZMod.lean`): the existing `CommRing (Fp p)` is reused as
the ring parent (so there is **no `CommRing` diamond** — `Field.toCommRing`
resolves to `FpCommRing`'s instance), and only the two genuinely field-specific
axioms `mul_inv_cancel` / `inv_zero` are supplied, both discharged by transport
along the injective `toZMod : Fp p → ZMod p`. The rational-scalar data
(`nnqsmul` / `qsmul`) takes its structure defaults (`:= _`, `_def := rfl`), and
`Div` / `zpow` take the `DivInvMonoid` defaults (`a / b = a * b⁻¹`, `zpowRec`).
-/

set_option autoImplicit false

namespace LeanPoseidon

namespace Fp

variable {p : Nat} [Fact (Nat.Prime p)]

/-- `p ≠ 0`, from primality — so the `[NeZero p]` machinery (`CommRing (Fp p)`,
`ZMod.val_lt`, the `toZMod_*` lemmas) applies under `[Fact p.Prime]`. `NeZero` is
a `Prop`, so this is proof-irrelevant and never conflicts with another instance. -/
instance : NeZero p := ⟨(Nat.Prime.pos Fact.out).ne'⟩

/-- Field inversion, computed through `ZMod p` (a field for prime `p`); `0⁻¹ = 0`
by the `ZMod`/`DivisionRing` convention. The result is reduced (`< p`) by
`ZMod.val_lt`, so it lands back in `Fp p`. -/
instance : Inv (Fp p) := ⟨fun a => ⟨((a.val : ZMod p)⁻¹).val, ZMod.val_lt _⟩⟩

/-- `toZMod` preserves inversion — immediate, since the inverse is *defined*
through `ZMod p` (`ZMod.natCast_zmod_val` cancels the `val`/cast round-trip). -/
theorem toZMod_inv (a : Fp p) : toZMod a⁻¹ = (toZMod a)⁻¹ := by
  show (((a.val : ZMod p)⁻¹).val : ZMod p) = ((a.val : ZMod p))⁻¹
  rw [ZMod.natCast_zmod_val]

/-- `Fp p` is a field for prime `p`. Built like `Field (ZMod p)`: reuse the
`CommRing` parent, transport the two field axioms along `toZMod`. -/
instance instField : Field (Fp p) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have h2 : toZMod (0 : Fp p) = toZMod (1 : Fp p) := congrArg toZMod h
    rw [toZMod_zero, toZMod_one] at h2
    exact zero_ne_one h2⟩
  mul_inv_cancel a ha := by
    have hne : toZMod a ≠ 0 := fun h => ha (toZMod_injective (by rw [toZMod_zero]; exact h))
    apply toZMod_injective
    rw [toZMod_mul, toZMod_inv, toZMod_one]
    exact mul_inv_cancel₀ hne
  inv_zero := by
    apply toZMod_injective
    rw [toZMod_inv, toZMod_zero, inv_zero]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Fp

end LeanPoseidon
