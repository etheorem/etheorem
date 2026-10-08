import EthCLLib.Spec
import EthCLLib.Proofs.Run

/-!
# `EthCLLib.Proofs.StoreRun`: the fork-choice store runner these proofs run against

A theorem about a fork-choice `forkdef`'s effect has to pin down the monad the spec
body is elaborated into, since `StoreTransition` is a parameter of the fork body
rather than a fixed type. Every fork-choice proof pins the runner named here, at its
own fork's `Store`, through `(StoreTransition := ForkChoiceStoreRun (Store map))`.

The module lives in the framework, beside the other generic proof modules, rather
than in one fork's directory. The runner
is a monad over an arbitrary store type, so it belongs to no fork, and the theorems
that pin it live in `EthCLSpecs/Proofs/Gloas/` and `EthCLSpecs/Proofs/Heze/` alike.

`SPEC_AUTHORING_MODEL.md` sets out a fast/pure duality across four axes, and
`SPECS_ARCHITECTURE.md` §11.1 states that the fast configuration (`FastBox`,
`EStateM`, `hashMap`) is never a proof target. This is the pure column's store
monad, the store-side counterpart of `EthCLSpecs/Proofs/Gloas/Run.lean`'s `GloasRun`.

The generic `StateT`-over-`Except` bind, pure, throw, and `Except.bind` equations
live in `EthCLLib/Proofs/Run.lean`. The same module pins the box on the state side: a
state-transition theorem states its run on `pureState v`, the uncached box, and that
`.run` fact is what the nested-machine bridge consumes unchanged. This file keeps the
`ForkChoiceStoreRun` abbreviation
and the store-specific `throwArithmetic_run` equation: `throwArithmetic` lifts a
`StateTransitionError` that the store machine wraps as `.transition`, so the
generic `run_throw` does not apply. It also keeps `toNat_add_of_not_lt` and
`toNat_mul_of_guard`, the `Nat` values of a `checkedAdd` and a `checkedMul` that do
not raise.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (StoreTransitionError throwArithmetic)

/-- Pure runner for fork-choice store proofs: `StateT` over `Except`, threading an
arbitrary store state `σ` and rejecting with `StoreTransitionError`.

Parameterized by the store type rather than by a fork-specific `Store`, so Gloas and
Heze, and any later fork, pin `(StoreTransition := ForkChoiceStoreRun (Store map))` at
the same shared name. `abbrev` (reducible) so a goal mentioning it unifies with the
spelled-out `StateT σ (Except StoreTransitionError)`. -/
abbrev ForkChoiceStoreRun (σ : Type) : Type → Type :=
  StateT σ (Except StoreTransitionError)

/-- `.run` of `throwArithmetic` at `ForkChoiceStoreRun`. Closes by `rfl`
without unfolding `liftErr`. -/
theorem ForkChoiceStoreRun.throwArithmetic_run {σ α : Type}
    (descr : String) (s : σ) :
    (throwArithmetic
        (m := ForkChoiceStoreRun σ)
        (E := StoreTransitionError)
        descr : ForkChoiceStoreRun σ α).run s
      = .error (.transition (.arithmetic descr)) :=
  rfl

/-- A `checkedAdd` that does not raise adds the `Nat` values. Its test `a + b < a` is the
unsigned carry, so when the test fails the sum fits in `UInt64`. -/
theorem toNat_add_of_not_lt (a b : UInt64) (h : ¬ (a + b < a)) :
    (a + b).toNat = a.toNat + b.toNat := by
  have ha : a.toNat < 18446744073709551616 := a.toNat_lt
  have hb : b.toNat < 18446744073709551616 := b.toNat_lt
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  rw [UInt64.toNat_add]
  -- `omega` needs the modulus as a literal.
  have hp : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [hp] at h ⊢
  omega

/-- A `checkedMul a b` that does not raise multiplies the `Nat` values. Its guard says that
`a` is zero, or that the truncated product divides back to `b`. Then the product fits in
`UInt64`. -/
theorem toNat_mul_of_guard (a b : UInt64) (h : ¬ ((a != 0 && a * b / a != b) = true)) :
    (a * b).toNat = a.toNat * b.toNat := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at h
  by_cases ha : a = 0
  · subst ha
    simp
  · have hd := congrArg UInt64.toNat (h ha)
    have hpos : 0 < a.toNat := by
      rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) ha
      · exact h0
    simp only [UInt64.toNat_div, UInt64.toNat_mul] at hd
    -- `p` is the truncated product. It divides back to `b`, so it is at least `a * b`, and
    -- it never exceeds the true product.
    generalize hp : a.toNat * b.toNat % 2 ^ 64 = p at hd
    have hlo : a.toNat * b.toNat ≤ p := by
      have := (Nat.le_div_iff_mul_le hpos).mp (Nat.le_of_eq hd.symm)
      simpa [Nat.mul_comm] using this
    have hhi : p ≤ a.toNat * b.toNat := by
      rw [← hp]
      exact Nat.mod_le _ _
    rw [UInt64.toNat_mul, hp]
    omega

end EthCLLib.Proofs
