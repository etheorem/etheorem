/-!
# `EthCLLib.Proofs.OfFnM`: `Vector.ofFnM` in `Except`, when nothing fails

The toolchain gives `Vector.ofFnM` unfolding lemmas (`ofFnM_succ`, `ofFnM_add`) and the `Array`
and `List` conversions, but no `getElem` lemma. In `Except`, an all-succeeding build equals the
pure `Vector.ofFn` of its values, which recovers `getElem` reasoning for a `forkdef` that builds
a vector in `Except`.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

/-- `Vector.ofFnM` over `Except` succeeds with the pure `Vector.ofFn` when every index succeeds.

The hypothesis is pointwise. `f i` is `.ok (g i)` for each `i`, where `g` is the function the
pure build uses. -/
theorem ofFnM_eq_ok_ofFn {ε α : Type} {n : Nat} {f : Fin n → Except ε α} {g : Fin n → α}
    (h : ∀ i, f i = .ok (g i)) :
    Vector.ofFnM f = .ok (Vector.ofFn g) := by
  -- `Except ε`'s `pure` is `.ok`, so the hypothesis rewrites `f` into the shape
  -- `Vector.ofFnM_pure` wants; that lemma then closes the goal with no induction.
  have : f = fun i => pure (g i) := funext h
  subst this
  exact Vector.ofFnM_pure

end EthCLLib.Proofs
