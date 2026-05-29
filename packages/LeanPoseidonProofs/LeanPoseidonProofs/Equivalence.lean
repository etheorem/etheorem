import LeanPoseidon
import LeanPoseidonProofs.FpCommRing
import Mathlib.Tactic

/-!
# `LeanPoseidonProofs.Equivalence` — fast layers = dense reference

The shipped Poseidon2 linear layers use the cheap *fast* forms
(sum-plus-scaled-diagonal); `Poseidon2/LinearLayers.lean` also ships the
textbook *dense* `t×t` matrix–vector products as `mul*Ref`. Here we prove
they compute the same thing — hence the whole permutations coincide. This
is the machine-checked form of Poseidon2's central optimisation claim (the
`O(t²) → O(t)` linear-layer collapse).

## Generic over any commutative ring

The layer identities are pure ring identities — `xᵢ + Σⱼxⱼ = 2xᵢ + Σ_{j≠i}xⱼ`
and `(intDiagᵢ−1)xᵢ + Σⱼxⱼ = intDiagᵢxᵢ + Σ_{j≠i}xⱼ` — true over *any*
`[CommRing R]`, independent of the prime. So they are proved generically by
`ring` (after `Vector.ext` + `interval_cases` on the width-3 index), and then
specialised to the concrete fields via `CommRing (Fp p)` (`FpCommRing`).

`permute_eq_permuteRef` then follows by **congruence through the shared
schedule**: `permute` and `permuteRef` are both `permuteWith par _ _ st`,
differing only in the two linear-layer functions — so rewriting the two
function-level layer equalities is enough.

## Scope — what this does and does not certify

Because `permute` and `permuteRef` share the *same* `permuteWith` schedule,
they share the **S-box** (`x ↦ x⁵`), the **round-constant (ARK) additions**,
and the **round ordering** (initial layer + 4 full + 56 partial + 4 full,
with the same flattened-constant indexing) — these cancel in the equality.
So `permute_eq_permuteRef` certifies *only* that the fast linear layers equal
the dense ones; it says **nothing** about whether the S-box exponent, the
ARK indexing, the schedule, or the round constants match real Poseidon2 — it
would hold unchanged even if those were wrong (both sides would commit the
identical error). Those are pinned instead by the `native_decide` anchor KAT
in `Poseidon2/Permutation.lean` (and the differential test / committed KATs),
which carry `Lean.ofReduceBool` (compiler trust) / empirical trust. The
trust thus splits cleanly: the *optimisation* is proved with no compiler
trust here; the *S-box/ARK/schedule/constants* are validated empirically
there. Combined, the shipped `permute` is faithful Poseidon2.

## Axiom footprint

The proof path uses only `ring` / `CommRing` / `ZMod` (mathlib): its axioms
are the standard `propext`, `Classical.choice`, `Quot.sound` — **no
`Lean.ofReduceBool`** (the `native_decide` compiler-trust axiom that the
conformance KATs use) and **no FFI**. `#print axioms permute_eq_permuteRef`
shows exactly those three (so read it as "the layer optimisation is clean",
per *Scope* above — not "the whole permutation is independently verified").
(Not committed, per CLAUDE.md; run during review.)
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

variable {R : Type} [CommRing R]

/-- **Fast external layer = dense reference**, over any commutative ring.
`circ(2,1,1)`'s row dot product equals `xᵢ + Σⱼ xⱼ`. -/
theorem mulExternalFast_eq_ref (st : Vector R 3) :
    mulExternalFast st = mulExternalRef st := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [mulExternalFast, mulExternalRef, mulMat3, extMatrix3, Vector.getElem_ofFn,
      Fin.getElem_fin] <;> ring

/-- **Fast internal layer = dense reference**, over any commutative ring.
`J + diag(intDiagᵢ−1)`'s row dot product equals `Σⱼ xⱼ + (intDiagᵢ−1)·xᵢ`. -/
theorem mulInternalFast_eq_ref [Inhabited R] (par : Params R) (st : Vector R 3) :
    mulInternalFast par st = mulInternalRef par st := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [mulInternalFast, mulInternalRef, mulMat3, intMatrix3, Vector.getElem_ofFn,
      Fin.getElem_fin] <;> ring

/-- **The fast and reference permutations coincide.** Both are the shared
`permuteWith` schedule; they differ only in the linear-layer functions, so
this is congruence on the two layer equalities (lifted to function
equalities by `funext`). -/
theorem permute_eq_permuteRef [Inhabited R] (par : Params R) (st : Vector R 3) :
    permute par st = permuteRef par st := by
  unfold permute permuteRef
  rw [funext (mulExternalFast_eq_ref (R := R)), funext (mulInternalFast_eq_ref par)]

/-! ## Specialised to the shipped instances

The same theorem, instantiated at the two concrete fields (using
`CommRing (Fp p)` from `FpCommRing`). These are the "fast path is faithful"
results for `bn254Params` and `bls12Params`. -/

theorem permute_eq_permuteRef_bn254 (st : Vector Bn254Fr 3) :
    permute bn254Params st = permuteRef bn254Params st :=
  permute_eq_permuteRef bn254Params st

theorem permute_eq_permuteRef_bls12 (st : Vector Bls12Fr 3) :
    permute bls12Params st = permuteRef bls12Params st :=
  permute_eq_permuteRef bls12Params st

end LeanPoseidon.Poseidon2
