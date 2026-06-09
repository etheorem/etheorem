import LeanPoseidon.Poseidon2.Params

/-!
# `LeanPoseidon.LinearLayers`: the linear layers, fast and reference

This is the conceptual heart of the library and the subject of the
(deferred) equivalence proof. Between its non-linear S-box layers,
Poseidon2 diffuses the state with two matrix multiplies: the **external**
matrix `M_E` (used in the full rounds and once at the start) and the
**internal** matrix `M_I` (used in the partial rounds). The paper's
optimisation is that, for the chosen matrices, the dense `t×t`
matrix–vector product collapses to a sum-plus-scaled form costing `O(t)`
adds instead of `O(t²)` multiplies.

|                       | external `M_E` (t = 3)            | internal `M_I`                       |
| --------------------- | --------------------------------- | ------------------------------------ |
| **fast** (shipped)    | `s = Σ xᵢ;  outᵢ = xᵢ + s`        | `s = Σ xᵢ;  outᵢ = s + (diagᵢ − 1)·xᵢ` |
| **reference** (dense) | literal `t×t` matrix–vector prod  | literal `t×t` matrix–vector prod      |

For `t = 3` the external matrix is `circ(2,1,1)`, i.e. `M_E[i][j] = 1 + δᵢⱼ`
(diagonal 2, off-diagonal 1). So `outᵢ = xᵢ + (x₀+x₁+x₂)` *is* exactly
the dense product. The internal matrix is `J + diag(diagᵢ − 1)` (the
all-ones matrix `J` plus a diagonal), with `M_I[i][i] = diagᵢ` and
`M_I[i][j] = 1` off the diagonal, giving the scaled-sum form. Both
equalities are pure ring identities, *that* is what the
`LeanPoseidonProofs` package proves (deferred; see `docs/PLAN.md`).

## Generic over the coefficient ring (the Lean idiom)

All four functions are generic over `R` and **public** (not `private`):
the same definitions serve the concrete `Bn254Fr` core *and* the generic-ring
equivalence proof, which states `mul*Fast = mul*Ref` over any
`[CommRing R]`. To stay `mathlib`-free here, the core requires only the
minimal Lean-core algebra classes it actually uses, `Add`, `Mul`, `Sub`,
`One` (and `Inhabited`, to read the diagonal out of the params `Array`).
`mathlib`'s `CommRing` provides every one of these, so the proof package
specialises these same definitions to a `CommRing` without re-stating
them.

## Width

The shipped instance is `t = 3` (the width binary Merkle trees use), so
these layers are written concretely on `Vector R 3`. `Vector α n` is
Lean's length-indexed array, so the matrix dimensions are checked by the
type. Other widths are a deferred follow-up (`docs/PLAN.md` Phase 4); the
`Fin 3 → Fin 3 → R` matrix form below generalises cleanly when needed.
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

variable {R : Type} [Add R] [Mul R] [Sub R] [One R] [Inhabited R]

/-! ## Dense reference building blocks -/

/-- Dense `3×3` matrix–vector product: output component `i` is the dot
product of matrix row `i` with the state, `Σⱼ M[i][j]·xⱼ`. This is the
literal `O(t²)` form the fast layers optimise away. -/
def mulMat3 (m : Fin 3 → Fin 3 → R) (st : Vector R 3) : Vector R 3 :=
  Vector.ofFn (fun i => m i 0 * st[0] + m i 1 * st[1] + m i 2 * st[2])

/-- The external matrix `M_E` for `t = 3`: `circ(2,1,1)`, i.e.
`M[i][j] = 1 + δᵢⱼ` (diagonal `1 + 1`, off-diagonal `1`). -/
def extMatrix3 : Fin 3 → Fin 3 → R := fun i j => if i = j then (1 : R) + 1 else 1

/-- The internal matrix `M_I` for `t = 3` from an instance's diagonal:
`M[i][i] = intDiagᵢ` on the diagonal, `1` off it. That is `J + diag(intDiagᵢ − 1)`. -/
def intMatrix3 (par : Params R) : Fin 3 → Fin 3 → R :=
  fun i j => if i = j then par.intDiag[i.val]! else 1

/-! ## The four layers -/

/-- **Fast external layer (shipped).** `s = Σⱼ xⱼ; outᵢ = xᵢ + s`. For
the `circ(2,1,1)` matrix this equals the dense product:
`outᵢ = 2·xᵢ + Σ_{j≠i} xⱼ = xᵢ + (x₀+x₁+x₂)`. -/
def mulExternalFast (st : Vector R 3) : Vector R 3 :=
  let s := st[0] + st[1] + st[2]
  Vector.ofFn (fun i => st[i] + s)

/-- **Dense external layer (reference).** The literal `3×3` product with
`circ(2,1,1)`. Equal to `mulExternalFast` by a ring identity. -/
def mulExternalRef (st : Vector R 3) : Vector R 3 :=
  mulMat3 extMatrix3 st

/-- **Fast internal layer (shipped).** `s = Σⱼ xⱼ; outᵢ = s + (intDiagᵢ − 1)·xᵢ`.
For `M_I = J + diag(intDiagᵢ − 1)` this equals the dense product:
`outᵢ = intDiagᵢ·xᵢ + Σ_{j≠i} xⱼ = (intDiagᵢ − 1)·xᵢ + (x₀+x₁+x₂)`. -/
def mulInternalFast (par : Params R) (st : Vector R 3) : Vector R 3 :=
  let s := st[0] + st[1] + st[2]
  Vector.ofFn (fun i => s + (par.intDiag[i.val]! - 1) * st[i])

/-- **Dense internal layer (reference).** The literal `3×3` product with
`J + diag(intDiagᵢ − 1)`. Equal to `mulInternalFast` by a ring identity. -/
def mulInternalRef (par : Params R) (st : Vector R 3) : Vector R 3 :=
  mulMat3 (intMatrix3 par) st

/-! ## Sample-state cross-checks (a sanity gate before the general proof)

On the concrete BN254 t=3 instance, the fast and dense forms agree on
sample states. This is the early guard; the `LeanPoseidonProofs`
package's `mul*Fast_eq_ref` theorems (deferred) are the general result
over any `[CommRing R]`. -/

private def sampleA : Vector Bn254Fr 3 := Vector.ofFn (fun i => Bn254Fr.ofNat (i.val + 1))
private def sampleB : Vector Bn254Fr 3 := Vector.ofFn (fun i => Bn254Fr.ofNat (1000003 * i.val + 778201))

#guard mulExternalFast sampleA = mulExternalRef sampleA
#guard mulExternalFast sampleB = mulExternalRef sampleB
#guard mulInternalFast bn254Params sampleA = mulInternalRef bn254Params sampleA
#guard mulInternalFast bn254Params sampleB = mulInternalRef bn254Params sampleB

end LeanPoseidon.Poseidon2
