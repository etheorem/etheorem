import LeanPoseidon
import LeanPoseidonProofs.FpField
import LeanPoseidonProofs.Primality
import LeanPoseidonProofs.Equivalence
import Mathlib

/-!
# `LeanPoseidonProofs.Bijective` — the Poseidon2 permutation is a bijection

Phase 6 flagship: the shipped `permute` is an actual *permutation* (a bijection
of the state space). Proved structurally — S-box, linear layers, and ARK
additions are each bijective, composed through the shared `permuteWith`
schedule — on the **dense reference** `permuteRef`, then transported to the
shipped fast `permute` via the Phase-3 equivalence `permute_eq_permuteRef`.

This file builds the pieces bottom-up (each compiled in turn):
* Stage A — `Fp p ≃+* ZMod p`, `Finite (Fp p)`, `Nat.card (Fp p) = p`.
-/

set_option autoImplicit false
-- The Stage C section shares `[CommRing R] [Inhabited R]`; some lemmas use only a
-- subset (e.g. the external layer needs neither `Inhabited` nor the full ring),
-- which is benign — silence the per-lemma unused-section-variable lint.
set_option linter.unusedSectionVars false

open Function

namespace LeanPoseidon.Fp

variable {p : Nat} [Fact (Nat.Prime p)]

/-! ## Stage A — `Fp p` as a finite field via `ZMod p`

`toZMod` is an injective ring hom and (being a finite bijection) a ring
*iso* `Fp p ≃+* ZMod p`. That gives `Fp p` its `Finite` instance and pins its
cardinality to `p` — the facts the finite-field S-box argument needs. -/

/-- `Fp p` is ring-isomorphic to `ZMod p`: `toZMod` is the injective ring hom
(`FpCommRing`), with explicit inverse `z ↦ ⟨z.val, _⟩`. -/
def ringEquivZMod : Fp p ≃+* ZMod p where
  toFun := toZMod
  invFun z := ⟨z.val, ZMod.val_lt _⟩
  left_inv a := by
    obtain ⟨v, hv⟩ := a
    have hval : ((v : ZMod p)).val = v := ZMod.val_natCast_of_lt hv
    simp only [toZMod, hval]
  right_inv z := by
    show ((z.val : ZMod p)) = z
    exact ZMod.natCast_zmod_val z
  map_mul' := toZMod_mul
  map_add' := toZMod_add

/-- `Fp p` is finite (it injects into the finite `ZMod p`). -/
instance instFinite : Finite (Fp p) := Finite.of_injective toZMod toZMod_injective

/-- `Fp p` has exactly `p` elements (via the iso to `ZMod p`). -/
theorem card_eq : Nat.card (Fp p) = p := by
  rw [Nat.card_congr ringEquivZMod.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end LeanPoseidon.Fp

namespace LeanPoseidon.Poseidon2

open LeanPoseidon

variable {p : Nat} [Fact (Nat.Prime p)]

/-! ## Stage B — the S-box `x ↦ x⁵` is bijective

The non-linear layer. `sbox x = x⁵` (`x²·x²·x` by `ring`), and `x ↦ xⁿ` is a
bijection of a finite field exactly when `gcd(n, |F|−1) = 1` — here `gcd(5, p−1)`,
which holds for the shipped fields. The `0 ↦ 0` point is handled separately; on
the units `(Fp p)ˣ` (a finite group of order `p−1`) it is
`Nat.Coprime.pow_left_bijective`. -/

/-- The S-box is bijective on `Fp p` whenever `gcd(5, p−1) = 1`. -/
theorem sbox_bijective (hcop : Nat.Coprime 5 (p - 1)) :
    Bijective (sbox : Fp p → Fp p) := by
  have hpow : (sbox : Fp p → Fp p) = (fun x => x ^ 5) := by
    funext x; simp only [sbox]; ring
  rw [hpow]
  apply Finite.injective_iff_bijective.mp
  intro a b hab
  simp only at hab
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rcases eq_or_ne b 0 with hb | hb
    · exact hb.symm
    · exact absurd (by simpa using hab.symm) (pow_ne_zero 5 hb)
  · rcases eq_or_ne b 0 with hb | hb
    · subst hb
      exact absurd (by simpa using hab) (pow_ne_zero 5 ha)
    · lift a to (Fp p)ˣ using ha.isUnit with ua
      lift b to (Fp p)ˣ using hb.isUnit with ub
      have hu : ua ^ 5 = ub ^ 5 := by
        apply Units.ext; push_cast at hab ⊢; simpa using hab
      have hcard : (Nat.card (Fp p)ˣ).Coprime 5 := by
        rw [Nat.card_units, Fp.card_eq]; exact hcop.symm
      have heq := (Nat.Coprime.pow_left_bijective hcard).1 hu
      rw [heq]

end LeanPoseidon.Poseidon2

namespace LeanPoseidon.Poseidon2

/-! ## Stage C — the dense linear layers are bijective

Each dense layer is `mulMat3 m` (a literal `3×3` matrix–vector product). Over a
commutative ring, if `IsUnit (det M)` then `M.mulVec` is bijective
(`Matrix.mulVec_injective_of_isUnit` / `…_surjective_iff_isUnit`); `mulMat3 m`
is `M.mulVec` conjugated by the `Vector R 3 ≃ (Fin 3 → R)` bridge, so it is
bijective too. The determinants (`4` external, `7` internal for the shipped
diagonal) are supplied as `IsUnit` hypotheses, discharged per field in Stage E. -/

variable {R : Type} [CommRing R] [Inhabited R]

/-- The length-3 vector ↔ `Fin 3 → R` bridge (indexing vs. `Vector.ofFn`). -/
def vecEquiv : Vector R 3 ≃ (Fin 3 → R) where
  toFun st i := st[i.val]'i.isLt
  invFun := Vector.ofFn
  left_inv st := by apply Vector.ext; intro i hi; simp
  right_inv f := by funext i; simp

/-- `mulMat3 m` written through the bridge: `ofFn ∘ (Matrix.of m).mulVec ∘ get`. -/
theorem mulMat3_eq_conj (m : Fin 3 → Fin 3 → R) :
    mulMat3 m = vecEquiv.symm ∘ (Matrix.of m).mulVec ∘ vecEquiv := by
  funext st; apply Vector.ext; intro i hi
  simp [mulMat3, Function.comp_apply, vecEquiv, Vector.getElem_ofFn, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Fin.sum_univ_three]

/-- A dense `3×3` layer is bijective when its matrix determinant is a unit. -/
theorem mulMat3_bijective (m : Fin 3 → Fin 3 → R) (hdet : IsUnit (Matrix.of m).det) :
    Bijective (mulMat3 m) := by
  have hM : IsUnit (Matrix.of m) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hmv : Bijective ((Matrix.of m).mulVec) :=
    ⟨Matrix.mulVec_injective_of_isUnit hM, Matrix.mulVec_surjective_iff_isUnit.mpr hM⟩
  rw [mulMat3_eq_conj]
  exact vecEquiv.symm.bijective.comp (hmv.comp vecEquiv.bijective)

/-- The dense **external** layer is bijective when `det M_E` is a unit. -/
theorem mulExternalRef_bijective (hdet : IsUnit (Matrix.of (extMatrix3 (R := R))).det) :
    Bijective (mulExternalRef : Vector R 3 → Vector R 3) :=
  mulMat3_bijective extMatrix3 hdet

/-- The dense **internal** layer is bijective when `det M_I` is a unit. -/
theorem mulInternalRef_bijective (par : Params R)
    (hdet : IsUnit (Matrix.of (intMatrix3 par)).det) :
    Bijective (mulInternalRef par : Vector R 3 → Vector R 3) :=
  mulMat3_bijective (intMatrix3 par) hdet

/-- A per-coordinate map `st ↦ ofFn (fun i => g i st[i])` is bijective when each
coordinate map `g i` is — the building block for the ARK + S-box layers. -/
theorem piMap_conj_bijective (g : Fin 3 → R → R) (hg : ∀ i, Bijective (g i)) :
    Bijective (fun st : Vector R 3 => Vector.ofFn (fun i => g i (vecEquiv st i))) := by
  have hpi : Bijective (fun (f : Fin 3 → R) (i : Fin 3) => g i (f i)) :=
    (Equiv.piCongrRight (fun i => Equiv.ofBijective (g i) (hg i))).bijective
  have heq : (fun st : Vector R 3 => Vector.ofFn (fun i => g i (vecEquiv st i)))
           = vecEquiv.symm ∘ (fun (f : Fin 3 → R) (i : Fin 3) => g i (f i)) ∘ vecEquiv := by
    funext st; rfl
  rw [heq]; exact vecEquiv.symm.bijective.comp (hpi.comp vecEquiv.bijective)

end LeanPoseidon.Poseidon2

/-! ## Stage D — fold of bijections, rounds, and the full schedule -/

section Fold
open Function

/-- Folding a list of bijections is bijective (each step a bijection of the
accumulator). Proved by list induction — avoids `Nat.fold`'s dependent proof. -/
theorem bijective_list_foldl {α β : Type*} (l : List β) (g : β → α → α)
    (hg : ∀ x ∈ l, Bijective (g x)) :
    Bijective (fun init => l.foldl (fun acc x => g x acc) init) := by
  induction l with
  | nil => simpa using bijective_id
  | cons x xs ih =>
    have hx : Bijective (g x) := hg x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : Bijective (fun init => xs.foldl (fun acc y => g y acc) init) :=
      ih (fun y hy => hg y (List.mem_cons.mpr (Or.inr hy)))
    have heq : (fun init => (x :: xs).foldl (fun acc y => g y acc) init)
             = (fun init => xs.foldl (fun acc y => g y acc) init) ∘ (g x) := by
      funext init; simp [List.foldl_cons]
    rw [heq]; exact hxs.comp hx

/-- `Nat.fold` of per-index bijections is bijective (via `finRange` + `foldl`). -/
theorem bijective_nat_fold {α : Type*} (n : Nat) (f : (i : Nat) → i < n → α → α)
    (hf : ∀ i (h : i < n), Bijective (f i h)) :
    Bijective (fun init => Nat.fold n f init) := by
  have heq : (fun init => Nat.fold n f init)
           = (fun init => (List.finRange n).foldl (fun acc (x : Fin n) => f x.1 x.2 acc) init) := by
    funext init; rw [Nat.fold_eq_finRange_foldl]
  rw [heq]
  exact bijective_list_foldl (List.finRange n) (fun (x : Fin n) acc => f x.1 x.2 acc)
    (fun x _ => hf x.1 x.2)

end Fold

namespace LeanPoseidon.Poseidon2

open LeanPoseidon

variable {p : Nat} [Fact (Nat.Prime p)]

/-- One **full round** is bijective: ARK (a translation), the S-box on all
coordinates, then the (bijective) external layer. -/
theorem fullRound_bijective (extLayer : Vector (Fp p) 3 → Vector (Fp p) 3) (c : Fin 3 → Fp p)
    (hext : Bijective extLayer) (hcop : Nat.Coprime 5 (p - 1)) :
    Bijective (fullRound extLayer c) := by
  have hg : ∀ i, Bijective (fun x : Fp p => sbox (x + c i)) :=
    fun i => (sbox_bijective hcop).comp (Equiv.addRight (c i)).bijective
  have key := piMap_conj_bijective (fun i x => sbox (x + c i)) hg
  have heq : fullRound extLayer c
           = extLayer ∘ (fun st : Vector (Fp p) 3 =>
               Vector.ofFn (fun i => sbox (vecEquiv st i + c i))) := by
    funext st; simp [fullRound, Function.comp, vecEquiv, Vector.getElem_ofFn]
  rw [heq]; exact hext.comp key

/-- One **partial round** is bijective: ARK + S-box on coordinate 0 (identity on
the rest), then the (bijective) internal layer. -/
theorem partialRound_bijective (intLayer : Vector (Fp p) 3 → Vector (Fp p) 3) (c : Fp p)
    (hint : Bijective intLayer) (hcop : Nat.Coprime 5 (p - 1)) :
    Bijective (partialRound intLayer c) := by
  have hg : ∀ i : Fin 3, Bijective (fun x : Fp p => if i = 0 then sbox (x + c) else x) := by
    intro i
    by_cases hi : i = 0
    · subst hi; simpa using (sbox_bijective hcop).comp (Equiv.addRight c).bijective
    · simp only [if_neg hi]; exact bijective_id
  have key := piMap_conj_bijective (fun i x => if i = 0 then sbox (x + c) else x) hg
  have heq : partialRound intLayer c
           = intLayer ∘ (fun st : Vector (Fp p) 3 =>
               Vector.ofFn (fun i => if i = 0 then sbox (vecEquiv st i + c) else vecEquiv st i)) := by
    funext st
    simp only [partialRound, Function.comp_apply, vecEquiv, Equiv.coe_fn_mk]
    congr 1
  rw [heq]; exact hint.comp key

/-- The shared schedule is bijective given bijective layers (initial external
layer + the three round-folds, all composed). -/
theorem permuteWith_bijective (par : Params (Fp p))
    (extLayer intLayer : Vector (Fp p) 3 → Vector (Fp p) 3)
    (hext : Bijective extLayer) (hint : Bijective intLayer) (hcop : Nat.Coprime 5 (p - 1)) :
    Bijective (permuteWith par extLayer intLayer) := by
  unfold permuteWith
  have h1 : Bijective (fun s : Vector (Fp p) 3 =>
      Nat.fold (par.fullRounds / 2)
        (fun r _ s => fullRound extLayer (fun i => par.roundConstants[3 * r + i.val]!) s) s) :=
    bijective_nat_fold _ _ (fun r _ => fullRound_bijective extLayer _ hext hcop)
  have h2 : Bijective (fun s : Vector (Fp p) 3 =>
      Nat.fold par.partialRounds
        (fun j _ s => partialRound intLayer (par.roundConstants[3 * (par.fullRounds / 2) + j]!) s) s) :=
    bijective_nat_fold _ _ (fun j _ => partialRound_bijective intLayer _ hint hcop)
  have h3 : Bijective (fun s : Vector (Fp p) 3 =>
      Nat.fold (par.fullRounds / 2)
        (fun k _ s => fullRound extLayer
          (fun i => par.roundConstants[3 * (par.fullRounds / 2) + par.partialRounds + 3 * k + i.val]!) s) s) :=
    bijective_nat_fold _ _ (fun k _ => fullRound_bijective extLayer _ hext hcop)
  exact h3.comp (h2.comp (h1.comp hext))

/-- The dense reference permutation is bijective given bijective dense layers. -/
theorem permuteRef_bijective (par : Params (Fp p))
    (hext : Bijective (mulExternalRef : Vector (Fp p) 3 → Vector (Fp p) 3))
    (hint : Bijective (mulInternalRef par : Vector (Fp p) 3 → Vector (Fp p) 3))
    (hcop : Nat.Coprime 5 (p - 1)) :
    Bijective (permuteRef par) :=
  permuteWith_bijective par _ _ hext hint hcop

end LeanPoseidon.Poseidon2

/-! ## Stage E — the shipped permutations are bijections; `compress` has collisions

Discharge the structural hypotheses for the two shipped instances: the S-box
exponent is coprime to `p − 1` (`decide`), and the external/internal matrices
have nonzero (hence unit) determinant (`det = 4` / `det = 7`, by
`Matrix.det_fin_three` + `decide`). Then transport `Bijective (permuteRef …)` to
the shipped fast `Bijective (permute …)` along the Phase-3 equivalence. -/

namespace LeanPoseidon.Poseidon2

open LeanPoseidon

/-- **The shipped BN254 Poseidon2 permutation is a bijection.** Novel: the first
machine-checked structural-correctness fact about the bare Poseidon2 permutation.
Proved on the dense reference, transported via `permute_eq_permuteRef_bn254`. -/
theorem permute_bijective_bn254 : Function.Bijective (permute bn254Params) := by
  have hcop : Nat.Coprime 5 (bn254FrModulus - 1) := by decide
  have hext : Function.Bijective (mulExternalRef : Vector Bn254Fr 3 → Vector Bn254Fr 3) := by
    apply mulExternalRef_bijective
    apply Ne.isUnit
    rw [Matrix.det_fin_three]; decide
  have hint : Function.Bijective (mulInternalRef bn254Params : Vector Bn254Fr 3 → Vector Bn254Fr 3) := by
    apply mulInternalRef_bijective
    apply Ne.isUnit
    rw [Matrix.det_fin_three]; decide
  rw [funext permute_eq_permuteRef_bn254]
  exact permuteRef_bijective bn254Params hext hint hcop

/-- **The shipped BLS12-381 Poseidon2 permutation is a bijection.** -/
theorem permute_bijective_bls12 : Function.Bijective (permute bls12Params) := by
  have hcop : Nat.Coprime 5 (blsFrModulus - 1) := by decide
  have hext : Function.Bijective (mulExternalRef : Vector Bls12Fr 3 → Vector Bls12Fr 3) := by
    apply mulExternalRef_bijective
    apply Ne.isUnit
    rw [Matrix.det_fin_three]; decide
  have hint : Function.Bijective (mulInternalRef bls12Params : Vector Bls12Fr 3 → Vector Bls12Fr 3) := by
    apply mulInternalRef_bijective
    apply Ne.isUnit
    rw [Matrix.det_fin_three]; decide
  rw [funext permute_eq_permuteRef_bls12]
  exact permuteRef_bijective bls12Params hext hint hcop

/-- **`compress` alone is not collision-resistant.** As a 2-to-1 map
(`Bn254Fr × Bn254Fr → Bn254Fr`) it has collisions by pigeonhole — domain `p²`,
codomain `p`. This is the structural reason a binary-Merkle node built from a
(bijective, hence invertible) permutation needs leaf pre-hashing + domain
separation for collision resistance, not `compress` in isolation
(cf. *The Billion Dollar Merkle Tree*, ARCHITECTURE.md §7). -/
theorem compress_not_injective :
    ¬ Function.Injective (fun ab : Bn254Fr × Bn254Fr => compress ab.1 ab.2) := by
  intro hinj
  have hle : Nat.card (Bn254Fr × Bn254Fr) ≤ Nat.card Bn254Fr := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Fp.card_eq] at hle
  have h1 : 1 < bn254FrModulus := bn254FrModulus_prime.one_lt
  nlinarith [hle, h1]

end LeanPoseidon.Poseidon2
