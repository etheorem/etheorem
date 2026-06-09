import LeanPoseidonProofs.FpCommRing
import LeanPoseidonProofs.Equivalence
import LeanPoseidonProofs.FpField
import LeanPoseidonProofs.Primality
import LeanPoseidonProofs.Bijective
import LeanPoseidonProofs.Padding
import LeanPoseidonProofs.RoundCount

/-!
# `LeanPoseidonProofs`: the fast-≡-reference equivalence proof (library root)

The machine-checked form of Poseidon2's central optimisation claim: the
cheap *fast* linear layers `LeanPoseidon` ships compute exactly the same
field elements as the textbook *dense* matrix layers, hence
`permute = permuteRef`.

This is the monorepo's **only `mathlib` dependency**, isolated in this
package on purpose: the core `LeanPoseidon` library and its conformance
gates stay `mathlib`-free and fast, while the equivalence theorem, the
publishable artefact, lives here in the verified layer. mathlib is pinned
to the `v4.29.1` tag, whose toolchain matches the repo's, so its prebuilt
olean cache is used (`lake exe cache get`); nothing is compiled from
scratch.

Re-exports:

* `LeanPoseidonProofs.FpCommRing`: `instance [NeZero p] : CommRing (Fp p)`,
  transported from `ZMod p` along `a ↦ (a.val : ZMod p)` so the core's own
  `Fp` arithmetic stays the ring operations. One instance covers `Bn254Fr`,
  `Bls12Fr`, and any future `Fp`-based field.
* `LeanPoseidonProofs.Equivalence`: `mulExternalFast_eq_ref`,
  `mulInternalFast_eq_ref` (generic over `[CommRing R]`, closed by `ring`),
  `permute_eq_permuteRef` (congruence through the shared `permuteWith`
  schedule), and specialisations to `bn254Params` / `bls12Params`.

## Trust boundary

`#print axioms permute_eq_permuteRef` shows exactly `propext`,
`Classical.choice`, `Quot.sound`, mathlib's standard axioms, with **no
`Lean.ofReduceBool`** (the `native_decide` compiler-trust axiom the
conformance KATs use) and **no FFI axiom**. So this theorem carries no
empirical trust on its proof path.

The split is by *scope*, not just by axiom: this proof covers the
**linear-layer optimisation** only (the S-box, ARK additions, and schedule
are shared by `permute`/`permuteRef`, so they cancel and are *not*
cross-validated here, see `Equivalence`'s *Scope* note). Those are pinned
by the conformance gates' empirical/compiler trust (zkhash, the anchor
KATs). Optimisation: clean. Spec-faithfulness of the non-linear parts:
empirical. Together they cover the shipped `permute`.
-/
