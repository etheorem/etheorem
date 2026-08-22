import LeanImtPlus.Hasher.Class
import LeanPoseidon.Poseidon2.Compress

set_option autoImplicit false

/-!
# Poseidon2 LeanIMT+ adapter

Values and digests live in the canonical BN254 scalar field. Inputs at or above
the modulus are rejected before hashing, so `ofNat` never introduces a silent
modular alias for an accepted LeanIMT+ value.
-/

namespace LeanImtPlus

/-- Phantom tag selecting pure-Lean BN254 Poseidon2 compression. -/
inductive Poseidon2 : Type

@[reducible] instance : Hasher Poseidon2 where
  Digest := LeanPoseidon.Bn254Fr
  digestInhabited := inferInstance
  digestBEq := ⟨fun left right => decide (left = right)⟩
  digestRepr := inferInstance
  validValue := fun value => value < LeanPoseidon.bn254FrModulus
  validDigest := fun _ => true
  ofNat := LeanPoseidon.Bn254Fr.ofNat
  compress := LeanPoseidon.Poseidon2.compress

end LeanImtPlus
