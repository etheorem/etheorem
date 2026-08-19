import SizzLean.Hasher.Sha256Spec
import SizzLean.Hasher.Sha256Equiv

/-!
# `SizzLean.Hasher.CombineWidth`: the combine-width witnesses

`CombineWidth32` instances for both concrete hashers. The class itself is in
`Hasher/Class.lean`.
-/

set_option autoImplicit false

namespace SizzLean.Hasher

/-- `Sha256Spec.combine` always returns a 32-byte digest, by
`LeanSha256.combine_size_eq_32`. No axiom. -/
theorem sha256Spec_combine_size (a b : ByteArray) :
    (Hasher.combine (H := Sha256Spec) a b).size = 32 :=
  LeanSha256.combine_size_eq_32 a b

/-- The `CombineWidth32` witness for the pure-Lean hasher. -/
instance : CombineWidth32 Sha256Spec := ⟨sha256Spec_combine_size⟩

/-- `Sha256.combine` always returns a 32-byte digest, by `sha256Combine_eq_spec`
then `LeanSha256.combine_size_eq_32`. -/
theorem sha256_combine_size (a b : ByteArray) :
    (Hasher.combine (H := Sha256) a b).size = 32 := by
  show (LeanHazmat.Sha256.sha256Combine a b).size = 32
  rw [sha256Combine_eq_spec]
  exact LeanSha256.combine_size_eq_32 a b

/-- The `CombineWidth32` witness for the FFI hasher. -/
instance : CombineWidth32 Sha256 := ⟨sha256_combine_size⟩

end SizzLean.Hasher
