import LeanHazmatSha256
import LeanImtPlus.Hasher.Sha256

set_option autoImplicit false

/-!
# OpenSSL SHA-256 LeanIMT+ adapter

The digest format is identical to `Sha256Spec`; only the SHA-256 engine changes
to the OpenSSL-backed LeanHazmat primitive.
-/

namespace LeanImtPlus

/-- Phantom tag selecting the OpenSSL-backed SHA-256 implementation. -/
inductive Sha256Ffi : Type

namespace Sha256Ffi

/-- FFI SHA-256 over two 216-bit circuit inputs. -/
def hash2 (left right : Nat) : Nat :=
  Sha256.hash2With LeanHazmat.Sha256.sha256Hash left right

end Sha256Ffi

@[reducible] instance : Hasher Sha256Ffi where
  Digest := Nat
  digestInhabited := inferInstance
  digestBEq := inferInstance
  digestRepr := inferInstance
  validValue := Sha256.fits216
  validDigest := Sha256.fits216
  ofNat := id
  compress := Sha256Ffi.hash2

end LeanImtPlus
