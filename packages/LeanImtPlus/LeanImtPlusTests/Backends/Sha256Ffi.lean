import LeanImtPlus.Hasher.Sha256Ffi
import LeanImtPlusTests.Backends.Support

set_option autoImplicit false

/-!
# FFI SHA-256 adapter acceptance tests

The OpenSSL backend must produce exactly the same roots and paths as the
pure-Lean specification backend.
-/

namespace LeanImtPlusTests.Backends.Sha256Ffi

open LeanImtPlus

/-- OpenSSL SHA-256 supports the complete tree-and-proof lifecycle. -/
example : lifecyclePasses LeanImtPlus.Sha256Ffi = true := by
  native_decide

private def implementationsAgree : Bool :=
  match (do
    let specTree ← (Tree.empty Sha256Spec).insertMany #[10, 25, 7, 3, 41, 18]
    let ffiTree ← (Tree.empty LeanImtPlus.Sha256Ffi).insertMany #[10, 25, 7, 3, 41, 18]
    let specRoot ← specTree.root
    let ffiRoot ← ffiTree.root
    let specProof ← specTree.generateProof 20
    let ffiProof ← ffiTree.generateProof 20
    return (specRoot : Nat) == (ffiRoot : Nat) &&
      (specProof.root : Nat) == (ffiProof.root : Nat) &&
      specProof.leaf == ffiProof.leaf &&
      specProof.leafIndex == ffiProof.leafIndex &&
      (specProof.siblings : Array Nat) == (ffiProof.siblings : Array Nat)) with
  | .ok passed => passed
  | .error _ => false

/-- FFI execution changes performance and trust, not commitments. -/
example : implementationsAgree = true := by
  native_decide

end LeanImtPlusTests.Backends.Sha256Ffi
