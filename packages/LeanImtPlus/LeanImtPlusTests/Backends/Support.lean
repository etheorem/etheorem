import LeanImtPlus

set_option autoImplicit false

namespace LeanImtPlusTests.Backends

open LeanImtPlus

/-- Exercise the complete tree and unified-proof lifecycle for hasher `H`. -/
def lifecyclePasses (H : Type) [Hasher H] : Bool :=
  match (do
    let tree ← (Tree.empty H).insertMany #[10, 25, 7, 3, 41, 18]
    let membership ← tree.generateProof 25
    let belowMinimum ← tree.generateProof 1
    let between ← tree.generateProof 20
    let aboveMaximum ← tree.generateProof 100

    let removed ← tree.remove 25
    let removedProof ← removed.generateProof 25
    let updated ← removed.update 18 19
    let updatedProof ← updated.generateProof 19

    return (verifyProof membership).isOk &&
      (verifyProof belowMinimum).isOk &&
      (verifyProof between).isOk &&
      (verifyProof aboveMaximum).isOk &&
      (verifyProof removedProof).isOk &&
      (verifyProof updatedProof).isOk) with
  | .ok passed => passed
  | .error _ => false

end LeanImtPlusTests.Backends
