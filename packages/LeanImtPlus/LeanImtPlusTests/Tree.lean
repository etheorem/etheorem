import LeanImtPlusTests.Fixture

set_option autoImplicit false

/-!
# LeanIMT+ tree acceptance tests

These tests follow the SHA-256 scenarios in `vplasencia/leanimt-plus`: mixed
order insertion, three non-membership positions, removal, update, and the
rejection guards used by the verifier circuit.
-/

namespace LeanImtPlusTests
namespace TreeTests

open LeanImtPlus

private def accepts (proof : Proof Sha256Spec) : Bool :=
  match verifyProof proof with
  | .ok () => true
  | .error _ => false

private def rejectsWith (expected : VerifyError) (proof : Proof Sha256Spec) : Bool :=
  match verify proof.depth proof with
  | .error actual => actual == expected
  | .ok () => false

def referenceLifecyclePasses : Bool :=
  match (do
    let tree ← (Tree.empty Sha256Spec).insertMany #[10, 25, 7, 3, 41, 18]
    let root ← tree.root
    let membership ← tree.generateProof 25
    let belowMinimum ← tree.generateProof 1
    let between ← tree.generateProof 20
    let aboveMaximum ← tree.generateProof 100

    let removed ← tree.remove 25
    let removedProof ← removed.generateProof 25
    let updated ← removed.update 18 19
    let updatedProof ← updated.generateProof 19

    let forgedTombstone := {
      between with
      leaf := { value := 0, nextValue := 0 }
    }
    let wrongRoot := { membership with root := 1 }
    return (root == Fixture.expectedRoot &&
      tree.size == 6 &&
      membership.proofType == ProofType.membership &&
      accepts membership &&
      belowMinimum.proofType == ProofType.nonMembership &&
      belowMinimum.leaf == ({ value := 0, nextValue := 3 } : Leaf) &&
      accepts belowMinimum &&
      between.leaf == ({ value := 18, nextValue := 25 } : Leaf) &&
      accepts between &&
      aboveMaximum.leaf == ({ value := 41, nextValue := 0 } : Leaf) &&
      accepts aboveMaximum &&
      removedProof.proofType == ProofType.nonMembership &&
      removedProof.leaf == ({ value := 18, nextValue := 41 } : Leaf) &&
      accepts removedProof &&
      updated.contains 19 &&
      !updated.contains 18 &&
      !updated.contains 0 &&
      updated.size == 5 &&
      accepts updatedProof &&
      rejectsWith .rootMismatch wrongRoot &&
      rejectsWith .tombstoneReplay forgedTombstone)) with
  | .ok passed => passed
  | .error _ => false

/--
The compiled evaluator checks concrete SHA-256 roots and paths. This follows
the repository rule for tests that reduce a hash to bytes.
-/
example : referenceLifecyclePasses = true := by
  native_decide

def mutationErrorsPass : Bool :=
  let inserted := (Tree.empty Sha256Spec).insert 7
  let zeroRejected := match (Tree.empty Sha256Spec).insert 0 with
    | .error .zeroValue => true
    | _ => false
  let emptyBatchRejected := match (Tree.empty Sha256Spec).insertMany #[] with
    | .error .emptyBatch => true
    | _ => false
  let duplicateRejected := match inserted with
    | .ok tree => match tree.insert 7 with
      | .error .duplicateValue => true
      | _ => false
    | .error _ => false
  let missingRejected := match inserted with
    | .ok tree => match tree.remove 8 with
      | .error .missingValue => true
      | _ => false
    | .error _ => false
  zeroRejected && emptyBatchRejected && duplicateRejected && missingRejected

example : mutationErrorsPass = true := by
  native_decide

end TreeTests
end LeanImtPlusTests
