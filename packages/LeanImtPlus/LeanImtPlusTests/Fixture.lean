import LeanImtPlus

set_option autoImplicit false

namespace LeanImtPlusTests
namespace Fixture

open LeanImtPlus
open LeanImtPlus.Sha256

def expectedRoot : Nat :=
  89522155904212176319481870299496985371520560182393209332108238187

/- Values from vplasencia/leanimt-plus:
   circuits/circuits/leanimt-plus-sha256/input-sha256.json.
   The unified proof omits the circuit input's unused zero padding. The
   expected root is computed with the reference SHA-256 hash2 helper. -/
def fixtureProof : Proof Sha256Spec where
  proofType := .membership
  root := expectedRoot
  value := 25
  leaf := { value := 25, nextValue := 41 }
  leafIndex := 2
  depth := 3
  siblings := #[
    44760521111385847688757584136291837775290581510593835802622506551,
    83336585336304545966697494887200522584217139303658635531604770253,
    92552056940898985611095539493417979120963194309751734001885444591
  ]

def fixtureVerifies : Bool :=
  match verify 10 fixtureProof with
  | .ok () => true
  | .error _ => false

example : fixtureVerifies = true := by
  native_decide

def fixtureRecomputes : Bool :=
  match recomputeRoot 10 fixtureProof with
  | .ok root => root == expectedRoot
  | .error _ => false

example : fixtureRecomputes = true := by
  native_decide

def wrongRootRejected : Bool :=
  match verify 10 { fixtureProof with root := 1 } with
  | .error .rootMismatch => true
  | _ => false

example : wrongRootRejected = true := by
  native_decide

private def rejectsAs (maxDepth : Nat) (proof : Proof Sha256Spec)
    (expected : VerifyError) : Bool :=
  match verify maxDepth proof with
  | .error actual => actual == expected
  | .ok () => false

private def rejectsProofAs (proof : Proof Sha256Spec) (expected : VerifyError) : Bool :=
  match verifyProof proof with
  | .error actual => actual == expected
  | .ok () => false

def rejectionMatrixPasses : Bool :=
  rejectsAs 252 fixtureProof .invalidMaxDepth &&
  rejectsAs 10 { fixtureProof with root := twoPow216 } .rootOutOfRange &&
  rejectsAs 10 { fixtureProof with value := 0 } .zeroValue &&
  rejectsAs 10 { fixtureProof with value := twoPow216 } .valueOutOfRange &&
  rejectsAs 10 { fixtureProof with leaf := { value := twoPow216, nextValue := 41 } }
    .leafValueOutOfRange &&
  rejectsAs 10 { fixtureProof with siblings := fixtureProof.siblings.set! 0 twoPow216 }
    (.siblingOutOfRange 0) &&
  rejectsAs 10 { fixtureProof with value := 26 } .membershipLeafMismatch &&
  rejectsAs 10 { fixtureProof with proofType := .nonMembership } .nonMembershipRange &&
  rejectsAs 10 { fixtureProof with depth := 11 } .depthTooLarge &&
  rejectsAs 10 { fixtureProof with depth := 5 } .notEnoughSiblings &&
  rejectsProofAs { fixtureProof with siblings := fixtureProof.siblings.push 0 }
    .nonCanonicalSiblings &&
  rejectsAs 10 { fixtureProof with leafIndex := 8 } .nonCanonicalIndex &&
  rejectsAs 10 { fixtureProof with root := 1 } .rootMismatch

example : rejectionMatrixPasses = true := by
  native_decide

end Fixture
end LeanImtPlusTests
