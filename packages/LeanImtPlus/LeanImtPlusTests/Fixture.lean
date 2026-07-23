import LeanImtPlus

set_option autoImplicit false

namespace LeanImtPlusTests
namespace Fixture

open LeanImtPlus

/- Values from protocolwhisper/leanimt-plus:
   circuits/circuits/leanimt-plus-sha256/input-sha256.json.
   The expected root is computed with the test helper's SHA-256 hash2. -/
def fixtureProof : Proof where
  proofType := .membership
  value := 25
  leaf := { value := 25, nextValue := 41 }
  leafIndex := 2
  depth := 3
  siblings := #[
    44760521111385847688757584136291837775290581510593835802622506551,
    83336585336304545966697494887200522584217139303658635531604770253,
    92552056940898985611095539493417979120963194309751734001885444591,
    0
  ]

def expectedRoot : Nat :=
  89522155904212176319481870299496985371520560182393209332108238187

def fixtureVerifies : Bool :=
  match verify 10 fixtureProof with
  | .ok root => root == expectedRoot
  | .error _ => false

example : fixtureVerifies = true := by
  native_decide

end Fixture
end LeanImtPlusTests
