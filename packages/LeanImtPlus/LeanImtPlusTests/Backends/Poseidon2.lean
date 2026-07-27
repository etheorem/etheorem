import LeanImtPlus.Hasher.Poseidon2
import LeanImtPlusTests.Backends.Support

set_option autoImplicit false

/-! Acceptance tests for the BN254 Poseidon2 adapter. -/

namespace LeanImtPlusTests.Backends.Poseidon2

open LeanImtPlus

/-- BN254 Poseidon2 supports the complete tree-and-proof lifecycle. -/
example : lifecyclePasses LeanImtPlus.Poseidon2 = true := by
  native_decide

private def rangeCheckPasses : Bool :=
  let tooLarge := LeanPoseidon.bn254FrModulus
  match (Tree.empty LeanImtPlus.Poseidon2).insert tooLarge with
  | .error .valueOutOfRange => true
  | _ => false

/-- Values that would alias after field reduction are rejected. -/
example : rangeCheckPasses = true := by
  native_decide

end LeanImtPlusTests.Backends.Poseidon2
