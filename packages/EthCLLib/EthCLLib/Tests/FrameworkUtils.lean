import EthCLLib

/-!
# `EthCLLib.Tests.FrameworkUtils`: Phase 2.1 framework self-tests

The framework's own self-tests for what it adds (`FRAMEWORK_ARCHITECTURE.md`
§14): map-backing equivalence (`hashMap` and `treeMap` agree on `FcMap` results,
so the proof-side backing matches the runner's), the arithmetic layer, and the
hashing-based crypto primitives. Inheritance-macro dispatch is covered by
`InheritanceReplay` / `ReplayChild`; the crypto-cache-transparency test waits on
the caching backend (Phase 4).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean.Hasher

namespace EthCLLib.Tests.FrameworkUtils

/-! ## Arithmetic layer -/

#guard isqrt 0 = 0
#guard isqrt 16 = 4
#guard isqrt 17 = 4
#guard isqrt 1000000 = 1000
#guard umax 3 5 = 5
#guard umin 3 5 = 3
#guard (uint64ToBytes 258).size = 8
#guard le8 (uint64ToBytes 258) = 258
#guard le8 (uintToBytes (258 : UInt64)) = 258

/-! ## Map-backing equivalence: `treeMap` and `hashMap` agree -/

private def pairs : List (Nat × Nat) := [(3, 30), (1, 10), (2, 20), (1, 11), (5, 50)]

private def buildMap (map : MapKind) [FcMap map] : map Nat Nat :=
  pairs.foldl (fun m kv => FcMap.insert m kv.1 kv.2) FcMap.empty

-- Lookups agree across the two backings on every probed key (including the
-- overwritten `1` and the absent `4`).
#guard (List.range 7).all fun k =>
  FcMap.lookup (buildMap treeMap) k == FcMap.lookup (buildMap hashMap) k

-- The key sets agree (sorted, since `hashMap` has no guaranteed order).
#guard (FcMap.keys (buildMap treeMap)).mergeSort (· ≤ ·)
     == (FcMap.keys (buildMap hashMap)).mergeSort (· ≤ ·)

-- `contains` agrees.
#guard (List.range 7).all fun k =>
  FcMap.contains (buildMap treeMap) k == FcMap.contains (buildMap hashMap) k

/-! ## Hashing-based crypto primitives (FFI `Sha256`, via `native_decide`) -/

private def v0 : Vector UInt8 4 := Vector.replicate 4 0
private def r0 : Vector UInt8 32 := Vector.replicate 32 0

-- `computeForkDataRoot` / `computeDomain` produce 32-byte outputs at the fast tag.
example : (@computeForkDataRoot fastHasherTag v0 r0).toArray.size = 32 := by native_decide
example : (@computeDomain fastHasherTag ⟨#[0,0,0,1]⟩ v0 r0).toArray.size = 32 := by native_decide

-- A depth-0 Merkle branch holds iff the leaf is the root (no siblings to mix).
example : @isValidMerkleBranch fastHasherTag r0 #[] 0 0 r0 = true := by native_decide
example : @isValidMerkleBranch fastHasherTag r0 #[] 0 0 (Vector.replicate 32 1) = false := by native_decide

end EthCLLib.Tests.FrameworkUtils
