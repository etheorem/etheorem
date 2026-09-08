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
open EthCLLib.PySpecTests
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

/-! ## Checked `uint64` arithmetic: the faithful over/underflow faults

`checkedAdd` / `checkedSub` / `checkedMul` mirror remerkleable's `uint64`, which raises on
over/underflow rather than wrapping. In range they reduce to `.ok`; out of range they raise the
uncaught `.arithmetic` fault (never an expected rejection). The same source fault rides in as
`.arithmetic` on the state machine and, via `[ErrorConv …]`, as `.transition (.arithmetic …)` on
the store machine, so both instantiations are pinned. Faults are unreachable on well-formed
vectors, so these guards are the only thing exercising the throw. -/
#guard (checkedAdd 2 3 "x" : Except StateTransitionError UInt64).toOption = some 5
#guard (checkedSub 5 3 "x" : Except StateTransitionError UInt64).toOption = some 2
#guard (checkedMul 6 7 "x" : Except StateTransitionError UInt64).toOption = some 42
#guard (checkedSub 3 5 "u" : Except StateTransitionError UInt64) matches .error (.arithmetic _)
#guard (checkedAdd 0xffffffffffffffff 1 "o" : Except StateTransitionError UInt64) matches .error (.arithmetic _)
#guard (checkedMul 0x8000000000000000 4 "o" : Except StateTransitionError UInt64) matches .error (.arithmetic _)
#guard (checkedSub 3 5 "u" : Except StoreTransitionError UInt64) matches .error (.transition (.arithmetic _))

/-! ## The per-case caught set (`RunnerCaughtSet`)

One test, under `epoch_processing` / `registry_updates`, scores its invalid vector with its own
`except ValueError` wrapper. There the `.arithmetic` fault is the expected rejection, and an
`assert` is not. Every other case uses `expect_assertion_error`, whose set is `AssertionError`
and `IndexError`. The guards pin both sets and the pair that selects them. -/

#guard RunnerCaughtSet.ofCase "epoch_processing" "registry_updates" == .valueError
#guard RunnerCaughtSet.ofCase "epoch_processing" "slashings" == .assertionAndIndex
#guard RunnerCaughtSet.ofCase "operations" "deposit" == .assertionAndIndex
#guard RunnerCaughtSet.ofCase "sanity" "blocks" == .assertionAndIndex

#guard RunnerCaughtSet.assertionAndIndex.admits (.assert "x") == true
#guard RunnerCaughtSet.assertionAndIndex.admits (.outOfBounds 0 0) == true
#guard RunnerCaughtSet.assertionAndIndex.admits (.arithmetic "x") == false

#guard RunnerCaughtSet.valueError.admits (.arithmetic "x") == true
#guard RunnerCaughtSet.valueError.admits (.assert "x") == false
#guard RunnerCaughtSet.valueError.admits (.outOfBounds 0 0) == false

/-! ### The reject table (`classifyReject`)

`admits` answers whether the wrapper catches a reject. `classifyReject` turns that answer into
a pass or a fail. The guards above pin the first. These pin the second, one row each. -/

#guard (classifyReject .assertionAndIndex (.assert "x")).passed == true
#guard (classifyReject .assertionAndIndex (.assert "x")).bucket == .expectedRejection
#guard (classifyReject .assertionAndIndex (.outOfBounds 0 0)).passed == true
#guard (classifyReject .assertionAndIndex (.outOfBounds 0 0)).flagged == true
#guard (classifyReject .assertionAndIndex (.arithmetic "x")).passed == false
#guard (classifyReject .assertionAndIndex (.arithmetic "x")).bucket == .uncaughtFault

#guard (classifyReject .valueError (.arithmetic "x")).passed == true
#guard (classifyReject .valueError (.arithmetic "x")).bucket == .expectedRejection
#guard (classifyReject .valueError (.assert "x")).passed == false
#guard (classifyReject .valueError (.assert "x")).bucket == .likelyBug
#guard (classifyReject .valueError (.outOfBounds 0 0)).passed == false
#guard (classifyReject .valueError (.outOfBounds 0 0)).bucket == .likelyBug

#guard (classifyReject .valueError (.todo "x")).bucket == .todo
#guard (classifyReject .assertionAndIndex (.todo "x")).bucket == .todo
#guard (classifyReject .valueError (.outOfScope "x")).bucket == .outOfScope
#guard (classifyReject .assertionAndIndex (.outOfScope "x")).bucket == .outOfScope

/-! ## Fuel exhaustion: a deferral, never an expected rejection

`fuelIterateM!` throws when its bound runs out. That bound is a modeling artifact rather than
spec text, so the reject is `todo` (a work-queue `xfail`) and stays outside the caught set a
runner scores as a `valid: false` step's expected rejection. Pinned on the constructor: a
regression to `.assert` would turn a wrong loop bound into a green step, and breaks the build
here instead. -/
private def fuelOut : Except StoreTransitionError Nat :=
  fuelIterateM! 0 (0 : Nat) "pin" fun n => pure (.next (n + 1))

#guard fuelOut matches .error (.todo _)
#guard (match fuelOut with | .error e => !e.isExpectedRejection | .ok _ => false)
-- A walk inside its bound still returns normally: fuel 3 reaches the `.done` at 2.
#guard (fuelIterateM! 3 (0 : Nat) "pin" (fun n =>
  pure (if n ≥ 2 then .done n else .next (n + 1))) : Except StoreTransitionError Nat).toOption
    = some 2

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

-- The length guard (`depth != len(branch)`) rejects on either mismatch, before
-- the walk hashes anything. The second case is the one a defaulting read would
-- get wrong: at depth 0 the walk never touches the extra sibling, so it would
-- reconstruct `r0` and accept.
example : @isValidMerkleBranch fastHasherTag r0 #[] 1 0 r0 = false := by native_decide
example : @isValidMerkleBranch fastHasherTag r0 #[r0] 0 0 r0 = false := by native_decide

-- `computeMerkleBranchRoot` reports an out-of-range sibling read as an
-- `IndexError` carrying the real index and bound. The walk reads levels 0 and 1
-- from the two siblings, then asks for level 2 against a size-2 array. Only a
-- direct caller reaches this arm; `isValidMerkleBranch`'s guard runs first.
--
-- The result is projected to a `Nat` pair because `Except IndexError (Vector
-- UInt8 32)` carries no `DecidableEq` instance, so the equation cannot be
-- stated on the `Except` value itself.
example :
    (match @computeMerkleBranchRoot fastHasherTag r0 #[r0, r0] 3 0 with
     | .error (.indexError idx bound) => some (idx, bound)
     | .ok _ => none) = some (2, 2) := by native_decide

end EthCLLib.Tests.FrameworkUtils
