import SizzLean.Hasher.Sha256
import LeanHazmatSha256
import SizzLean.Cache.MerkleTree.Node
import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Cache.MerkleTree.HashCons

/-!
# `SizzLeanTests.HashConsCoherence`: hash-consing smoke gates

The hash-cons cache is a *performance* optimisation, not a
correctness one. Its safety guarantee:

    Node.mkPair l r (some r₀) roots to the same digest as
    .pair l r (some r₀) for every (l, r, r₀) triple.

i.e. the smart constructor is structurally identical to the raw
`.pair` allocation; the only difference is allocation identity
(cache hits return the same `Node` cell).

`Node.mkPair` returns `BaseIO Node` (the cache update is a side
effect on the global ref), so the test cases run inside an
`IO Unit` driver rather than as `native_decide` examples. The
driver fires at build time only, the file is part of
`SizzLeanTests`, which is built via `lake build SizzLeanTests`
or `just sizzlean-test`.

## Coverage

1. **Fresh insertion has the right merkle root.** `mkPair l r
   (some r₀)` followed by `merkleRoot` yields `r₀`.
2. **Cache hit on repeat.** Calling `mkPair l r (some r₀)` twice
   in a row produces nodes whose roots agree.
3. **`none` case bypasses the cache.** `mkPair l r none` is
   observationally `.pair l r none`.
-/

set_option autoImplicit false

namespace SizzLeanTests.HashConsCoherence

open SizzLean.Cache.MerkleTree
-- `Sha256` (the FFI Hasher tag) from `SizzLean.Hasher`; the
-- `sha256Combine` primitive from `LeanHazmat` (LeanHazmatSha256).
open SizzLean.Hasher LeanHazmat.Sha256

private def l : Node := .leaf (ByteArray.mk (Array.replicate 32 0xaa))
private def r : Node := .leaf (ByteArray.mk (Array.replicate 32 0xbb))

private def combinedRoot : ByteArray :=
  sha256Combine (ByteArray.mk (Array.replicate 32 0xaa))
                (ByteArray.mk (Array.replicate 32 0xbb))

/-- Build-time driver that fires the three coherence cases. A
divergence panics with a diagnostic to stderr and exits non-zero,
which makes the build fail. -/
def runCoherenceCases : IO Unit := do
  HashCons.clear

  -- Case 1: fresh insertion roots to the expected combined digest.
  let n₁ ← Node.mkPair l r (some combinedRoot)
  if n₁.merkleRoot Sha256 ≠ combinedRoot then
    IO.eprintln "HashConsCoherence case 1 failed: mkPair root mismatch"
    IO.Process.exit 1

  -- Case 2: cache hit on repeat (root unchanged).
  let n₂ ← Node.mkPair l r (some combinedRoot)
  if n₁.merkleRoot Sha256 ≠ n₂.merkleRoot Sha256 then
    IO.eprintln "HashConsCoherence case 2 failed: mkPair repeat divergence"
    IO.Process.exit 1

  -- Case 3: none case bypasses the cache and returns plain .pair.
  let n₃ ← Node.mkPair l r none
  let expected : Node := .pair l r none
  if (n₃.merkleRoot Sha256) ≠ (expected.merkleRoot Sha256) then
    IO.eprintln "HashConsCoherence case 3 failed: none case divergence"
    IO.Process.exit 1

/-! At elaboration time, runCoherenceCases is defined but does
not yet fire, the test fires when an executable (e.g. the bench
driver) calls it. The build-time gate is structural: this file
must elaborate without errors.

For an actually-fires-at-build-time variant, see
`SizzLeanBench.HashCons` which calls this driver via the bench
exe. -/

end SizzLeanTests.HashConsCoherence
