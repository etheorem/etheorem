import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLean.Cache.MerkleTree.SetAt
import SizzLean.Cache.MerkleTree.Merkle
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# `SizzLeanBench.Profile`: phase-by-phase profile of S10 cached

S10 BatchedWritesLarge's cached column is currently ~3× slower
than its pure counterpart (5.75 ms vs 1.92 ms on
`ValidatorSet256`, 512 writes + 1 read). The bench tells us
*that* the cached path is slower but not *where* the cost
lives. This module breaks the path into seven phases (P1–P7)
with a final cross-check (P8 = P6 sanity) so the per-phase
cost is read directly off the TSV.

## Phases

| Phase | What runs | Used to compute |
|---|---|---|
| **P1** | build value (no wrapping)              | construction baseline |
| **P2** | build + `SSZ.FastBox v`                 | Box wrapping cost = P2 − P1 |
| **P3** | build + 512 plain record updates        | pure update cost = P3 − P1 |
| **P4** | build + box + 512 `sszUpdate`           | cached update accumulation cost = P4 − P2 |
| **P5** | P3 + `SSZ.hashTreeRoot`                 | pure full re-hash cost = P5 − P3 |
| **P6** | P4 + `box.hashTreeRoot` (full S10 cached) | cached commit + walk = P6 − P4 |
| **P7** | P4 + extract pending + `treeBase.setManyAt` (no final hash) | cached commit-only cost = P7 − P4 |
| **P8** | P7 + `merkleRoot` on the committed tree | cross-check, should ≈ P6 |

Derived costs to inspect:

* **Overlay accumulation overhead** = (P4 − P2) − (P3 − P1). If positive,
  `Std.TreeMap.insert` + per-write fresh `Thunk` allocation are
  costlier than the pure record-update pattern.
* **Cached commit walk** = P7 − P4. Pure `setManyAt` over 512
  updates on a depth-12 tree.
* **Post-commit hash cost** = P8 − P7. The Merkle root over the
  committed tree; this is what a "warm-cache cold-root" feels
  like when every interior `pair` along the touched spine has
  `none`.
* **Pure full re-hash** = P5 − P3. The baseline `SSZ.hashTreeRoot`
  walk on the post-update value with no cache; *should be
  similar to post-commit-hash* (both walk the full tree under
  the writes).
* **S10 verification** = P8 − P6. Two ways to spell the same
  computation; this difference should be in measurement noise.

If post-commit hash ≈ pure full re-hash but P6 ≫ P5, then the
overlay accumulation (P4 − P2) is paying for the difference.
If post-commit hash ≫ pure full re-hash, the cache-clear in
`setManyAt` is forcing fresh hashes that the pure path didn't
need (which would be suspicious because pure also hashes from
scratch).

## Anti-DCE

Every probe sinks at least one value derived from the work
into an `IO.Ref Nat`. For probes that don't naturally produce
bytes (P1–P4, P7), we sink the post-state's first-validator
effective-balance, a `UInt64` read off the `view` that the
compiler can't elide because it crosses an `IO.modify` boundary.
-/

set_option autoImplicit false

namespace SizzLeanBench.Profile

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Cache.MerkleTree
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

/-- Writes per probe, matches S10 BatchedWritesLarge so the
profile numbers compare directly to the bench TSV. -/
private def N : Nat := 512

/-- The fixture indexer, same shape as S10's loop. -/
@[inline] private def idxOf (i : Nat) : Nat := i % 256

/-- Build the post-update *pure* value: 512 record-updates over
the `validators` vector. Used by P3 / P5. -/
@[inline] private def buildPureFinal (salt : UInt8) : ValidatorSet256 := Id.run do
  let mut s := mkValidatorSet256 salt
  for i in [:N] do
    let idx := idxOf i
    let oldV := s.validators[idx]!
    let newV : ValidatorShape :=
      { oldV with effectiveBalance := UInt64.ofNat (i + 1) }
    s := { s with validators := s.validators.set! idx newV }
  return s

/-- Build the post-update *cached* box: 512 `sszUpdate` clauses
that accumulate in the pending overlay. Used by P4 / P6 / P7 / P8. -/
@[inline] private def buildCachedFinal (salt : UInt8) : SSZ.Box Sha256 ValidatorSet256 := Id.run do
  let mut box : SSZ.Box Sha256 ValidatorSet256 :=
    SSZ.FastBox (mkValidatorSet256 salt)
  for i in [:N] do
    let idx := idxOf i
    let oldV := box.view.validators[idx]!
    let newV : ValidatorShape :=
      { oldV with effectiveBalance := UInt64.ofNat (i + 1) }
    box := sszUpdate box with validators[idx]! := newV
  return box

/-- Sink the post-state's first-validator effective balance,
defeats DCE on probes that don't compute hashes. -/
@[inline] private def sinkFirstField (sink : IO.Ref Nat) (s : ValidatorSet256) : IO Unit :=
  sink.modify (· + s.validators[0]!.effectiveBalance.toNat)

private def sinkBoxFirstField (sink : IO.Ref Nat) (box : SSZ.Box Sha256 ValidatorSet256) : IO Unit :=
  sink.modify (· + box.view.validators[0]!.effectiveBalance.toNat)

/-! ## Probes -/

private def p1_buildOnly (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidatorSet256 salt
  sinkFirstField sink v

private def p2_buildAndBox (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidatorSet256 salt
  let box := SSZ.FastBox v
  sinkBoxFirstField sink box

private def p3_pureUpdates (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let s := buildPureFinal salt
  sinkFirstField sink s

private def p4_cachedUpdates (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let box := buildCachedFinal salt
  sinkBoxFirstField sink box

private def p5_pureFull (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let s := buildPureFinal salt
  sink.modify (· + consume (SSZ.hashTreeRoot Sha256 s))

private def p6_cachedFull (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let box := buildCachedFinal salt
  sink.modify (· + consume box.hashTreeRoot.1)

/-- P7 reaches into the cached `TreeBacked` after the 512
`sszUpdate`s, pulls `pending` out, runs `Node.setManyAt` over
it, and sinks the committed tree's *leaf-count parity* (a tiny
recursive walk that prevents DCE without invoking the hasher).
This is the commit walk on its own.

The match on `Box.cached` is exhaustive in practice because
`SSZ.FastBox` produces the cached arm; the `uncached` branch is
defensive. -/
private def sinkNodeShape (sink : IO.Ref Nat) : Node → IO Unit
  | .leaf b      => sink.modify (· + b.size)
  | .pair l r _  => do
      sinkNodeShape sink l
      sinkNodeShape sink r

/-- P7 measures the cached commit (setManyAt) only. Extract
pending, materialise via Node.ofShape, walk setManyAt, sink the
resulting committed tree's structure (no merkleRoot work). -/
private def p7_cachedCommitOnly (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let box := buildCachedFinal salt
  match box with
  | .cached t =>
      let updates := t.pending.toList.filterMap fun (g, d) =>
        (d t.view).map fun n => (gindexBits g, n)
      let committed := t.treeBase.get.setManyAt updates
      sinkNodeShape sink committed
  | .uncached _ => sink.modify (· + 1)

/-- P8 = P7 + `merkleRoot` on the committed tree. Should track
P6 to within noise; mismatches expose a difference between this
manual split and `hashTreeRootCached`'s internal commit + walk. -/
private def p8_cachedSplit (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let box := buildCachedFinal salt
  match box with
  | .cached t =>
      let updates := t.pending.toList.filterMap fun (g, d) =>
        (d t.view).map fun n => (gindexBits g, n)
      let committed := t.treeBase.get.setManyAt updates
      sink.modify (· + consume (committed.merkleRoot Sha256))
  | .uncached _ => sink.modify (· + 1)

/-! ## Driver -/

/-- Run every probe, emit TSV rows. The iteration count is
auto-tuned to land each row near ~200 ms total wall-clock. The
fast probes (P1, P2) run more iterations to amortise the
per-call timer overhead. -/
def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  -- Construction (fast), many iterations.
  runBench "P1 build only                    · ValidatorSet256" 2000 (p1_buildOnly sink 1)
  runBench "P2 build + Box wrap              · ValidatorSet256" 2000 (p2_buildAndBox sink 1)
  -- 512 updates without final hash, medium speed.
  runBench "P3 pure: build + 512 updates     · ValidatorSet256"  500 (p3_pureUpdates sink 1)
  runBench "P4 cached: build + 512 sszUpdate · ValidatorSet256"  500 (p4_cachedUpdates sink 1)
  -- Full cycles, same shape as S10.
  runBench "P5 pure: build + 512 + root      · ValidatorSet256" 200 (p5_pureFull sink 1)
  runBench "P6 cached: build + 512 + root    · ValidatorSet256" 200 (p6_cachedFull sink 1)
  -- Split form, commit only, then commit + hash separately.
  runBench "P7 cached: commit (setManyAt) only · ValidatorSet256" 200 (p7_cachedCommitOnly sink 1)
  runBench "P8 cached: setManyAt + merkleRoot · ValidatorSet256" 200 (p8_cachedSplit sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "Profile sink unexpectedly 0"

end SizzLeanBench.Profile
