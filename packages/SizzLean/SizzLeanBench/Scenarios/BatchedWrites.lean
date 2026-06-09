import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# Scenario S2: Batched writes (pre-root + writes + post-root)

The block-processing shape: compute the *pre-state* root, apply
32 mutations, compute the *post-state* root. Models a consensus
client receiving a block whose pre-state it already has rooted
(slot N-1's final root = slot N's pre-state root), applying the
block's mutations, then computing the post-state root for
inclusion in the next slot's block header.

What this measures: the **cache layer's advantage on the
post-root walk**. On the cached path:

1. Pre-root forces the Thunk, materialises the initial tree,
   fills cache slots, returns `(root, box')` with
   `treeBase = Thunk.pure cachedTree`.
2. 32 `sszUpdate`s accumulate in `pending` *on top of* the
   already-cache-filled tree.
3. Post-root commits via `setManyAt` over the cached tree,
   untouched subtrees keep their cached `(some r)` slots, so
   only the touched spine + new subtrees need re-hashing.

The pure path (`PureBox`) does 2 full `SSZ.hashTreeRoot` walks
end-to-end (no incremental Merkle). On a workload where most
of the tree is untouched, the cached path's incremental walk
in step 3 is where the win lives.

## Operation sequence (one bench iteration)

```
build value (salted)
preRoot := hashTreeRoot
sink += consume preRoot
for i in 1..32:
  set effectiveBalance := i        (or validators[i % 16])
postRoot := hashTreeRoot
sink += consume postRoot
```
-/

set_option autoImplicit false

namespace SizzLeanBench.Scenarios.BatchedWrites

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

private def N : Nat := 32

/-! ### Validator fixture -/

private def pureValidator (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorShape :=
    SSZ.PureBox (mkValidator salt)
  let (preRoot, b₀) := box.hashTreeRoot
  box := b₀
  sink.modify (· + consume preRoot)
  for i in [:N] do
    box := sszUpdate box with effectiveBalance := UInt64.ofNat (i + 1)
  sink.modify (· + consume box.hashTreeRoot.1)

private def cachedValidator (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorShape :=
    SSZ.FastBox (mkValidator salt)
  let (preRoot, b₀) := box.hashTreeRoot
  box := b₀
  sink.modify (· + consume preRoot)
  for i in [:N] do
    box := sszUpdate box with effectiveBalance := UInt64.ofNat (i + 1)
  sink.modify (· + consume box.hashTreeRoot.1)

/-! ### ValidatorSet16 fixture: writes spread across the
16 validator positions (each mutated twice across N=32). -/

private def pureValidatorSet (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet16 :=
    SSZ.PureBox (mkValidatorSet salt)
  let (preRoot, b₀) := box.hashTreeRoot
  box := b₀
  sink.modify (· + consume preRoot)
  for i in [:N] do
    let idx : Nat := i % 16
    let oldV := box.view.validators[idx]!
    let newV : ValidatorShape :=
      { oldV with effectiveBalance := UInt64.ofNat (i + 1) }
    box := sszUpdate box with validators[idx] := newV
  sink.modify (· + consume box.hashTreeRoot.1)

private def cachedValidatorSet (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet16 :=
    SSZ.FastBox (mkValidatorSet salt)
  let (preRoot, b₀) := box.hashTreeRoot
  box := b₀
  sink.modify (· + consume preRoot)
  for i in [:N] do
    let idx : Nat := i % 16
    let oldV := box.view.validators[idx]!
    let newV : ValidatorShape :=
      { oldV with effectiveBalance := UInt64.ofNat (i + 1) }
    box := sszUpdate box with validators[idx] := newV
  sink.modify (· + consume box.hashTreeRoot.1)

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  runBench s!"S2 BatchedWrites ({N} writes, 1 read) · Validator    · pure"   500 (pureValidator sink 1)
  runBench s!"S2 BatchedWrites ({N} writes, 1 read) · Validator    · cached" 500 (cachedValidator sink 1)
  runBench s!"S2 BatchedWrites ({N} writes, 1 read) · ValidatorSet · pure"   100 (pureValidatorSet sink 1)
  runBench s!"S2 BatchedWrites ({N} writes, 1 read) · ValidatorSet · cached" 100 (cachedValidatorSet sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "S2 sink unexpectedly 0"

end SizzLeanBench.Scenarios.BatchedWrites
