import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# Scenario S5, Batched writes, large fixture (pre-root + writes + post-root)

The large-tier parallel of S2, same shape (pre-state root,
N writes, post-state root) at near-mainnet validator-set
size. 512 writes spread across 256 validator slots
(≈ 2 writes/slot, modelling a realistic block where multiple
processing steps touch the same validator's balance/state).

What this measures: **incremental Merkle on top of a cached
tree at scale**. The cached path's post-root walk benefits
from the cell-level cache slots filled by the pre-root walk:
untouched validators keep their cached roots; only the
touched spine (~depth-12 path × N_writes) needs hashing. The
pure path does two full re-hashes of the whole
`ValidatorSet256` (~4 K pair hashes each).

This is the closest single-iteration approximation of one
consensus slot's full work, pre-state root in hand, apply
the block, compute post-state root for the next slot's
parent reference.

## Operation sequence (one bench iteration)

```
build value (salted)
preRoot := hashTreeRoot
sink += consume preRoot
for i in 1..512:
  set validators[i % 256]
postRoot := hashTreeRoot
sink += consume postRoot
```
-/

set_option autoImplicit false

namespace SizzLeanBench.Scenarios.BatchedWritesLarge

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

private def N : Nat := 512

private def pureValidatorSet256 (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet256 :=
    SSZ.PureBox (mkValidatorSet256 salt)
  let (preRoot, b₀) := box.hashTreeRoot
  box := b₀
  sink.modify (· + consume preRoot)
  for i in [:N] do
    let idx : Nat := i % 256
    let oldV := box.view.validators[idx]!
    let newV : ValidatorShape :=
      { oldV with effectiveBalance := UInt64.ofNat (i + 1) }
    box := sszUpdate box with validators[idx] := newV
  sink.modify (· + consume box.hashTreeRoot.1)

private def cachedValidatorSet256 (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet256 :=
    SSZ.FastBox (mkValidatorSet256 salt)
  let (preRoot, b₀) := box.hashTreeRoot
  box := b₀
  sink.modify (· + consume preRoot)
  for i in [:N] do
    let idx : Nat := i % 256
    let oldV := box.view.validators[idx]!
    let newV : ValidatorShape :=
      { oldV with effectiveBalance := UInt64.ofNat (i + 1) }
    box := sszUpdate box with validators[idx] := newV
  sink.modify (· + consume box.hashTreeRoot.1)

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  runBench s!"S5 BatchedWritesLarge ({N} writes, 1 read) · ValidatorSet256 · pure"   30 (pureValidatorSet256 sink 1)
  runBench s!"S5 BatchedWritesLarge ({N} writes, 1 read) · ValidatorSet256 · cached" 30 (cachedValidatorSet256 sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "S5 sink unexpectedly 0"

end SizzLeanBench.Scenarios.BatchedWritesLarge
