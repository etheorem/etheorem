import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# Scenario S3: Block processing

The realistic mixed workload. Eight "block" cycles; each cycle
mutates four fields, then takes one root, then serialises once.
Models a chain processing eight consecutive blocks, where each
block applies a small batch of state-transition mutations and
broadcasts its post-block state.

What this measures: the **combined wins across realistic
mixed shape**. Each block-cycle:

* The 4 mutations accumulate in the pending overlay; the single
  `box.hashTreeRoot` at the end commits them in one walk
  (cross-statement batching).
* The block's serialise call is on a fresh post-mutation Box,
  so the bytes Thunk is forced once that block; the win comes
  from the absence of a re-walk of the tree (each block has a
  different view, so the bytes memo does not apply): `SSZ.serialize`
  on plain T does its own pass; the cached path goes through
  the same `SSZ.serialize` but on the already-current view).

Pure does 4 record updates + 1 full re-hash + 1 spec serialise
per block.

This is the most realistic row in the suite. It's where
production consensus-state-transition code lands on the
bench grid.

## Operation sequence (one bench iteration)

```
build value (salted)
for block in 1..8:
  for j in 1..4:
    set <some field by (block, j)>
  sink += consume hashTreeRoot
  sink += consume serialize
```
-/

set_option autoImplicit false

namespace SizzLeanBench.Scenarios.BlockProcessing

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

private def BLOCKS : Nat := 8
private def MUTATIONS_PER_BLOCK : Nat := 4

/-! ### Validator fixture -/

private def pureValidator (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorShape :=
    SSZ.PureBox (mkValidator salt)
  for block in [:BLOCKS] do
    for j in [:MUTATIONS_PER_BLOCK] do
      let mark := UInt64.ofNat (block * MUTATIONS_PER_BLOCK + j + 1)
      box := sszUpdate box with effectiveBalance := mark
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
    sink.modify (· + consume box.serialize)

private def cachedValidator (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorShape :=
    SSZ.FastBox (mkValidator salt)
  for block in [:BLOCKS] do
    for j in [:MUTATIONS_PER_BLOCK] do
      let mark := UInt64.ofNat (block * MUTATIONS_PER_BLOCK + j + 1)
      box := sszUpdate box with effectiveBalance := mark
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
    sink.modify (· + consume box.serialize)

/-! ### ValidatorSet16 fixture: each block's 4 mutations hit
different validator positions, so each block touches 4 of the
16 slots before its root read. -/

private def pureValidatorSet (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet16 :=
    SSZ.PureBox (mkValidatorSet salt)
  for block in [:BLOCKS] do
    for j in [:MUTATIONS_PER_BLOCK] do
      let idx : Nat := (block * MUTATIONS_PER_BLOCK + j) % 16
      let mark := UInt64.ofNat (block * MUTATIONS_PER_BLOCK + j + 1)
      let oldV := box.view.validators[idx]!
      let newV : ValidatorShape := { oldV with effectiveBalance := mark }
      box := sszUpdate box with validators[idx] := newV
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
    sink.modify (· + consume box.serialize)

private def cachedValidatorSet (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet16 :=
    SSZ.FastBox (mkValidatorSet salt)
  for block in [:BLOCKS] do
    for j in [:MUTATIONS_PER_BLOCK] do
      let idx : Nat := (block * MUTATIONS_PER_BLOCK + j) % 16
      let mark := UInt64.ofNat (block * MUTATIONS_PER_BLOCK + j + 1)
      let oldV := box.view.validators[idx]!
      let newV : ValidatorShape := { oldV with effectiveBalance := mark }
      box := sszUpdate box with validators[idx] := newV
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
    sink.modify (· + consume box.serialize)

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  runBench s!"S3 BlockProcessing ({BLOCKS} blocks × {MUTATIONS_PER_BLOCK} writes) · Validator    · pure"   200 (pureValidator sink 1)
  runBench s!"S3 BlockProcessing ({BLOCKS} blocks × {MUTATIONS_PER_BLOCK} writes) · Validator    · cached" 200 (cachedValidator sink 1)
  runBench s!"S3 BlockProcessing ({BLOCKS} blocks × {MUTATIONS_PER_BLOCK} writes) · ValidatorSet · pure"    50 (pureValidatorSet sink 1)
  runBench s!"S3 BlockProcessing ({BLOCKS} blocks × {MUTATIONS_PER_BLOCK} writes) · ValidatorSet · cached"  50 (cachedValidatorSet sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "S3 sink unexpectedly 0"

end SizzLeanBench.Scenarios.BlockProcessing
