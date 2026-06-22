import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# Scenario S6: Block processing, large fixture

The large-tier parallel of S6: process many blocks against a
large fixture. Each block applies a batch of mutations, then
takes one root, then serialises once.

What this measures: **the most realistic compounded shape at
scale**. 32 blocks × 8 mutations per block on
`ValidatorSet256` produces 256 total writes, coincidentally
matching one mutation per validator slot, and 32 (root,
serialise) pairs. The cached path's per-block cost is the
overlay-commit + spine-walk + Thunk-force for the root, plus
the bytes-Thunk-force for the serialise (each block forces a
fresh bytes Thunk because each block has a different view).
The pure path does 8 record updates + 1 full re-hash + 1 spec
serialise per block.

This row is where production consensus-state-transition code
lands on the bench grid at scale. The cached/pure ratio here
is the best single-number predictor of the real-world cache win.

## Operation sequence (one bench iteration)

```
build value (salted)
for block in 1..32:
  for j in 1..8:
    set <some field by (block, j)>
  sink += consume hashTreeRoot
  sink += consume serialize
```
-/

set_option autoImplicit false

namespace SizzLeanBench.Scenarios.BlockProcessingLarge

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

private def BLOCKS : Nat := 32
private def MUTATIONS_PER_BLOCK : Nat := 8

private def pureValidatorSet256 (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet256 :=
    SSZ.PureBox (mkValidatorSet256 salt)
  for block in [:BLOCKS] do
    for j in [:MUTATIONS_PER_BLOCK] do
      let idx : Nat := (block * MUTATIONS_PER_BLOCK + j) % 256
      let mark := UInt64.ofNat (block * MUTATIONS_PER_BLOCK + j + 1)
      let oldV := box.view.validators[idx]!
      let newV : ValidatorShape := { oldV with effectiveBalance := mark }
      box := sszUpdate box with validators[idx]! := newV
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
    sink.modify (· + consume box.serialize)

private def cachedValidatorSet256 (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let mut box : SSZ.Box Sha256 ValidatorSet256 :=
    SSZ.FastBox (mkValidatorSet256 salt)
  for block in [:BLOCKS] do
    for j in [:MUTATIONS_PER_BLOCK] do
      let idx : Nat := (block * MUTATIONS_PER_BLOCK + j) % 256
      let mark := UInt64.ofNat (block * MUTATIONS_PER_BLOCK + j + 1)
      let oldV := box.view.validators[idx]!
      let newV : ValidatorShape := { oldV with effectiveBalance := mark }
      box := sszUpdate box with validators[idx]! := newV
    let (root, b₁) := box.hashTreeRoot
    box := b₁
    sink.modify (· + consume root)
    sink.modify (· + consume box.serialize)

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  runBench s!"S6 BlockProcessingLarge ({BLOCKS} blocks × {MUTATIONS_PER_BLOCK} writes) · ValidatorSet256 · pure"   20 (pureValidatorSet256 sink 1)
  runBench s!"S6 BlockProcessingLarge ({BLOCKS} blocks × {MUTATIONS_PER_BLOCK} writes) · ValidatorSet256 · cached" 20 (cachedValidatorSet256 sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "S6 sink unexpectedly 0"

end SizzLeanBench.Scenarios.BlockProcessingLarge
