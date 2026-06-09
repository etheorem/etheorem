import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# Scenario S1: Cold root

The simplest possible workload: build a fresh value, compute
its hash-tree root *once*, throw it away. No reuse, no
follow-up operations.

What this measures: the *baseline wrapper cost*. The cached
column should be slightly slower than pure here. `SSZ.FastBox`
runs `Node.ofShape` on top of (essentially) the same hashing
work pure does. With no follow-up operations there's no
payback.

This row tells the user when *not* to use the library: a piece
of code that only computes a single one-shot root on a fresh
value is faster with plain `T`.

## Operation sequence (one bench iteration)

```
build value (salted)
root := hashTreeRoot          -- one call
sink += consume root
```
-/

set_option autoImplicit false

namespace SizzLeanBench.Scenarios.ColdRoot

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

/-! ### Validator fixture -/

private def pureValidator (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidator salt
  let box := SSZ.PureBox v
  sink.modify (· + consume box.hashTreeRoot.1)

private def cachedValidator (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidator salt
  let box := SSZ.FastBox v
  sink.modify (· + consume box.hashTreeRoot.1)

/-! ### ValidatorSet16 fixture -/

private def pureValidatorSet (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidatorSet salt
  let box := SSZ.PureBox v
  sink.modify (· + consume box.hashTreeRoot.1)

private def cachedValidatorSet (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidatorSet salt
  let box := SSZ.FastBox v
  sink.modify (· + consume box.hashTreeRoot.1)

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  runBench "S1 ColdRoot · Validator    · pure"   1000 (pureValidator sink 1)
  runBench "S1 ColdRoot · Validator    · cached" 1000 (cachedValidator sink 1)
  runBench "S1 ColdRoot · ValidatorSet · pure"    100 (pureValidatorSet sink 1)
  runBench "S1 ColdRoot · ValidatorSet · cached"  100 (cachedValidatorSet sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "S1 sink unexpectedly 0"

end SizzLeanBench.Scenarios.ColdRoot
