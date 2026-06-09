import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLeanBench.Fixtures
import SizzLeanBench.Runner

/-!
# Scenario S4: Cold root, large fixture

A single `hashTreeRoot` on a freshly constructed `ValidatorSet256`
(depth 12, ~36 KB serialised, ~4 K pair hashes). Diagnostic
sentinel for "Box construction + first-walk cost at scale".
Regressions here surface in `ofValue` / `Node.ofShape` /
`merkleRootWithCache` before they confound the multi-write
scenarios (S5, S6).

## Operation sequence (one bench iteration)

```
build value (salted)
sink += consume hashTreeRoot
```

`pure` invokes `SSZ.hashTreeRoot Sha256 v` directly on the
plain value; `cached` constructs an `SSZ.FastBox` and then
calls `box.hashTreeRoot` (forces the Thunk-deferred initial
tree, walks `merkleRootWithCache` filling cache slots).
-/

set_option autoImplicit false

namespace SizzLeanBench.Scenarios.ColdRootLarge

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanBench.Fixtures
open SizzLeanBench.Runner

/-! ### ValidatorSet256 (depth 12, ~36 KB) -/

private def pureValidatorSet256 (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidatorSet256 salt
  let box := SSZ.PureBox v
  sink.modify (· + consume box.hashTreeRoot.1)

private def cachedValidatorSet256 (sink : IO.Ref Nat) (salt : UInt8) : IO Unit := do
  let v := mkValidatorSet256 salt
  let box := SSZ.FastBox v
  sink.modify (· + consume box.hashTreeRoot.1)

def runAll : IO Unit := do
  let sink ← IO.mkRef (0 : Nat)
  runBench "S4 ColdRootLarge · ValidatorSet256 · pure"   50 (pureValidatorSet256 sink 1)
  runBench "S4 ColdRootLarge · ValidatorSet256 · cached" 50 (cachedValidatorSet256 sink 1)
  let total ← sink.get
  if total == 0 then IO.eprintln "S4 sink unexpectedly 0"

end SizzLeanBench.Scenarios.ColdRootLarge
